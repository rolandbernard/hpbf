//! Contains the runtime for Brainfuck and a simple interpreter.

use std::{
    alloc::{alloc_zeroed, dealloc, Layout},
    io::{stdin, stdout, Read, Write},
    mem, ptr,
};

use crate::CellType;

/// Memory context for the Brainfuck program. This acts as an unbounded array of
/// cells each containing an value of type `C` initialized to zero. The memory
/// is bounds checked and will automatically grow in either direction.
#[repr(C)]
pub struct Memory<C: CellType> {
    // Do not change the order or position of the these fields. They are
    // used by the code generated in the jit compiler.
    buffer: *mut C,
    size: usize,
    offset: usize,
}

/// Context for the Brainfuck execution environment.
#[repr(C)]
pub struct Context<'a, C: CellType> {
    // Do not change the order or position of the three first fields. They are
    // used by the code generated in the jit compiler.
    pub memory: Memory<C>,
    input: Option<Box<dyn Read + 'a>>,
    output: Option<Box<dyn Write + 'a>>,
}

impl<C: CellType> Memory<C> {
    /// Create a new memory. All values are initially set to `C::ZERO`.
    pub fn new() -> Self {
        Memory {
            buffer: ptr::null_mut(),
            size: 0,
            offset: 0,
        }
    }

    /// Returns a pointer to the current location in the buffer. Requesting the
    /// buffer does not mean that the memory located at the returned address is
    /// actually accessible. To ensure the pointer points to valid memory,
    /// call [`Self::make_accessible`] beforehand.
    pub fn current_ptr(&self) -> *mut C {
        self.buffer.wrapping_add(self.offset)
    }

    /// Move the current pointer. No memory will be allocated.
    pub fn mov(&mut self, offset: isize) {
        self.offset = self.offset.wrapping_add_signed(offset);
    }

    /// Move the current pointer. No memory will be allocated.
    pub fn set_current_ptr(&mut self, ptr: *mut C) {
        self.offset = ((ptr as isize).wrapping_sub(self.buffer as isize)
            / mem::size_of::<C>() as isize) as usize;
    }

    /// Read from the given offset from the current pointer. Reading from
    /// outside the currently allocated memory buffer will not allocate new
    /// memory, but immediately return zero.
    pub fn read(&self, offset: isize) -> C {
        let ptr = self.offset.wrapping_add_signed(offset);
        if ptr < self.size {
            // Safety: The area from `memory` can safely be accessed up to `size`.
            unsafe { *self.buffer.add(ptr) }
        } else {
            C::ZERO
        }
    }

    /// Make sure that subsequent calls to [`Self::read`] and [`Self::write`] will
    /// not cause a bounds check failure for offsets in the range `start..end`.
    #[cold]
    pub fn make_accessible(&mut self, start: isize, end: isize) {
        let start_ptr = (self.offset as isize).wrapping_add(start);
        let end_ptr = (self.offset as isize).wrapping_add(end);
        let needed_below = if start_ptr < 0 {
            start_ptr.abs() as usize
        } else {
            0
        };
        let needed_above = if end_ptr > self.size as isize {
            (end_ptr - self.size as isize) as usize
        } else {
            0
        };
        if needed_below == 0 && needed_above == 0 {
            // No resize is needed.
            return;
        }
        let new_size = self.size + (self.size / 2).max(needed_below + needed_above);
        let added_below = match (needed_below, needed_above) {
            (0, _) => 0,
            (_, 0) => new_size - self.size,
            (_, _) => needed_below
                .max((new_size - self.size) / 2)
                .min(new_size - self.size - needed_above),
        };
        let new_layout = Layout::array::<C>(new_size).unwrap();
        // Safety: Layout is never zero-sized.
        let new_buffer = unsafe { alloc_zeroed(new_layout) as *mut C };
        if self.size != 0 {
            // Safety: If the old size is non-zero, the old region is valid.
            unsafe {
                self.buffer
                    .copy_to_nonoverlapping(new_buffer.wrapping_add(added_below), self.size);
                let old_layout = Layout::array::<C>(self.size).unwrap();
                dealloc(self.buffer as *mut u8, old_layout);
            }
        }
        self.buffer = new_buffer;
        self.size = new_size;
        self.offset = self.offset.wrapping_add(added_below);
    }

    #[cold]
    fn write_out_of_bounds(&mut self, offset: isize, value: C) {
        self.make_accessible(offset, offset + 1);
        let ptr = self.offset.wrapping_add_signed(offset);
        // Safety: `make_accessible` ensures that `ptr` can be written safely.
        unsafe { *self.buffer.add(ptr) = value };
    }

    /// Write to the given offset from the current pointer. If the currently
    /// allocated memory buffer is exceeded, new memory will be allocated.
    pub fn write(&mut self, offset: isize, value: C) {
        let ptr = self.offset.wrapping_add_signed(offset);
        if ptr < self.size {
            // Safety: The area from `memory` can safely be accessed up to `size`.
            unsafe { *self.buffer.add(ptr) = value };
        } else {
            self.write_out_of_bounds(offset, value);
        }
    }

    /// Test whether the given offset can be accessed without having to resize.
    pub fn check(&mut self, offset: isize) -> bool {
        self.offset.wrapping_add_signed(offset) < self.size
    }

    /// Test whether the given pointer can be accessed without having to resize.
    pub fn check_ptr(&mut self, ptr: *mut C) -> bool {
        ((ptr as usize).wrapping_sub(self.buffer as usize) / mem::size_of::<C>()) < self.size
    }
}

impl<'a, C: CellType> Context<'a, C> {
    /// Create a new context for executing a Brainfuck program.
    pub fn new(input: Option<Box<dyn Read + 'a>>, output: Option<Box<dyn Write + 'a>>) -> Self {
        Context {
            memory: Memory::new(),
            input,
            output,
        }
    }

    /// Create a new context that uses standard input and output.
    pub fn with_stdio() -> Self {
        Self::new(Some(Box::new(stdin())), Some(Box::new(stdout())))
    }

    /// Create a new context that does not have any input or output.
    pub fn without_io() -> Self {
        Self::new(None, None)
    }

    /// Input one byte from standard input.
    #[cold]
    pub fn input(&mut self) -> Option<u8> {
        if let Some(input) = &mut self.input {
            let mut result = [0];
            input.read(&mut result).ok()?;
            Some(result[0])
        } else {
            None
        }
    }

    /// Output one byte to standard output.
    #[cold]
    pub fn output(&mut self, value: u8) -> Option<()> {
        if let Some(output) = &mut self.output {
            match output.write(&[value]) {
                Ok(0) => None,
                Err(_) => None,
                _ => Some(()),
            }
        } else {
            Some(())
        }
    }
}

impl<C: CellType> Drop for Memory<C> {
    fn drop(&mut self) {
        if self.size != 0 {
            // Safety: If the old size is non-zero, the old region is valid.
            unsafe {
                let old_layout = Layout::array::<C>(self.size).unwrap();
                dealloc(self.buffer as *mut u8, old_layout);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{runtime::Context, runtime::Memory};

    #[test]
    fn reading_unused_cells_return_zero() {
        let mem = Memory::<u8>::new();
        assert_eq!(mem.read(0), 0);
        assert_eq!(mem.read(1), 0);
        assert_eq!(mem.read(100), 0);
        assert_eq!(mem.read(-1), 0);
        assert_eq!(mem.read(-100), 0);
    }

    #[test]
    fn initial_cell_reads_written_value() {
        let mut mem = Memory::<u8>::new();
        mem.write(0, 100);
        assert_eq!(mem.read(0), 100);
    }

    #[test]
    fn positive_cell_reads_written_value() {
        let mut mem = Memory::<u8>::new();
        mem.write(100, 42);
        assert_eq!(mem.read(100), 42);
    }

    #[test]
    fn negative_cell_reads_written_value() {
        let mut mem = Memory::<u8>::new();
        mem.write(-100, 42);
        assert_eq!(mem.read(-100), 42);
    }

    #[test]
    fn resizes_preserve_pointer() {
        let mut mem = Memory::<u8>::new();
        mem.write(-100, 1);
        assert_eq!(mem.read(-100), 1);
        mem.write(100, 2);
        assert_eq!(mem.read(-100), 1);
        assert_eq!(mem.read(100), 2);
        mem.write(-10000, 3);
        assert_eq!(mem.read(-100), 1);
        assert_eq!(mem.read(100), 2);
        assert_eq!(mem.read(-10000), 3);
        mem.write(10000, 4);
        assert_eq!(mem.read(-100), 1);
        assert_eq!(mem.read(100), 2);
        assert_eq!(mem.read(-10000), 3);
        assert_eq!(mem.read(10000), 4);
    }

    #[test]
    fn pointer_movements_affect_read_and_write() {
        let mut mem = Memory::<u8>::new();
        mem.mov(-100);
        mem.write(0, 1);
        assert_eq!(mem.read(0), 1);
        mem.mov(200);
        mem.write(0, 2);
        assert_eq!(mem.read(-200), 1);
        assert_eq!(mem.read(0), 2);
        mem.mov(-10100);
        mem.write(0, 3);
        assert_eq!(mem.read(9900), 1);
        assert_eq!(mem.read(10100), 2);
        assert_eq!(mem.read(0), 3);
        mem.mov(20000);
        mem.write(0, 4);
        assert_eq!(mem.read(-10100), 1);
        assert_eq!(mem.read(-9900), 2);
        assert_eq!(mem.read(-20000), 3);
        assert_eq!(mem.read(0), 4);
    }

    #[test]
    fn output_writes_to_output() {
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
        ctx.output(42).unwrap();
        ctx.output(1).unwrap();
        ctx.output(3).unwrap();
        drop(ctx);
        assert_eq!(&buf, &[42, 1, 3]);
    }

    #[test]
    fn input_reads_from_input() {
        let buf = vec![42, 1, 3];
        let mut ctx = Context::<u8>::new(Some(Box::new(buf.as_slice())), None);
        assert_eq!(ctx.input(), Some(42));
        assert_eq!(ctx.input(), Some(1));
        assert_eq!(ctx.input(), Some(3));
    }
}
