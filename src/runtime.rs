//! Contains the runtime for Brainfuck and a simple interpreter.

use std::{
    alloc::{alloc_zeroed, dealloc, Layout},
    io::{stdin, stdout, Read, Write},
    ptr,
};

/// Context for the Brainfuck execution environment.
#[repr(C)]
pub struct Context<'a> {
    mem_low: *mut u8,
    mem_high: *mut u8,
    mem_ptr: *mut u8,
    input: Option<Box<dyn Read + 'a>>,
    output: Option<Box<dyn Write + 'a>>,
}

impl<'a> Context<'a> {
    /// Create a new context for executing a Brainfuck program.
    pub fn new(input: Option<Box<dyn Read + 'a>>, output: Option<Box<dyn Write + 'a>>) -> Self {
        Context {
            mem_low: ptr::null_mut(),
            mem_high: ptr::null_mut(),
            mem_ptr: ptr::null_mut(),
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

    /// Move the current pointer. No memory will be allocated.
    pub fn mov(&mut self, offset: isize) {
        self.mem_ptr = self.mem_ptr.wrapping_offset(offset);
    }

    /// Read from the given offset from the current pointer. Reading from
    /// outside the currently allocated memory buffer will not allocate new
    /// memory, but immediately return zero.
    pub fn read(&self, offset: isize) -> u8 {
        let ptr = self.mem_ptr.wrapping_offset(offset);
        if self.mem_low <= ptr && ptr < self.mem_high {
            // SAFETY: The area from `mem_low` to `mem_high` can safely be accessed.
            unsafe { ptr.read() }
        } else {
            0
        }
    }

    fn make_accessible(&mut self, min: isize, max: isize) {
        let old_size = self.mem_high as isize - self.mem_low as isize;
        let old_ptr = self.mem_ptr as isize - self.mem_low as isize;
        let min_ptr = old_ptr + min;
        let max_ptr = old_ptr + max + 1;
        let needed_below = if min_ptr < 0 { min_ptr.abs() } else { 0 };
        let needed_above = if max_ptr > old_size {
            max_ptr - old_size
        } else {
            0
        };
        if needed_below == 0 && needed_above == 0 {
            // No resize is needed.
            return;
        }
        let new_size = old_size + (old_size / 2).max(needed_below + needed_above);
        let added_below = match (needed_below, needed_above) {
            (0, _) => 0,
            (_, 0) => new_size - old_size,
            (_, _) => (new_size - old_size) / 2,
        };
        let new_layout = Layout::array::<u8>(new_size as usize).unwrap();
        // SAFETY: Layout is never zero-sized.
        let new_buffer = unsafe { alloc_zeroed(new_layout) };
        if old_size != 0 {
            // SAFETY: If the old size is non-zero, the old region is valid.
            unsafe {
                self.mem_low
                    .copy_to_nonoverlapping(new_buffer.offset(added_below), old_size as usize);
                let old_layout = Layout::array::<u8>(old_size as usize).unwrap();
                dealloc(self.mem_low, old_layout);
            }
        }
        self.mem_low = new_buffer;
        self.mem_ptr = new_buffer.wrapping_offset(old_ptr + added_below);
        // SAFETY: The result will be one byte past the allocation.
        self.mem_high = unsafe { new_buffer.offset(new_size) };
    }

    #[cold]
    fn write_out_of_bounds(&mut self, offset: isize, value: u8) {
        self.make_accessible(offset, offset);
        let ptr = self.mem_ptr.wrapping_offset(offset);
        // SAFETY: `make_accessible` ensures that `ptr` can be written safely.
        unsafe { ptr.write(value) }
    }

    /// Write to the given offset from the current pointer. If the currently
    /// allocated memory buffer is exceeded, new memory will be allocated.
    pub fn write(&mut self, offset: isize, value: u8) {
        let ptr = self.mem_ptr.wrapping_offset(offset);
        if self.mem_low <= ptr && ptr < self.mem_high {
            // SAFETY: The area from `mem_low` to `mem_high` can safely be accessed.
            unsafe { ptr.write(value) }
        } else {
            self.write_out_of_bounds(offset, value);
        }
    }

    /// Input one byte from standard input.
    pub fn input(&mut self) -> u8 {
        let mut result = [0];
        if let Some(input) = &mut self.input {
            input.read(&mut result).ok();
        }
        result[0]
    }

    /// Output one byte to standard output.
    pub fn output(&mut self, value: u8) {
        if let Some(output) = &mut self.output {
            output.write(&[value]).ok();
        }
    }
}

impl<'a> Drop for Context<'a> {
    fn drop(&mut self) {
        let old_size = self.mem_high as usize - self.mem_low as usize;
        if old_size != 0 {
            // SAFETY: If the old size is non-zero, the old region is valid.
            unsafe {
                let old_layout = Layout::array::<u8>(old_size).unwrap();
                dealloc(self.mem_low, old_layout);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Context;

    #[test]
    fn reading_unused_cells_return_zero() {
        let ctx = Context::without_io();
        assert_eq!(ctx.read(0), 0);
        assert_eq!(ctx.read(1), 0);
        assert_eq!(ctx.read(100), 0);
        assert_eq!(ctx.read(-1), 0);
        assert_eq!(ctx.read(-100), 0);
    }

    #[test]
    fn initial_cell_reads_written_value() {
        let mut ctx = Context::without_io();
        ctx.write(0, 100);
        assert_eq!(ctx.read(0), 100);
    }

    #[test]
    fn positive_cell_reads_written_value() {
        let mut ctx = Context::without_io();
        ctx.write(100, 42);
        assert_eq!(ctx.read(100), 42);
    }

    #[test]
    fn negative_cell_reads_written_value() {
        let mut ctx = Context::without_io();
        ctx.write(-100, 42);
        assert_eq!(ctx.read(-100), 42);
    }

    #[test]
    fn resizes_preserve_pointer() {
        let mut ctx = Context::without_io();
        ctx.write(-100, 1);
        assert_eq!(ctx.read(-100), 1);
        ctx.write(100, 2);
        assert_eq!(ctx.read(-100), 1);
        assert_eq!(ctx.read(100), 2);
        ctx.write(-10000, 3);
        assert_eq!(ctx.read(-100), 1);
        assert_eq!(ctx.read(100), 2);
        assert_eq!(ctx.read(-10000), 3);
        ctx.write(10000, 4);
        assert_eq!(ctx.read(-100), 1);
        assert_eq!(ctx.read(100), 2);
        assert_eq!(ctx.read(-10000), 3);
        assert_eq!(ctx.read(10000), 4);
    }

    #[test]
    fn pointer_movements_affect_read_and_write() {
        let mut ctx = Context::without_io();
        ctx.mov(-100);
        ctx.write(0, 1);
        assert_eq!(ctx.read(0), 1);
        ctx.mov(200);
        ctx.write(0, 2);
        assert_eq!(ctx.read(-200), 1);
        assert_eq!(ctx.read(0), 2);
        ctx.mov(-10100);
        ctx.write(0, 3);
        assert_eq!(ctx.read(9900), 1);
        assert_eq!(ctx.read(10100), 2);
        assert_eq!(ctx.read(0), 3);
        ctx.mov(20000);
        ctx.write(0, 4);
        assert_eq!(ctx.read(-10100), 1);
        assert_eq!(ctx.read(-9900), 2);
        assert_eq!(ctx.read(-20000), 3);
        assert_eq!(ctx.read(0), 4);
    }

    #[test]
    fn output_writes_to_output() {
        let mut buf = Vec::new();
        let mut ctx = Context::new(None, Some(Box::new(&mut buf)));
        ctx.output(42);
        ctx.output(1);
        ctx.output(3);
        drop(ctx);
        assert_eq!(&buf, &[42, 1, 3]);
    }

    #[test]
    fn input_reads_from_input() {
        let buf = vec![42, 1, 3];
        let mut ctx = Context::new(Some(Box::new(buf.as_slice())), None);
        assert_eq!(ctx.input(), 42);
        assert_eq!(ctx.input(), 1);
        assert_eq!(ctx.input(), 3);
    }
}
