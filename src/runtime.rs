//! Contains the runtime for Brainfuck and a simple interpreter.

use std::{
    alloc::{alloc_zeroed, dealloc, Layout}, io::{stdin, stdout, Read, Write}, mem, process::exit, ptr
};

use crate::{Block, CellType, Instr};

/// Context for the Brainfuck execution environment.
#[repr(C)]
pub struct Context<'a, C: CellType> {
    // Do not change the order or position of the three first fields. They are
    // used by the code generated in the jit compiler.
    mem_low: *mut C,
    mem_high: *mut C,
    mem_ptr: *mut C,
    input: Option<Box<dyn Read + 'a>>,
    output: Option<Box<dyn Write + 'a>>,
}

impl<'a, C: CellType> Context<'a, C> {
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
    pub fn read(&self, offset: isize) -> C {
        let ptr = self.mem_ptr.wrapping_offset(offset);
        if self.mem_low <= ptr && ptr < self.mem_high {
            // SAFETY: The area from `mem_low` to `mem_high` can safely be accessed.
            unsafe { ptr.read() }
        } else {
            C::ZERO
        }
    }

    pub fn make_accessible(&mut self, start: isize, end: isize) {
        let old_size =
            (self.mem_high as isize - self.mem_low as isize) / mem::size_of::<C>() as isize;
        let old_ptr =
            (self.mem_ptr as isize - self.mem_low as isize) / mem::size_of::<C>() as isize;
        let min_ptr = old_ptr + start;
        let max_ptr = old_ptr + end;
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
            (_, _) => needed_below
                .max((new_size - old_size) / 2)
                .min(new_size - old_size - needed_above),
        };
        let new_layout = Layout::array::<C>(new_size as usize).unwrap();
        // SAFETY: Layout is never zero-sized.
        let new_buffer = unsafe { alloc_zeroed(new_layout) as *mut C };
        if old_size != 0 {
            // SAFETY: If the old size is non-zero, the old region is valid.
            unsafe {
                self.mem_low
                    .copy_to_nonoverlapping(new_buffer.offset(added_below), old_size as usize);
                let old_layout = Layout::array::<C>(old_size as usize).unwrap();
                dealloc(self.mem_low as *mut u8, old_layout);
            }
        }
        self.mem_low = new_buffer;
        self.mem_ptr = new_buffer.wrapping_offset(old_ptr + added_below);
        // SAFETY: The result will be one byte past the allocation.
        self.mem_high = unsafe { new_buffer.offset(new_size) };
    }

    #[cold]
    fn write_out_of_bounds(&mut self, offset: isize, value: C) {
        self.make_accessible(offset, offset + 1);
        let ptr = self.mem_ptr.wrapping_offset(offset);
        // SAFETY: `make_accessible` ensures that `ptr` can be written safely.
        unsafe { ptr.write(value) }
    }

    /// Write to the given offset from the current pointer. If the currently
    /// allocated memory buffer is exceeded, new memory will be allocated.
    pub fn write(&mut self, offset: isize, value: C) {
        let ptr = self.mem_ptr.wrapping_offset(offset);
        if self.mem_low <= ptr && ptr < self.mem_high {
            // SAFETY: The area from `mem_low` to `mem_high` can safely be accessed.
            unsafe { ptr.write(value) }
        } else {
            self.write_out_of_bounds(offset, value);
        }
    }

    /// Input one byte from standard input.
    #[cold]
    pub fn input(&mut self) -> u8 {
        let mut result = [0];
        if let Some(input) = &mut self.input {
            if input.read(&mut result).is_err() {
                exit(1);
            }
        }
        result[0]
    }

    /// Output one byte to standard output.
    #[cold]
    pub fn output(&mut self, value: u8) {
        if let Some(output) = &mut self.output {
            match output.write(&[value]) {
                Ok(0) => exit(0),
                Err(_) => exit(1),
                _ => { /* Everything is ok. */ }
            }
        }
    }
}

impl<'a, C: CellType> Context<'a, C> {
    /// Interpreter based execution engine for Brainfuck.
    pub fn execute(&mut self, program: &Block<C>) {
        for instr in program {
            match instr {
                Instr::Move(offset) => {
                    self.mov(*offset);
                }
                Instr::Load(val, dst) => {
                    self.write(*dst, *val);
                }
                Instr::Add(val, dst) => {
                    self.write(*dst, self.read(*dst).wrapping_add(*val));
                }
                Instr::MulAdd(val, src, dst) => {
                    self.write(
                        *dst,
                        self.read(*dst)
                            .wrapping_add(val.wrapping_mul(self.read(*src))),
                    );
                }
                Instr::Output(src) => {
                    self.output(self.read(*src).into_u8());
                }
                Instr::Input(dst) => {
                    let val = self.input();
                    self.write(*dst, C::from_u8(val));
                }
                Instr::Loop(cond, block) => {
                    while self.read(*cond) != C::ZERO {
                        self.execute(block);
                    }
                }
                Instr::If(cond, block) => {
                    if self.read(*cond) != C::ZERO {
                        self.execute(block);
                    }
                }
            }
        }
    }
}

impl<'a, C: CellType> Drop for Context<'a, C> {
    fn drop(&mut self) {
        let old_size = (self.mem_high as usize - self.mem_low as usize) / mem::size_of::<C>();
        if old_size != 0 {
            // SAFETY: If the old size is non-zero, the old region is valid.
            unsafe {
                let old_layout = Layout::array::<C>(old_size).unwrap();
                dealloc(self.mem_low as *mut u8, old_layout);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{parse, Context, Error};

    #[test]
    fn reading_unused_cells_return_zero() {
        let ctx = Context::<u8>::without_io();
        assert_eq!(ctx.read(0), 0);
        assert_eq!(ctx.read(1), 0);
        assert_eq!(ctx.read(100), 0);
        assert_eq!(ctx.read(-1), 0);
        assert_eq!(ctx.read(-100), 0);
    }

    #[test]
    fn initial_cell_reads_written_value() {
        let mut ctx = Context::<u8>::without_io();
        ctx.write(0, 100);
        assert_eq!(ctx.read(0), 100);
    }

    #[test]
    fn positive_cell_reads_written_value() {
        let mut ctx = Context::<u8>::without_io();
        ctx.write(100, 42);
        assert_eq!(ctx.read(100), 42);
    }

    #[test]
    fn negative_cell_reads_written_value() {
        let mut ctx = Context::<u8>::without_io();
        ctx.write(-100, 42);
        assert_eq!(ctx.read(-100), 42);
    }

    #[test]
    fn resizes_preserve_pointer() {
        let mut ctx = Context::<u8>::without_io();
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
        let mut ctx = Context::<u8>::without_io();
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
        let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
        ctx.output(42);
        ctx.output(1);
        ctx.output(3);
        drop(ctx);
        assert_eq!(&buf, &[42, 1, 3]);
    }

    #[test]
    fn input_reads_from_input() {
        let buf = vec![42, 1, 3];
        let mut ctx = Context::<u8>::new(Some(Box::new(buf.as_slice())), None);
        assert_eq!(ctx.input(), 42);
        assert_eq!(ctx.input(), 1);
        assert_eq!(ctx.input(), 3);
    }

    #[test]
    fn simple_execution() -> Result<(), Error> {
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
        ctx.execute(&parse(
            ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.",
        )?);
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    fn simple_execution_u16() -> Result<(), Error> {
        let mut buf = Vec::new();
        let mut ctx = Context::<u16>::new(None, Some(Box::new(&mut buf)));
        ctx.execute(&parse(
            ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.",
        )?);
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    fn simple_execution_u32() -> Result<(), Error> {
        let mut buf = Vec::new();
        let mut ctx = Context::<u32>::new(None, Some(Box::new(&mut buf)));
        ctx.execute(&parse(
            ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.",
        )?);
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    fn simple_execution_u64() -> Result<(), Error> {
        let mut buf = Vec::new();
        let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
        ctx.execute(&parse(
            ">++++++++[-<+++++++++>]<.>>+>-[+]++>++>+++[>[->+++<<+++>]<<]>-----.>->
            +++..+++.>-.<<+[>[+>+]>>]<--------------.>>.+++.------.--------.>+.>+.",
        )?);
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "Hello World!\n");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_program_access_distant_cell() -> Result<(), Error> {
        let mut buf = Vec::new();
        let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
        ctx.execute(&parse(
            "++++[>++++++<-]>[>+++++>+++++++<<-]>>++++<[[>[[
            >>+<<-]<]>>>-]>-[>+>+<<-]>]+++++[>+++++++<<++>-]>.<<.",
        )?);
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "#\n");
        Ok(())
    }

    #[test]
    fn test_program_output_h() -> Result<(), Error> {
        let mut buf = Vec::new();
        let mut ctx = Context::<u64>::new(None, Some(Box::new(&mut buf)));
        ctx.execute(&parse(
            "[]++++++++++[>>+>+>++++++[<<+<+++>>>-]<<<<-]
            \"A*$\";?@![#>>+<<]>[>>]<<<<[>++<[-]]>.>.",
        )?);
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "H\n");
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_program_rot13() -> Result<(), Error> {
        let mut buf = Vec::new();
        let mut ctx = Context::<u8>::new(
            Some(Box::new("~mlk zyx".as_bytes())),
            Some(Box::new(&mut buf)),
        );
        ctx.execute(&parse(
            ",
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>++++++++++++++<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>>+++++[<----->-]<<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>++++++++++++++<-
            [>+<-[>+<-[>+<-[>+<-[>+<-
            [>++++++++++++++<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>>+++++[<----->-]<<-
            [>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-
            [>++++++++++++++<-
            [>+<-]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
            ]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]>.[-]<,]",
        )?);
        drop(ctx);
        assert_eq!(String::from_utf8(buf).unwrap(), "~zyx mlk");
        Ok(())
    }
}
