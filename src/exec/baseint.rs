use crate::{Block, CellType, Context, Error, Instr, Program};

use super::Executor;

/// A basic interpreter that does some limited optimizing transformations of the
/// program and executes the result using a loop-and-switch interpreter.
///
/// # Examples
/// ```
/// # use hpbf::{Program, Block, Instr, Error, Context, Executor, BaseInterpreter};
/// # let mut buf = Vec::new();
/// # let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
/// # let code = "++++++[>+++++<-]>++[>++<-]++++[>++<-]>[.>]";
/// let exec = BaseInterpreter::<u8>::create(code, false, 1)?;
/// exec.execute(&mut ctx)?;
/// # drop(ctx);
/// # assert_eq!(String::from_utf8(buf).unwrap(), "H");
/// # Ok::<(), Error>(())
/// ```
pub struct BaseInterpreter<C: CellType> {
    program: Program<C>,
}

impl<C: CellType> BaseInterpreter<C> {
    pub fn print_ir(&self) {
        println!("{:#?}", self.program);
    }

    /// Execute a single block within the given program. The block does not necessary
    /// have to be part of the program, but all loops and ifs must refer to blocks
    /// within the program.
    fn execute_block(&self, cxt: &mut Context<C>, block: &Block<C>) -> Result<(), ()> {
        for instr in &block.insts {
            match *instr {
                Instr::Output { src } => {
                    cxt.output(cxt.memory.read(src).into_u8())?;
                }
                Instr::Input { dst } => {
                    let val = C::from_u8(cxt.input()?);
                    cxt.memory.write(dst, val);
                }
                Instr::Load { val, dst } => {
                    cxt.memory.write(dst, val);
                }
                Instr::Add { val, dst } => {
                    let val = val.wrapping_add(cxt.memory.read(dst));
                    cxt.memory.write(dst, val);
                }
                Instr::MulAdd { val, src, dst } => {
                    let val = val
                        .wrapping_mul(cxt.memory.read(src))
                        .wrapping_add(cxt.memory.read(dst));
                    cxt.memory.write(dst, val);
                }
                Instr::Loop { cond, block } => {
                    let block = &self.program.blocks[block];
                    while cxt.memory.read(cond) != C::ZERO {
                        cxt.memory.mov(cond);
                        self.execute_block(cxt, block)?;
                        cxt.memory.mov(block.shift - cond);
                    }
                }
                Instr::If { cond, block } => {
                    if cxt.memory.read(cond) != C::ZERO {
                        cxt.memory.mov(cond);
                        let block = &self.program.blocks[block];
                        self.execute_block(cxt, block)?;
                        cxt.memory.mov(block.shift - cond);
                    }
                }
            }
        }
        Ok(())
    }
}

impl<'p, C: CellType> Executor<'p, C> for BaseInterpreter<C> {
    fn create(code: &str, no_opt: bool, opt: u32) -> Result<Self, Error> {
        let mut program = Program::<C>::parse(code)?;
        if !no_opt {
            for _ in 0..opt {
                program = program.optimize();
            }
        }
        Ok(BaseInterpreter { program })
    }

    fn execute(&self, context: &mut Context<C>) -> Result<(), Error<'p>> {
        self.execute_block(context, &self.program.blocks[self.program.entry])
            .ok();
        Ok(())
    }
}

executor_tests!(BaseInterpreter);
