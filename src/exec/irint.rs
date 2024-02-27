//! A basic interpreter on the internal IR.

use crate::{
    ir::{Block, Instr, Program},
    runtime::Context,
    CellType, Error,
};

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
    /// Execute a single block within the given program. The block does not necessary
    /// have to be part of the program, but all loops and ifs must refer to blocks
    /// within the program.
    fn execute_block(&self, cxt: &mut Context<C>, block: &Block<C>) -> Option<()> {
        for instr in &block.insts {
            match instr {
                Instr::Output { src } => {
                    cxt.output(cxt.memory.read(*src).into_u8())?;
                }
                Instr::Input { dst } => {
                    let val = C::from_u8(cxt.input()?);
                    cxt.memory.write(*dst, val);
                }
                Instr::Calc { calcs } => {
                    if calcs.len() == 1 {
                        let (var, expr) = &calcs[0];
                        let val = expr.evaluate(|off| cxt.memory.read(off));
                        cxt.memory.write(*var, val);
                    } else {
                        let mut buffer = Vec::with_capacity(calcs.len());
                        for (_, expr) in calcs {
                            buffer.push(expr.evaluate(|off| cxt.memory.read(off)));
                        }
                        for (&(var, _), val) in calcs.iter().zip(buffer.into_iter()) {
                            cxt.memory.write(var, val);
                        }
                    }
                }
                Instr::Loop { cond, block } => {
                    while cxt.memory.read(*cond) != C::ZERO {
                        self.execute_block(cxt, block)?;
                        cxt.memory.mov(block.shift);
                    }
                }
                Instr::If { cond, block } => {
                    if cxt.memory.read(*cond) != C::ZERO {
                        self.execute_block(cxt, block)?;
                        cxt.memory.mov(block.shift);
                    }
                }
            }
        }
        Some(())
    }
}

impl<'p, C: CellType> Executor<'p, C> for BaseInterpreter<C> {
    fn create(code: &str, opt: u32) -> Result<Self, Error> {
        let mut program = Program::<C>::parse(code)?;
        program = program.optimize(opt);
        Ok(BaseInterpreter { program })
    }

    fn execute(&self, context: &mut Context<C>) -> Result<(), Error<'p>> {
        self.execute_block(context, &self.program);
        Ok(())
    }
}

executor_tests!(BaseInterpreter);
same_as_inplace_tests!(BaseInterpreter);
