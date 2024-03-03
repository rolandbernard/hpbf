//! A basic interpreter on the internal IR.

use crate::{
    ir::{Block, Instr, Program},
    runtime::Context,
    CellType, Error,
};

use super::{Executable, Executor};

/// A basic interpreter that does some limited optimizing transformations of the
/// program and executes the result using a loop-and-switch interpreter.
///
/// # Examples
/// ```
/// # use hpbf::{ir::{Program, Block, Instr}, Error, runtime::Context, exec::{Executor, Executable, IrInterpreter}};
/// # let mut buf = Vec::new();
/// # let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
/// # let code = "++++++[>+++++<-]>++[>++<-]++++[>++<-]>[.>]";
/// let exec = IrInterpreter::<u8>::create(code, 1)?;
/// exec.execute(&mut ctx)?;
/// # drop(ctx);
/// # assert_eq!(String::from_utf8(buf).unwrap(), "H");
/// # Ok::<(), Error>(())
/// ```
pub struct IrInterpreter<C: CellType> {
    program: Program<C>,
}

impl<C: CellType> IrInterpreter<C> {
    /// Execute a single block within the given program. The block does not necessary
    /// have to be part of the program, but all loops and ifs must refer to blocks
    /// within the program.
    fn execute_block(
        &self,
        cxt: &mut Context<C>,
        block: &Block<C>,
        limit: &mut Option<usize>,
    ) -> Option<bool> {
        for instr in &block.insts {
            if let Some(lim) = limit {
                if *lim == 0 {
                    return Some(false);
                }
                *lim -= 1;
            }
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
                        self.execute_block(cxt, block, limit)?;
                        cxt.memory.mov(block.shift);
                        if let Some(lim) = limit {
                            if *lim == 0 {
                                return Some(false);
                            }
                            *lim -= 1;
                        }
                    }
                }
                Instr::If { cond, block } => {
                    if cxt.memory.read(*cond) != C::ZERO {
                        self.execute_block(cxt, block, limit)?;
                        cxt.memory.mov(block.shift);
                    }
                }
            }
        }
        Some(true)
    }
}

impl<'p, C: CellType> Executor<'p, C> for IrInterpreter<C> {
    fn create(code: &str, opt: u32) -> Result<Self, Error> {
        let mut program = Program::<C>::parse(code)?;
        program = program.optimize(opt);
        Ok(IrInterpreter { program })
    }
}

impl<'p, C: CellType> Executable<'p, C> for IrInterpreter<C> {
    fn execute(&self, context: &mut Context<C>) -> Result<(), Error<'p>> {
        self.execute_block(context, &self.program, &mut None);
        Ok(())
    }

    fn execute_limited(&self, context: &mut Context<C>, limit: usize) -> Result<bool, Error<'p>> {
        Ok(self
            .execute_block(context, &self.program, &mut Some(limit))
            .unwrap_or(true))
    }
}

executor_tests!(IrInterpreter);
same_as_inplace_tests!(IrInterpreter);
