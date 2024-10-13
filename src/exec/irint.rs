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

/// Execute a single block within some program. The block does not necessary
/// have to be part of the same program, but all loops and ifs must refer to
/// valid blocks, and blocks can only be owned by one program.
fn execute_block<C: CellType, const LIMITED: bool>(
    cxt: &mut Context<C>,
    block: &Block<C>,
) -> Option<bool> {
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
            Instr::Loop { cond, block, .. } => {
                while cxt.memory.read(*cond) != C::ZERO {
                    execute_block::<_, LIMITED>(cxt, block)?;
                    cxt.memory.mov(block.shift);
                    if LIMITED {
                        if cxt.budget == 0 {
                            return Some(false);
                        }
                        cxt.budget -= 1;
                    }
                }
            }
            Instr::If { cond, block } => {
                if cxt.memory.read(*cond) != C::ZERO {
                    execute_block::<_, LIMITED>(cxt, block)?;
                    cxt.memory.mov(block.shift);
                    if LIMITED {
                        if cxt.budget == 0 {
                            return Some(false);
                        }
                        cxt.budget -= 1;
                    }
                }
            }
        }
    }
    Some(true)
}

impl<C: CellType> Executor<'_, C> for IrInterpreter<C> {
    fn create(code: &str, opt: u32) -> Result<Self, Error> {
        let mut program = Program::<C>::parse(code)?;
        program = program.optimize(opt);
        Ok(IrInterpreter { program })
    }
}

impl<C: CellType> Executable<C> for IrInterpreter<C> {
    fn execute(&self, context: &mut Context<C>) -> Result<(), Error> {
        execute_block::<_, false>(context, &self.program);
        Ok(())
    }

    fn execute_limited(&self, context: &mut Context<C>) -> Result<bool, Error> {
        Ok(execute_block::<_, true>(context, &self.program).unwrap_or(true))
    }
}

executor_tests!(IrInterpreter);
same_as_inplace_tests!(IrInterpreter);
