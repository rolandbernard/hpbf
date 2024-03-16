//! An inplace interpreter that works directly on the code string.

use std::marker::PhantomData;

use crate::{runtime::Context, CellType, Error, ErrorKind};

use super::{Executable, Executor};

/// An inplace non-optimizing interpreter.
///
/// # Examples
/// ```
/// # use hpbf::{ir::{Program, Block, Instr}, Error, runtime::Context, exec::{Executor, Executable, InplaceInterpreter}};
/// # let mut buf = Vec::new();
/// # let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
/// # let code = "++++++[>+++++<-]>++[>++<-]++++[>++<-]>[.>]";
/// let exec = InplaceInterpreter::<u8>::create(code, 1)?;
/// exec.execute(&mut ctx)?;
/// # drop(ctx);
/// # assert_eq!(String::from_utf8(buf).unwrap(), "H");
/// # Ok::<(), Error>(())
/// ```
pub struct InplaceInterpreter<'code, C: CellType> {
    code: &'code str,
    _phantom: PhantomData<C>,
}

impl<'code, C: CellType> InplaceInterpreter<'code, C> {
    /// Execute the brainfuck program in the given context.
    fn execute_in<const LIMITED: bool>(&self, cxt: &mut Context<C>) -> Result<bool, Error> {
        let code_bytes = self.code.as_bytes();
        let mut loop_stack = Vec::new();
        let mut pc = 0;
        while pc < code_bytes.len() {
            let code = code_bytes[pc];
            pc += 1;
            match code {
                b'<' => {
                    cxt.memory.mov(-1);
                }
                b'>' => {
                    cxt.memory.mov(1);
                }
                b'+' => {
                    cxt.memory.write(0, cxt.memory.read(0).wrapping_add(C::ONE));
                }
                b'-' => {
                    cxt.memory
                        .write(0, cxt.memory.read(0).wrapping_add(C::NEG_ONE));
                }
                b'.' => {
                    if cxt.output(cxt.memory.read(0).into_u8()).is_none() {
                        return Ok(true);
                    }
                }
                b',' => {
                    if let Some(val) = cxt.input() {
                        cxt.memory.write(0, C::from_u8(val));
                    } else {
                        return Ok(true);
                    }
                }
                b'[' => {
                    if cxt.memory.read(0) == C::ZERO {
                        let mut cnt = 0;
                        while pc < code_bytes.len() {
                            if code_bytes[pc] == b']' {
                                if cnt == 0 {
                                    break;
                                }
                                cnt -= 1;
                            } else if code_bytes[pc] == b'[' {
                                cnt += 1;
                            }
                            pc += 1;
                        }
                        pc += 1;
                    } else {
                        loop_stack.push(pc);
                    }
                }
                b']' => {
                    if LIMITED {
                        if cxt.budget == 0 {
                            return Ok(false);
                        }
                        cxt.budget -= 1;
                    }
                    let target = loop_stack.pop().ok_or_else(|| Error {
                        kind: ErrorKind::LoopNotOpened,
                        str: self.code.to_owned(),
                        position: pc - 1,
                    })?;
                    if cxt.memory.read(0) != C::ZERO {
                        pc = target;
                        loop_stack.push(pc);
                    }
                }
                _ => { /* ignore comments */ }
            }
        }
        Ok(true)
    }
}

impl<'code, C: CellType> Executor<'code, C> for InplaceInterpreter<'code, C> {
    fn create(code: &'code str, _opt: u32) -> Result<Self, Error> {
        Ok(InplaceInterpreter {
            code,
            _phantom: PhantomData,
        })
    }
}

impl<'code, C: CellType> Executable<C> for InplaceInterpreter<'code, C> {
    fn execute(&self, context: &mut Context<C>) -> Result<(), Error> {
        self.execute_in::<false>(context).map(|_| ())
    }

    fn execute_limited(&self, context: &mut Context<C>) -> Result<bool, Error> {
        self.execute_in::<true>(context)
    }
}

executor_tests!(InplaceInterpreter);
