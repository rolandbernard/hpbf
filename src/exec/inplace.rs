//! An inplace interpreter that works directly on the code string.

use std::marker::PhantomData;

use crate::{runtime::Context, CellType, Error, ErrorKind};

use super::Executor;

/// An inplace non-optimizing interpreter.
///
/// # Examples
/// ```
/// # use hpbf::{Program, Block, Instr, Error, Context, Executor, InplaceInterpreter};
/// # let mut buf = Vec::new();
/// # let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
/// # let code = "++++++[>+++++<-]>++[>++<-]++++[>++<-]>[.>]";
/// let exec = InplaceInterpreter::<u8>::create(code, false, 1)?;
/// exec.execute(&mut ctx)?;
/// # drop(ctx);
/// # assert_eq!(String::from_utf8(buf).unwrap(), "H");
/// # Ok::<(), Error>(())
/// ```
pub struct InplaceInterpreter<'code, C: CellType> {
    code: &'code str,
    _phantom: PhantomData<C>,
}

impl<'code, C: CellType> Executor<'code, C> for InplaceInterpreter<'code, C> {
    fn create(code: &'code str, _opt: u32) -> Result<Self, Error> {
        Ok(InplaceInterpreter {
            code,
            _phantom: PhantomData,
        })
    }

    fn execute(&self, context: &mut Context<C>) -> Result<(), Error<'code>> {
        let code_bytes = self.code.as_bytes();
        let mut loop_stack = Vec::new();
        let mut pc = 0;
        while pc < code_bytes.len() {
            let code = code_bytes[pc];
            pc += 1;
            match code {
                b'<' => {
                    context.memory.mov(-1);
                }
                b'>' => {
                    context.memory.mov(1);
                }
                b'+' => {
                    context
                        .memory
                        .write(0, context.memory.read(0).wrapping_add(C::ONE));
                }
                b'-' => {
                    context
                        .memory
                        .write(0, context.memory.read(0).wrapping_add(C::NEG_ONE));
                }
                b'.' => {
                    if let None = context.output(context.memory.read(0).into_u8()) {
                        return Ok(());
                    }
                }
                b',' => {
                    if let Some(val) = context.input() {
                        context.memory.write(0, C::from_u8(val));
                    } else {
                        return Ok(());
                    }
                }
                b'[' => {
                    if context.memory.read(0) == C::ZERO {
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
                    let target = loop_stack.pop().ok_or(Error {
                        kind: ErrorKind::LoopNotOpened,
                        str: self.code,
                        position: pc - 1,
                    })?;
                    if context.memory.read(0) != C::ZERO {
                        pc = target;
                        loop_stack.push(pc);
                    }
                }
                _ => { /* ignore comments */ }
            }
        }
        Ok(())
    }
}

executor_tests!(InplaceInterpreter);
