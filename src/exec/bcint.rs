//! A basic interpreter on the internal bytecode.

use crate::{
    bc::{self, Instr, Loc, Program},
    ir,
    runtime::Context,
    CellType, Error,
};

use super::Executor;

/// A basic interpreter that does some limited optimizing transformations of the
/// program and executes the result using a loop-and-switch interpreter.
///
/// # Examples
/// ```
/// ```
pub struct BcInterpreter<C: CellType> {
    bytecode: Program<C>,
}

impl<C: CellType> BcInterpreter<C> {
    /// Execute the bytecode program in the given context.
    fn execute_in(&self, cxt: &mut Context<C>, mut limit: Option<usize>) -> Option<bool> {
        #[inline]
        fn read<C: CellType>(cxt: &Context<C>, tmps: &[C], loc: Loc<C>) -> C {
            match loc {
                Loc::Mem(mem) => cxt.memory.read(mem),
                Loc::Tmp(tmp) => tmps[tmp],
                Loc::Imm(imm) => imm,
            }
        }
        #[inline]
        fn write<C: CellType>(cxt: &mut Context<C>, tmps: &mut [C], loc: Loc<C>, val: C) {
            match loc {
                Loc::Mem(mem) => cxt.memory.write(mem, val),
                Loc::Tmp(tmp) => tmps[tmp] = val,
                Loc::Imm(_) => unreachable!(),
            }
        }
        let mut temps = vec![C::ZERO; self.bytecode.temps];
        let mut ip = 0;
        while let Some(instr) = self.bytecode.insts.get(ip) {
            if let Some(lim) = limit {
                if lim == 0 {
                    return Some(false);
                }
                limit = Some(lim - 1);
            }
            match *instr {
                Instr::Noop => { /* Do nothing. */ }
                Instr::Scan(cond, shift) => {
                    while cxt.memory.read(cond) != C::ZERO {
                        cxt.memory.mov(shift);
                    }
                }
                Instr::Mov(shift) => cxt.memory.mov(shift),
                Instr::Inp(dst) => {
                    let value = C::from_u8(cxt.input()?);
                    cxt.memory.write(dst, value)
                }
                Instr::Out(src) => cxt.output(cxt.memory.read(src).into_u8())?,
                Instr::BrZ(cond, off) => {
                    if cxt.memory.read(cond) == C::ZERO {
                        ip = ip.wrapping_add_signed(off - 1);
                    }
                }
                Instr::BrNZ(cond, off) => {
                    if cxt.memory.read(cond) != C::ZERO {
                        ip = ip.wrapping_add_signed(off - 1);
                    }
                }
                Instr::Add(dst, src0, src1) => {
                    let result = read(cxt, &temps, src0).wrapping_add(read(cxt, &temps, src1));
                    write(cxt, &mut temps, dst, result);
                }
                Instr::Sub(dst, src0, src1) => {
                    let result = read(cxt, &temps, src0)
                        .wrapping_add(read(cxt, &temps, src1).wrapping_neg());
                    write(cxt, &mut temps, dst, result);
                }
                Instr::Mul(dst, src0, src1) => {
                    let result = read(cxt, &temps, src0).wrapping_mul(read(cxt, &temps, src1));
                    write(cxt, &mut temps, dst, result);
                }
                Instr::Copy(dst, src) => {
                    let result = read(cxt, &temps, src);
                    write(cxt, &mut temps, dst, result);
                }
            }
            ip += 1;
        }
        Some(true)
    }
}

impl<'p, C: CellType> Executor<'p, C> for BcInterpreter<C> {
    fn create(code: &str, opt: u32) -> Result<Self, Error> {
        let mut program = ir::Program::<C>::parse(code)?;
        program = program.optimize(opt);
        let bytecode = bc::CodeGen::translate(&program, 2);
        Ok(BcInterpreter { bytecode })
    }

    fn execute(&self, context: &mut Context<C>) -> Result<(), Error<'p>> {
        self.execute_in(context, None);
        Ok(())
    }

    fn execute_limited(&self, context: &mut Context<C>, instr: usize) -> Result<bool, Error<'p>> {
        Ok(self.execute_in(context, Some(instr)).unwrap_or(true))
    }
}

executor_tests!(BcInterpreter);
same_as_inplace_tests!(BcInterpreter);
