//! A basic interpreter on the internal bytecode.

use std::{
    alloc::{alloc_zeroed, dealloc, Layout},
    mem, ptr,
};

use crate::{
    bc::{self, Instr, Loc, Program},
    ir,
    runtime::Context,
    CellType, Error,
};

use self::ops::{adjust_branch, emit, emit_return, enter_ops, OpCode};

use super::Executor;

mod ops;

/// A basic interpreter that does some limited optimizing transformations of the
/// program and executes the result using a loop-and-switch interpreter.
///
/// # Examples
/// ```
/// # use hpbf::{ir::{Program, Block, Instr}, Error, runtime::Context, exec::{Executor, BcInterpreter}};
/// # let mut buf = Vec::new();
/// # let mut ctx = Context::<u8>::new(None, Some(Box::new(&mut buf)));
/// # let code = "++++++[>+++++<-]>++[>++<-]++++[>++<-]>[.>]";
/// let exec = BcInterpreter::<u8>::create(code, 1)?;
/// exec.execute(&mut ctx)?;
/// # drop(ctx);
/// # assert_eq!(String::from_utf8(buf).unwrap(), "H");
/// # Ok::<(), Error>(())
/// ```
pub struct BcInterpreter<C: CellType> {
    bytecode: Program<C>,
}

/// The context for the threaded code interpreter.
#[repr(C)]
pub struct OpsContext<'cxt, C: CellType> {
    min_accessed: isize,
    max_accessed: isize,
    budget: usize,
    context: Context<'cxt, C>,
    temps: [C; 0],
}

impl<C: CellType> BcInterpreter<C> {
    /// Generate, from the bytecode, the corresponding threaded code.
    fn build_threaded_code(&self) -> Vec<OpCode<C>> {
        let mut inst_offset = Vec::with_capacity(self.bytecode.insts.len() + 1);
        inst_offset.push(0);
        let mut insts = Vec::new();
        for &inst in &self.bytecode.insts {
            emit(&mut insts, inst);
            inst_offset.push(insts.len());
        }
        emit_return(&mut insts);
        for (i, &inst) in self.bytecode.insts.iter().enumerate() {
            if let Instr::BrZ(_, off) | Instr::BrNZ(_, off) = inst {
                let offset =
                    inst_offset[i.wrapping_add_signed(off)] as isize - inst_offset[i] as isize;
                adjust_branch(&mut insts[inst_offset[i]..], offset);
            }
        }
        return insts;
    }

    /// Build the context required for the threaded code interpreter.
    fn build_context<'a>(&self, cxt: Context<'a, C>) -> *mut OpsContext<'a, C> {
        let layout = Layout::from_size_align(
            mem::size_of::<OpsContext<C>>() + mem::size_of::<C>() * self.bytecode.temps.max(2),
            mem::align_of::<OpsContext<C>>(),
        )
        .unwrap();
        unsafe {
            let ptr = alloc_zeroed(layout) as *mut OpsContext<C>;
            ptr::addr_of_mut!((*ptr).min_accessed).write(self.bytecode.min_accessed);
            ptr::addr_of_mut!((*ptr).max_accessed).write(self.bytecode.max_accessed);
            ptr::addr_of_mut!((*ptr).context).write(cxt);
            ptr
        }
    }

    /// Free the context and return the captured context.
    fn free_context<'a>(&self, cxt: *mut OpsContext<'a, C>) -> Context<'a, C> {
        let layout = Layout::from_size_align(
            mem::size_of::<OpsContext<C>>() + mem::size_of::<C>() * self.bytecode.temps.max(2),
            mem::align_of::<OpsContext<C>>(),
        )
        .unwrap();
        unsafe {
            let rt_cxt = ptr::addr_of!((*cxt).context).read();
            dealloc(cxt as *mut _, layout);
            rt_cxt
        }
    }

    /// Execute in the given context using the threaded code interpreter.
    fn execute_fast_in(&self, cxt: &mut Context<C>) {
        let mut def_cxt = Context::without_io();
        mem::swap(cxt, &mut def_cxt);
        let ops_cxt = self.build_context(def_cxt);
        let code = self.build_threaded_code();
        let mut ip = code.as_ptr();
        while !ip.is_null() {
            // Safety: We rely on the threaded code being generated correctly.
            unsafe { ip = enter_ops(ops_cxt, ip) };
        }
        let mut def_cxt = self.free_context(ops_cxt);
        mem::swap(cxt, &mut def_cxt);
    }
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
        self.execute_fast_in(context);
        Ok(())
    }

    fn execute_limited(&self, context: &mut Context<C>, instr: usize) -> Result<bool, Error<'p>> {
        Ok(self.execute_in(context, Some(instr)).unwrap_or(true))
    }
}

executor_tests!(BcInterpreter);
same_as_inplace_tests!(BcInterpreter);
