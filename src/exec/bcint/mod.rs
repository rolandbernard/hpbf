//! A basic interpreter on the internal bytecode.

use std::{
    alloc::{alloc_zeroed, dealloc, Layout},
    mem, ptr,
};

use crate::{
    bc::{self, Instr, Program},
    ir,
    runtime::Context,
    CellType, Error,
};

use self::ops::{adjust_branch, emit, emit_limit, emit_return, enter_ops, OpCode};

use super::{Executable, Executor};

mod ops;

/// A basic interpreter that does some limited optimizing transformations of the
/// program and executes the result using a translation to direct threaded code.
///
/// # Examples
/// ```
/// # use hpbf::{ir::{Program, Block, Instr}, Error, runtime::Context, exec::{Executor, Executable, BcInterpreter}};
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
    context: Context<'cxt, C>,
    temps: [C; 0],
}

impl<C: CellType> BcInterpreter<C> {
    /// Generate, from the bytecode, the corresponding threaded code.
    fn build_threaded_code(&self, limited: bool) -> Vec<OpCode<C>> {
        let mut inst_offset = Vec::with_capacity(self.bytecode.insts.len() + 1);
        let mut inst_start = Vec::with_capacity(self.bytecode.insts.len() + 1);
        let mut insts = Vec::new();
        for &inst in &self.bytecode.insts {
            inst_start.push(insts.len());
            if limited {
                if let Instr::BrZ(_, _) | Instr::BrNZ(_, _) = inst {
                    emit_limit(&mut insts, 1);
                }
                if let Instr::Scan(_, shift) = inst {
                    if shift == 0 {
                        emit_limit(&mut insts, usize::MAX);
                    }
                }
            }
            inst_offset.push(insts.len());
            emit(&mut insts, inst);
        }
        inst_start.push(insts.len());
        inst_offset.push(insts.len());
        emit_return(&mut insts);
        for (i, &inst) in self.bytecode.insts.iter().enumerate() {
            if let Instr::BrZ(_, off) | Instr::BrNZ(_, off) = inst {
                let offset =
                    inst_start[i.wrapping_add_signed(off)] as isize - inst_offset[i] as isize;
                adjust_branch(&mut insts[inst_offset[i]..], offset);
            }
        }
        return insts;
    }

    /// Build the context required for the threaded code interpreter.
    fn build_context<'a>(&self, cxt: Context<'a, C>, budget: usize) -> *mut OpsContext<'a, C> {
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
            ptr::addr_of_mut!((*ptr).context.budget).write(budget);
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
    fn execute_in(&self, cxt: &mut Context<C>) {
        let mut def_cxt = Context::without_io();
        mem::swap(cxt, &mut def_cxt);
        let ops_cxt = self.build_context(def_cxt, 0);
        let code = self.build_threaded_code(false);
        let mut ip = code.as_ptr();
        while !ip.is_null() {
            // Safety: We rely on the threaded code being generated correctly.
            unsafe { ip = enter_ops(ops_cxt, ip) };
        }
        let mut def_cxt = self.free_context(ops_cxt);
        mem::swap(cxt, &mut def_cxt);
    }

    /// Execute in the given context using the threaded code interpreter.
    fn execute_limited_in(&self, cxt: &mut Context<C>, budget: usize) -> bool {
        let mut def_cxt = Context::without_io();
        mem::swap(cxt, &mut def_cxt);
        let ops_cxt = self.build_context(def_cxt, budget);
        let code = self.build_threaded_code(true);
        let mut finished = true;
        let mut ip = code.as_ptr();
        while !ip.is_null() {
            // Safety: We rely on the threaded code being generated correctly.
            unsafe {
                if (*ops_cxt).context.budget == 0 {
                    finished = false;
                    break;
                }
                ip = enter_ops(ops_cxt, ip);
            }
        }
        let mut def_cxt = self.free_context(ops_cxt);
        mem::swap(cxt, &mut def_cxt);
        return finished;
    }
}

impl<'code, C: CellType> Executor<'code, C> for BcInterpreter<C> {
    fn create(code: &str, opt: u32) -> Result<Self, Error> {
        let mut program = ir::Program::<C>::parse(code)?;
        program = program.optimize(opt);
        let bytecode = bc::CodeGen::translate(&program, 2, true);
        Ok(BcInterpreter { bytecode })
    }
}

impl<C: CellType> Executable<C> for BcInterpreter<C> {
    fn execute(&self, context: &mut Context<C>) -> Result<(), Error> {
        self.execute_in(context);
        Ok(())
    }

    fn execute_limited(&self, context: &mut Context<C>, instr: usize) -> Result<bool, Error> {
        Ok(self.execute_limited_in(context, instr))
    }
}

executor_tests!(BcInterpreter);
same_as_inplace_tests!(BcInterpreter);
