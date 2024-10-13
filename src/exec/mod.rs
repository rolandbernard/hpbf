//! This module contains different execution providers.

use crate::{runtime::Context, CellType, Error};

#[macro_use]
mod testdef;

mod bcint;
mod inplace;
mod irint;

#[cfg(all(target_arch = "x86_64", target_family = "unix"))]
mod basejit;

#[cfg(feature = "llvm")]
mod llvmjit;

pub use bcint::BcInterpreter;
pub use inplace::InplaceInterpreter;
pub use irint::IrInterpreter;

#[cfg(all(target_arch = "x86_64", target_family = "unix"))]
pub use basejit::BaseJitCompiler;

#[cfg(feature = "llvm")]
pub use llvmjit::LlvmJitCompiler;

/// Trait implemented by the different execution strategies provided by this crate.
pub trait Executable<C: CellType> {
    /// Execute the executor in the given [`Context`].
    fn execute(&self, context: &mut Context<C>) -> Result<(), Error>;

    /// Execute the executor in the given [`Context`] without performing memory bounds checks.
    ///
    /// # Safety
    /// This is only safe if the program does not leave the preallocated memory bounds.
    unsafe fn execute_unsafe(&self, context: &mut Context<C>) -> Result<(), Error> {
        self.execute(context)
    }

    /// Like execute, but terminate after the budget set in `context` is exhausted.
    /// Note that the budge here does not have to mean number of Brainfuck instructions,
    /// but some other internal metric. The only important thing is that the
    /// runtime is finite and roughly proportional to the budget.
    /// Must return true if the execution finished normally, and false if interrupted.
    fn execute_limited(&self, context: &mut Context<C>) -> Result<bool, Error>;
}

pub trait Executor<'code, C: CellType>: Executable<C> + Sized {
    /// Creates a new instance of the executor to run on the given code. The
    /// code may be captured or used to create other internal representations.
    /// If the executor supports optimizations, they should be influenced by the
    /// `opt` parameter to this method.
    fn create(code: &'code str, opt: u32) -> Result<Self, Error>;
}
