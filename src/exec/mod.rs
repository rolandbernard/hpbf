//! This module contains different execution providers.

use crate::{runtime::Context, CellType, Error};

#[macro_use]
mod testdef;

mod bcint;
mod inplace;
mod irint;

#[cfg(feature = "llvm")]
mod llvmjit;

pub use bcint::BcInterpreter;
pub use inplace::InplaceInterpreter;
pub use irint::IrInterpreter;

#[cfg(feature = "llvm")]
pub use llvmjit::LlvmInterpreter;

/// Trait implemented by the different execution strategies provided by this crate.
pub trait Executable<C: CellType> {
    /// Execute the executor in the given [`Context`].
    fn execute(&self, context: &mut Context<C>) -> Result<(), Error>;

    /// Like execute, but terminate after executing approximately `instr` instructions.
    /// Not that instructions here does not have to mean Brainfuck instructions,
    /// but some other internal format. The only important thing is that the
    /// runtime is finite and roughly proportional to `instr`.
    fn execute_limited(&self, context: &mut Context<C>, instr: usize) -> Result<bool, Error>;
}

pub trait Executor<'code, C: CellType>: Executable<C> + Sized {
    /// Creates a new instance of the executor to run on the given code. The
    /// code may be captured or used to create other internal representations.
    /// If the executor supports optimizations, they should be influenced by the
    /// `opt` parameter to this method.
    fn create(code: &'code str, opt: u32) -> Result<Self, Error>;
}
