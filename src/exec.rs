//! This module contains different execution providers.

use crate::{runtime::Context, CellType, Error};

#[macro_use]
mod testdef;

mod inplace;
mod irint;

pub use inplace::InplaceInterpreter;
pub use irint::BaseInterpreter;

/// Trait implemented by the different execution strategies provided by this crate.
pub trait Executor<'p, C: CellType>: Sized {
    /// Creates a new instance of the executor to run on the given code. The
    /// code may be captured or used to create other internal representations.
    /// If the executor supports optimizations, they should be influenced by the
    /// `opt` parameter to this method.
    fn create(code: &'p str, opt: u32) -> Result<Self, Error<'p>>;

    /// Execute the executor in the given [`Context`].
    fn execute(&self, context: &mut Context<C>) -> Result<(), Error<'p>>;
}
