use crate::{CellType, Context, Error};

#[macro_use]
mod testdef;

mod baseint;

pub use baseint::BaseInterpreter;

/// Trait implemented by the different execution strategies provided by this crate.
pub trait Executor<'p, C: CellType>: Sized {
    /// Creates a new instance of the executor to run on the given code. The
    /// code may be captured or used to create other internal representations.
    /// If the executor supports optimizations, they should be influenced by the
    /// `no_opt` and `opt` parameters to this method.
    fn create(code: &'p str, no_opt: bool, opt: u32) -> Result<Self, Error>;

    /// Execute the executor in the given [`Context`].
    fn execute(&self, context: &mut Context<C>) -> Result<(), Error>;
}
