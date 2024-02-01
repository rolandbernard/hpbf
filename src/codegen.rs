//! Contains the JIT compiler using LLVM as the backend.

use crate::{CellType, Context, Program};

impl<'a, C: CellType> Context<'a, C> {
    /// Print the JIT internal IR for the given `program` and optimization level
    /// `opt` to stderr. Do not execute anything.
    pub fn jit_print_module<'b>(
        &'b mut self,
        _opt: u32,
        _program: &Program<C>,
    ) -> Result<(), String> {
        todo!();
    }

    /// Execute the given `program` in this context. Do execution using the JIT
    /// compiler with the optimization level given by `opt`.
    pub fn jit_execute<'b>(&'b mut self, _opt: u32, _program: &Program<C>) -> Result<(), String> {
        todo!();
    }
}
