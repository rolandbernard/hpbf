//! Contains the JIT compiler using LLVM as the backend.

use crate::{CellType, Context, Program};

impl<'a, C: CellType> Context<'a, C> {
    pub fn jit_print_module<'b>(
        &'b mut self,
        _opt: u32,
        _program: &Program<C>,
    ) -> Result<(), String> {
        todo!();
    }

    pub fn jit_execute<'b>(&'b mut self, _opt: u32, _program: &Program<C>) -> Result<(), String> {
        todo!();
    }
}
