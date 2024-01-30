use crate::{Block, CellType, Context};

impl<'a, C: CellType> Context<'a, C> {
    pub fn jit_print_module<'b>(
        &'b mut self,
        _opt: u32,
        _program: &Block<C>,
    ) -> Result<(), String> {
        todo!();
    }

    pub fn jit_execute<'b>(&'b mut self, _opt: u32, _program: &Block<C>) -> Result<(), String> {
        todo!();
    }
}
