use crate::{Block, CellType, Context};

impl<'a, C: CellType> Context<'a, C> {
    pub fn jit_execute(&mut self, program: &Block<C>) {
        // TODO: implement JIT compiler.
        self.execute(program);
    }
}
