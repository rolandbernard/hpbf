use crate::{CellType, Program};

impl<C: CellType> Program<C> {
    /// Optimize the program, and return the optimized copy of the program.
    pub fn optimize(&self) -> Self {
        // TODO:
        self.clone()
    }
}
