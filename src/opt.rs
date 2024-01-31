use std::collections::{HashMap, HashSet};

use crate::{Block, CellType, Program};

enum OptBlockAnalysis<C: CellType> {
    Moving,
    Static {
        read: HashSet<isize>,
        written: HashSet<isize>,
        known_adds: HashMap<isize, C>,
    },
}

struct Optimizer<C: CellType> {
    original: Program<C>,
    analysis: Vec<OptBlockAnalysis<C>>,
    blocks: HashMap<Block<C>, usize>,
}

impl<C: CellType> Program<C> {
    /// Optimize the program, and return the optimized program.
    pub fn optimize(self) -> Self {
        todo!()
    }
}
