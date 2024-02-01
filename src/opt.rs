use std::collections::{HashMap, HashSet};

use crate::{Block, CellType, Instr, Program};

enum OptValue<C: CellType> {
    Unknown,
    Known(Vec<C>),
}

enum OptMemFallback<'p, C: CellType> {
    Constant(C),
    Parent(&'p OptMemory<'p, C>),
}

struct OptMemory<'p, C: CellType> {
    fallback: OptMemFallback<'p, C>,
    known: HashMap<isize, OptValue<C>>,
}

#[derive(Clone)]
struct OptBlockAnalysis<C: CellType> {
    analyzed: bool,
    shift: bool,
    read: HashSet<isize>,
    written: HashSet<isize>,
    known_adds: HashMap<isize, C>,
    known_loads: HashMap<isize, C>,
}

struct Optimizer<'p, C: CellType> {
    original: &'p Program<C>,
    analysis: Vec<OptBlockAnalysis<C>>,
    blocks: HashMap<Block<C>, usize>,
    entry: usize,
}

impl<C: CellType> Program<C> {
    /// Optimize the program, and return the optimized copy of the program.
    pub fn optimize(&self) -> Self {
        let mut opt = Optimizer::new(&self);
        opt.analyze();
        opt.rebuild();
        return opt.finalize();
    }
}

impl<'p, C: CellType> Optimizer<'p, C> {
    fn new(original: &'p Program<C>) -> Self {
        Optimizer {
            original,
            analysis: vec![
                OptBlockAnalysis {
                    analyzed: false,
                    shift: false,
                    read: HashSet::new(),
                    written: HashSet::new(),
                    known_adds: HashMap::new(),
                    known_loads: HashMap::new(),
                };
                original.blocks.len()
            ],
            blocks: HashMap::new(),
            entry: 0,
        }
    }

    fn analyze_block(&mut self, block_id: usize) {
        let analysis = &mut self.analysis[block_id];
        if analysis.analyzed {
            return;
        }
        analysis.analyzed = true;
        let mut analysis = analysis.clone();
        let block = &self.original.blocks[block_id];
        for instr in &block.insts {
            match instr {
                Instr::Output { src } => {
                    if !analysis.written.contains(src) && !analysis.known_loads.contains_key(src) {
                        analysis.read.insert(*src);
                    }
                }
                Instr::Input { dst } => {
                    analysis.written.insert(*dst);
                    analysis.known_adds.remove(dst);
                    analysis.known_loads.remove(dst);
                }
                Instr::Load { val, dst } => {
                    analysis.known_adds.remove(dst);
                    analysis.known_loads.insert(*dst, *val);
                }
                Instr::Add { val, dst } => {
                    if let Some(v) = analysis.known_loads.get_mut(dst) {
                        *v = v.wrapping_add(*val);
                    } else if !analysis.written.contains(dst) {
                        let v = analysis.known_adds.entry(*dst).or_insert(C::ZERO);
                        *v = v.wrapping_add(*val);
                        if *v == C::ZERO {
                            analysis.known_adds.remove(dst);
                        }
                    }
                }
                Instr::MulAdd { val, src, dst } => {
                    if let Some(src_val) = analysis.known_loads.get(src) {
                        let val = val.wrapping_mul(*src_val);
                        if let Some(v) = analysis.known_loads.get_mut(dst) {
                            *v = v.wrapping_add(val);
                        } else if !analysis.written.contains(dst) {
                            let v = analysis.known_adds.entry(*dst).or_insert(C::ZERO);
                            *v = v.wrapping_add(val);
                            if *v == C::ZERO {
                                analysis.known_adds.remove(dst);
                            }
                        }
                    } else {
                        if !analysis.written.contains(src)
                            && !analysis.known_loads.contains_key(src)
                        {
                            analysis.read.insert(*src);
                        }
                        analysis.written.insert(*dst);
                        analysis.known_adds.remove(dst);
                        analysis.known_loads.remove(dst);
                    }
                }
                Instr::Loop { cond, block } | Instr::If { cond, block } => {
                    let is_loop = matches!(instr, Instr::Load { .. });
                    if !analysis.written.contains(cond) && !analysis.known_loads.contains_key(cond)
                    {
                        analysis.read.insert(*cond);
                    }
                    self.analyze_block(*block);
                    let sub_analysis = &self.analysis[*block];
                    let sub_shift = self.original.blocks[*block].shift;
                    if sub_analysis.shift || sub_shift != 0 {
                        analysis.shift = true;
                        analysis.known_adds.clear();
                        analysis.known_loads.clear();
                        analysis.written.clear();
                    } else {
                        for var in &sub_analysis.read {
                            analysis.read.insert(*var);
                        }
                        for var in sub_analysis
                            .written
                            .iter()
                            .chain(sub_analysis.known_adds.keys())
                        {
                            analysis.known_adds.remove(var);
                            analysis.known_loads.remove(var);
                            analysis.written.insert(*var);
                        }
                    }
                    for (var, val) in &sub_analysis.known_loads {
                        analysis.known_adds.remove(&(*var - sub_shift));
                        analysis.known_loads.insert(*var - sub_shift, *val);
                    }
                    if is_loop {
                        analysis.known_adds.remove(cond);
                        analysis.known_loads.insert(*cond, C::ZERO);
                    }
                }
            }
        }
        self.analysis[block_id] = analysis;
    }

    fn analyze(&mut self) {
        self.analyze_block(self.original.entry);
    }

    fn rebuild(&mut self) {
        todo!();
    }

    fn finalize(self) -> Program<C> {
        todo!();
    }
}
