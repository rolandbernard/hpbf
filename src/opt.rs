use std::collections::{HashMap, HashSet};

use crate::{Block, CellType, Instr, Program};

#[derive(Clone)]
enum OptValue<C: CellType> {
    Unknown,
    Known(Vec<C>),
}

enum OptMemFallback<'p, C: CellType> {
    Constant(OptValue<C>),
    Parent {
        offset: isize,
        parent: &'p OptMemory<'p, C>,
    },
}

struct OptMemory<'p, C: CellType> {
    fallback: OptMemFallback<'p, C>,
    cells: HashMap<isize, OptValue<C>>,
}

struct OptRebuildState<'p, C: CellType> {
    mem: &'p mut OptMemory<'p, C>,
    insts: Vec<Instr<C>>,
    pending_loads: HashMap<isize, C>,
    pending_adds: HashMap<isize, C>,
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

impl<C: CellType> OptValue<C> {
    fn unique(&self) -> Option<C> {
        match self {
            OptValue::Known(v) if v.len() == 1 => Some(v[0]),
            _ => None,
        }
    }
}

impl<'p, C: CellType> OptMemory<'p, C> {
    fn get(&self, off: isize) -> &OptValue<C> {
        self.cells
            .get(&off)
            .unwrap_or_else(|| match &self.fallback {
                OptMemFallback::Constant(c) => c,
                OptMemFallback::Parent { offset, parent } => parent.get(off + offset),
            })
    }

    fn get_mut(&mut self, off: isize) -> &mut OptValue<C> {
        self.cells
            .entry(off)
            .or_insert_with(|| match &self.fallback {
                OptMemFallback::Constant(c) => c.clone(),
                OptMemFallback::Parent { offset, parent } => parent.get(off + offset).clone(),
            })
    }

    fn set(&mut self, off: isize, val: OptValue<C>) {
        self.cells.insert(off, val);
    }
}

impl<C: CellType> OptBlockAnalysis<C> {
    fn write(&mut self, dst: isize) {
        self.written.insert(dst);
        self.known_adds.remove(&dst);
        self.known_loads.remove(&dst);
    }

    fn read(&mut self, src: isize) {
        if !self.written.contains(&src) && !self.known_loads.contains_key(&src) {
            self.read.insert(src);
        }
    }

    fn add(&mut self, dst: isize, val: C) {
        if let Some(v) = self.known_loads.get_mut(&dst) {
            *v = v.wrapping_add(val);
        } else if !self.written.contains(&dst) {
            let v = self.known_adds.entry(dst).or_insert(C::ZERO);
            *v = v.wrapping_add(val);
            if *v == C::ZERO {
                self.known_adds.remove(&dst);
            }
        }
    }

    fn load(&mut self, dst: isize, val: C) {
        self.known_adds.remove(&dst);
        self.known_loads.insert(dst, val);
    }
}

impl<'p, C: CellType> OptRebuildState<'p, C> {
    fn write(&mut self, dst: isize) {
        self.pending_adds.remove(&dst);
        self.pending_loads.remove(&dst);
        self.mem.set(dst, OptValue::Unknown);
    }

    fn add(&mut self, dst: isize, val: C) {
        if let Some(v) = self.pending_loads.get_mut(&dst) {
            *v = v.wrapping_add(val);
        } else {
            let v = self.pending_adds.entry(dst).or_insert(C::ZERO);
            *v = v.wrapping_add(val);
            if *v == C::ZERO {
                self.pending_adds.remove(&dst);
            }
        }
    }

    fn load(&mut self, dst: isize, val: C) {
        self.pending_adds.remove(&dst);
        self.pending_loads.insert(dst, val);
    }

    fn get_unique(&self, src: isize) -> Option<C> {
        if let Some(v) = self.pending_loads.get(&src) {
            Some(*v)
        } else if let Some(v) = self.mem.get(src).unique() {
            if let Some(add) = self.pending_adds.get(&src) {
                Some(add.wrapping_add(v))
            } else {
                Some(v)
            }
        } else {
            None
        }
    }

    fn emit(&mut self, dst: isize) {
        if let Some(val) = self.pending_loads.remove(&dst) {
            if self.mem.get(dst).unique() != Some(val) {
                self.mem.set(dst, OptValue::Known(vec![val]));
                self.insts.push(Instr::Load { val, dst });
            }
        } else if let Some(val) = self.pending_adds.remove(&dst) {
            if val != C::ZERO {
                if let OptValue::Known(vs) = self.mem.get_mut(dst) {
                    for v in vs {
                        *v = v.wrapping_add(val);
                    }
                }
                self.insts.push(Instr::Add { val, dst });
            }
        }
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
            match instr.clone() {
                Instr::Output { src } => {
                    analysis.read(src);
                }
                Instr::Input { dst } => {
                    analysis.write(dst);
                }
                Instr::Load { val, dst } => {
                    analysis.load(dst, val);
                }
                Instr::Add { val, dst } => {
                    analysis.add(dst, val);
                }
                Instr::MulAdd { val, src, dst } => {
                    if let Some(src_val) = analysis.known_loads.get(&src) {
                        let val = val.wrapping_mul(*src_val);
                        analysis.add(dst, val);
                    } else {
                        analysis.read(src);
                        analysis.read(dst);
                        analysis.write(dst);
                    }
                }
                Instr::Loop { cond, block } | Instr::If { cond, block } => {
                    let is_loop = matches!(instr, Instr::Load { .. });
                    analysis.read(cond);
                    self.analyze_block(block);
                    let sub_analysis = &self.analysis[block];
                    let sub_shift = self.original.blocks[block].shift;
                    if sub_analysis.shift || sub_shift != 0 {
                        analysis.shift = true;
                        analysis.known_adds.clear();
                        analysis.known_loads.clear();
                        analysis.written.clear();
                    } else {
                        for &var in &sub_analysis.read {
                            analysis.read(var);
                        }
                        for &var in &sub_analysis.written {
                            analysis.write(var);
                        }
                        for &var in sub_analysis.known_adds.keys() {
                            analysis.read(var);
                            analysis.write(var);
                        }
                    }
                    for (&var, &val) in &sub_analysis.known_loads {
                        analysis.load(var - sub_shift, val);
                    }
                    if is_loop {
                        analysis.load(cond, C::ZERO);
                    }
                }
            }
        }
        self.analysis[block_id] = analysis;
    }

    fn analyze(&mut self) {
        self.analyze_block(self.original.entry);
    }

    fn rebuild_block<'b>(
        &mut self,
        block_id: usize,
        mem: &'b mut OptMemory<'b, C>,
    ) -> OptRebuildState<'b, C> {
        let mut state = OptRebuildState {
            mem,
            insts: Vec::new(),
            pending_loads: HashMap::new(),
            pending_adds: HashMap::new(),
        };
        let block = &self.original.blocks[block_id];
        for instr in &block.insts {
            match instr.clone() {
                Instr::Output { src } => {
                    state.emit(src);
                    state.insts.push(Instr::Output { src });
                }
                Instr::Input { dst } => {
                    state.write(dst);
                    state.insts.push(Instr::Input { dst });
                }
                Instr::Load { val, dst } => {
                    state.load(dst, val);
                }
                Instr::Add { val, dst } => {
                    state.add(dst, val);
                }
                Instr::MulAdd { val, src, dst } => {
                    if let Some(src_val) = state.get_unique(src) {
                        state.add(dst, val.wrapping_mul(src_val));
                    } else {
                        state.emit(src);
                        state.emit(dst);
                        state.write(dst);
                        state.insts.push(Instr::MulAdd { val, src, dst });
                    }
                }
                Instr::Loop { cond, block } | Instr::If { cond, block } => {
                    let is_loop = matches!(instr, Instr::Load { .. });
                    todo!();
                }
            }
        }
        return state;
    }

    fn rebuild(&mut self) {
        let mut memory = OptMemory {
            fallback: OptMemFallback::Constant(OptValue::Known(vec![C::ZERO])),
            cells: HashMap::new(),
        };
        let build_result = self.rebuild_block(self.original.entry, &mut memory);
        todo!();
    }

    fn finalize(self) -> Program<C> {
        let mut program = Program {
            entry: self.entry,
            blocks: vec![
                Block {
                    shift: 0,
                    insts: Vec::new()
                };
                self.blocks.len()
            ],
        };
        for (block, idx) in self.blocks {
            program.blocks[idx] = block;
        }
        return program;
    }
}
