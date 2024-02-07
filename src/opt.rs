use std::collections::{HashMap, HashSet};

use crate::{Block, CellType, Instr, Program};

#[derive(Clone, Copy, PartialEq)]
enum OptValue<C: CellType> {
    Unknown,
    KnownNonZero,
    Known(C),
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
    mem: OptMemory<'p, C>,
    shift: isize,
    sub_shift: bool,
    insts: Vec<Instr<C>>,
    read: HashSet<isize>,
    written: HashSet<isize>,
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

enum OptLoop<C: CellType> {
    Unknown,
    Infinite,
    NeverOrInfinite,
    AtLeastOnce,
    AtMostOnce,
    Finite,
    Simple,
    SimpleNeg,
    FiniteAtLeastOnce,
    SimpleAtLeastOnce,
    SimpleNegAtLeastOnce,
    NTimes(C),
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

impl<'p, C: CellType> OptMemory<'p, C> {
    fn get(&self, off: isize) -> OptValue<C> {
        self.cells
            .get(&off)
            .copied()
            .unwrap_or_else(|| match &self.fallback {
                OptMemFallback::Constant(c) => *c,
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

impl<C: CellType> OptLoop<C> {
    fn never(&self) -> bool {
        match self {
            OptLoop::NTimes(c) if *c == C::ZERO => true,
            _ => false,
        }
    }

    fn finite(&self) -> bool {
        match self {
            OptLoop::Unknown => false,
            OptLoop::Infinite => false,
            OptLoop::NeverOrInfinite => false,
            OptLoop::AtLeastOnce => false,
            _ => true,
        }
    }

    fn simple(&self) -> bool {
        match self {
            OptLoop::Simple => true,
            OptLoop::SimpleNeg => true,
            OptLoop::SimpleAtLeastOnce => true,
            OptLoop::SimpleNegAtLeastOnce => true,
            OptLoop::NTimes(_) => true,
            _ => false,
        }
    }

    fn at_most_once(&self) -> bool {
        match self {
            OptLoop::AtMostOnce => true,
            OptLoop::NTimes(c) if *c == C::ZERO || *c == C::ONE => true,
            _ => false,
        }
    }

    fn at_least_once(&self) -> bool {
        match self {
            OptLoop::FiniteAtLeastOnce => true,
            OptLoop::SimpleAtLeastOnce => true,
            OptLoop::SimpleNegAtLeastOnce => true,
            OptLoop::AtLeastOnce => true,
            OptLoop::NTimes(c) if *c != C::ZERO => true,
            _ => false,
        }
    }

    fn visible_effect(&self) -> bool {
        match self {
            OptLoop::Infinite => false,
            OptLoop::NeverOrInfinite => false,
            OptLoop::NTimes(c) if *c == C::ZERO => false,
            _ => true,
        }
    }
}

impl<C: CellType> OptBlockAnalysis<C> {
    fn new() -> Self {
        OptBlockAnalysis {
            analyzed: false,
            shift: false,
            read: HashSet::new(),
            written: HashSet::new(),
            known_adds: HashMap::new(),
            known_loads: HashMap::new(),
        }
    }

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

    fn clobbered<'a>(&'a self) -> impl Iterator<Item = isize> + 'a {
        self.written
            .iter()
            .chain(self.known_loads.keys())
            .chain(self.known_adds.keys())
            .copied()
    }
}

impl<'p, C: CellType> OptRebuildState<'p, C> {
    fn new(fallback: OptMemFallback<'p, C>) -> Self {
        OptRebuildState {
            mem: OptMemory {
                fallback,
                cells: HashMap::new(),
            },
            shift: 0,
            sub_shift: false,
            insts: Vec::new(),
            read: HashSet::new(),
            written: HashSet::new(),
            pending_loads: HashMap::new(),
            pending_adds: HashMap::new(),
        }
    }

    fn write(&mut self, dst: isize) {
        self.written.insert(dst);
        self.pending_adds.remove(&dst);
        self.pending_loads.remove(&dst);
        self.mem.set(dst, OptValue::Unknown);
    }

    fn add(&mut self, dst: isize, val: C) {
        if let OptValue::Known(v) = self.get(dst) {
            self.load(dst, v.wrapping_add(val));
        } else {
            let v = self.pending_adds.entry(dst).or_insert(C::ZERO);
            *v = v.wrapping_add(val);
            if *v == C::ZERO {
                self.pending_adds.remove(&dst);
            }
        }
    }

    fn load(&mut self, dst: isize, val: C) {
        if self.get(dst) != OptValue::Known(val) {
            self.pending_adds.remove(&dst);
            self.pending_loads.insert(dst, val);
        }
    }

    fn muladd(&mut self, dst: isize, src: isize, val: C) {
        if let OptValue::Known(src_val) = self.get(src) {
            self.add(dst, val.wrapping_mul(src_val));
        } else {
            self.emit(src);
            self.emit(dst);
            self.write(dst);
            self.insts.push(Instr::MulAdd { val, src, dst });
        }
    }

    fn get(&self, src: isize) -> OptValue<C> {
        if let Some(v) = self.pending_loads.get(&src) {
            OptValue::Known(*v)
        } else if let Some(add) = self.pending_adds.get(&src) {
            if let OptValue::Known(v) = self.mem.get(src) {
                OptValue::Known(add.wrapping_add(v))
            } else {
                OptValue::Unknown
            }
        } else {
            self.mem.get(src)
        }
    }

    fn pending(&self) -> Vec<isize> {
        let mut vec = self
            .pending_adds
            .keys()
            .chain(self.pending_loads.keys())
            .copied()
            .collect::<Vec<_>>();
        vec.sort();
        return vec;
    }

    fn pending_adds(&self) -> Vec<(isize, C)> {
        let mut vec = self
            .pending_adds
            .iter()
            .map(|(k, v)| (*k, *v))
            .collect::<Vec<_>>();
        vec.sort();
        return vec;
    }

    fn pending_loads(&self) -> Vec<(isize, C)> {
        let mut vec = self
            .pending_loads
            .iter()
            .map(|(k, v)| (*k, *v))
            .collect::<Vec<_>>();
        vec.sort();
        return vec;
    }

    fn emit(&mut self, dst: isize) {
        if !self.written.contains(&dst) && !self.pending_loads.contains_key(&dst) {
            self.read.insert(dst);
        }
        if let Some(val) = self.pending_loads.remove(&dst) {
            if self.mem.get(dst) != OptValue::Known(val) {
                self.mem.set(dst, OptValue::Known(val));
                self.insts.push(Instr::Load { val, dst });
            }
        } else if let Some(val) = self.pending_adds.remove(&dst) {
            if val != C::ZERO {
                if let OptValue::Known(v) = self.mem.get_mut(dst) {
                    *v = v.wrapping_add(val);
                } else {
                    self.mem.set(dst, OptValue::Unknown);
                }
                self.insts.push(Instr::Add { val, dst });
            }
        }
    }

    fn reads(&self) -> Vec<isize> {
        let mut vec = self.read.iter().copied().collect::<Vec<_>>();
        vec.sort();
        return vec;
    }

    fn writes(&self) -> Vec<isize> {
        let mut vec = self.written.iter().copied().collect::<Vec<_>>();
        vec.sort();
        return vec;
    }
}

impl<'p, C: CellType> Optimizer<'p, C> {
    fn new(original: &'p Program<C>) -> Self {
        Optimizer {
            original,
            analysis: vec![OptBlockAnalysis::new(); original.blocks.len()],
            blocks: HashMap::new(),
            entry: 0,
        }
    }

    fn analyze_block(&mut self, block_id: usize, non_zero_cond: bool) {
        let analysis = &mut self.analysis[block_id];
        if analysis.analyzed {
            return;
        }
        analysis.analyzed = true;
        let mut analysis = OptBlockAnalysis::new();
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
                    let is_loop = matches!(instr, Instr::Loop { .. });
                    let runs_never =
                        matches!(analysis.known_loads.get(&cond), Some(c) if *c == C::ZERO);
                    let at_least_once = matches!(analysis.known_loads.get(&cond), Some(c) if *c != C::ZERO)
                        || (cond == 0
                            && non_zero_cond
                            && !analysis.known_adds.contains_key(&cond)
                            && !analysis.known_loads.contains_key(&cond)
                            && !analysis.written.contains(&cond));
                    analysis.read(cond);
                    self.analyze_block(block, true);
                    if !runs_never {
                        let sub_analysis = &self.analysis[block];
                        let sub_shift = self.original.blocks[block].shift;
                        if sub_analysis.shift || sub_shift != 0 {
                            analysis.shift = true;
                            analysis.known_adds.clear();
                            analysis.known_loads.clear();
                            analysis.written.clear();
                        } else {
                            for &var in &sub_analysis.read {
                                analysis.read(cond + var);
                            }
                            for &var in &sub_analysis.written {
                                analysis.write(cond + var);
                            }
                            if !at_least_once {
                                for &var in sub_analysis.known_loads.keys() {
                                    analysis.write(cond + var);
                                }
                            }
                            for &var in sub_analysis.known_adds.keys() {
                                analysis.read(cond + var);
                                analysis.write(cond + var);
                            }
                        }
                        if at_least_once {
                            for (&var, &val) in &sub_analysis.known_loads {
                                analysis.load(cond + var - sub_shift, val)
                            }
                        }
                        if is_loop {
                            analysis.load(cond, C::ZERO);
                        }
                    }
                }
            }
        }
        self.analysis[block_id] = analysis;
    }

    fn analyze(&mut self) {
        self.analyze_block(self.original.entry, false);
    }

    fn analyze_loop_in(
        &self,
        cond: isize,
        initial_state: &OptRebuildState<C>,
        block_id: usize,
        is_loop: bool,
    ) -> OptLoop<C> {
        let analysis = &self.analysis[block_id];
        let block = &self.original.blocks[block_id];
        if let OptValue::Known(known_val) = initial_state.get(cond) {
            if known_val == C::ZERO {
                OptLoop::NTimes(C::ZERO)
            } else if !is_loop {
                OptLoop::NTimes(C::ONE)
            } else if let Some(v) = analysis.known_loads.get(&block.shift) {
                if *v == C::ZERO {
                    OptLoop::NTimes(C::ONE)
                } else {
                    OptLoop::Infinite
                }
            } else if analysis.shift || block.shift != 0 {
                OptLoop::AtLeastOnce
            } else if let Some(inc) = analysis.known_adds.get(&block.shift) {
                if let Some(count) = known_val.wrapping_div(inc.wrapping_neg()) {
                    OptLoop::NTimes(count)
                } else {
                    OptLoop::Infinite
                }
            } else {
                OptLoop::AtLeastOnce
            }
        } else {
            let at_least_once = matches!(initial_state.get(cond), OptValue::KnownNonZero);
            if !is_loop {
                if at_least_once {
                    OptLoop::NTimes(C::ONE)
                } else {
                    OptLoop::AtMostOnce
                }
            } else if let Some(v) = analysis.known_loads.get(&block.shift) {
                if *v == C::ZERO {
                    if at_least_once {
                        OptLoop::NTimes(C::ONE)
                    } else {
                        OptLoop::AtMostOnce
                    }
                } else {
                    if at_least_once {
                        OptLoop::Infinite
                    } else {
                        OptLoop::NeverOrInfinite
                    }
                }
            } else if analysis.shift || block.shift != 0 {
                if at_least_once {
                    OptLoop::AtLeastOnce
                } else {
                    OptLoop::Unknown
                }
            } else if let Some(inc) = analysis.known_adds.get(&block.shift) {
                if *inc == C::ZERO {
                    if at_least_once {
                        OptLoop::Infinite
                    } else {
                        OptLoop::NeverOrInfinite
                    }
                } else if *inc == C::ONE {
                    if at_least_once {
                        OptLoop::SimpleNegAtLeastOnce
                    } else {
                        OptLoop::SimpleNeg
                    }
                } else if *inc == C::NEG_ONE {
                    if at_least_once {
                        OptLoop::SimpleAtLeastOnce
                    } else {
                        OptLoop::Simple
                    }
                } else if inc.is_odd() {
                    if at_least_once {
                        OptLoop::FiniteAtLeastOnce
                    } else {
                        OptLoop::Finite
                    }
                } else {
                    if at_least_once {
                        OptLoop::AtLeastOnce
                    } else {
                        OptLoop::Unknown
                    }
                }
            } else if !analysis.written.contains(&block.shift) {
                if at_least_once {
                    OptLoop::Infinite
                } else {
                    OptLoop::NeverOrInfinite
                }
            } else {
                if at_least_once {
                    OptLoop::AtLeastOnce
                } else {
                    OptLoop::Unknown
                }
            }
        }
    }

    fn rebuild_block(&mut self, block_id: usize, state: &mut OptRebuildState<C>) {
        let block = &self.original.blocks[block_id];
        for instr in &block.insts {
            match instr.clone() {
                Instr::Output { src } => {
                    let src = src + state.shift;
                    state.emit(src);
                    state.insts.push(Instr::Output { src });
                }
                Instr::Input { dst } => {
                    let dst = dst + state.shift;
                    state.write(dst);
                    state.insts.push(Instr::Input { dst });
                }
                Instr::Load { val, dst } => {
                    let dst = dst + state.shift;
                    state.load(dst, val);
                }
                Instr::Add { val, dst } => {
                    let dst = dst + state.shift;
                    state.add(dst, val);
                }
                Instr::MulAdd { val, src, dst } => {
                    let dst = dst + state.shift;
                    let src = src + state.shift;
                    state.muladd(dst, src, val);
                }
                Instr::Loop { cond, block } | Instr::If { cond, block } => {
                    let is_loop = matches!(instr, Instr::Loop { .. });
                    let cond = cond + state.shift;
                    let loop_analysis = self.analyze_loop_in(cond, &state, block, is_loop);
                    if loop_analysis.at_least_once() && loop_analysis.at_most_once() {
                        state.shift += cond;
                        self.rebuild_block(block, state);
                        state.shift -= cond;
                    } else if !loop_analysis.never() {
                        let sub_block = &self.original.blocks[block];
                        let analysis = &self.analysis[block];
                        let mut sub_state = OptRebuildState::new(OptMemFallback::Parent {
                            offset: cond,
                            parent: &state.mem,
                        });
                        if !loop_analysis.at_most_once() {
                            if !loop_analysis.at_most_once()
                                && (analysis.shift || sub_block.shift != 0)
                            {
                                sub_state.mem.fallback =
                                    OptMemFallback::Constant(OptValue::Unknown);
                            } else {
                                for var in analysis.clobbered() {
                                    sub_state.mem.set(var, OptValue::Unknown);
                                }
                            }
                        }
                        if let OptValue::Unknown = sub_state.mem.get(0) {
                            sub_state.mem.set(0, OptValue::KnownNonZero);
                        }
                        self.rebuild_block(block, &mut sub_state);
                        let sub_shift = sub_state.shift != 0 || sub_state.sub_shift;
                        if sub_shift {
                            state.sub_shift = true;
                        }
                        if !loop_analysis.simple() {
                            for (var, _) in sub_state.pending_adds() {
                                sub_state.emit(var);
                            }
                        }
                        if !loop_analysis.at_most_once() {
                            if sub_shift {
                                for var in sub_state.pending() {
                                    sub_state.emit(var);
                                }
                            } else {
                                for var in sub_state.reads() {
                                    sub_state.emit(var);
                                }
                            }
                            if !sub_state.insts.is_empty() {
                                sub_state.emit(sub_state.shift);
                            }
                        }
                        let reads = sub_state.reads();
                        let writes = sub_state.writes();
                        let pending_adds = sub_state.pending_adds();
                        let pending_loads = sub_state.pending_loads();
                        let can_eliminate =
                            !sub_shift && sub_state.insts.is_empty() && loop_analysis.finite();
                        let needs_if = loop_analysis.at_most_once()
                            || (!loop_analysis.at_least_once() && !pending_loads.is_empty());
                        let mut new_insts = Vec::new();
                        if loop_analysis.at_most_once() {
                            new_insts.append(&mut sub_state.insts);
                        } else if !can_eliminate {
                            let sub_block_id = self.blocks.len();
                            let sub_block_id = *self
                                .blocks
                                .entry(Block {
                                    shift: sub_state.shift,
                                    insts: sub_state.insts,
                                })
                                .or_insert(sub_block_id);
                            new_insts.push(Instr::Loop {
                                cond: if needs_if { 0 } else { cond },
                                block: sub_block_id,
                            });
                        }
                        let mut has_pending_cond = false;
                        if !loop_analysis.at_least_once() {
                            for &(var, val) in &pending_loads {
                                if var == 0 {
                                    has_pending_cond = true;
                                } else {
                                    new_insts.push(Instr::Load {
                                        val,
                                        dst: if loop_analysis.at_most_once() {
                                            var
                                        } else {
                                            if needs_if {
                                                var - sub_state.shift
                                            } else {
                                                cond + var - sub_state.shift
                                            }
                                        },
                                    })
                                }
                            }
                        }
                        if needs_if {
                            let sub_block_id = self.blocks.len();
                            let sub_block_id = *self
                                .blocks
                                .entry(Block {
                                    shift: if loop_analysis.at_most_once() {
                                        sub_state.shift
                                    } else {
                                        0
                                    },
                                    insts: new_insts,
                                })
                                .or_insert(sub_block_id);
                            new_insts = vec![Instr::If {
                                cond,
                                block: sub_block_id,
                            }];
                        }
                        if sub_shift {
                            for var in state.pending() {
                                state.emit(var);
                            }
                        } else if !can_eliminate {
                            state.emit(cond);
                            for var in reads {
                                state.emit(cond + var);
                            }
                        }
                        for (var, val) in pending_adds {
                            if var == 0 {
                                has_pending_cond = true;
                            } else {
                                match loop_analysis {
                                    OptLoop::Simple | OptLoop::SimpleAtLeastOnce => {
                                        state.muladd(cond + var, cond, val);
                                    }
                                    OptLoop::SimpleNeg | OptLoop::SimpleNegAtLeastOnce => {
                                        state.muladd(cond + var, cond, val.wrapping_neg());
                                    }
                                    OptLoop::NTimes(n) => {
                                        state.add(cond + var, n.wrapping_mul(val));
                                    }
                                    _ => unreachable!(),
                                }
                            }
                        }
                        state.insts.append(&mut new_insts);
                        if loop_analysis.visible_effect() {
                            if sub_shift {
                                state.mem.fallback = OptMemFallback::Constant(OptValue::Unknown);
                                state.mem.cells.clear();
                            } else if !can_eliminate {
                                for var in writes {
                                    state.mem.set(cond + var, OptValue::Unknown);
                                }
                            }
                        }
                        if loop_analysis.at_least_once() {
                            for (var, val) in pending_loads {
                                state.load(cond + var - sub_block.shift, val);
                            }
                        }
                        if is_loop {
                            if has_pending_cond {
                                state.load(cond, C::ZERO);
                            } else {
                                state.mem.set(cond, OptValue::Known(C::ZERO));
                            }
                        }
                    }
                }
            }
        }
        state.shift += block.shift;
    }

    fn rebuild(&mut self) {
        let mut state = OptRebuildState::new(OptMemFallback::Constant(OptValue::Known(C::ZERO)));
        self.rebuild_block(self.original.entry, &mut state);
        self.entry = self.blocks.len();
        self.blocks.insert(
            Block {
                shift: state.shift,
                insts: state.insts,
            },
            self.entry,
        );
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
