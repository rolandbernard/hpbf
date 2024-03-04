//! Contains transformation form the IR to the interpreter Bytecode.

use std::{
    cmp::Reverse,
    collections::{BTreeSet, BinaryHeap, HashMap, HashSet},
    fmt::{self, Debug},
    mem,
};

use crate::{
    ir::{self, Block, Expr},
    CellType,
};

/// Location form which to load or store values.
#[derive(PartialEq, Hash, Clone, Copy)]
pub enum Loc<C: CellType> {
    Mem(isize),
    MemZero(isize),
    Tmp(usize),
    Imm(C),
}

/// Instruction representation for the bytecode. Only select instructions use
/// [`Loc`]. All other access memory only.
#[derive(PartialEq, Hash, Clone, Copy)]
pub enum Instr<C: CellType> {
    Noop,
    Scan(isize, isize),
    Mov(isize),
    Inp(isize),
    Out(isize),
    BrZ(isize, isize),
    BrNZ(isize, isize),
    Add(Loc<C>, Loc<C>, Loc<C>),
    Sub(Loc<C>, Loc<C>, Loc<C>),
    Mul(Loc<C>, Loc<C>, Loc<C>),
    Copy(Loc<C>, Loc<C>),
}

/// Represents a bytecode program. Includes, in addition to the instructions,
/// also the number of necessary temporaries.
pub struct Program<C: CellType> {
    pub temps: usize,
    pub min_accessed: isize,
    pub max_accessed: isize,
    pub insts: Vec<Instr<C>>,
}

/// Analysis result used for bytecode generation.
struct Analysis {
    has_shift: bool,
    writes: HashSet<isize>,
    sub_anal: Vec<Analysis>,
    min_accessed: isize,
    max_accessed: isize,
}

/// Live range information for the temporaries, used later on during temp allocation.
struct RangeInfo {
    created: usize,
    first_use: Option<usize>,
    last_use: Option<usize>,
    num_uses: usize,
}

/// Computation to be used with the global value numbering.
#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub enum GvnExpr<C: CellType> {
    Imm(C),
    Mem(isize),
    Add(usize, usize),
    Sub(usize, usize),
    Mul(usize, usize),
}

/// State for the bytecode generator.
pub struct CodeGen<C: CellType> {
    min_accessed: isize,
    max_accessed: isize,
    writes: HashMap<isize, BTreeSet<usize>>,
    ranges: Vec<RangeInfo>,
    exprs: Vec<GvnExpr<C>>,
    values: HashMap<GvnExpr<C>, usize>,
    insts: Vec<Instr<C>>,
    current_start: usize,
    outer_accessed: Vec<usize>,
}

impl Analysis {
    /// Record that the memory address `var` has been accessed.
    fn accessed(&mut self, var: isize) {
        if self.min_accessed > var {
            self.min_accessed = var;
        }
        if self.max_accessed < var {
            self.max_accessed = var;
        }
    }

    /// Record that the memory address `var` has been written. Written addresses
    /// also count as accessed.
    fn written(&mut self, var: isize) {
        self.accessed(var);
        if !self.has_shift {
            self.writes.insert(var);
        }
    }

    /// Analyze the given `block` and return the result.
    fn analyze<C: CellType>(block: &Block<C>) -> Self {
        let mut anal = Analysis {
            has_shift: false,
            writes: HashSet::new(),
            sub_anal: Vec::new(),
            min_accessed: 0,
            max_accessed: 0,
        };
        for inst in &block.insts {
            match inst {
                ir::Instr::Output { src } => anal.accessed(*src),
                ir::Instr::Input { dst } => anal.written(*dst),
                ir::Instr::Calc { calcs } => {
                    for (var, calc) in calcs {
                        for var in calc.variables() {
                            anal.accessed(var);
                        }
                        anal.written(*var);
                    }
                }
                ir::Instr::Loop { cond, block, .. } | ir::Instr::If { cond, block } => {
                    anal.accessed(*cond);
                    let sub_analysis = Self::analyze(block);
                    anal.accessed(sub_analysis.min_accessed);
                    anal.accessed(sub_analysis.max_accessed);
                    if sub_analysis.has_shift {
                        anal.has_shift = true;
                        anal.writes = HashSet::new();
                    } else if !anal.has_shift {
                        for &var in &sub_analysis.writes {
                            anal.written(var);
                        }
                    }
                    anal.sub_anal.push(sub_analysis);
                }
            }
        }
        if block.shift != 0 {
            anal.has_shift = true;
        }
        return anal;
    }
}

impl<C: CellType> ir::CodeGen<C> for CodeGen<C> {
    type Output = usize;
    type Error = ();

    fn imm(&mut self, imm: C) -> Result<Self::Output, Self::Error> {
        Ok(self.get_value(GvnExpr::Imm(imm)))
    }

    fn mem(&mut self, var: isize) -> Result<Self::Output, Self::Error> {
        Ok(self.get_value(GvnExpr::Mem(var)))
    }

    fn add(&mut self, a: Self::Output, b: Self::Output) -> Result<Self::Output, Self::Error> {
        Ok(self.get_value(GvnExpr::Add(a, b)))
    }

    fn sub(&mut self, a: Self::Output, b: Self::Output) -> Result<Self::Output, Self::Error> {
        Ok(self.get_value(GvnExpr::Sub(a, b)))
    }

    fn mul(&mut self, a: Self::Output, b: Self::Output) -> Result<Self::Output, Self::Error> {
        Ok(self.get_value(GvnExpr::Mul(a, b)))
    }
}

impl<C: CellType> CodeGen<C> {
    /// Like a range extend but not to the end of the currently emitted program.
    fn range_extend_to(&mut self, value: usize, to: usize) {
        if self.ranges[value].first_use.is_none() {
            self.ranges[value].first_use = Some(to);
        }
        self.ranges[value].last_use = Some(to);
    }

    /// Like a read, but does not increment the uses counter, only extends the range.
    fn range_extend(&mut self, value: usize) {
        if self.ranges[value].created < self.current_start {
            if self.ranges[value].last_use.is_none()
                || self.ranges[value].last_use.unwrap() < self.current_start
            {
                self.outer_accessed.push(value);
            }
        }
        self.range_extend_to(value, self.insts.len());
    }

    /// Record in the live ranges that the given `value` has been accessed.
    fn read(&mut self, value: usize) {
        self.range_extend(value);
        self.ranges[value].num_uses += 1;
    }

    /// Get the temporary number for the given expression. This will reuse existing
    /// temporaries, or emit new instructions to perform the necessary operations.
    fn get_value(&mut self, expr: GvnExpr<C>) -> usize {
        if let Some(value) = self.values.get(&expr) {
            *value
        } else {
            let value = self.ranges.len();
            self.ranges.push(RangeInfo {
                created: self.insts.len(),
                first_use: None,
                last_use: None,
                num_uses: 0,
            });
            self.exprs.push(expr);
            if let GvnExpr::Add(a, b) | GvnExpr::Sub(a, b) | GvnExpr::Mul(a, b) = expr {
                self.read(a);
                self.read(b);
            }
            let inst = match expr {
                GvnExpr::Imm(v) => Instr::Copy(Loc::Tmp(value), Loc::Imm(v)),
                GvnExpr::Mem(v) => Instr::Copy(Loc::Tmp(value), Loc::Mem(v)),
                GvnExpr::Add(a, b) => Instr::Add(Loc::Tmp(value), Loc::Tmp(a), Loc::Tmp(b)),
                GvnExpr::Sub(a, b) => Instr::Sub(Loc::Tmp(value), Loc::Tmp(a), Loc::Tmp(b)),
                GvnExpr::Mul(a, b) => Instr::Mul(Loc::Tmp(value), Loc::Tmp(a), Loc::Tmp(b)),
            };
            self.insts.push(inst);
            self.values.insert(expr, value);
            value
        }
    }

    /// Create/get a temporary containing the result of the given expression.
    fn get_expr_value(&mut self, expr: &Expr<C>, var: isize) -> usize {
        expr.codegen(self, |x| if x == var { 1 } else { 0 })
            .unwrap()
    }

    /// Record that the value stored in the given memory location is from now on
    /// the value of the given temporary `value`.
    fn mem_write(&mut self, var: isize, value: usize) {
        self.read(value);
        self.writes
            .entry(var)
            .or_insert(BTreeSet::new())
            .insert(self.insts.len());
        self.values.insert(GvnExpr::Mem(var), value);
        self.insts.push(Instr::Copy(Loc::Mem(var), Loc::Tmp(value)));
    }

    /// Emit the instructions for the inside of the given block. This does not
    /// include the move instruction of the block.
    fn emit_block(&mut self, block: &Block<C>, anal: &Analysis) {
        let mut block_idx = 0;
        let prev_start = self.current_start;
        for inst in &block.insts {
            match inst {
                ir::Instr::Output { src } => {
                    self.insts.push(Instr::Out(*src));
                }
                ir::Instr::Input { dst } => {
                    self.values.remove(&GvnExpr::Mem(*dst));
                    self.writes
                        .entry(*dst)
                        .or_insert(BTreeSet::new())
                        .insert(self.insts.len());
                    self.insts.push(Instr::Inp(*dst));
                }
                ir::Instr::Calc { calcs } => {
                    let mut values = Vec::with_capacity(calcs.len());
                    for (var, calc) in calcs {
                        values.push((*var, self.get_expr_value(calc, *var)));
                    }
                    for (var, value) in values {
                        self.mem_write(var, value);
                    }
                }
                ir::Instr::Loop { cond, block, .. } | ir::Instr::If { cond, block } => {
                    let is_loop = matches!(inst, ir::Instr::Loop { .. });
                    let at_least_once = matches!(inst, ir::Instr::Loop { once: true, .. });
                    let sub_anal = &anal.sub_anal[block_idx];
                    if is_loop {
                        if sub_anal.has_shift {
                            self.values.clear();
                        } else {
                            for &var in &sub_anal.writes {
                                self.values.remove(&GvnExpr::Mem(var));
                            }
                        }
                    }
                    let prev_exprs = self.exprs.len();
                    let num_outer = self.outer_accessed.len();
                    if !is_loop || !block.insts.is_empty() {
                        if !at_least_once {
                            self.insts.push(Instr::Noop);
                        }
                        let start_instr = self.insts.len();
                        if is_loop {
                            self.current_start = start_instr;
                        }
                        self.emit_block(block, sub_anal);
                        if block.shift != 0 {
                            self.insts.push(Instr::Mov(block.shift))
                        }
                        if is_loop {
                            let mut i = num_outer;
                            while i < self.outer_accessed.len() {
                                let var = self.outer_accessed[i];
                                if self.ranges[var].created < prev_start {
                                    i += 1;
                                } else {
                                    self.range_extend(var);
                                    self.outer_accessed.swap_remove(i);
                                }
                            }
                            let off = start_instr as isize - self.insts.len() as isize;
                            self.insts.push(Instr::BrNZ(*cond, off));
                        }
                        if !at_least_once {
                            let branch_at = start_instr - 1;
                            let off = self.insts.len() as isize - branch_at as isize;
                            self.insts[branch_at] = Instr::BrZ(*cond, off);
                        }
                        self.current_start = prev_start;
                    } else {
                        self.insts.push(Instr::Scan(*cond, block.shift));
                    }
                    if sub_anal.has_shift {
                        self.values.clear();
                    } else if !at_least_once {
                        for &var in &sub_anal.writes {
                            self.values.remove(&GvnExpr::Mem(var));
                        }
                        for expr in &self.exprs[prev_exprs..] {
                            self.values.remove(expr);
                        }
                    }
                    block_idx += 1;
                }
            }
        }
    }

    /// Eliminate trivially dead stores. This is only a local pass.
    fn dead_store_elim(&mut self) {
        let mut dead = HashSet::new();
        for i in (0..self.insts.len()).rev() {
            match self.insts[i] {
                Instr::Add(dst, src0, src1)
                | Instr::Sub(dst, src0, src1)
                | Instr::Mul(dst, src0, src1) => {
                    if let Loc::Mem(mem) = dst {
                        if dead.contains(&mem) {
                            for src in [src0, src1] {
                                if let Loc::Tmp(tmp) = src {
                                    self.ranges[tmp].num_uses -= 1;
                                }
                            }
                            self.insts[i] = Instr::Noop;
                            continue;
                        }
                        dead.insert(mem);
                    } else if let Loc::Tmp(tmp) = dst {
                        if self.ranges[tmp].num_uses == 0 {
                            for src in [src0, src1] {
                                if let Loc::Tmp(tmp) = src {
                                    self.ranges[tmp].num_uses -= 1;
                                }
                            }
                            self.insts[i] = Instr::Noop;
                            continue;
                        }
                    }
                }
                Instr::Copy(dst, src) => {
                    if let Loc::Mem(mem) = dst {
                        if dead.contains(&mem) {
                            if let Loc::Tmp(tmp) = src {
                                self.ranges[tmp].num_uses -= 1;
                            }
                            self.insts[i] = Instr::Noop;
                            continue;
                        }
                        dead.insert(mem);
                    }
                }
                _ => { /* No store here. */ }
            }
            match self.insts[i] {
                Instr::Noop => { /* Does nothing. */ }
                Instr::Add(_, src0, src1)
                | Instr::Sub(_, src0, src1)
                | Instr::Mul(_, src0, src1) => {
                    for src in [src1, src0] {
                        if let Loc::Mem(mem) = src {
                            dead.remove(&mem);
                        }
                    }
                }
                Instr::Copy(_, src) => {
                    if let Loc::Mem(mem) = src {
                        dead.remove(&mem);
                    }
                }
                Instr::BrNZ(_, _) | Instr::BrZ(_, _) | Instr::Mov(_) | Instr::Scan(_, _) => {
                    dead.clear();
                }
                Instr::Out(mem) => {
                    dead.remove(&mem);
                }
                Instr::Inp(mem) => {
                    dead.insert(mem);
                }
            }
        }
    }

    /// Test whether the given memory location has a write in the given range.
    /// Inclusive `from` exclusive `to`.
    fn has_write_in_range(&self, var: isize, from: usize, to: usize) -> bool {
        from < to
            && self
                .writes
                .get(&var)
                .is_some_and(|w| w.range(from..to).any(|_| true))
    }

    /// Try to more efficiently allocate the necessary temporaries using the computed
    /// live ranges information and write sets.
    fn allocate_temps(&mut self, num_regs: usize) {
        let mut next_fresh = num_regs;
        let mut free_regs = BinaryHeap::new();
        for i in 0..num_regs {
            free_regs.push(Reverse(i));
        }
        let mut free_temps = BinaryHeap::new();
        let mut next_range_end = BinaryHeap::<(Reverse<usize>, usize)>::new();
        let mut replacements = HashMap::new();
        for i in 0..self.insts.len() {
            let mut about_to_free = HashSet::new();
            while let Some((Reverse(end), tmp)) = next_range_end.peek() {
                if *end <= i {
                    let last_use = self.ranges[*tmp].last_use.unwrap();
                    if *end >= last_use {
                        about_to_free.insert(*tmp);
                    } else {
                        next_range_end.push((Reverse(last_use), *tmp));
                    }
                    next_range_end.pop();
                } else {
                    break;
                }
            }
            let can_alloc_reg = match self.insts[i] {
                Instr::Add(Loc::Tmp(tmp), _, _)
                | Instr::Sub(Loc::Tmp(tmp), _, _)
                | Instr::Mul(Loc::Tmp(tmp), _, _)
                | Instr::Copy(Loc::Tmp(tmp), _) => {
                    let live = self.ranges[tmp].last_use.unwrap() - i;
                    live < 16
                        && (!free_regs.is_empty() || about_to_free.iter().any(|&x| x < num_regs))
                }
                _ => false,
            };
            match self.insts[i] {
                Instr::Add(dst, src0, src1)
                | Instr::Sub(dst, src0, src1)
                | Instr::Mul(dst, src0, src1) => {
                    if let Loc::Tmp(tmp) = dst {
                        if let Some(last_use) = self.ranges[tmp].last_use {
                            let first_use = self.ranges[tmp].first_use.unwrap();
                            let num_uses = self.ranges[tmp].num_uses;
                            if let Instr::Copy(Loc::Mem(mem), _) = self.insts[first_use] {
                                if (num_uses == 1 || !can_alloc_reg)
                                    && !self.has_write_in_range(mem, first_use + 1, last_use)
                                    && [src0, src1].into_iter().all(|src| {
                                        !matches!(src, Loc::Mem(m) if self.has_write_in_range(m, i, first_use))
                                        && !matches!(src, Loc::Tmp(tmp) if matches!(
                                            replacements.get(&tmp).unwrap(),
                                            &Loc::Mem(m) if self.has_write_in_range(m, i, first_use)
                                        ))
                                    })
                                {
                                    for src in [src0, src1] {
                                        if let Loc::Tmp(tmp) = src {
                                            self.range_extend_to(tmp, first_use);
                                            if about_to_free.remove(&tmp) {
                                                next_range_end.push((Reverse(first_use), tmp));
                                            }
                                        }
                                    }
                                    replacements.insert(tmp, Loc::Mem(mem));
                                    next_range_end.push((Reverse(last_use), tmp));
                                    self.insts[first_use] = self.insts[i];
                                    self.insts[i] = Instr::Noop;
                                    if let Instr::Add(dst, _, _)
                                    | Instr::Sub(dst, _, _)
                                    | Instr::Mul(dst, _, _) = &mut self.insts[first_use]
                                    {
                                        *dst = Loc::Mem(mem);
                                    }
                                }
                            }
                        }
                    }
                }
                _ => { /* Handled later. */ }
            }
            match &mut self.insts[i] {
                Instr::Add(_, src0, src1)
                | Instr::Sub(_, src0, src1)
                | Instr::Mul(_, src0, src1) => {
                    for src in [src0, src1] {
                        if let Loc::Tmp(tmp) = src {
                            *src = *replacements.get(tmp).unwrap();
                        }
                    }
                }
                Instr::Copy(_, src) => {
                    if let Loc::Tmp(tmp) = src {
                        *src = *replacements.get(tmp).unwrap();
                    }
                }
                _ => { /* These do not access temps. */ }
            }
            for tmp in about_to_free {
                if let Some(Loc::Tmp(tmp)) = replacements.remove(&tmp) {
                    if tmp < num_regs {
                        free_regs.push(Reverse(tmp));
                    } else {
                        free_temps.push(Reverse(tmp));
                    }
                }
            }
            let mut alloc_temp = |instr: &mut Instr<C>| {
                if let Instr::Add(dst, _, _)
                | Instr::Sub(dst, _, _)
                | Instr::Mul(dst, _, _)
                | Instr::Copy(dst, _) = instr
                {
                    if let Loc::Tmp(old) = dst {
                        let last_use = self.ranges[*old].last_use.unwrap();
                        let live = last_use - i;
                        let mut tmp = None;
                        if live < 16 {
                            // Don't allocate registers to temps with long live ranges.
                            tmp = free_regs.pop();
                        }
                        if tmp.is_none() {
                            tmp = free_temps.pop();
                        }
                        if tmp.is_none() {
                            tmp = Some(Reverse(next_fresh));
                            next_fresh += 1;
                        }
                        let Reverse(tmp) = tmp.unwrap();
                        replacements.insert(*old, Loc::Tmp(tmp));
                        next_range_end.push((Reverse(last_use), *old));
                        *dst = Loc::Tmp(tmp);
                    }
                }
            };
            match self.insts[i] {
                Instr::Add(dst, _, _) | Instr::Sub(dst, _, _) | Instr::Mul(dst, _, _) => {
                    if let Loc::Tmp(tmp) = dst {
                        if self.ranges[tmp].num_uses != 0 {
                            alloc_temp(&mut self.insts[i]);
                        } else {
                            self.insts[i] = Instr::Noop;
                        }
                    }
                }
                Instr::Copy(dst, src) => {
                    if let Loc::Tmp(tmp) = dst {
                        if let Some(last_use) = self.ranges[tmp].last_use {
                            let num_uses = self.ranges[tmp].num_uses;
                            if num_uses == 0 {
                                self.insts[i] = Instr::Noop;
                            } else {
                                if let Loc::Imm(_) = src {
                                    replacements.insert(tmp, src);
                                    next_range_end.push((Reverse(last_use), tmp));
                                    self.insts[i] = Instr::Noop;
                                } else if let Loc::Mem(mem) = src {
                                    if (num_uses == 1 || !can_alloc_reg)
                                        && !self.has_write_in_range(mem, i, last_use)
                                    {
                                        replacements.insert(tmp, src);
                                        next_range_end.push((Reverse(last_use), tmp));
                                        self.insts[i] = Instr::Noop;
                                    } else {
                                        alloc_temp(&mut self.insts[i]);
                                    }
                                } else {
                                    alloc_temp(&mut self.insts[i]);
                                }
                            }
                        } else {
                            self.insts[i] = Instr::Noop;
                        }
                    }
                }
                _ => { /* These do not access temps. */ }
            }
        }
        assert!(replacements.is_empty());
    }

    /// Try to reorder the parameters of Add and Mul instructions, such that if the
    /// destination is the same as one of the parameters, that parameter is first.
    /// Further, this pass tries to put immediate as the last parameter.
    fn parameter_reordering(&mut self) {
        for i in (0..self.insts.len()).rev() {
            match &mut self.insts[i] {
                Instr::Add(dst, src0, src1) | Instr::Mul(dst, src0, src1) => {
                    if let Loc::Tmp(tmp0) = src0 {
                        if let Loc::Tmp(tmp1) = src1 {
                            if tmp1 < tmp0 {
                                mem::swap(src0, src1);
                            }
                        } else {
                            mem::swap(src0, src1);
                        }
                    }
                    if matches!(src0, Loc::Imm(_)) {
                        mem::swap(src0, src1);
                    }
                    if dst == src1 {
                        mem::swap(src0, src1);
                    }
                }
                _ => { /* Not commutative. */ }
            }
        }
    }

    /// Find zeroing copies and move them to the last use.
    fn zeroing_move_detection(&mut self) {
        let mut zerod = HashMap::new();
        for i in (0..self.insts.len()).rev() {
            match &mut self.insts[i] {
                Instr::Noop => { /* Does nothing. */ }
                Instr::Add(dst, src0, src1)
                | Instr::Sub(dst, src0, src1)
                | Instr::Mul(dst, src0, src1) => {
                    if let Loc::Mem(mem) = *dst {
                        zerod.remove(&mem);
                    }
                    let mut to_remove = Vec::new();
                    for src in [src1, src0] {
                        if let Loc::Mem(mem) = src {
                            if let Some(i) = zerod.remove(mem) {
                                *src = Loc::MemZero(*mem);
                                to_remove.push(i);
                            }
                        }
                    }
                    for i in to_remove {
                        self.insts[i] = Instr::Noop;
                    }
                }
                Instr::Copy(dst, src) => {
                    if let Loc::Mem(mem) = *dst {
                        zerod.remove(&mem);
                        if let Loc::Imm(imm) = *src {
                            if imm == C::ZERO {
                                zerod.insert(mem, i);
                            }
                        }
                    }
                    if let Loc::Mem(mem) = src {
                        if let Some(i) = zerod.remove(mem) {
                            *src = Loc::MemZero(*mem);
                            self.insts[i] = Instr::Noop;
                        }
                    }
                }
                Instr::BrNZ(_, _) | Instr::BrZ(_, _) | Instr::Mov(_) | Instr::Scan(_, _) => {
                    zerod.clear();
                }
                Instr::Out(mem) | Instr::Inp(mem) => {
                    zerod.remove(mem);
                    zerod.remove(mem);
                }
            }
        }
    }

    /// The temporary allocation algorithm will likely generate a lot of noop
    /// instructions when it eliminates copy instructions. For simplicity of the
    /// preceding passes these are only removed at the end, as that requires
    /// fixing of the branch target offsets.
    fn strip_noops(&mut self) {
        let mut cum_noop = Vec::with_capacity(self.insts.len() + 1);
        cum_noop.push(0);
        for instr in &self.insts {
            cum_noop.push(*cum_noop.last().unwrap());
            if let Instr::Noop = instr {
                *cum_noop.last_mut().unwrap() += 1;
            }
        }
        for (i, instr) in self.insts.iter_mut().enumerate() {
            if let Instr::BrZ(_, off) | Instr::BrNZ(_, off) = instr {
                let target = i.wrapping_add_signed(*off);
                *off -= cum_noop[target] - cum_noop[i];
            }
        }
        self.insts.retain(|inst| !matches!(inst, Instr::Noop));
    }

    /// Return the number of temporary variables needed to execute this program.
    /// This information is part of the program struct ans used to allocate the
    /// correctly sized temporary memory during execution.
    fn count_temps(&self) -> usize {
        fn get_max<C: CellType>(slice: &[&Loc<C>]) -> usize {
            slice
                .iter()
                .map(|&l| if let Loc::Tmp(t) = l { *t + 1 } else { 0 })
                .max()
                .unwrap_or(0)
        }
        self.insts
            .iter()
            .map(|inst| match inst {
                Instr::Add(a, b, c) | Instr::Sub(a, b, c) | Instr::Mul(a, b, c) => {
                    get_max(&[a, b, c])
                }
                Instr::Copy(a, b) => get_max(&[a, b]),
                _ => 0,
            })
            .max()
            .unwrap_or(0)
    }

    /// Translate the IR program into an BC program.
    pub fn translate(program: &ir::Program<C>, num_regs: usize) -> Program<C> {
        let analysis = Analysis::analyze(program);
        let mut codegen = CodeGen {
            min_accessed: analysis.min_accessed,
            max_accessed: analysis.max_accessed,
            writes: HashMap::new(),
            ranges: Vec::new(),
            exprs: Vec::new(),
            values: HashMap::new(),
            insts: Vec::new(),
            current_start: 0,
            outer_accessed: Vec::new(),
        };
        codegen.emit_block(program, &analysis);
        codegen.dead_store_elim();
        codegen.allocate_temps(num_regs);
        codegen.parameter_reordering();
        codegen.zeroing_move_detection();
        codegen.strip_noops();
        let temp_size = codegen.count_temps();
        Program {
            temps: temp_size,
            min_accessed: codegen.min_accessed,
            max_accessed: codegen.max_accessed,
            insts: codegen.insts,
        }
    }
}

impl<C: CellType> Debug for Loc<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Loc::Mem(var) | Loc::MemZero(var) => write!(f, "[{var}]"),
            Loc::Tmp(tmp) => write!(f, "%{tmp}"),
            Loc::Imm(imm) => write!(f, "{imm:?}"),
        }
    }
}

impl<C: CellType> Instr<C> {
    fn fmt_at(&self, f: &mut fmt::Formatter<'_>, idx: usize) -> fmt::Result {
        match self {
            Instr::Noop => write!(f, "noop")?,
            Instr::Scan(cond, shift) => write!(f, "scan [{cond}], {shift}")?,
            Instr::Mov(shift) => write!(f, "mov {shift}")?,
            Instr::Inp(dst) => write!(f, "inp [{dst}]")?,
            Instr::Out(src) => write!(f, "out [{src}]")?,
            Instr::BrZ(cond, off) => write!(f, "brz [{cond}], .L{}", idx as isize + *off)?,
            Instr::BrNZ(cond, off) => write!(f, "brnz [{cond}], .L{}", idx as isize + *off)?,
            Instr::Add(dst, src0, src1) => write!(f, "add {dst:?}, {src0:?}, {src1:?}")?,
            Instr::Sub(dst, src0, src1) => write!(f, "sub {dst:?}, {src0:?}, {src1:?}")?,
            Instr::Mul(dst, src0, src1) => write!(f, "mul {dst:?}, {src0:?}, {src1:?}")?,
            Instr::Copy(dst, src) => write!(f, "copy {dst:?}, {src:?}")?,
        }
        match self {
            Instr::Add(_, src0, src1) | Instr::Sub(_, src0, src1) | Instr::Mul(_, src0, src1) => {
                for src in [src0, src1] {
                    if let Loc::MemZero(mem) = src {
                        write!(f, "; copy [{mem}], 0")?;
                    }
                }
            }
            Instr::Copy(_, src) => {
                if let Loc::MemZero(mem) = src {
                    write!(f, "; copy [{mem}], 0")?;
                }
            }
            _ => { /* These have no locations. */ }
        }
        Ok(())
    }
}

impl<C: CellType> Debug for Instr<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_at(f, 0)
    }
}

impl<C: CellType> Debug for Program<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut branch_target = HashSet::new();
        for (i, instr) in self.insts.iter().enumerate() {
            if let Instr::BrNZ(_, off) | Instr::BrZ(_, off) = instr {
                branch_target.insert(i.wrapping_add_signed(*off));
            }
        }
        writeln!(f, "; temps {}", self.temps)?;
        writeln!(f, "; min {}", self.min_accessed)?;
        writeln!(f, "; max {}", self.max_accessed)?;
        for (i, instr) in self.insts.iter().enumerate() {
            if branch_target.contains(&i) {
                writeln!(f, ".L{i}")?;
            }
            write!(f, "  ")?;
            instr.fmt_at(f, i)?;
            writeln!(f)?;
        }
        if branch_target.contains(&self.insts.len()) {
            writeln!(f, ".L{}", self.insts.len())?;
        }
        Ok(())
    }
}
