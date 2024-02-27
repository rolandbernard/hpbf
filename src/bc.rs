//! Contains transformation form the IR to the interpreter Bytecode.

use std::{
    collections::{BTreeSet, HashMap, HashSet},
    fmt::{self, Debug},
};

use crate::{
    ir::{self, Block, Expr},
    CellType,
};

/// Location form which to load or store values.
#[derive(PartialEq, Hash)]
pub enum Loc<C: CellType> {
    Mem(isize),
    Tmp(usize),
    Imm(C),
}

/// Instruction representation for the bytecode. Only select instructions use
/// [`Loc`]. All other access memory only.
#[derive(PartialEq, Hash)]
pub enum Instr<C: CellType> {
    Noop,
    Scan(isize, isize),
    Mov(isize),
    Check(isize),
    Check2(isize, isize),
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
    temps: usize,
    insts: Vec<Instr<C>>,
}

/// Analysis result used for bytecode generation.
struct Analysis {
    has_shift: bool,
    writes: HashSet<isize>,
    sub_anal: Vec<Analysis>,
    min_accessed: Option<isize>,
    max_accessed: Option<isize>,
}

/// Live range information for the temporaries, used later on during temp allocation.
struct RangeInfo {
    created: usize,
    last_used: Option<usize>,
    num_uses: usize,
}

/// Computation to be used with the global value numbering.
#[derive(PartialEq, Eq, Hash)]
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
    values: HashMap<GvnExpr<C>, usize>,
    insts: Vec<Instr<C>>,
    current_start: usize,
    outer_accessed: Vec<usize>,
}

impl Analysis {
    /// Record that the memory address `var` has been accessed.
    fn accessed(&mut self, var: isize) {
        if self.min_accessed.is_none() || self.min_accessed.unwrap() > var {
            self.min_accessed = Some(var);
        }
        if self.max_accessed.is_none() || self.max_accessed.unwrap() < var {
            self.max_accessed = Some(var);
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
            min_accessed: None,
            max_accessed: None,
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
                ir::Instr::Loop { cond, block } | ir::Instr::If { cond, block } => {
                    anal.accessed(*cond);
                    let sub_analysis = Self::analyze(block);
                    if let Some(min) = sub_analysis.min_accessed {
                        anal.accessed(min);
                    }
                    if let Some(max) = sub_analysis.max_accessed {
                        anal.accessed(max);
                    }
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
    /// Record in the live ranges that the given `value` has been accessed.
    fn read(&mut self, value: usize) {
        if self.ranges[value].created < self.current_start {
            if self.ranges[value].last_used.is_none()
                || self.ranges[value].last_used.unwrap() < self.current_start
            {
                self.outer_accessed.push(value);
            }
        }
        self.ranges[value].last_used = Some(2 * self.insts.len());
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
                created: 2 * self.insts.len() + 1,
                last_used: None,
                num_uses: 0,
            });
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
        self.values.insert(GvnExpr::Mem(var), value);
        self.insts.push(Instr::Copy(Loc::Mem(var), Loc::Tmp(value)));
        self.writes
            .entry(var)
            .or_insert(BTreeSet::new())
            .insert(2 * self.insts.len() + 1);
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
                ir::Instr::Loop { cond, block } | ir::Instr::If { cond, block } => {
                    let is_loop = matches!(inst, ir::Instr::Loop { .. });
                    let sub_anal = &anal.sub_anal[block_idx];
                    if is_loop {
                        if sub_anal.has_shift {
                            self.values.clear();
                        }
                        for &var in &sub_anal.writes {
                            self.values.remove(&GvnExpr::Mem(var));
                        }
                    }
                    let num_outer = self.outer_accessed.len();
                    let start_addr = self.insts.len();
                    if !is_loop || !block.insts.is_empty() {
                        if is_loop {
                            self.current_start = 2 * self.insts.len();
                        }
                        self.insts.push(Instr::Noop);
                        self.emit_block(block, sub_anal);
                    } else {
                        self.insts.push(Instr::Scan(*cond, block.shift));
                    }
                    if block.shift < 0 {
                        self.insts.push(Instr::Check(self.min_accessed))
                    } else if block.shift > 0 {
                        self.insts.push(Instr::Check(self.max_accessed))
                    }
                    if !is_loop || !block.insts.is_empty() {
                        if is_loop {
                            self.current_start = prev_start;
                            let mut i = num_outer;
                            while i < self.outer_accessed.len() {
                                let var = self.outer_accessed[i];
                                if self.ranges[var].created > self.current_start {
                                    self.read(var);
                                    self.outer_accessed.swap_remove(i);
                                } else {
                                    i += 1;
                                }
                            }
                            let off = start_addr as isize + 1 - self.insts.len() as isize;
                            self.insts.push(Instr::BrNZ(*cond, off));
                        }
                        let off = self.insts.len() as isize - start_addr as isize;
                        self.insts[start_addr] = Instr::BrZ(*cond, off);
                    }
                    if sub_anal.has_shift {
                        self.values.clear();
                    }
                    for &var in &sub_anal.writes {
                        self.values.remove(&GvnExpr::Mem(var));
                    }
                    block_idx += 1;
                }
            }
        }
        if block.shift != 0 {
            self.insts.push(Instr::Mov(block.shift));
        }
    }

    /// Try to more efficiently allocate the necessary temporaries using the computed
    /// live ranges information and write sets. `num_regs` indicates the number of
    /// temporaries that are expected to be particularly fast. Therefore the allocator
    /// will try to allocate these in the first `num_regs` temporaries.
    fn allocate_temps(&mut self, _num_regs: usize) {
        // TODO
    }

    /// The temporary allocation algorithm will likely generate a lot of noop
    /// instructions when it eliminates copy instructions. For simplicity of the
    /// preceding passes these are only removed at the end, as that requires
    /// fixing of the branch target offsets.
    fn strip_noops(&mut self) {
        // TODO
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
            min_accessed: analysis.min_accessed.unwrap_or(0),
            max_accessed: analysis.max_accessed.unwrap_or(0),
            writes: HashMap::new(),
            ranges: Vec::new(),
            values: HashMap::new(),
            insts: Vec::new(),
            current_start: 0,
            outer_accessed: Vec::new(),
        };
        codegen
            .insts
            .push(Instr::Check2(codegen.min_accessed, codegen.max_accessed));
        codegen.emit_block(program, &analysis);
        codegen.allocate_temps(num_regs);
        codegen.strip_noops();
        let temp_size = codegen.count_temps();
        Program {
            temps: temp_size,
            insts: codegen.insts,
        }
    }
}

impl<C: CellType> Debug for Loc<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Loc::Mem(var) => write!(f, "[{var}]"),
            Loc::Tmp(tmp) => write!(f, "%{tmp}"),
            Loc::Imm(imm) => write!(f, "{imm:?}"),
        }
    }
}

impl<C: CellType> Debug for Program<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut branch_target = HashSet::new();
        for (i, instr) in self.insts.iter().enumerate() {
            if let Instr::BrNZ(_, off) | Instr::BrZ(_, off) = instr {
                branch_target.insert(i.saturating_add_signed(*off));
            }
        }
        writeln!(f, "; {} temps", self.temps)?;
        for (i, instr) in self.insts.iter().enumerate() {
            if branch_target.contains(&i) {
                writeln!(f, ".L{i}")?;
            }
            match instr {
                Instr::Noop => writeln!(f, "  noop")?,
                Instr::Scan(cond, shift) => writeln!(f, "  scan [{cond}], {shift}")?,
                Instr::Mov(shift) => writeln!(f, "  mov {shift}")?,
                Instr::Check(var) => writeln!(f, "  check [{var}]")?,
                Instr::Check2(min, max) => writeln!(f, "  check2 [{min}], [{max}]")?,
                Instr::Inp(dst) => writeln!(f, "  inp [{dst}]")?,
                Instr::Out(src) => writeln!(f, "  out [{src}]")?,
                Instr::BrZ(cond, off) => {
                    writeln!(f, "  brz [{cond}], .L{}", i.saturating_add_signed(*off))?
                }
                Instr::BrNZ(cond, off) => {
                    writeln!(f, "  brnz [{cond}], .L{}", i.saturating_add_signed(*off))?
                }
                Instr::Add(dst, src0, src1) => writeln!(f, "  add {dst:?}, {src0:?}, {src1:?}")?,
                Instr::Sub(dst, src0, src1) => writeln!(f, "  sub {dst:?}, {src0:?}, {src1:?}")?,
                Instr::Mul(dst, src0, src1) => writeln!(f, "  mul {dst:?}, {src0:?}, {src1:?}")?,
                Instr::Copy(dst, src) => writeln!(f, "  copy {dst:?}, {src:?}")?,
            }
        }
        Ok(())
    }
}
