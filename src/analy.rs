//! Module that performs and prints some program analysis.

use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Debug},
};

use crate::{CellType, Instr, Program};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct PolyPart<C: CellType> {
    coef: C,
    vars: Vec<isize>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Poly<C: CellType> {
    parts: Vec<PolyPart<C>>,
}

pub struct PolyBlock<C: CellType> {
    shift: isize,
    insts: Vec<PolyInstr<C>>,
}

pub enum PolyInstr<C: CellType> {
    Output { src: isize },
    Input { dst: isize },
    Calc { calcs: Vec<(isize, Poly<C>)> },
    Loop { cond: isize, block: PolyBlock<C> },
    If { cond: isize, block: PolyBlock<C> },
}

enum CellValue<C: CellType> {
    Unknown,
    Poly(Poly<C>),
}

struct AnalysisState<C: CellType> {
    constant: Option<C>,
    shift: isize,
    sub_shift: bool,
    insts: Vec<PolyInstr<C>>,
    read: HashSet<isize>,
    cells: HashMap<isize, CellValue<C>>,
    pending: HashMap<isize, Poly<C>>,
    reverse: HashMap<isize, HashSet<isize>>,
}

impl<C: CellType> Poly<C> {
    pub fn val(coef: C) -> Self {
        if coef == C::ZERO {
            Poly { parts: vec![] }
        } else {
            Poly {
                parts: vec![PolyPart { coef, vars: vec![] }],
            }
        }
    }

    pub fn var(var: isize) -> Self {
        Poly {
            parts: vec![PolyPart {
                coef: C::ONE,
                vars: vec![var],
            }],
        }
    }

    pub fn mul(&self, other: &Self) -> Self {
        let mut parts = HashMap::new();
        for self_part in &self.parts {
            for other_part in &other.parts {
                let mut vars = self_part
                    .vars
                    .iter()
                    .chain(other_part.vars.iter())
                    .copied()
                    .collect::<Vec<_>>();
                vars.sort();
                let coef = self_part.coef.wrapping_mul(other_part.coef);
                let v = parts.entry(vars).or_insert(C::ZERO);
                *v = v.wrapping_add(coef);
            }
        }
        let mut parts = parts
            .into_iter()
            .filter(|(_, coef)| *coef != C::ZERO)
            .map(|(vars, coef)| PolyPart { coef, vars })
            .collect::<Vec<_>>();
        parts.sort_by(|a, b| a.vars.cmp(&b.vars));
        Poly { parts }
    }

    pub fn add(&self, other: &Self) -> Self {
        let (mut i, mut j) = (0, 0);
        let mut parts = Vec::new();
        while i < self.parts.len() && j < other.parts.len() {
            if self.parts[i].vars < other.parts[j].vars {
                parts.push(self.parts[i].clone());
                i += 1;
            } else if self.parts[i].vars > other.parts[j].vars {
                parts.push(other.parts[j].clone());
                j += 1;
            } else {
                let coef = self.parts[i].coef.wrapping_add(other.parts[j].coef);
                if coef != C::ZERO {
                    parts.push(PolyPart {
                        coef,
                        vars: self.parts[i].vars.clone(),
                    });
                }
                i += 1;
                j += 1;
            }
        }
        while i < self.parts.len() {
            parts.push(self.parts[i].clone());
            i += 1;
        }
        while j < other.parts.len() {
            parts.push(other.parts[j].clone());
            j += 1;
        }
        Poly { parts }
    }
}

impl<C: CellType> AnalysisState<C> {
    fn to_spill(&self, var: isize) -> HashSet<isize> {
        let mut to_spill = HashSet::new();
        let mut stack = vec![var];
        while let Some(x) = stack.pop() {
            if self.pending.contains_key(&var) && !to_spill.contains(&x) {
                to_spill.insert(x);
                if let Some(req) = self.reverse.get(&x) {
                    for var in req {
                        stack.push(*var);
                    }
                }
            }
        }
        return to_spill;
    }

    fn perform(&mut self, var: isize, poly: &Poly<C>) {
        let value = self.apply_pending(poly);
        if let Some(old) = self.pending.get(&var) {
            for part in &old.parts {
                for v in &part.vars {
                    if let Some(p) = self.reverse.get_mut(v) {
                        p.remove(&var);
                        if p.is_empty() {
                            self.reverse.remove(v);
                        }
                    }
                }
            }
        }
        for part in &value.parts {
            for v in &part.vars {
                let p = self.reverse.entry(*v).or_insert(HashSet::new());
                p.insert(var);
            }
        }
        if value == Poly::var(var) {
            self.pending.remove(&var);
        } else {
            self.pending.insert(var, value);
        }
    }

    fn perform_all(&mut self, calcs: Vec<(isize, Poly<C>)>) {
        let mut values = Vec::new();
        for (var, poly) in calcs {
            let value = self.apply_pending(&poly);
            if let Some(old) = self.pending.get(&var) {
                for part in &old.parts {
                    for v in &part.vars {
                        if let Some(p) = self.reverse.get_mut(v) {
                            p.remove(&var);
                            if p.is_empty() {
                                self.reverse.remove(v);
                            }
                        }
                    }
                }
            }
            for part in &value.parts {
                for v in &part.vars {
                    let p = self.reverse.entry(*v).or_insert(HashSet::new());
                    p.insert(var);
                }
            }
            values.push((var, value));
        }
        for (var, value) in values {
            if value == Poly::var(var) {
                self.pending.remove(&var);
            } else {
                self.pending.insert(var, value);
            }
        }
    }

    fn apply_pending(&self, poly: &Poly<C>) -> Poly<C> {
        let mut val = Poly::val(C::ZERO);
        for part in &poly.parts {
            let mut part_val = Poly::val(part.coef);
            for var in &part.vars {
                if let Some(var_val) = self.pending.get(&var) {
                    part_val = part_val.mul(var_val);
                } else {
                    part_val = part_val.mul(&Poly::var(*var));
                }
            }
            val = val.add(&part_val);
        }
        return val;
    }

    fn apply_cells(&self, poly: &Poly<C>) -> Option<Poly<C>> {
        let mut val = Poly::val(C::ZERO);
        for part in &poly.parts {
            let mut part_val = Poly::val(part.coef);
            for var in &part.vars {
                if let Some(var_val) = self.cells.get(&var) {
                    if let CellValue::Poly(poly) = var_val {
                        part_val = part_val.mul(poly);
                    } else {
                        return None;
                    }
                } else if let Some(v) = self.constant {
                    part_val = part_val.mul(&Poly::val(v));
                } else {
                    part_val = part_val.mul(&Poly::var(*var));
                }
            }
            val = val.add(&part_val);
        }
        return Some(val);
    }

    fn apply(&self, poly: &Poly<C>) -> Option<Poly<C>> {
        self.apply_cells(&self.apply_pending(poly))
    }

    fn spill(&mut self, vars: HashSet<isize>) {
        let mut to_run = Vec::new();
        let mut new_cell = Vec::new();
        for var in vars {
            let op = self.apply_pending(&Poly::var(var));
            for part in &op.parts {
                for var in &part.vars {
                    if !self.cells.contains_key(var) {
                        self.read.insert(*var);
                    }
                }
            }
            let cell = self.apply_cells(&op);
            if cell.is_none() || cell != self.apply_cells(&Poly::var(var)) {
                new_cell.push((var, cell));
                to_run.push((var, op));
            }
            self.pending.remove(&var);
        }
        if !to_run.is_empty() {
            to_run.sort_by_key(|(v, _)| *v);
            self.insts.push(PolyInstr::Calc { calcs: to_run });
            for (var, val) in new_cell {
                if let Some(poly) = val {
                    if poly == Poly::var(var) {
                        self.cells.remove(&var);
                    } else {
                        self.cells.insert(var, CellValue::Poly(poly));
                    }
                } else {
                    self.cells.insert(var, CellValue::Unknown);
                }
            }
        }
    }

    fn spill_for(&mut self, var: isize) {
        if !self.cells.contains_key(&var) {
            self.read.insert(var);
        }
        let to_spill = self.to_spill(var);
        self.spill(to_spill);
    }

    fn clobber(&mut self, var: isize) {
        self.cells.insert(var, CellValue::Unknown);
        self.pending.remove(&var);
        self.reverse.remove(&var);
    }

    fn clobber_all(&mut self) {
        self.constant = None;
        self.read.clear();
        self.cells.clear();
        self.pending.clear();
        self.reverse.clear();
    }

    fn read(&self) -> Vec<isize> {
        let mut vars = self.read.iter().copied().collect::<Vec<_>>();
        vars.sort();
        return vars;
    }

    fn pending(&self) -> Vec<isize> {
        let mut vars = self.pending.keys().copied().collect::<Vec<_>>();
        vars.sort();
        return vars;
    }
}

impl<C: CellType> Program<C> {
    fn poly_block_for(
        &self,
        block_id: usize,
        shift: isize,
        constant: Option<C>,
    ) -> AnalysisState<C> {
        let mut state = AnalysisState {
            constant,
            shift,
            sub_shift: false,
            insts: Vec::new(),
            read: HashSet::new(),
            cells: HashMap::new(),
            pending: HashMap::new(),
            reverse: HashMap::new(),
        };
        let block = &self.blocks[block_id];
        for instr in &block.insts {
            match instr {
                Instr::Output { src } => {
                    let src = *src + state.shift;
                    state.spill_for(src);
                    state.insts.push(PolyInstr::Output { src });
                }
                Instr::Input { dst } => {
                    let dst = *dst + state.shift;
                    state.clobber(dst);
                    state.insts.push(PolyInstr::Input { dst });
                }
                Instr::Load { val, dst } => {
                    let dst = *dst + state.shift;
                    state.perform(dst, &Poly::val(*val));
                }
                Instr::Add { val, dst } => {
                    let dst = *dst + state.shift;
                    state.perform(dst, &Poly::var(dst).add(&Poly::val(*val)));
                }
                Instr::MulAdd { val, src, dst } => {
                    let src = *src + state.shift;
                    let dst = *dst + state.shift;
                    state.perform(
                        dst,
                        &Poly::var(dst).add(&Poly::var(src).mul(&Poly::val(*val))),
                    );
                }
                Instr::Loop { cond, block } | Instr::If { cond, block } => {
                    let cond = *cond + state.shift;
                    let is_loop = matches!(instr, Instr::Loop { .. });
                    if state.apply(&Poly::var(cond)) != Some(Poly::val(C::ZERO)) {
                        let mut sub_state = self.poly_block_for(*block, cond, None);
                        if sub_state.sub_shift || sub_state.shift != cond {
                            state.sub_shift = true;
                            for var in sub_state.pending() {
                                sub_state.spill_for(var);
                            }
                            for var in sub_state.read() {
                                state.spill_for(var);
                            }
                            state.clobber_all();
                        } else {
                            let mut before = Vec::new();
                            if sub_state.apply(&Poly::var(cond))
                                == Some(Poly::var(cond).add(&Poly::val(C::NEG_ONE)))
                            {
                                for (var, poly) in &sub_state.pending {
                                    if *var != cond
                                        && !sub_state.cells.contains_key(var)
                                        && !sub_state.read.contains(var)
                                        && poly.parts.iter().any(|part| {
                                            part.coef == C::ONE && part.vars == vec![*var]
                                        })
                                        && poly
                                            .parts
                                            .iter()
                                            .filter(|part| part.vars != vec![*var])
                                            .flat_map(|part| part.vars.iter())
                                            .all(|&v| {
                                                *var != v && !sub_state.cells.contains_key(&v)
                                            })
                                    {
                                        let poly = Poly {
                                            parts: poly
                                                .parts
                                                .iter()
                                                .cloned()
                                                .filter(|part| part.vars != vec![*var])
                                                .collect(),
                                        }
                                        .mul(&Poly::var(cond))
                                        .add(&Poly::var(*var));
                                        before.push((*var, poly));
                                    }
                                }
                                before.sort_by_key(|(k, _)| *k);
                                for (var, _) in &before {
                                    sub_state.pending.remove(var);
                                }
                                state.perform_all(before);
                            }
                            for var in sub_state.pending() {
                                if !is_loop || var != cond {
                                    sub_state.spill_for(var);
                                }
                            }
                            if !sub_state.insts.is_empty() {
                                sub_state.spill_for(cond);
                                for var in sub_state.read() {
                                    state.spill_for(var);
                                }
                                for var in sub_state.cells.keys() {
                                    state.clobber(*var);
                                }
                            }
                        }
                        if sub_state.sub_shift
                            || sub_state.shift != cond
                            || !sub_state.insts.is_empty()
                        {
                            if is_loop {
                                state.insts.push(PolyInstr::Loop {
                                    cond,
                                    block: PolyBlock {
                                        shift: sub_state.shift - cond,
                                        insts: sub_state.insts,
                                    },
                                });
                            } else {
                                state.insts.push(PolyInstr::If {
                                    cond,
                                    block: PolyBlock {
                                        shift: sub_state.shift - cond,
                                        insts: sub_state.insts,
                                    },
                                });
                            }
                        }
                        if is_loop {
                            state.perform(cond, &Poly::val(C::ZERO));
                        }
                    }
                }
            }
        }
        state.shift += block.shift;
        return state;
    }

    pub fn poly_block(&self) -> PolyBlock<C> {
        let mut state = self.poly_block_for(self.entry, 0, Some(C::ZERO));
        for var in state.pending() {
            state.spill_for(var);
        }
        return PolyBlock {
            shift: state.shift,
            insts: state.insts,
        };
    }
}

impl<C: CellType> PolyBlock<C> {
    fn print_block(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        for instr in &self.insts {
            match instr {
                PolyInstr::Output { src } => {
                    writeln!(f, "{:indent$}output [{}]", "", src, indent = indent)?;
                }
                PolyInstr::Input { dst } => {
                    writeln!(f, "{:indent$}input [{}]", "", dst, indent = indent)?;
                }
                PolyInstr::Calc { calcs } => {
                    let mut indent = indent;
                    if calcs.len() != 1 {
                        writeln!(f, "{:indent$}(", "", indent = indent)?;
                        indent += 2;
                    }
                    for (dst, val) in calcs {
                        write!(f, "{:indent$}[{}] = ", "", dst, indent = indent)?;
                        if val.parts.is_empty() {
                            write!(f, "0")?;
                        }
                        for (i, part) in val.parts.iter().enumerate() {
                            if i != 0 {
                                write!(f, " + ")?;
                            }
                            if part.coef != C::ONE || part.vars.is_empty() {
                                write!(f, "{:?}", part.coef)?;
                            }
                            for (j, var) in part.vars.iter().enumerate() {
                                if j != 0 || part.coef != C::ONE || part.vars.is_empty() {
                                    write!(f, "*")?;
                                }
                                write!(f, "[{var}]")?;
                            }
                        }
                        writeln!(f)?;
                    }
                    if calcs.len() != 1 {
                        indent -= 2;
                        writeln!(f, "{:indent$})", "", indent = indent)?;
                    }
                }
                PolyInstr::Loop { cond, block } => {
                    writeln!(f, "{:indent$}loop [{}] {{", "", cond, indent = indent)?;
                    block.print_block(f, indent + 2)?;
                    writeln!(f, "{:indent$}}}", "", indent = indent)?;
                }
                PolyInstr::If { cond, block } => {
                    writeln!(f, "{:indent$}if [{}] {{", "", cond, indent = indent)?;
                    block.print_block(f, indent + 2)?;
                    writeln!(f, "{:indent$}}}", "", indent = indent)?;
                }
            }
        }
        if self.shift != 0 {
            writeln!(f, "{:indent$}move {}", "", self.shift, indent = indent)?;
        }
        Ok(())
    }
}

impl<C: CellType> Debug for PolyBlock<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.print_block(f, 0)
    }
}
