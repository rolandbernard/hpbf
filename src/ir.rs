//! Contains parsing and some optimizing transformations for a Brainfuck program.

use std::fmt::{self, Debug};

use crate::{
    hasher::{HashMap, HashSet},
    CellType, Error, ErrorKind,
};

/// Parts of expression. Represents the product of the coefficient and the set
/// of variables.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ExprPart<C: CellType> {
    coef: C,
    vars: Vec<isize>,
}

/// An expression used in the IR to represent a calculation. Expressions in the
/// IR represent sums of products. Currently, all expressions are normalized.
/// This ensures that two equivalent expressions compare ans hash equals.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Expr<C: CellType> {
    parts: Vec<ExprPart<C>>,
}

/// Represents a complete Brainfuck program.
pub type Program<C> = Block<C>;

/// Represents the inside of a loop.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Block<C: CellType> {
    pub shift: isize,
    pub insts: Vec<Instr<C>>,
}

/// This represents a Brainfuck instruction. It includes not only the basic
/// Brainfuck instructions, but also some additional operations that are common
/// in Brainfuck and help the backend to generate better code.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Instr<C: CellType> {
    Output { src: isize },
    Input { dst: isize },
    Calc { calcs: Vec<(isize, Expr<C>)> },
    Loop { cond: isize, block: Block<C> },
    If { cond: isize, block: Block<C> },
}

impl<C: CellType> Expr<C> {
    /// Return the expression representing the constant value given by `coef`.
    pub fn val(coef: C) -> Self {
        if coef == C::ZERO {
            Expr { parts: vec![] }
        } else {
            Expr {
                parts: vec![ExprPart { coef, vars: vec![] }],
            }
        }
    }

    /// Return the expression representing the value at memory offset `var`.
    pub fn var(var: isize) -> Self {
        Expr {
            parts: vec![ExprPart {
                coef: C::ONE,
                vars: vec![var],
            }],
        }
    }

    /// Special detection of e.g. 128*x + 129*x*x which is equivalent to x*x.
    /// For now, only do this when it enables us to eliminate a multiplication
    /// or even a complete term.
    fn special_normalization_rules(parts: &mut HashMap<Vec<isize>, C>) {
        if parts.len() >= 2 && parts.iter().any(|(vs, c)| vs.len() >= 2 && *c != C::ZERO) {
            let half_mod = C::ONE.wrapping_shl(C::BITS - 1);
            let half_mod_p = half_mod.wrapping_add(C::ONE);
            let half_mod_m = half_mod.wrapping_add(C::NEG_ONE);
            if parts.iter().any(|(vs, c)| {
                !vs.is_empty() && (*c == half_mod || *c == half_mod_p || *c == half_mod_m)
            }) {
                for vars in parts
                    .iter()
                    .filter(|(v, c)| v.len() >= 2 && *c != &C::ZERO)
                    .map(|(v, _)| v.clone())
                    .collect::<Vec<_>>()
                {
                    for i in 0..vars.len() {
                        let vars_m = vars
                            .iter()
                            .enumerate()
                            .filter(|(j, _)| *j != i)
                            .map(|(_, v)| *v)
                            .collect::<Vec<_>>();
                        if let (Some(&coef), Some(&coef_m)) = (parts.get(&vars), parts.get(&vars_m))
                        {
                            if (coef != C::ZERO && (coef_m != C::ZERO || coef == half_mod))
                                && (coef == half_mod
                                    || coef == half_mod_p
                                    || coef == half_mod_m
                                    || coef_m == half_mod
                                    || coef_m == half_mod_p
                                    || coef_m == half_mod_m)
                            {
                                *parts.get_mut(&vars).unwrap() = coef.wrapping_add(half_mod);
                                *parts.get_mut(&vars_m).unwrap() = coef_m.wrapping_add(half_mod);
                            }
                        }
                    }
                }
            }
        }
    }

    /// Multiply two expressions and return the resulting expressions.
    pub fn mul(&self, other: &Self) -> Self {
        let mut parts = HashMap::with_capacity(self.parts.len() * other.parts.len());
        for self_part in &self.parts {
            for other_part in &other.parts {
                let mut vars = self_part.vars.clone();
                vars.extend(other_part.vars.iter().copied());
                vars.sort();
                let coef = self_part.coef.wrapping_mul(other_part.coef);
                let v = parts.entry(vars).or_insert(C::ZERO);
                *v = v.wrapping_add(coef);
            }
        }
        Self::special_normalization_rules(&mut parts);
        let mut parts = parts
            .into_iter()
            .filter(|(_, coef)| *coef != C::ZERO)
            .map(|(vars, coef)| ExprPart { coef, vars })
            .collect::<Vec<_>>();
        parts.sort_by(|a, b| a.vars.cmp(&b.vars));
        Expr { parts }
    }

    /// Add two expressions and return the resulting expressions.
    pub fn add(&self, other: &Self) -> Self {
        let (mut i, mut j) = (0, 0);
        let mut parts = Vec::with_capacity(self.parts.len() + other.parts.len());
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
                    parts.push(ExprPart {
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
        Expr { parts }
    }

    /// Wrapping negate all coefficients.
    pub fn neg(&self) -> Self {
        Expr {
            parts: self
                .parts
                .iter()
                .map(|part| ExprPart {
                    coef: part.coef.wrapping_neg(),
                    vars: part.vars.clone(),
                })
                .collect(),
        }
    }

    /// Try to divide by two. This is only possible if all coefficients are off.
    pub fn half(&self) -> Option<Self> {
        if self.parts.iter().all(|part| !part.coef.is_odd()) {
            let mut parts = Vec::with_capacity(self.parts.len());
            for part in &self.parts {
                parts.push(ExprPart {
                    coef: part.coef.wrapping_shr(1),
                    vars: part.vars.clone(),
                });
            }
            Some(Expr { parts })
        } else {
            None
        }
    }

    /// If this expression has a constant value, return that constant value.
    ///
    /// # Examples
    /// ```
    /// # use hpbf::{Expr};
    /// let expr = Expr::<u8>::val(5);
    /// assert_eq!(expr.constant(), Some(5));
    /// let expr = Expr::<u8>::var(0).add(&Expr::<u8>::val(5));
    /// assert_eq!(expr.constant(), None);
    /// ```
    pub fn constant(&self) -> Option<C> {
        if self.parts.is_empty() {
            Some(C::ZERO)
        } else if self.parts.len() == 1 && self.parts[0].vars.is_empty() {
            Some(self.parts[0].coef)
        } else {
            None
        }
    }

    /// If this expression is a simple sum of the variable `var` with some other
    /// expression, return that expression.
    ///
    /// # Examples
    /// ```
    /// # use hpbf::{Expr};
    /// let expr = Expr::<u8>::var(0).add(&Expr::<u8>::val(5));
    /// assert_eq!(expr.inc_of(0), Some(Expr::val(5)));
    /// assert_eq!(expr.inc_of(1), None);
    /// let expr = Expr::<u8>::var(0).mul(&Expr::<u8>::val(5));
    /// assert_eq!(expr.inc_of(0), None);
    /// ```
    pub fn inc_of(&self, var: isize) -> Option<Self> {
        if self
            .parts
            .iter()
            .any(|part| part.vars.len() == 1 && part.vars[0] == var && part.coef == C::ONE)
            && self
                .parts
                .iter()
                .all(|part| !part.vars.contains(&var) || part.vars.len() == 1)
        {
            Some(Expr {
                parts: self
                    .parts
                    .iter()
                    .filter(|part| part.vars.len() != 1 || part.vars[0] != var)
                    .cloned()
                    .collect(),
            })
        } else {
            None
        }
    }

    /// Split this expression into parts that are either completely constant or
    /// linear. For linear parts, the initial value and increment are given.
    pub fn split_along(
        &self,
        constant: &HashSet<isize>,
        linear: &HashMap<isize, Self>,
    ) -> (Self, Self, Vec<(Self, Self)>) {
        let mut const_parts = Vec::new();
        let mut linear_parts = Vec::new();
        let mut other_parts = Vec::new();
        for part in &self.parts {
            if part.vars.iter().all(|v| constant.contains(v)) {
                const_parts.push(part.clone());
            } else if part
                .vars
                .iter()
                .all(|v| constant.contains(v) || linear.contains_key(v))
                && part.vars.iter().filter(|x| !constant.contains(x)).count() == 1
            {
                let lin_var = part.vars.iter().find(|x| !constant.contains(x)).unwrap();
                let increment = ExprPart {
                    coef: part.coef,
                    vars: part
                        .vars
                        .iter()
                        .filter(|&x| x != lin_var)
                        .copied()
                        .collect(),
                };
                linear_parts.push((
                    Expr {
                        parts: vec![part.clone()],
                    },
                    Expr {
                        parts: vec![increment],
                    }
                    .mul(&linear[lin_var]),
                ));
            } else {
                other_parts.push(part.clone());
            }
        }
        (
            Expr { parts: const_parts },
            Expr { parts: other_parts },
            linear_parts,
        )
    }

    /// Combination of [`Self::inc_of`] and [`Self::constant`].
    ///
    /// # Examples
    /// ```
    /// # use hpbf::{Expr};
    /// let expr = Expr::<u8>::val(5);
    /// assert_eq!(expr.const_inc_of(0), None);
    /// let expr = Expr::<u8>::var(0).add(&Expr::<u8>::val(5));
    /// assert_eq!(expr.const_inc_of(0), Some(5));
    /// let expr = Expr::<u8>::var(0).add(&Expr::<u8>::var(5));
    /// assert_eq!(expr.const_inc_of(0), None);
    /// let expr = Expr::<u8>::var(0).mul(&Expr::<u8>::val(5));
    /// assert_eq!(expr.const_inc_of(0), None);
    /// ```
    pub fn const_inc_of(&self, var: isize) -> Option<C> {
        if self.parts.len() == 1
            && self.parts[0].coef == C::ONE
            && self.parts[0].vars.len() == 1
            && self.parts[0].vars[0] == var
        {
            Some(C::ZERO)
        } else if self.parts.len() == 2
            && self.parts[0].vars.is_empty()
            && self.parts[1].coef == C::ONE
            && self.parts[1].vars.len() == 1
            && self.parts[1].vars[0] == var
        {
            Some(self.parts[0].coef)
        } else {
            None
        }
    }

    /// If this expression is a simple product of the variable `var` with some other
    /// expression, return that expression.
    ///
    /// # Examples
    /// ```
    /// # use hpbf::{Expr};
    /// let expr = Expr::<u8>::var(0).mul(&Expr::<u8>::val(5));
    /// assert_eq!(expr.prod_of(0), Some(Expr::val(5)));
    /// assert_eq!(expr.prod_of(1), None);
    /// let expr = Expr::<u8>::var(0).add(&Expr::<u8>::val(5));
    /// assert_eq!(expr.prod_of(0), None);
    /// ```
    pub fn prod_of(&self, var: isize) -> Option<Self> {
        if self
            .parts
            .iter()
            .all(|part| part.vars.iter().filter(|&x| x == &var).count() == 1)
        {
            Some(Expr {
                parts: self
                    .parts
                    .iter()
                    .map(|part| ExprPart {
                        coef: part.coef,
                        vars: part.vars.iter().copied().filter(|&v| v != var).collect(),
                    })
                    .collect(),
            })
        } else {
            None
        }
    }

    /// Combination of [`Self::prod_of`] and [`Self::constant`].
    ///
    /// # Examples
    /// ```
    /// # use hpbf::{Expr};
    /// let expr = Expr::<u8>::val(5);
    /// assert_eq!(expr.const_prod_of(0), None);
    /// let expr = Expr::<u8>::var(0).mul(&Expr::<u8>::val(5));
    /// assert_eq!(expr.const_prod_of(0), Some(5));
    /// let expr = Expr::<u8>::var(0).mul(&Expr::<u8>::var(5));
    /// assert_eq!(expr.const_prod_of(0), None);
    /// ```
    pub fn const_prod_of(&self, var: isize) -> Option<C> {
        if self.parts.is_empty() {
            Some(C::ZERO)
        } else if self.parts.len() == 1
            && self.parts[0].vars.len() == 1
            && self.parts[0].vars[0] == var
        {
            Some(self.parts[0].coef)
        } else {
            None
        }
    }

    /// If this expression is the identity of a single variable, return the
    /// number of that variable, otherwise return [`None`].
    pub fn identity(&self) -> Option<isize> {
        if self.parts.len() == 1 && self.parts[0].coef == C::ONE && self.parts[0].vars.len() == 1 {
            Some(self.parts[0].vars[0])
        } else {
            None
        }
    }

    /// Evaluate the expression by taking getting variable values from the
    /// provided function.
    pub fn evaluate<F: Fn(isize) -> C>(&self, func: F) -> C {
        let mut val = C::ZERO;
        for part in &self.parts {
            let mut part_val = part.coef;
            for &var in &part.vars {
                part_val = part_val.wrapping_mul(func(var));
            }
            val = val.wrapping_add(part_val);
        }
        return val;
    }

    /// Evaluate the expression by taking getting variable values from the
    /// provided function. This differs from [`Self::evaluate`] in that the
    /// values returned for the variables are in turn expressions.
    pub fn symb_evaluate<F>(&self, func: F) -> Option<Self>
    where
        F: Fn(isize) -> Option<Self>,
    {
        if let Some(var) = self.identity() {
            func(var)
        } else if let Some(val) = self.constant() {
            Some(Expr::val(val))
        } else {
            let mut parts = HashMap::with_capacity(self.parts.len());
            for part in &self.parts {
                if part.vars.is_empty() {
                    let v = parts.entry(vec![]).or_insert(C::ZERO);
                    *v = v.wrapping_add(part.coef);
                } else if part.vars.len() == 1 {
                    for var_part in func(part.vars[0])?.parts {
                        let v = parts.entry(var_part.vars).or_insert(C::ZERO);
                        *v = v.wrapping_add(part.coef.wrapping_mul(var_part.coef));
                    }
                } else {
                    let mut partial = func(part.vars[0])?.parts;
                    for &var in part.vars.iter().skip(1) {
                        let var_parts = func(var)?.parts;
                        if var_parts.is_empty() {
                            partial.clear();
                        } else if var_parts.len() == 1 {
                            for ExprPart { vars, coef } in &mut partial {
                                vars.extend(var_parts[0].vars.iter().copied());
                                vars.sort();
                                *coef = coef.wrapping_mul(var_parts[0].coef);
                            }
                        } else {
                            let mut new_partial = HashMap::new();
                            for ExprPart { vars, coef } in partial {
                                for var_part in &var_parts {
                                    let mut vars = vars.clone();
                                    vars.extend(var_part.vars.iter().copied());
                                    vars.sort();
                                    let v = new_partial.entry(vars).or_insert(C::ZERO);
                                    *v = v.wrapping_add(coef.wrapping_mul(var_part.coef));
                                }
                            }
                            partial = new_partial
                                .into_iter()
                                .map(|(vars, coef)| ExprPart { coef, vars })
                                .collect::<Vec<_>>();
                        }
                    }
                    for ExprPart { vars, coef } in partial {
                        let v = parts.entry(vars).or_insert(C::ZERO);
                        *v = v.wrapping_add(part.coef.wrapping_mul(coef));
                    }
                }
            }
            Self::special_normalization_rules(&mut parts);
            let mut parts = parts
                .into_iter()
                .filter(|(_, coef)| *coef != C::ZERO)
                .map(|(vars, coef)| ExprPart { coef, vars })
                .collect::<Vec<_>>();
            parts.sort_by(|a, b| a.vars.cmp(&b.vars));
            Some(Expr { parts })
        }
    }

    /// Return an iterator over all the variables used in this expression.
    pub fn variables<'a>(&'a self) -> impl Iterator<Item = isize> + 'a {
        self.parts.iter().flat_map(|part| part.vars.iter()).copied()
    }
}

impl<C: CellType> Instr<C> {
    /// Create an instruction equivalent to loading the value `val` into the
    /// variable `var`.
    pub fn load(var: isize, val: C) -> Instr<C> {
        Instr::Calc {
            calcs: vec![(var, Expr::val(val))],
        }
    }

    /// Create an instruction equivalent to adding the value `val` onto the
    /// value already in the variable `var`.
    pub fn add(var: isize, val: C) -> Instr<C> {
        Instr::Calc {
            calcs: vec![(var, Expr::val(val).add(&Expr::var(var)))],
        }
    }
}

impl<C: CellType> Program<C> {
    /// Parses a string containing a Brainfuck program into an internal
    /// representation. This will already merge sequential increments
    /// and eliminate movement instructions.
    ///
    /// # Examples
    /// ```
    /// # use hpbf::{Program, Block, Instr, Error};
    /// use Instr::*;
    /// let prog = Program::<u8>::parse("+[-->-[>>+>-----<<]<--<---]>-.")?;
    /// assert_eq!(prog,
    ///     Program {
    ///         shift: 1,
    ///         insts: vec![
    ///             Instr::add(0, 1),
    ///             Loop { cond: 0, block: Block {
    ///                 shift: -1,
    ///                 insts: vec![
    ///                     Instr::add(0, 254),
    ///                     Instr::add(1, 255),
    ///                     Loop { cond: 1, block: Block {
    ///                         shift: 1,
    ///                         insts: vec![
    ///                             Instr::add(3, 1),
    ///                             Instr::add(4, 251),
    ///                         ]
    ///                     } },
    ///                     Instr::add(-1, 253),
    ///                     Instr::add(0, 254),
    ///                 ]
    ///             } },
    ///             Instr::add(1, 255),
    ///             Output { src: 1 },
    ///         ]
    ///     }
    /// );
    /// # Ok::<(), Error>(())
    /// ```
    pub fn parse<'str>(program: &'str str) -> Result<Self, Error<'str>> {
        let mut stack = vec![(0, false, Vec::new(), HashMap::new())];
        let mut positions = vec![];
        for (i, char) in program.chars().enumerate() {
            let (shift, _, insts, buff) = stack.last_mut().unwrap();
            match char {
                '>' => {
                    *shift += 1;
                }
                '<' => {
                    *shift -= 1;
                }
                '+' => {
                    let val = buff.entry(*shift).or_insert(C::ZERO);
                    *val = val.wrapping_add(C::ONE);
                }
                '-' => {
                    let val = buff.entry(*shift).or_insert(C::ZERO);
                    *val = val.wrapping_add(C::NEG_ONE);
                }
                '.' => {
                    let val = buff.entry(*shift).or_insert(C::ZERO);
                    if *val != C::ZERO {
                        insts.push(Instr::add(*shift, *val));
                        *val = C::ZERO;
                    }
                    insts.push(Instr::Output { src: *shift });
                }
                ',' => {
                    insts.push(Instr::Input { dst: *shift });
                    buff.insert(*shift, C::ZERO);
                }
                '[' => {
                    positions.push(i);
                    let cond = *shift;
                    stack.push((cond, false, Vec::new(), HashMap::new()));
                }
                ']' => {
                    if positions.len() == 0 {
                        return Err(Error {
                            kind: ErrorKind::LoopNotOpened,
                            str: program,
                            position: i,
                        });
                    }
                    positions.pop();
                    let (sub_shift, sub_moved, mut sub_insts, sub_buff) = stack.pop().unwrap();
                    let mut vars = sub_buff.into_iter().collect::<Vec<_>>();
                    vars.sort();
                    for &(var, val) in &vars {
                        if val != C::ZERO {
                            sub_insts.push(Instr::add(var, val));
                        }
                    }
                    let (shift, moved, insts, buff) = stack.last_mut().unwrap();
                    if !sub_moved
                        && sub_shift == *shift
                        && sub_insts.len() == 1
                        && matches!(&sub_insts[0],
                            Instr::Calc { calcs } if calcs.len() == 1 && calcs[0].0 == *shift
                                && matches!(calcs[0].1.const_inc_of(*shift),
                                    Some(inc) if inc.is_odd()))
                    {
                        insts.push(Instr::load(*shift, C::ZERO));
                        buff.insert(*shift, C::ZERO);
                    } else {
                        for (var, _) in vars {
                            let v = buff.entry(var).or_insert(C::ZERO);
                            if *v != C::ZERO {
                                insts.push(Instr::add(var, *v));
                                *v = C::ZERO;
                            }
                        }
                        if sub_moved || sub_shift != *shift {
                            let mut vars = buff.iter_mut().collect::<Vec<_>>();
                            vars.sort();
                            for (var, val) in vars {
                                if *val != C::ZERO {
                                    insts.push(Instr::add(*var, *val));
                                    *val = C::ZERO;
                                }
                            }
                            *moved = true;
                        }
                        let val = buff.entry(*shift).or_insert(C::ZERO);
                        if *val != C::ZERO {
                            insts.push(Instr::add(*shift, *val));
                            *val = C::ZERO;
                        }
                        insts.push(Instr::Loop {
                            cond: *shift,
                            block: Block {
                                shift: sub_shift - *shift,
                                insts: sub_insts,
                            },
                        });
                    }
                }
                _ => { /* comment */ }
            }
        }
        if stack.len() != 1 {
            return Err(Error {
                kind: ErrorKind::LoopNotClosed,
                str: program,
                position: *positions.last().unwrap(),
            });
        }
        let (shift, _, mut insts, vars) = stack.pop().unwrap();
        let mut vars = vars.into_iter().collect::<Vec<_>>();
        vars.sort();
        for (var, val) in vars {
            if val != C::ZERO {
                insts.push(Instr::add(var, val));
            }
        }
        return Ok(Block { shift, insts });
    }
}

impl<C: CellType> Debug for Expr<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.parts.is_empty() {
            write!(f, "0")?;
        }
        for (i, part) in self
            .parts
            .iter()
            .rev()
            .filter(|p| p.coef < p.coef.wrapping_neg())
            .chain(
                self.parts
                    .iter()
                    .rev()
                    .filter(|p| p.coef.wrapping_neg() <= p.coef),
            )
            .enumerate()
        {
            if i != 0 {
                if part.coef.wrapping_neg() <= part.coef {
                    write!(f, " - ")?;
                } else {
                    write!(f, " + ")?;
                }
            } else if part.coef.wrapping_neg() <= part.coef {
                write!(f, "-")?;
            }
            let need_num = (part.coef != C::ONE && part.coef != C::NEG_ONE) || part.vars.is_empty();
            if need_num {
                if part.coef.wrapping_neg() <= part.coef {
                    write!(f, "{:?}", part.coef.wrapping_neg())?;
                } else {
                    write!(f, "{:?}", part.coef)?;
                }
            }
            for (j, var) in part.vars.iter().enumerate() {
                if j != 0 || need_num {
                    write!(f, "*")?;
                }
                write!(f, "[{var}]")?;
            }
        }
        Ok(())
    }
}

impl<C: CellType> Block<C> {
    /// Pretty print the block with the given `block_id` and indented by `indent`
    /// spaces into the formatter `f`. Referenced blocks are printed recursively.
    fn print_block(&self, f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
        for instr in &self.insts {
            match instr {
                Instr::Output { src } => {
                    writeln!(f, "{:indent$}output [{}]", "", src, indent = indent)?;
                }
                Instr::Input { dst } => {
                    writeln!(f, "{:indent$}input [{}]", "", dst, indent = indent)?;
                }
                Instr::Calc { calcs } => {
                    let mut indent = indent;
                    if calcs.len() != 1 {
                        writeln!(f, "{:indent$}(", "", indent = indent)?;
                        indent += 2;
                    }
                    for (dst, val) in calcs {
                        if val.constant() == Some(C::ZERO) {
                            writeln!(f, "{:indent$}[{}] = 0", "", dst, indent = indent)?;
                        } else if let Some(inc) = val.inc_of(*dst) {
                            if inc
                                .parts
                                .iter()
                                .all(|part| part.coef.wrapping_neg() <= part.coef)
                            {
                                let dec = inc.neg();
                                writeln!(f, "{:indent$}[{}] -= {dec:?}", "", dst, indent = indent)?;
                            } else {
                                writeln!(f, "{:indent$}[{}] += {inc:?}", "", dst, indent = indent)?;
                            }
                        } else if let Some(mul) = val.prod_of(*dst) {
                            writeln!(f, "{:indent$}[{}] *= {mul:?}", "", dst, indent = indent)?;
                        } else {
                            writeln!(f, "{:indent$}[{}] = {val:?}", "", dst, indent = indent)?;
                        }
                    }
                    if calcs.len() != 1 {
                        indent -= 2;
                        writeln!(f, "{:indent$})", "", indent = indent)?;
                    }
                }
                Instr::Loop { cond, block } => {
                    writeln!(f, "{:indent$}loop [{}] {{", "", cond, indent = indent)?;
                    block.print_block(f, indent + 2)?;
                    writeln!(f, "{:indent$}}}", "", indent = indent)?;
                }
                Instr::If { cond, block } => {
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

impl<C: CellType> Debug for Program<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.print_block(f, 0)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Block, Error, ErrorKind, Instr, Program};
    use Instr::*;

    #[test]
    fn parsing_valid_brainfuck_returns_block() -> Result<(), Error<'static>> {
        let prog = Program::<u8>::parse("+++++[>[-],.<--]")?;
        assert_eq!(
            prog,
            Program {
                shift: 0,
                insts: vec![
                    Instr::add(0, 5),
                    Loop {
                        cond: 0,
                        block: Block {
                            shift: 0,
                            insts: vec![
                                Instr::load(1, 0),
                                Input { dst: 1 },
                                Output { src: 1 },
                                Instr::add(0, 254),
                            ]
                        }
                    }
                ]
            }
        );
        Ok(())
    }

    #[test]
    fn parsing_with_missing_closing_returns_error() {
        let code = "+++++[>[-],.<--";
        let prog = Program::<u8>::parse(code);
        assert_eq!(
            prog,
            Err(Error {
                kind: ErrorKind::LoopNotClosed,
                str: code,
                position: 5
            })
        );
    }

    #[test]
    fn parsing_with_missing_opening_return_error() {
        let code = "+++++>[-],.<]--";
        let prog = Program::<u8>::parse(code);
        assert_eq!(
            prog,
            Err(Error {
                kind: ErrorKind::LoopNotOpened,
                str: code,
                position: 12
            })
        );
    }

    #[test]
    fn ir_implements_debug() {
        let code = "+++++[>[-],.<]--";
        let prog = Program::<u8>::parse(code).unwrap();
        assert_eq!(
            format!("{prog:?}"),
            "[0] += 5\n\
            loop [0] {\n  \
                [1] = 0\n  \
                input [1]\n  \
                output [1]\n\
            }\n\
            [0] -= 2\n\
            "
        );
    }
}
