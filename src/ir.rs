//! Contains parsing and some optimizing transformations for a Brainfuck program.

use std::fmt::{self, Debug};

use crate::{
    hasher::{HashMap, HashSet},
    smallvec::SmallVec,
    CellType, Error, ErrorKind,
};

/// Parts of expression. Represents the product of the coefficient and the set
/// of variables.
#[derive(Clone, PartialEq, Eq, Hash)]
struct ExprPart<C: CellType> {
    coef: C,
    vars: SmallVec<isize, 1>,
}

/// An expression used in the IR to represent a calculation. Expressions in the
/// IR represent sums of products. Currently, all expressions are normalized.
/// This ensures that two equivalent expressions compare ans hash equals.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Expr<C: CellType> {
    parts: SmallVec<ExprPart<C>, 2>,
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
    Output {
        src: isize,
    },
    Input {
        dst: isize,
    },
    Calc {
        calcs: SmallVec<(isize, Expr<C>), 1>,
    },
    Loop {
        cond: isize,
        block: Block<C>,
    },
    If {
        cond: isize,
        block: Block<C>,
    },
}

/// Type for abstracting over the different code generation backends.
pub trait CodeGen<C: CellType> {
    /// This is the input and output type of the operations.
    type Output;
    type Error;

    /// Generate code for loading an immediate value.
    fn imm(&mut self, imm: C) -> Result<Self::Output, Self::Error>;

    /// Generate code for loading from a memory location.
    fn mem(&mut self, var: isize) -> Result<Self::Output, Self::Error>;

    /// Generate code for loading from a adding two values.
    fn add(&mut self, a: Self::Output, b: Self::Output) -> Result<Self::Output, Self::Error>;

    /// Generate code for loading from a subtracting two values.
    fn sub(&mut self, a: Self::Output, b: Self::Output) -> Result<Self::Output, Self::Error>;

    /// Generate code for loading from a multiplying two values.
    fn mul(&mut self, a: Self::Output, b: Self::Output) -> Result<Self::Output, Self::Error>;
}

impl<C: CellType> Expr<C> {
    /// Return the expression representing the constant value given by `coef`.
    pub fn val(coef: C) -> Self {
        if coef == C::ZERO {
            Expr {
                parts: SmallVec::new(),
            }
        } else {
            Expr {
                parts: SmallVec::with(ExprPart {
                    coef,
                    vars: SmallVec::new(),
                }),
            }
        }
    }

    /// Return the expression representing the value at memory offset `var`.
    pub fn var(var: isize) -> Self {
        Expr {
            parts: SmallVec::with(ExprPart {
                coef: C::ONE,
                vars: SmallVec::with(var),
            }),
        }
    }

    /// Return the number of operations needed to compute this expressions.
    /// This is only a loose worst case approximation.
    pub fn op_count(&self) -> usize {
        (self.parts.iter().map(|p| 2 * p.vars.len()).sum::<usize>()
            + self
                .parts
                .iter()
                .filter(|p| p.coef != C::ONE && p.coef != C::NEG_ONE)
                .count())
        .saturating_sub(1)
    }

    /// Return the number of additions needed to compute this expressions.
    pub fn add_count(&self) -> usize {
        self.parts.len().saturating_sub(1)
    }

    /// Return true if this expression is a constant zero.
    pub fn is_zero(&self) -> bool {
        self.parts.is_empty()
    }

    /// Special detection of e.g. 128*x + 129*x*x which is equivalent to x*x.
    /// For now, only do this when it enables us to eliminate a multiplication
    /// or even a complete term.
    pub fn normalize(mut self) -> Self {
        if !self.parts.is_empty() && self.parts.iter().any(|p| p.vars.len() >= 2) {
            let half_mod = C::ONE.wrapping_shl(C::BITS - 1);
            let half_mod_p = half_mod.wrapping_add(C::ONE);
            let half_mod_m = half_mod.wrapping_add(C::NEG_ONE);
            if self
                .parts
                .iter()
                .any(|p| p.vars.len() >= 2 && p.coef == half_mod)
            {
                let mut need_elim = false;
                for part in &mut self.parts {
                    if part.coef == half_mod {
                        let prev_len = part.vars.len();
                        part.vars.dedup();
                        if prev_len != part.vars.len() {
                            need_elim = true;
                        }
                    }
                }
                if need_elim {
                    self.parts.sort_by(|a, b| a.vars.cmp(&b.vars));
                    for chunk in self.parts.chunk_by_mut(|p1, p2| p1.vars == p2.vars) {
                        for i in 1..chunk.len() {
                            chunk[0].coef = chunk[0].coef.wrapping_add(chunk[i].coef);
                            chunk[i].coef = C::ZERO;
                        }
                    }
                    self.parts.retain(|p| p.coef != C::ZERO);
                }
            }
            if self
                .parts
                .iter()
                .any(|p| !p.vars.is_empty() && (p.coef <= half_mod_p || p.coef >= half_mod_m))
            {
                let mut need_elim = false;
                let mut by_reduced = HashMap::<SmallVec<isize, 1>, SmallVec<usize, 1>>::new();
                for i in 0..self.parts.len() {
                    if !self.parts[i].vars.is_empty() {
                        let mut vars = self.parts[i].vars.clone();
                        vars.dedup();
                        if let Some(others) = by_reduced.get_mut(&vars) {
                            for &j in others.iter() {
                                if ((self.parts[i].coef <= half_mod_p
                                    || self.parts[i].coef >= half_mod_m)
                                    && (self.parts[j].coef > C::ONE
                                        || self.parts[j].coef < C::NEG_ONE))
                                    || ((self.parts[i].coef > C::ONE
                                        && self.parts[i].coef < C::NEG_ONE)
                                        && (self.parts[j].coef <= half_mod_p
                                            || self.parts[j].coef >= half_mod_m))
                                {
                                    let new_coef_i = self.parts[i].coef.wrapping_add(half_mod);
                                    let new_coef_j = self.parts[j].coef.wrapping_add(half_mod);
                                    self.parts[i].coef = new_coef_i;
                                    self.parts[j].coef = new_coef_j;
                                    if new_coef_i == C::ZERO || new_coef_j == C::ZERO {
                                        need_elim = true;
                                    }
                                }
                            }
                            others.push(i);
                        } else {
                            by_reduced.insert(vars, SmallVec::<_, 1>::with(i));
                        }
                    }
                }
                if need_elim {
                    self.parts.retain(|p| p.coef != C::ZERO);
                }
            }
        }
        return self;
    }

    /// Multiply two expressions and return the resulting expressions.
    pub fn mul(&self, other: impl AsRef<Self> + Into<Self>) -> Self {
        if self.parts.is_empty() || other.as_ref().parts.is_empty() {
            return Expr::val(C::ZERO);
        } else if self.parts.len() == 1 {
            let mut res = other.into();
            res.parts.retain_mut(|ExprPart { coef, vars }| {
                vars.extend(self.parts[0].vars.iter().copied());
                *coef = coef.wrapping_mul(self.parts[0].coef);
                *coef != C::ZERO
            });
            return res;
        } else if other.as_ref().parts.len() == 1 {
            let mut res = self.clone();
            res.parts.retain_mut(|ExprPart { coef, vars }| {
                vars.extend(other.as_ref().parts[0].vars.iter().copied());
                *coef = coef.wrapping_mul(other.as_ref().parts[0].coef);
                *coef != C::ZERO
            });
            return res;
        } else {
            let mut parts = HashMap::with_capacity(self.parts.len() * other.as_ref().parts.len());
            for self_part in &self.parts {
                for other_part in &other.as_ref().parts {
                    let mut vars = self_part.vars.clone();
                    vars.extend(other_part.vars.iter().copied());
                    vars.sort();
                    let coef = self_part.coef.wrapping_mul(other_part.coef);
                    let v = parts.entry(vars).or_insert(C::ZERO);
                    *v = v.wrapping_add(coef);
                }
            }
            let mut parts_vec = SmallVec::new();
            parts_vec.extend(
                parts
                    .into_iter()
                    .filter(|(_, coef)| *coef != C::ZERO)
                    .map(|(vars, coef)| ExprPart { coef, vars }),
            );
            parts_vec.sort_by(|a, b| a.vars.cmp(&b.vars));
            Expr { parts: parts_vec }
        }
    }

    /// Add two expressions and return the resulting expressions.
    pub fn add(&self, other: impl AsRef<Self>) -> Self {
        let (mut i, mut j) = (0, 0);
        let mut parts = SmallVec::new();
        while i < self.parts.len() && j < other.as_ref().parts.len() {
            if self.parts[i].vars < other.as_ref().parts[j].vars {
                parts.push(self.parts[i].clone());
                i += 1;
            } else if self.parts[i].vars > other.as_ref().parts[j].vars {
                parts.push(other.as_ref().parts[j].clone());
                j += 1;
            } else {
                let coef = self.parts[i]
                    .coef
                    .wrapping_add(other.as_ref().parts[j].coef);
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
        while j < other.as_ref().parts.len() {
            parts.push(other.as_ref().parts[j].clone());
            j += 1;
        }
        Expr { parts }
    }

    /// Wrapping negate all coefficients.
    pub fn neg(&self) -> Self {
        let mut res = self.clone();
        for part in &mut res.parts {
            part.coef = part.coef.wrapping_neg();
        }
        res
    }

    /// Try to divide by two. This is only possible if all coefficients are off.
    pub fn half(&self) -> Option<Self> {
        if self.parts.iter().all(|part| !part.coef.is_odd()) {
            let mut res = self.clone();
            for part in &mut res.parts {
                part.coef = part.coef.wrapping_shr(1);
            }
            Some(res)
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
    /// let expr = Expr::<u8>::var(0).add(Expr::<u8>::val(5));
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
    /// let expr = Expr::<u8>::var(0).add(Expr::<u8>::val(5));
    /// assert_eq!(expr.inc_of(0), Some(Expr::val(5)));
    /// assert_eq!(expr.inc_of(1), None);
    /// let expr = Expr::<u8>::var(0).mul(Expr::<u8>::val(5));
    /// assert_eq!(expr.inc_of(0), None);
    /// ```
    pub fn inc_of(&self, var: isize) -> Option<Self> {
        if self
            .parts
            .iter()
            .any(|part| part.coef == C::ONE && part.vars.len() == 1 && part.vars[0] == var)
            && self
                .parts
                .iter()
                .all(|part| !part.vars.contains(&var) || part.vars.len() == 1)
        {
            let mut parts = SmallVec::with_capacity(self.parts.len() - 1);
            for part in &self.parts {
                if part.vars.len() != 1 || part.vars[0] != var {
                    parts.push(part.clone());
                }
            }
            Some(Expr { parts })
        } else {
            None
        }
    }

    /// If this expression is a simple sum of a multiple of the variable `var`
    /// with some other expression, return that expression and the multiple.
    ///
    /// # Examples
    /// ```
    /// # use hpbf::{Expr};
    /// let expr = Expr::<u8>::var(0).add(Expr::<u8>::val(5));
    /// assert_eq!(expr.prod_inc_of(0), Some((Expr::val(5), 1)));
    /// assert_eq!(expr.prod_inc_of(1), Some((expr, 0)));
    /// let expr = Expr::<u8>::var(0).mul(Expr::<u8>::val(5));
    /// assert_eq!(expr.prod_inc_of(0), Some((Expr::val(0), 5)));
    /// ```
    pub fn prod_inc_of(&self, var: isize) -> Option<(Self, C)> {
        if self
            .parts
            .iter()
            .all(|part| !part.vars.contains(&var) || part.vars.len() == 1)
        {
            let mut mul = C::ZERO;
            let mut parts = SmallVec::with_capacity(self.parts.len());
            for part in &self.parts {
                if part.vars.len() != 1 || part.vars[0] != var {
                    parts.push(part.clone());
                } else {
                    mul = part.coef;
                }
            }
            Some((Expr { parts }, mul))
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
        let mut const_parts = SmallVec::new();
        let mut other_parts = SmallVec::new();
        let mut linear_parts = Vec::new();
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
                let mut vars = SmallVec::with_capacity(part.vars.len() - 1);
                vars.extend(part.vars.iter().filter(|&x| x != lin_var).copied());
                let increment = ExprPart {
                    coef: part.coef,
                    vars,
                };
                linear_parts.push((
                    Expr {
                        parts: SmallVec::with(part.clone()),
                    },
                    Expr {
                        parts: SmallVec::with(increment),
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
    /// let expr = Expr::<u8>::var(0).add(Expr::<u8>::val(5));
    /// assert_eq!(expr.const_inc_of(0), Some(5));
    /// let expr = Expr::<u8>::var(0).add(Expr::<u8>::var(5));
    /// assert_eq!(expr.const_inc_of(0), None);
    /// let expr = Expr::<u8>::var(0).mul(Expr::<u8>::val(5));
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
    /// let expr = Expr::<u8>::var(0).mul(Expr::<u8>::val(5));
    /// assert_eq!(expr.prod_of(0), Some(Expr::val(5)));
    /// assert_eq!(expr.prod_of(1), None);
    /// let expr = Expr::<u8>::var(0).add(Expr::<u8>::val(5));
    /// assert_eq!(expr.prod_of(0), None);
    /// ```
    pub fn prod_of(&self, var: isize) -> Option<Self> {
        if self
            .parts
            .iter()
            .all(|part| part.vars.iter().filter(|&x| x == &var).count() == 1)
        {
            let mut parts = SmallVec::with_capacity(self.parts.len());
            for part in &self.parts {
                let mut vars = SmallVec::with_capacity(part.vars.len() - 1);
                vars.extend(part.vars.iter().copied().filter(|&v| v != var));
                parts.push(ExprPart {
                    coef: part.coef,
                    vars,
                });
            }
            Some(Expr { parts })
        } else {
            None
        }
    }

    /// Return the part of this expression that is the result of all variables
    /// evaluating to zero. This is a more efficient implementation for this
    /// specific case than using [`Self::evaluate`].
    pub fn constant_part(&self) -> C {
        if self.parts.is_empty() || !self.parts[0].vars.is_empty() {
            C::ZERO
        } else {
            self.parts[0].coef
        }
    }

    /// Return the variables but grouped by multiplication.
    pub fn grouped_vars<'a>(&'a self) -> impl Iterator<Item = &'a SmallVec<isize, 1>> + 'a {
        self.parts.iter().map(|part| &part.vars)
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

    /// Multiply the two expressions continuing the given parts.
    /// Only for internal use.
    fn mul_parts(
        mut left: SmallVec<ExprPart<C>, 2>,
        mut right: SmallVec<ExprPart<C>, 2>,
    ) -> SmallVec<ExprPart<C>, 2> {
        if left.is_empty() {
            right.clear();
            return right;
        } else if right.is_empty() {
            left.clear();
            return left;
        } else if left.len() == 1 {
            right.retain_mut(|ExprPart { vars, coef }| {
                vars.extend(left[0].vars.iter().copied());
                vars.sort();
                *coef = coef.wrapping_mul(left[0].coef);
                *coef != C::ZERO
            });
            return right;
        } else if right.len() == 1 {
            left.retain_mut(|ExprPart { vars, coef }| {
                vars.extend(right[0].vars.iter().copied());
                vars.sort();
                *coef = coef.wrapping_mul(right[0].coef);
                *coef != C::ZERO
            });
            return left;
        } else {
            let mut new_partial = HashMap::new();
            for ExprPart { vars, coef } in right {
                for var_part in &left {
                    let mut vars = vars.clone();
                    vars.extend(var_part.vars.iter().copied());
                    vars.sort();
                    let v = new_partial.entry(vars).or_insert(C::ZERO);
                    *v = v.wrapping_add(coef.wrapping_mul(var_part.coef));
                }
            }
            left.clear();
            left.extend(
                new_partial
                    .into_iter()
                    .filter(|(_, coef)| *coef != C::ZERO)
                    .map(|(vars, coef)| ExprPart { coef, vars }),
            );
            return left;
        }
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
                    let v = parts.entry(SmallVec::new()).or_insert(C::ZERO);
                    *v = v.wrapping_add(part.coef);
                } else if part.vars.len() == 1 {
                    for var_part in func(part.vars[0])?.parts {
                        let v = parts.entry(var_part.vars.clone()).or_insert(C::ZERO);
                        *v = v.wrapping_add(part.coef.wrapping_mul(var_part.coef));
                    }
                } else {
                    let mut partial = func(part.vars[0])?.parts;
                    for &var in part.vars.iter().skip(1) {
                        let var_parts = func(var)?.parts;
                        partial = Self::mul_parts(partial, var_parts);
                    }
                    for ExprPart { vars, coef } in partial {
                        let v = parts.entry(vars).or_insert(C::ZERO);
                        *v = v.wrapping_add(part.coef.wrapping_mul(coef));
                    }
                }
            }
            let mut parts_vec = SmallVec::new();
            parts_vec.extend(
                parts
                    .into_iter()
                    .filter(|(_, coef)| *coef != C::ZERO)
                    .map(|(vars, coef)| ExprPart { coef, vars }),
            );
            parts_vec.sort_by(|a, b| a.vars.cmp(&b.vars));
            Some(Expr { parts: parts_vec })
        }
    }

    /// Perform the given operations on the codegen object to evaluate the expression.
    /// Try to perform operations that use variables for which `ordering` returns
    /// a low value first and others later.
    pub fn codegen<G: CodeGen<C>>(
        &self,
        codegen: &mut G,
        ordering: impl Fn(isize) -> usize,
    ) -> Result<G::Output, G::Error> {
        fn codegen_part<C: CellType, G: CodeGen<C>>(
            part: &ExprPart<C>,
            codegen: &mut G,
            ordering: &impl Fn(isize) -> usize,
        ) -> Result<G::Output, G::Error> {
            if part.vars.is_empty() {
                codegen.imm(part.coef)
            } else {
                let mut sorted = part.vars.clone();
                sorted.sort_by_key(|&x| ordering(x));
                let mut result = codegen.mem(sorted[0])?;
                for var in sorted.into_iter().skip(1) {
                    let mem = codegen.mem(var)?;
                    result = codegen.mul(result, mem)?;
                }
                if part.coef == C::ONE || part.coef == C::NEG_ONE {
                    Ok(result)
                } else {
                    let imm = codegen.imm(part.coef)?;
                    codegen.mul(result, imm)
                }
            }
        }
        if self.parts.is_empty() {
            codegen.imm(C::ZERO)
        } else {
            let mut sorted = self.parts.iter().collect::<Vec<_>>();
            sorted.sort_by_key(|part| part.vars.iter().map(|&v| ordering(v)).min().unwrap_or(0));
            if !sorted[0].vars.is_empty() && sorted[0].coef == C::NEG_ONE {
                if let Some(idx) = sorted
                    .iter()
                    .position(|p| p.vars.is_empty() || p.coef != C::NEG_ONE)
                {
                    sorted.swap(0, idx);
                }
            }
            let mut result = codegen_part(sorted[0], codegen, &ordering)?;
            if sorted[0].coef == C::NEG_ONE {
                let zero = codegen.imm(C::ZERO)?;
                result = codegen.sub(zero, result)?;
            }
            for part in sorted.into_iter().skip(1) {
                let part_res = codegen_part(part, codegen, &ordering)?;
                if part.coef == C::NEG_ONE {
                    result = codegen.sub(result, part_res)?;
                } else {
                    result = codegen.add(result, part_res)?;
                }
            }
            Ok(result)
        }
    }

    /// Return an iterator over all the variables used in this expression.
    pub fn variables<'a>(&'a self) -> impl Iterator<Item = isize> + 'a {
        self.parts.iter().flat_map(|part| part.vars.iter()).copied()
    }

    /// Return an iterator over all the variables used in this expression.
    pub fn variables_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut isize> + 'a {
        self.parts.iter_mut().flat_map(|part| part.vars.iter_mut())
    }
}

impl<C: CellType> Instr<C> {
    /// Create an instruction equivalent to loading the value `val` into the
    /// variable `var`.
    pub fn load(var: isize, val: C) -> Instr<C> {
        Instr::Calc {
            calcs: SmallVec::with((var, Expr::val(val))),
        }
    }

    /// Create an instruction equivalent to adding the value `val` onto the
    /// value already in the variable `var`.
    pub fn add(var: isize, val: C) -> Instr<C> {
        Instr::Calc {
            calcs: SmallVec::with((
                var,
                Expr {
                    parts: SmallVec::with_all([
                        ExprPart {
                            coef: val,
                            vars: SmallVec::new(),
                        },
                        ExprPart {
                            coef: C::ONE,
                            vars: SmallVec::with(var),
                        },
                    ]),
                },
            )),
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
    /// Pretty print the block indented by `indent` spaces into the formatter `f`.
    /// Referenced blocks are printed recursively.
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

impl<C: CellType> AsRef<Expr<C>> for Expr<C> {
    fn as_ref(&self) -> &Expr<C> {
        self
    }
}

impl<C: CellType> Into<Expr<C>> for &Expr<C> {
    fn into(self) -> Expr<C> {
        self.clone()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ir::{Block, Instr, Program},
        Error, ErrorKind,
    };
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
