//! Contains parsing and some optimizing transformations for a Brainfuck program.

use std::{
    collections::HashMap,
    fmt::{self, Debug},
};

use crate::{CellType, Error, ErrorKind};

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

    /// Multiply two expressions and return the resulting expressions.
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
            .map(|(vars, coef)| ExprPart { coef, vars })
            .collect::<Vec<_>>();
        parts.sort_by(|a, b| a.vars.cmp(&b.vars));
        Expr { parts }
    }

    /// Add two expressions and return the resulting expressions.
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
    pub fn inc_of(&self, var: isize) -> Option<Expr<C>> {
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
    pub fn prod_of(&self, var: isize) -> Option<Expr<C>> {
        if self.parts.iter().all(|part| part.vars.contains(&var)) {
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
        let mut val = Expr::val(C::ZERO);
        for part in &self.parts {
            let mut part_val = Expr::val(part.coef);
            for &var in &part.vars {
                part_val = part_val.mul(&func(var)?);
            }
            val = val.add(&part_val);
        }
        return Some(val);
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
        for (i, part) in self.parts.iter().enumerate() {
            if i != 0 {
                write!(f, " + ")?;
            }
            if part.coef != C::ONE || part.vars.is_empty() {
                if part.coef.wrapping_neg() < part.coef {
                    write!(f, "-{:?}", part.coef.wrapping_neg())?;
                } else {
                    write!(f, "{:?}", part.coef)?;
                }
            }
            for (j, var) in part.vars.iter().enumerate() {
                if j != 0 || part.coef != C::ONE || part.vars.is_empty() {
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
                        if let Some(c) = val.constant() {
                            writeln!(f, "{:indent$}[{}] = {c:?}", "", dst, indent = indent)?;
                        } else if let Some(inc) = val.inc_of(*dst) {
                            writeln!(f, "{:indent$}[{}] += {inc:?}", "", dst, indent = indent)?;
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
}
