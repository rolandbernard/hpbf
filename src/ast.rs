//! Contains parsing and optimizing transformations for a Brainfuck program.

use std::collections::{HashMap, HashSet};

use crate::{CellType, Error, ErrorKind};

/// Represents a complete Brainfuck program or inside of a loop.
pub type Block<C> = Vec<Instr<C>>;

/// This represents a Brainfuck instruction. It includes not only the basic
/// Brainfuck instructions, but also some additional operations that are common
/// in Brainfuck and help the backend to generate better code.
#[derive(Clone, PartialEq, Debug)]
pub enum Instr<C: CellType> {
    Move(isize),
    Load(C, isize),
    Add(C, isize),
    MulAdd(C, isize, isize),
    Output(isize),
    Input(isize),
    Loop(isize, Block<C>),
}

/// Parses a string containing a Brainfuck program into an internal
/// representation. This will already cluster sequential increment, decrement,
/// and movement instructions.
///
/// # Examples
/// ```
/// # use hpbf::{parse, Error, Instr};
/// use Instr::*;
///
/// let prog = parse::<u8>("+[-->-[>>+>-----<<]<--<---]>-.>>>+.>>..+++[.>]<<<<.+++.------.<<-.>>>>+.")?;
///
/// assert_eq!(prog, vec![
///     Add(1, 0),
///     Loop(0, vec![
///         Add(254, 0), Move(1), Add(255, 0),
///         Loop(0, vec![Move(2), Add(1, 0), Move(1), Add(251, 0), Move(-2)]),
///         Move(-1), Add(254, 0), Move(-1), Add(253, 0),
///     ]),
///     Move(1), Add(255, 0), Output(0), Move(3), Add(1, 0), Output(0),
///     Move(2), Output(0), Output(0), Add(3, 0),
///     Loop(0, vec![Output(0), Move(1)]),
///     Move(-4), Output(0), Add(3, 0), Output(0), Add(250, 0), Output(0),
///     Move(-2), Add(255, 0), Output(0), Move(4), Add(1, 0), Output(0),
/// ]);
/// # Ok::<(), Error>(())
/// ```
pub fn parse<C: CellType>(program: &str) -> Result<Block<C>, Error> {
    let mut blocks = vec![Block::<C>::new()];
    let mut positions = vec![];
    for (i, char) in program.chars().enumerate() {
        let block = blocks.last_mut().unwrap();
        match char {
            '>' => {
                if let Some(Instr::Move(i)) = block.last_mut() {
                    *i += 1;
                } else {
                    block.push(Instr::Move(1));
                }
            }
            '<' => {
                if let Some(Instr::Move(i)) = block.last_mut() {
                    *i -= 1;
                } else {
                    block.push(Instr::Move(-1));
                }
            }
            '+' => {
                if let Some(Instr::Add(i, 0)) = block.last_mut() {
                    *i = i.wrapping_add(C::ONE);
                } else {
                    block.push(Instr::Add(C::ONE, 0));
                }
            }
            '-' => {
                if let Some(Instr::Add(i, 0)) = block.last_mut() {
                    *i = i.wrapping_add(C::NEG_ONE);
                } else {
                    block.push(Instr::Add(C::NEG_ONE, 0));
                }
            }
            '.' => {
                block.push(Instr::Output(0));
            }
            ',' => {
                block.push(Instr::Input(0));
            }
            '[' => {
                positions.push(i);
                blocks.push(Block::new());
            }
            ']' => {
                if positions.len() == 0 {
                    return Err(Error {
                        kind: ErrorKind::LoopNotOpened,
                        position: i,
                    });
                } else {
                    positions.pop();
                    let instr = Instr::Loop(0, blocks.pop().unwrap());
                    blocks.last_mut().unwrap().push(instr);
                }
            }
            _ => { /* comment */ }
        }
    }
    if blocks.len() == 1 {
        return Ok(blocks.remove(0));
    } else {
        return Err(Error {
            kind: ErrorKind::LoopNotClosed,
            position: *positions.last().unwrap(),
        });
    }
}

enum OptimizerValue<C> {
    UnknownValue,
    UnknownAddition { pending: C },
    KnownValue { value: C, pending: bool },
    KnownAddition { value: C, pending: C },
}

struct OptimizerContext<C> {
    ptr: isize,
    had_shift: bool,
    cell_values: HashMap<isize, OptimizerValue<C>>,
    read_cells: HashSet<isize>,
    written_cells: HashSet<isize>,
}

enum OptimizerLoopCount<C: CellType> {
    Unknown,
    Finite,
    Simple,
    SimpleNegated,
    AtLeastOnce,
    AtMostOnce,
    NeverOrInfinite,
    Infinite,
    NTimes(C),
}

impl<C: CellType> OptimizerLoopCount<C> {
    fn never(&self) -> bool {
        match self {
            OptimizerLoopCount::NTimes(c) if *c == C::ZERO => true,
            _ => false,
        }
    }

    fn at_least_once(&self) -> bool {
        match self {
            OptimizerLoopCount::AtLeastOnce => true,
            OptimizerLoopCount::Infinite => true,
            OptimizerLoopCount::NTimes(c) if *c != C::ZERO => true,
            _ => false,
        }
    }

    fn at_most_once(&self) -> bool {
        match self {
            OptimizerLoopCount::AtMostOnce => true,
            OptimizerLoopCount::NTimes(c) if *c == C::ZERO || *c == C::ONE => true,
            _ => false,
        }
    }

    fn effects_seen_later(&self) -> bool {
        match self {
            OptimizerLoopCount::NeverOrInfinite => false,
            OptimizerLoopCount::Infinite => false,
            OptimizerLoopCount::NTimes(c) if *c == C::ZERO => false,
            _ => true,
        }
    }

    fn is_finite(&self) -> bool {
        match self {
            OptimizerLoopCount::Finite => true,
            OptimizerLoopCount::Simple => true,
            OptimizerLoopCount::SimpleNegated => true,
            OptimizerLoopCount::AtMostOnce => true,
            OptimizerLoopCount::NTimes(_) => true,
            _ => false,
        }
    }
}

impl<C: CellType> OptimizerContext<C> {
    fn new(ptr: isize) -> Self {
        OptimizerContext::<C> {
            ptr,
            had_shift: false,
            cell_values: HashMap::new(),
            read_cells: HashSet::new(),
            written_cells: HashSet::new(),
        }
    }

    fn emit(&mut self, src: isize, block: &mut Block<C>) {
        match self.cell_values.get_mut(&src) {
            Some(OptimizerValue::KnownValue { value, pending }) if *pending => {
                block.push(Instr::Load(*value, src));
                *pending = false;
                self.written_cells.insert(src);
            }
            Some(
                OptimizerValue::KnownAddition { pending, .. }
                | OptimizerValue::UnknownAddition { pending },
            ) if *pending != C::ZERO => {
                block.push(Instr::Add(*pending, src));
                *pending = C::ZERO;
                self.read_cells.insert(src);
                self.written_cells.insert(src);
            }
            _ => {
                if !self.written_cells.contains(&src) {
                    self.read_cells.insert(src);
                }
            }
        }
    }

    fn emit_all(&mut self, to_emit: &[isize], block: &mut Block<C>) {
        for &cell in to_emit {
            self.emit(cell, block);
        }
    }

    fn pending(&self) -> Vec<isize> {
        self.cell_values
            .iter()
            .filter(|(k, v)| match v {
                OptimizerValue::KnownValue { value, pending } if *pending => true,
                OptimizerValue::KnownAddition { pending, .. }
                | OptimizerValue::UnknownAddition { pending }
                    if *pending != C::ZERO =>
                {
                    true
                }
                _ => false,
            })
            .map(|(k, _)| *k)
            .collect()
    }

    fn read_and_pending(&self) -> Vec<isize> {
        self.cell_values
            .iter()
            .filter(|(k, v)| match v {
                OptimizerValue::KnownValue { value, pending } if *pending => true,
                OptimizerValue::KnownAddition { pending, .. }
                | OptimizerValue::UnknownAddition { pending }
                    if *pending != C::ZERO =>
                {
                    true
                }
                _ => false,
            })
            .map(|(k, _)| *k)
            .filter(|dst| self.read_cells.contains(dst))
            .collect()
    }

    fn read(&self) -> Vec<isize> {
        self.read_cells.iter().copied().collect()
    }

    fn compute_loop_count(&self, cond: isize, sub_cxt: &Self) -> OptimizerLoopCount<C> {
        if self.ptr != sub_cxt.ptr || sub_cxt.had_shift {
            OptimizerLoopCount::Unknown
        } else if let Some(OptimizerValue::KnownValue { value, .. }) = self.cell_values.get(&cond) {
            if *value == C::ZERO {
                OptimizerLoopCount::NTimes(C::ZERO)
            } else {
                match sub_cxt.cell_values.get(&cond) {
                    Some(OptimizerValue::KnownValue { value, .. }) => {
                        if *value == C::ZERO {
                            OptimizerLoopCount::NTimes(C::ONE)
                        } else {
                            OptimizerLoopCount::Infinite
                        }
                    }
                    Some(OptimizerValue::KnownAddition { value: inc, .. }) => {
                        if let Some(n) = value.wrapping_div(inc.wrapping_negate()) {
                            OptimizerLoopCount::NTimes(n)
                        } else {
                            OptimizerLoopCount::Infinite
                        }
                    }
                    Some(_) => OptimizerLoopCount::AtLeastOnce,
                    None => OptimizerLoopCount::Infinite,
                }
            }
        } else {
            match sub_cxt.cell_values.get(&cond) {
                Some(OptimizerValue::KnownValue { value, .. }) => {
                    if *value == C::ZERO {
                        OptimizerLoopCount::AtMostOnce
                    } else {
                        OptimizerLoopCount::NeverOrInfinite
                    }
                }
                Some(OptimizerValue::KnownAddition { value: inc, .. }) => {
                    if *inc == C::NEG_ONE {
                        OptimizerLoopCount::Simple
                    } else if *inc == C::ONE {
                        OptimizerLoopCount::SimpleNegated
                    } else if *inc == C::ZERO {
                        OptimizerLoopCount::NeverOrInfinite
                    } else if inc.is_odd() {
                        OptimizerLoopCount::Finite
                    } else {
                        OptimizerLoopCount::Unknown
                    }
                }
                Some(_) => OptimizerLoopCount::Unknown,
                None => OptimizerLoopCount::NeverOrInfinite,
            }
        }
    }

    fn load_cell(&mut self, dst: isize, val: C) {
        match self
            .cell_values
            .entry(dst)
            .or_insert(OptimizerValue::UnknownValue)
        {
            a @ (OptimizerValue::UnknownValue
            | OptimizerValue::UnknownAddition { .. }
            | OptimizerValue::KnownAddition { .. }) => {
                *a = OptimizerValue::KnownValue {
                    value: val,
                    pending: true,
                };
            }
            OptimizerValue::KnownValue { value, pending } => {
                if *value != val {
                    *value = val;
                    *pending = true;
                }
            }
        }
    }

    fn add_cell(&mut self, dst: isize, val: C) {
        if val != C::ZERO {
            match self
                .cell_values
                .entry(dst)
                .or_insert(OptimizerValue::KnownAddition {
                    value: C::ZERO,
                    pending: C::ZERO,
                }) {
                a @ OptimizerValue::UnknownValue => {
                    *a = OptimizerValue::UnknownAddition { pending: val };
                }
                OptimizerValue::KnownValue { value, pending } => {
                    *value = value.wrapping_add(val);
                    *pending = true;
                }
                OptimizerValue::KnownAddition { pending, .. }
                | OptimizerValue::UnknownAddition { pending } => {
                    *pending = pending.wrapping_add(val);
                }
            }
        }
    }

    fn add_mul_cell(&mut self, dst: isize, val: C, src: isize) {
        if val != C::ZERO {
            todo!();
        }
    }

    fn optimize_block(&mut self, block: Block<C>) -> Block<C> {
        let mut optimized = Block::new();
        for instr in block {
            match instr {
                Instr::Move(offset) => self.ptr += offset,
                Instr::Load(val, dst) => {
                    let dst = dst + self.ptr;
                    self.load_cell(dst, val);
                }
                Instr::Add(val, dst) => {
                    let dst = dst + self.ptr;
                    self.add_cell(dst, val);
                }
                Instr::MulAdd(val, src, dst) => {
                    let src = src + self.ptr;
                    let dst = dst + self.ptr;
                    self.add_mul_cell(dst, val, src);
                }
                Instr::Output(src) => {
                    let src = src + self.ptr;
                    self.emit(src, &mut optimized);
                    optimized.push(Instr::Output(src));
                }
                Instr::Input(dst) => {
                    let dst = dst + self.ptr;
                    optimized.push(Instr::Input(dst));
                    self.cell_values.insert(dst, OptimizerValue::UnknownValue);
                    self.written_cells.insert(dst);
                }
                Instr::Loop(cond, sub_block) => {
                    let cond = cond + self.ptr;
                    let mut sub_cxt = Self::new(self.ptr);
                    let mut sub_block = sub_cxt.optimize_block(sub_block);
                    let iters = self.compute_loop_count(cond, &sub_cxt);
                    if !iters.never() {
                        let ptr_shift = sub_cxt.ptr - self.ptr;
                        if ptr_shift != 0 || sub_cxt.had_shift {
                            sub_cxt.emit_all(&sub_cxt.pending(), &mut sub_block);
                            if ptr_shift != 0 {
                                sub_block.push(Instr::Move(ptr_shift));
                            }
                            self.emit_all(&self.pending(), &mut optimized);
                            optimized.push(Instr::Loop(cond, sub_block));
                            self.had_shift = true;
                            self.cell_values.clear();
                            self.read_cells.clear();
                            self.written_cells.clear();
                        } else {
                            sub_cxt.emit_all(&sub_cxt.read_and_pending(), &mut sub_block);
                            self.emit_all(&sub_cxt.read(), &mut optimized);
                            let mut to_add = Block::new();
                            if iters.at_most_once() {
                                if iters.at_least_once() {
                                    to_add.append(&mut sub_block);
                                    // TODO: update outer cell_values with adds and loads.
                                } else {
                                    // TODO: emit pending known adds into to_add
                                    to_add.append(&mut sub_block);
                                    sub_cxt.emit(cond, &mut to_add);
                                    // TODO: emit pending unknown adds into to_add
                                    // TODO: emit pending loads into to_add
                                    // TODO: update outer cell_values
                                }
                            } else {
                                // TODO: extract loop invariant loads
                                if iters.at_least_once() {
                                    // TODO: update outer cell_values with adds
                                } else {
                                    // TODO: emit pending known adds as mul_add into to_add
                                }
                                if !sub_block.is_empty() || !iters.is_finite() {
                                    sub_cxt.emit(cond, &mut sub_block);
                                    self.emit(cond, &mut optimized);
                                    to_add.push(Instr::Loop(cond, sub_block))
                                }
                                if iters.at_least_once() {
                                    // TODO: update outer cell_values with loads
                                } else {
                                    // TODO: emit pending unknown adds into to_add
                                    // TODO: emit pending loads into to_add
                                }
                                // TODO: update outer cell_values
                            }
                            if iters.at_least_once()
                                || to_add.is_empty()
                                || (to_add.len() == 1
                                    && if let Instr::Loop(cond, _) = to_add[0] {
                                        true
                                    } else {
                                        false
                                    })
                            {
                                optimized.append(&mut to_add);
                            } else {
                                self.emit(cond, &mut optimized);
                                optimized.push(Instr::Loop(cond, to_add));
                            }
                        }
                    }
                    self.load_cell(cond, C::ZERO);
                }
            }
        }
        return optimized;
    }
}

/// Optimize the Brainfuck program. It should be noted that the performed
/// optimizations are very much specific to this vm and use non-brainfuck
/// instructions. This is mainly a constant propagation pass.
pub fn optimize<C: CellType>(program: Block<C>) -> Block<C> {
    return OptimizerContext::new(0).optimize_block(program);
}

#[cfg(test)]
mod tests {
    use super::{parse, Error, ErrorKind, Instr};
    use Instr::*;

    #[test]
    fn parsing_valid_brainfuck_returns_block() -> Result<(), Error> {
        let prog = parse::<u8>("+++++[>[-],.<--]")?;
        assert_eq!(
            prog,
            vec![
                Add(5, 0),
                Loop(
                    0,
                    vec![
                        Move(1),
                        Loop(0, vec![Add(255, 0)]),
                        Input(0),
                        Output(0),
                        Move(-1),
                        Add(254, 0),
                    ]
                ),
            ]
        );
        Ok(())
    }

    #[test]
    fn parsing_with_missing_closing_returns_error() {
        let prog = parse::<u8>("+++++[>[-],.<--");
        assert_eq!(
            prog,
            Err(Error {
                kind: ErrorKind::LoopNotClosed,
                position: 5
            })
        );
    }

    #[test]
    fn parsing_with_missing_opening_return_error() {
        let prog = parse::<u8>("+++++>[-],.<]--");
        assert_eq!(
            prog,
            Err(Error {
                kind: ErrorKind::LoopNotOpened,
                position: 12
            })
        );
    }
}
