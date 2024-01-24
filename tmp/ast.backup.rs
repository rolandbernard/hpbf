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

struct OptimizerContext<C: CellType> {
    ptr: isize,
    adds: HashMap<isize, C>,
    values: HashMap<isize, C>,
    pending_adds: HashMap<isize, C>,
    pending_loads: HashMap<isize, C>,
    modified: HashMap<isize, usize>,
    written: HashSet<isize>,
    read: HashSet<isize>,
}

impl<C: CellType> OptimizerContext<C> {
    fn new(ptr: isize) -> Self {
        OptimizerContext::<C> {
            ptr,
            adds: HashMap::new(),
            values: HashMap::new(),
            pending_adds: HashMap::new(),
            pending_loads: HashMap::new(),
            modified: HashMap::new(),
            read: HashSet::new(),
            written: HashSet::new(),
        }
    }

    fn setup_for_read(&mut self, src: isize, block: &mut Block<C>) {
        if let Some(&v) = self.pending_loads.get(&src) {
            block.push(Instr::Load(v, src));
            self.written.insert(src);
            self.pending_loads.remove(&src);
            *self.modified.entry(src).or_insert(0) += 1;
        } else if let Some(&v) = self.pending_adds.get(&src) {
            block.push(Instr::Add(v, src));
            self.pending_adds.remove(&src);
            *self.modified.entry(src).or_insert(0) += 1;
        }
        if !self.written.contains(&src) {
            self.read.insert(src);
        }
    }

    fn finalize_loop(&mut self, known_iters: bool, block: &mut Block<C>) {
        let mut to_finalize = Vec::new();
        for dst in self.pending_adds.keys() {
            if !known_iters || self.read.contains(dst) {
                to_finalize.push(*dst);
            }
        }
        for dst in self.pending_loads.keys() {
            if self.read.contains(dst) {
                to_finalize.push(*dst);
            }
        }
        for dst in to_finalize {
            self.setup_for_read(dst, block);
        }
    }

    fn extract_invariant_loads(&self, src: &mut Block<C>, target: &mut Block<C>) {
        todo!();
    }

    fn optimize_block(&mut self, block: Block<C>) -> Block<C> {
        let mut optimized = Block::new();
        for instr in block {
            match instr {
                Instr::Move(offset) => self.ptr += offset,
                Instr::Load(val, dst) => {
                    let dst = dst + self.ptr;
                    if self.values.get(&dst) != Some(&val) {
                        self.adds.remove(&dst);
                        self.pending_adds.remove(&dst);
                        self.values.insert(dst, val);
                        self.pending_loads.insert(dst, val);
                    }
                }
                Instr::Add(val, dst) => {
                    if val != C::ZERO {
                        let dst = dst + self.ptr;
                        if let Some(v) = self.values.get_mut(&dst) {
                            *v = v.wrapping_add(val);
                            self.pending_loads.insert(dst, *v);
                        } else {
                            if !self.written.contains(&dst) {
                                self.adds
                                    .entry(dst)
                                    .and_modify(|v| *v = v.wrapping_add(val))
                                    .or_insert(val);
                            }
                            self.pending_adds
                                .entry(dst)
                                .and_modify(|v| *v = v.wrapping_add(val))
                                .or_insert(val);
                        }
                    }
                }
                Instr::MulAdd(val, src, dst) => {
                    if val != C::ZERO {
                        let src = src + self.ptr;
                        let dst = dst + self.ptr;
                        todo!();
                    }
                }
                Instr::Output(src) => {
                    let src = src + self.ptr;
                    self.setup_for_read(src, &mut optimized);
                    optimized.push(Instr::Output(src));
                }
                Instr::Input(dst) => {
                    let dst = dst + self.ptr;
                    self.pending_adds.remove(&dst);
                    self.pending_loads.remove(&dst);
                    self.values.remove(&dst);
                    optimized.push(Instr::Input(dst));
                    self.written.insert(dst);
                }
                Instr::Loop(cond, sub_block) => {
                    let cond = cond + self.ptr;
                    if let Some(&v) = self.values.get(&cond) {
                        if v == C::ZERO {
                            // We know that this loop will never be run. Therefore we completely skip it.
                        } else {
                            let mut sub_cxt = Self::new(self.ptr);
                            let mut sub_block = sub_cxt.optimize_block(sub_block);
                            sub_cxt.finalize_loop(true, &mut sub_block);
                            if sub_block.is_empty() && iters != 0 {
                                self.pending_loads.insert(cond, 0);
                                self.values.insert(cond, 0);
                            } else {
                                sub_cxt.setup_for_read(cond, &mut sub_block);
                                self.setup_for_read(cond, &mut optimized);
                                
                            }
                        }
                    } else {
                        let mut sub_cxt = Self::new(self.ptr);
                        let mut sub_block = sub_cxt.optimize_block(sub_block);
                        let mut known_iters = false;
                        if sub_cxt.adds.get(&cond) == Some(&C::NEG_ONE) {
                            known_iters = true;
                        }
                        sub_cxt.finalize_loop(known_iters, &mut sub_block);
                        // TODO: do we need to setup for read?
                        self.setup_for_read(cond, &mut optimized);
                    }
                    self.values.insert(cond, C::ZERO);
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
