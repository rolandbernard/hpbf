//! Contains parsing and optimizing transformations for a Brainfuck program.

use std::collections::HashMap;

use crate::{CellType, Error, ErrorKind};

/// Represents a complete Brainfuck program.
#[derive(Clone, PartialEq, Debug)]
pub struct Program<C: CellType>(pub usize, pub Vec<Block<C>>);

/// Represents the inside of a loop.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Block<C: CellType>(pub isize, pub Vec<Instr<C>>);

/// This represents a Brainfuck instruction. It includes not only the basic
/// Brainfuck instructions, but also some additional operations that are common
/// in Brainfuck and help the backend to generate better code.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Instr<C: CellType> {
    Output(isize),
    Input(isize),
    Load(C, isize),
    Add(C, isize),
    MulAdd(C, isize, isize),
    Loop(isize, usize),
    If(isize, usize),
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
    ///
    /// let prog = Program::<u8>::parse("+[-->-[>>+>-----<<]<--<---]>-.>>>+.>>..+++[.>]<<<<.+++.------.<<-.>>>>+.")?;
    ///
    /// assert_eq!(prog,
    ///     Program(
    ///         3,
    ///         vec![
    ///             Block(1, vec![Add(1, 2), Add(251, 3)]),
    ///             Block(-1, vec![Add(254, 0), Add(255, 1), Loop(1, 0), Add(253, -1), Add(254, 0)]),
    ///             Block(1, vec![Output(0)]),
    ///             Block(4, vec![
    ///                 Add(1, 0), Loop(0, 1), Add(255, 1), Output(1), Add(1, 4), Output(4), Output(6),
    ///                 Output(6), Add(3, 6), Loop(6, 2), Output(2), Add(3, 2), Output(2), Add(250, 2),
    ///                 Output(2), Add(255, 0), Output(0), Add(1, 4), Output(4)
    ///             ]),
    ///         ]
    ///     )
    /// );
    /// # Ok::<(), Error>(())
    /// ```
    pub fn parse(program: impl AsRef<str>) -> Result<Self, Error> {
        let mut blocks = HashMap::new();
        let mut stack = vec![(0, Vec::new(), HashMap::new())];
        let mut positions = vec![];
        for (i, char) in program.as_ref().chars().enumerate() {
            let top = stack.last_mut().unwrap();
            match char {
                '>' => {
                    top.0 += 1;
                }
                '<' => {
                    top.0 -= 1;
                }
                '+' => {
                    let val = top.2.entry(top.0).or_insert(C::ZERO);
                    *val = val.wrapping_add(C::ONE);
                }
                '-' => {
                    let val = top.2.entry(top.0).or_insert(C::ZERO);
                    *val = val.wrapping_add(C::NEG_ONE);
                }
                '.' => {
                    if let Some(v) = top.2.get_mut(&top.0) {
                        if *v != C::ZERO {
                            top.1.push(Instr::Add(*v, top.0));
                            *v = C::ZERO;
                        }
                    }
                    top.1.push(Instr::Output(top.0));
                }
                ',' => {
                    top.1.push(Instr::Input(top.0));
                    top.2.remove(&top.0);
                }
                '[' => {
                    positions.push(i);
                    stack.push((0, Vec::new(), HashMap::new()));
                }
                ']' => {
                    if positions.len() == 0 {
                        return Err(Error {
                            kind: ErrorKind::LoopNotOpened,
                            position: i,
                        });
                    }
                    positions.pop();
                    let (offset, mut insts, vars) = stack.pop().unwrap();
                    let mut vars = vars.into_iter().collect::<Vec<_>>();
                    vars.sort();
                    for &(var, val) in &vars {
                        if val != C::ZERO {
                            insts.push(Instr::Add(val, var));
                        }
                    }
                    let top = stack.last_mut().unwrap();
                    if insts.len() == 1 && matches!(insts[0], Instr::Add(c, 0) if c.is_odd()) {
                        top.1.push(Instr::Load(C::ZERO, top.0));
                        top.2.remove(&top.0);
                    } else {
                        let block_id = blocks.len();
                        let block_id = *blocks.entry(Block(offset, insts)).or_insert(block_id);
                        if offset == 0 {
                            for (var, _) in vars {
                                if let Some(v) = top.2.get_mut(&(top.0 + var)) {
                                    if *v != C::ZERO {
                                        top.1.push(Instr::Add(*v, top.0 + var));
                                        *v = C::ZERO;
                                    }
                                }
                            }
                        } else {
                            let mut vars = top.2.iter_mut().collect::<Vec<_>>();
                            vars.sort();
                            for (var, val) in vars {
                                if *val != C::ZERO {
                                    top.1.push(Instr::Add(*val, *var));
                                    *val = C::ZERO;
                                }
                            }
                        }
                        top.1.push(Instr::Loop(top.0, block_id));
                    }
                }
                _ => { /* comment */ }
            }
        }
        if stack.len() != 1 {
            return Err(Error {
                kind: ErrorKind::LoopNotClosed,
                position: *positions.last().unwrap(),
            });
        }
        let (offset, mut insts, vars) = stack.pop().unwrap();
        let mut vars = vars.into_iter().collect::<Vec<_>>();
        vars.sort();
        for (var, val) in vars {
            if val != C::ZERO {
                insts.push(Instr::Add(val, var));
            }
        }
        let block_id = blocks.len();
        blocks.insert(Block(offset, insts), block_id);
        let mut program = Program(block_id, vec![Block(0, Vec::new()); blocks.len()]);
        for (block, idx) in blocks {
            program.1[idx] = block;
        }
        return Ok(program);
    }
}

#[cfg(test)]
mod tests {
    use crate::{Block, Error, ErrorKind, Instr, Program};
    use Instr::*;

    #[test]
    fn parsing_valid_brainfuck_returns_block() -> Result<(), Error> {
        let prog = Program::<u8>::parse("+++++[>[-],.<--]")?;
        assert_eq!(
            prog,
            Program(
                1,
                vec![
                    Block(0, vec![Load(0, 1), Input(1), Output(1), Add(254, 0)]),
                    Block(0, vec![Add(5, 0), Loop(0, 0)])
                ]
            )
        );
        Ok(())
    }

    #[test]
    fn parsing_with_missing_closing_returns_error() {
        let prog = Program::<u8>::parse("+++++[>[-],.<--");
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
        let prog = Program::<u8>::parse("+++++>[-],.<]--");
        assert_eq!(
            prog,
            Err(Error {
                kind: ErrorKind::LoopNotOpened,
                position: 12
            })
        );
    }
}
