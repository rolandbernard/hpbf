//! Contains parsing and some optimizing transformations for a Brainfuck program.

use std::{
    collections::HashMap,
    fmt::{self, Debug},
};

use crate::{CellType, Error, ErrorKind};

/// Represents a complete Brainfuck program.
#[derive(Clone, PartialEq)]
pub struct Program<C: CellType> {
    pub entry: usize,
    pub blocks: Vec<Block<C>>,
}

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
    Load { val: C, dst: isize },
    Add { val: C, dst: isize },
    MulAdd { val: C, src: isize, dst: isize },
    Loop { cond: isize, block: usize },
    If { cond: isize, block: usize },
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
    /// let prog = Program::<u8>::parse("+[-->-[>>+>-----<<]<--<---]>-.>>>+.>>..+++[.>]<<<<.+++.------.<<-.>>>>+.")?;
    /// assert_eq!(prog,
    ///     Program {
    ///         entry: 3,
    ///         blocks: vec![
    ///             Block { shift: 1, insts: vec![
    ///                 Add { val: 1, dst: 2 }, Add { val: 251, dst: 3 }
    ///             ]},
    ///             Block { shift: -1, insts: vec![
    ///                 Add { val: 254, dst: 0 }, Add { val: 255, dst: 1 },
    ///                 Loop { cond: 1, block: 0 }, Add { val: 253, dst: -1 },
    ///                 Add { val: 254, dst: 0 }
    ///             ]},
    ///             Block { shift: 1, insts: vec![Output { src: 0 }]},
    ///             Block { shift: 4, insts: vec![
    ///                 Add { val: 1, dst: 0 }, Loop { cond: 0, block: 1 },
    ///                 Add { val: 255, dst: 1 }, Output { src: 1 },
    ///                 Add { val: 1, dst: 4 }, Output { src: 4 }, Output { src: 6 },
    ///                 Output { src: 6 }, Add { val: 3, dst: 6 },
    ///                 Loop { cond: 6, block: 2 }, Output { src: 2 },
    ///                 Add { val: 3, dst: 2 }, Output { src: 2 },
    ///                 Add { val: 250, dst: 2 }, Output { src: 2 },
    ///                 Add { val: 255, dst: 0 }, Output { src: 0 },
    ///                 Add { val: 1, dst: 4 }, Output { src: 4 },
    ///             ]},
    ///         ]
    ///     }
    /// );
    /// # Ok::<(), Error>(())
    /// ```
    pub fn parse<'str>(program: &'str str) -> Result<Self, Error<'str>> {
        let mut blocks = HashMap::new();
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
                        insts.push(Instr::Add {
                            val: *val,
                            dst: *shift,
                        });
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
                    stack.push((0, false, Vec::new(), HashMap::new()));
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
                            sub_insts.push(Instr::Add { val, dst: var });
                        }
                    }
                    let (shift, moved, insts, buff) = stack.last_mut().unwrap();
                    if sub_insts.len() == 1
                        && matches!(sub_insts[0], Instr::Add{val:c, dst:0} if c.is_odd())
                    {
                        insts.push(Instr::Load {
                            val: C::ZERO,
                            dst: *shift,
                        });
                        buff.insert(*shift, C::ZERO);
                    } else {
                        let block_id = blocks.len();
                        let block_id = *blocks
                            .entry(Block {
                                shift: sub_shift,
                                insts: sub_insts,
                            })
                            .or_insert(block_id);
                        for (var, _) in vars {
                            let v = buff.entry(*shift + var).or_insert(C::ZERO);
                            if *v != C::ZERO {
                                insts.push(Instr::Add {
                                    val: *v,
                                    dst: *shift + var,
                                });
                                *v = C::ZERO;
                            }
                        }
                        if sub_moved || sub_shift != 0 {
                            let mut vars = buff.iter_mut().collect::<Vec<_>>();
                            vars.sort();
                            for (var, val) in vars {
                                if *val != C::ZERO {
                                    insts.push(Instr::Add {
                                        val: *val,
                                        dst: *var,
                                    });
                                    *val = C::ZERO;
                                }
                            }
                            *moved = true;
                        }
                        let val = buff.entry(*shift).or_insert(C::ZERO);
                        if *val != C::ZERO {
                            insts.push(Instr::Add {
                                val: *val,
                                dst: *shift,
                            });
                            *val = C::ZERO;
                        }
                        insts.push(Instr::Loop {
                            cond: *shift,
                            block: block_id,
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
                insts.push(Instr::Add { val, dst: var });
            }
        }
        let block_id = blocks.len();
        blocks.insert(Block { shift, insts }, block_id);
        let mut program = Program {
            entry: block_id,
            blocks: vec![
                Block {
                    shift: 0,
                    insts: Vec::new()
                };
                blocks.len()
            ],
        };
        for (block, idx) in blocks {
            program.blocks[idx] = block;
        }
        return Ok(program);
    }
}

impl<C: CellType> Program<C> {
    /// Pretty print the block with the given `block_id` and indented by `indent`
    /// spaces into the formatter `f`. Referenced blocks are printed recursively.
    fn print_block(
        &self,
        f: &mut fmt::Formatter<'_>,
        block_id: usize,
        indent: usize,
    ) -> fmt::Result {
        let block = &self.blocks[block_id];
        for instr in &block.insts {
            match instr {
                Instr::Output { src } => {
                    writeln!(f, "{:indent$}output [{}]", "", src, indent = indent)?;
                }
                Instr::Input { dst } => {
                    writeln!(f, "{:indent$}input [{}]", "", dst, indent = indent)?;
                }
                Instr::Load { val, dst } => {
                    writeln!(f, "{:indent$}[{}] = {:?}", "", dst, val, indent = indent)?;
                }
                Instr::Add { val, dst } => {
                    writeln!(f, "{:indent$}[{}] += {:?}", "", dst, val, indent = indent)?;
                }
                Instr::MulAdd { val, src, dst } => {
                    writeln!(
                        f,
                        "{:indent$}[{}] += {:?} * [{}]",
                        "",
                        dst,
                        val,
                        src,
                        indent = indent
                    )?;
                }
                Instr::Loop { cond, block } => {
                    writeln!(f, "{:indent$}loop [{}] [", "", cond, indent = indent)?;
                    self.print_block(f, *block, indent + 2)?;
                    writeln!(f, "{:indent$}]", "", indent = indent)?;
                }
                Instr::If { cond, block } => {
                    writeln!(f, "{:indent$}if [{}] [", "", cond, indent = indent)?;
                    self.print_block(f, *block, indent + 2)?;
                    writeln!(f, "{:indent$}]", "", indent = indent)?;
                }
            }
        }
        if block.shift != 0 {
            writeln!(f, "{:indent$}move {}", "", block.shift, indent = indent)?;
        }
        Ok(())
    }
}

impl<C: CellType> Debug for Program<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.print_block(f, self.entry, 0)
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
                entry: 1,
                blocks: vec![
                    Block {
                        shift: 0,
                        insts: vec![
                            Load { val: 0, dst: 1 },
                            Input { dst: 1 },
                            Output { src: 1 },
                            Add { val: 254, dst: 0 }
                        ]
                    },
                    Block {
                        shift: 0,
                        insts: vec![Add { val: 5, dst: 0 }, Loop { cond: 0, block: 0 }]
                    },
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
