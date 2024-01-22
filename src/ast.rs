//! Contains parsing and optimizing transformations for a Brainfuck program.

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
