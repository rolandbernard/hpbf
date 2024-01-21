/// Represents a complete Brainfuck program or inside of a loop.
pub type Block = Vec<Instr>;

/// This represents a Brainfuck instruction. It includes not only the basic
/// Brainfuck instructions, but also some additional operations that are common
/// in Brainfuck and help the backend to generate better code.
#[derive(Clone, PartialEq, Debug)]
pub enum Instr {
    // Basic instructions of Brainfuck:
    Inp,
    Out,
    Inc(u8),
    Move(isize),
    Loop(Block),
    // Non-local instructions used for optimization:
    Load(u8, isize),
    Add(u8, isize),
    MulAdd(u8, isize, isize),
    Output(isize),
    Input(isize),
    While(isize, Block),
}

/// Kind of error that might be encountered during the parsing of a Brainfuck
/// program.
#[derive(Debug)]
pub enum ErrorKind {
    LoopNotClosed,
    LoopNotOpened,
}

/// Error that might be encountered during the parsing of a Brainfuck program.
/// Contains the index of the character that caused the error.
#[derive(Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub position: usize,
}

/// Parses a string containing a Brainfuck program into an internal
/// representation. This will already cluster sequential increment, decrement,
/// and movement instructions.
/// 
/// # Examples
/// ```
/// # use hpbf::ast::{parse, Error, Instr};
/// use Instr::*;
/// 
/// let prog = parse("+[-->-[>>+>-----<<]<--<---]>-.>>>+.>>..+++[.>]<<<<.+++.------.<<-.>>>>+.")?;
/// 
/// assert_eq!(prog, vec![
///     Inc(1),
///     Loop(vec![
///         Inc(254), Move(1), Inc(255),
///         Loop(vec![Move(2), Inc(1), Move(1), Inc(251), Move(-2)]),
///         Move(-1), Inc(254), Move(-1), Inc(253),
///     ]),
///     Move(1), Inc(255), Out, Move(3), Inc(1), Out, Move(2), Out, Out, Inc(3),
///     Loop(vec![Out, Move(1)]),
///     Move(-4), Out, Inc(3), Out, Inc(250), Out,
///     Move(-2), Inc(255), Out, Move(4), Inc(1), Out,
/// ]);
/// # Ok::<(), Error>(())
/// ```
pub fn parse(program: &str) -> Result<Block, Error> {
    let mut blocks = vec![Block::new()];
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
                if let Some(Instr::Inc(i)) = block.last_mut() {
                    *i = i.wrapping_add(1);
                } else {
                    block.push(Instr::Inc(1));
                }
            }
            '-' => {
                if let Some(Instr::Inc(i)) = block.last_mut() {
                    *i = i.wrapping_sub(1);
                } else {
                    block.push(Instr::Inc(255));
                }
            }
            '.' => {
                block.push(Instr::Out);
            }
            ',' => {
                block.push(Instr::Inp);
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
                    let instr = Instr::Loop(blocks.pop().unwrap());
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
