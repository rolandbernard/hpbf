pub mod ast;
pub mod codegen;
pub mod runtime;

pub use ast::{parse, Block, Instr};
pub use runtime::Context;

/// Kind of error that might be encountered during the parsing of a Brainfuck
/// program or other operations preventing execution.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum ErrorKind {
    LoopNotClosed,
    LoopNotOpened,
    FileReadFailed,
    FileEncodingError,
}

/// Error that might be encountered during the parsing of a Brainfuck program.
/// Contains the index of the character that caused the error.
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub position: usize,
}
