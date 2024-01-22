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

/// Only types implementing this trait are allowed for the cells.
pub trait CellType: Copy + PartialEq {
    /// Number of bits of this type. Needed for code generation.
    const BITS: usize;

    const ZERO: Self;
    const ONE: Self;
    const NEG_ONE: Self;

    /// Convert an input byte into a cell value.
    fn from_u8(val: u8) -> Self;

    /// Convert a cell value into an output byte.
    fn into_u8(self) -> u8;

    /// Wrapping addition.
    fn wrapping_add(self, rhs: Self) -> Self;

    /// Wrapping multiplication.
    fn wrapping_mul(self, rhs: Self) -> Self;
}

impl CellType for u8 {
    const BITS: usize = 8;

    const ZERO: Self = 0;
    const ONE: Self = 1;
    const NEG_ONE: Self = u8::MAX;

    fn from_u8(val: u8) -> Self {
        val
    }

    fn into_u8(self) -> u8 {
        self
    }

    fn wrapping_add(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }

    fn wrapping_mul(self, rhs: Self) -> Self {
        self.wrapping_mul(rhs)
    }
}

impl CellType for u16 {
    const BITS: usize = 16;

    const ZERO: Self = 0;
    const ONE: Self = 1;
    const NEG_ONE: Self = u16::MAX;

    fn from_u8(val: u8) -> Self {
        val as u16
    }

    fn into_u8(self) -> u8 {
        self as u8
    }

    fn wrapping_add(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }

    fn wrapping_mul(self, rhs: Self) -> Self {
        self.wrapping_mul(rhs)
    }
}

impl CellType for u32 {
    const BITS: usize = 32;

    const ZERO: Self = 0;
    const ONE: Self = 1;
    const NEG_ONE: Self = u32::MAX;

    fn from_u8(val: u8) -> Self {
        val as u32
    }

    fn into_u8(self) -> u8 {
        self as u8
    }

    fn wrapping_add(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }

    fn wrapping_mul(self, rhs: Self) -> Self {
        self.wrapping_mul(rhs)
    }
}

impl CellType for u64 {
    const BITS: usize = 64;

    const ZERO: Self = 0;
    const ONE: Self = 1;
    const NEG_ONE: Self = u64::MAX;

    fn from_u8(val: u8) -> Self {
        val as u64
    }

    fn into_u8(self) -> u8 {
        self as u8
    }

    fn wrapping_add(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }

    fn wrapping_mul(self, rhs: Self) -> Self {
        self.wrapping_mul(rhs)
    }
}

