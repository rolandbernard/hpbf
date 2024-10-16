//! Library for executing Brainfuck programs.

mod hasher;
mod smallvec;

pub mod bc;
pub mod exec;
pub mod ir;
pub mod opt;
pub mod runtime;

use std::{fmt::Debug, hash::Hash};

/// Kind of error that might be encountered during the parsing of a Brainfuck
/// program or other operations preventing execution.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum ErrorKind {
    LoopNotClosed,
    LoopNotOpened,
    FileReadFailed,
    FileEncodingError,
    LlvmError,
}

/// Error that might be encountered during the parsing of a Brainfuck program.
/// Contains the index of the character that caused the error.
#[derive(Clone, PartialEq, Debug)]
pub struct Error {
    pub kind: ErrorKind,
    pub str: String,
    pub position: usize,
}

/// Only types implementing this trait are allowed for the cells. It is
/// implemented in this library for [`u8`], [`u16`], [`u32`], and [`u64`].
pub trait CellType: Copy + Ord + Hash + Debug + 'static {
    /// Number of bits of this type. Needed for code generation.
    const BITS: u32;

    const ZERO: Self;
    const ONE: Self;
    const NEG_ONE: Self;

    /// Convert a cell value into an unsigned 64 bit value. Zero extend.
    fn into_u64(self) -> u64;

    /// Convert a cell value into an signed 64 bit value. Sign extend.
    fn into_i64(self) -> i64;

    /// Convert from an unsigned 64 bit value to a cell value.
    fn from_u64(val: u64) -> Self;

    /// Wrapping addition.
    fn wrapping_add(self, rhs: Self) -> Self;

    /// Wrapping multiplication.
    fn wrapping_mul(self, rhs: Self) -> Self;

    /// Return the value `x` such that `x.wrapping_add(self) == Self::ZERO`.
    fn wrapping_neg(self) -> Self;

    /// Bitwise and operation.
    fn bitand(self, rhs: Self) -> Self;

    /// Shift to the right. If the bit width of the type is exceeded return 0.
    fn wrapping_shr(self, by: u32) -> Self;

    /// Shift to the left. If the bit width of the type is exceeded return 0.
    fn wrapping_shl(self, by: u32) -> Self;

    /// Returns the number of trailing zeros.
    fn trailing_zeros(self) -> u32;

    /// Return true if the value is odd.
    fn is_odd(self) -> bool {
        self.bitand(Self::ONE) == Self::ONE
    }

    /// Wrapping exponentiation.
    fn wrapping_pow(mut self, mut exp: Self) -> Self {
        let mut result = Self::ONE;
        while exp != Self::ZERO {
            if exp.is_odd() {
                result = result.wrapping_mul(self);
            }
            self = self.wrapping_mul(self);
            exp = exp.wrapping_shr(1);
        }
        result
    }

    /// Compute the multiplicative inverse of `self`. Unlike [`Self::wrapping_div`],
    /// this never works when `self` is even.
    ///
    /// # Examples
    /// ```
    /// # use hpbf::CellType;
    /// assert_eq!(<u8 as CellType>::wrapping_inv(5), Some(205));
    /// assert_eq!(<u8 as CellType>::wrapping_inv(1), Some(1));
    /// assert_eq!(<u8 as CellType>::wrapping_inv(7), Some(183));
    /// assert_eq!(<u8 as CellType>::wrapping_inv(2), None);
    /// assert_eq!(<u8 as CellType>::wrapping_inv(4), None);
    /// assert_eq!(<u8 as CellType>::wrapping_inv(64), None);
    /// ```
    fn wrapping_inv(self) -> Option<Self> {
        if self.is_odd() {
            let tot = Self::ONE.wrapping_shl(Self::BITS - 1);
            let inv = self.wrapping_pow(tot.wrapping_add(Self::NEG_ONE));
            Some(inv)
        } else {
            None
        }
    }

    /// Compute the smallest value `x` such that `x.wrapping_mul(other) == self`.
    /// It should be noted that the semantics of this are very different from
    /// the standard `wrapping_div` that Rust provides for integer types.
    ///
    /// # Examples
    /// ```
    /// # use hpbf::CellType;
    /// assert_eq!(<u8 as CellType>::wrapping_div(5, 5), Some(1));
    /// assert_eq!(<u8 as CellType>::wrapping_div(5, 1), Some(5));
    /// assert_eq!(<u8 as CellType>::wrapping_div(5, 2), None);
    /// assert_eq!(<u8 as CellType>::wrapping_div(8, 7), Some(184));
    /// assert_eq!(<u8 as CellType>::wrapping_div(32, 4), Some(8));
    /// assert_eq!(<u8 as CellType>::wrapping_div(32, 64), None);
    /// ```
    fn wrapping_div(self, div: Self) -> Option<Self> {
        let shift = div.trailing_zeros();
        if self == Self::ZERO {
            Some(Self::ZERO)
        } else if shift > self.trailing_zeros() {
            None
        } else {
            let div = div.wrapping_shr(shift);
            let tot = Self::ONE.wrapping_shl(Self::BITS - shift - 1);
            let inv = div.wrapping_pow(tot.wrapping_add(Self::NEG_ONE));
            let result = inv.wrapping_mul(self.wrapping_shr(shift));
            Some(
                result.bitand(
                    Self::ONE
                        .wrapping_shl(Self::BITS - shift)
                        .wrapping_add(Self::NEG_ONE),
                ),
            )
        }
    }

    /// Convert an input byte into a cell value.
    fn from_u8(val: u8) -> Self {
        Self::from_u64(val as u64)
    }

    /// Convert a cell value into an output byte.
    fn into_u8(self) -> u8 {
        self.into_u64() as u8
    }

    /// Convert a signed 16 bit integer into a cell value.
    fn from_i16(val: i16) -> Self {
        Self::from_u64(val as i64 as u64)
    }

    /// Convert a cell value into a signed 16 bit integer, if possible.
    fn try_into_i16(self) -> Option<i16> {
        self.into_i64().try_into().ok()
    }
}

impl CellType for u8 {
    const BITS: u32 = 8;

    const ZERO: Self = 0;
    const ONE: Self = 1;
    const NEG_ONE: Self = u8::MAX;

    fn into_u64(self) -> u64 {
        self as u64
    }

    fn from_u64(val: u64) -> Self {
        val as u8
    }

    fn into_i64(self) -> i64 {
        self as i8 as i64
    }

    fn wrapping_add(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }

    fn wrapping_mul(self, rhs: Self) -> Self {
        self.wrapping_mul(rhs)
    }

    fn wrapping_neg(self) -> Self {
        self.wrapping_neg()
    }

    fn bitand(self, rhs: Self) -> Self {
        self & rhs
    }

    fn wrapping_shr(self, by: u32) -> Self {
        self.checked_shr(by).unwrap_or(0)
    }

    fn wrapping_shl(self, by: u32) -> Self {
        self.checked_shl(by).unwrap_or(0)
    }

    fn trailing_zeros(self) -> u32 {
        self.trailing_zeros()
    }
}

impl CellType for u16 {
    const BITS: u32 = 16;

    const ZERO: Self = 0;
    const ONE: Self = 1;
    const NEG_ONE: Self = u16::MAX;

    fn into_u64(self) -> u64 {
        self as u64
    }

    fn from_u64(val: u64) -> Self {
        val as u16
    }

    fn into_i64(self) -> i64 {
        self as i16 as i64
    }

    fn wrapping_add(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }

    fn wrapping_mul(self, rhs: Self) -> Self {
        self.wrapping_mul(rhs)
    }

    fn wrapping_neg(self) -> Self {
        self.wrapping_neg()
    }

    fn bitand(self, rhs: Self) -> Self {
        self & rhs
    }

    fn wrapping_shr(self, by: u32) -> Self {
        self.checked_shr(by).unwrap_or(0)
    }

    fn wrapping_shl(self, by: u32) -> Self {
        self.checked_shl(by).unwrap_or(0)
    }

    fn trailing_zeros(self) -> u32 {
        self.trailing_zeros()
    }
}

impl CellType for u32 {
    const BITS: u32 = 32;

    const ZERO: Self = 0;
    const ONE: Self = 1;
    const NEG_ONE: Self = u32::MAX;

    fn into_u64(self) -> u64 {
        self as u64
    }

    fn from_u64(val: u64) -> Self {
        val as u32
    }

    fn into_i64(self) -> i64 {
        self as i32 as i64
    }

    fn wrapping_add(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }

    fn wrapping_mul(self, rhs: Self) -> Self {
        self.wrapping_mul(rhs)
    }

    fn wrapping_neg(self) -> Self {
        self.wrapping_neg()
    }

    fn bitand(self, rhs: Self) -> Self {
        self & rhs
    }

    fn wrapping_shr(self, by: u32) -> Self {
        self.checked_shr(by).unwrap_or(0)
    }

    fn wrapping_shl(self, by: u32) -> Self {
        self.checked_shl(by).unwrap_or(0)
    }

    fn trailing_zeros(self) -> u32 {
        self.trailing_zeros()
    }
}

impl CellType for u64 {
    const BITS: u32 = 64;

    const ZERO: Self = 0;
    const ONE: Self = 1;
    const NEG_ONE: Self = u64::MAX;

    fn into_u64(self) -> u64 {
        self
    }

    fn from_u64(val: u64) -> Self {
        val
    }

    fn into_i64(self) -> i64 {
        self as i64
    }

    fn wrapping_add(self, rhs: Self) -> Self {
        self.wrapping_add(rhs)
    }

    fn wrapping_mul(self, rhs: Self) -> Self {
        self.wrapping_mul(rhs)
    }

    fn wrapping_neg(self) -> Self {
        self.wrapping_neg()
    }

    fn bitand(self, rhs: Self) -> Self {
        self & rhs
    }

    fn wrapping_shr(self, by: u32) -> Self {
        self.checked_shr(by).unwrap_or(0)
    }

    fn wrapping_shl(self, by: u32) -> Self {
        self.checked_shl(by).unwrap_or(0)
    }

    fn trailing_zeros(self) -> u32 {
        self.trailing_zeros()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::CellType;

    #[test]
    #[cfg_attr(miri, ignore)]
    fn wrapping_div_is_smallest() {
        for div in 0..=255 {
            let mut inv = HashMap::new();
            for x in 0..=255 {
                inv.entry(x.wrapping_mul(div)).or_insert(x);
            }
            for num in 0..=255 {
                if let Some(x) = <u8 as CellType>::wrapping_div(num, div) {
                    assert_eq!(x.wrapping_mul(div), num);
                    assert_eq!(inv.get(&num), Some(&x));
                } else {
                    assert!(!inv.contains_key(&num));
                }
            }
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn wrapping_div_is_smallest_u16() {
        for div in (0..=u16::MAX)
            .step_by(7919)
            .flat_map(|i| [i, i + 1].into_iter())
        {
            let mut inv = HashMap::new();
            for x in 0..=u16::MAX {
                inv.entry(x.wrapping_mul(div)).or_insert(x);
            }
            for num in 0..=u16::MAX {
                if let Some(x) = <u16 as CellType>::wrapping_div(num, div) {
                    assert_eq!(x.wrapping_mul(div), num);
                    assert_eq!(inv.get(&num), Some(&x));
                } else {
                    assert!(!inv.contains_key(&num));
                }
            }
        }
    }
}
