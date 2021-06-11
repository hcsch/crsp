use std::convert::TryFrom;

use derive_more::*;
use thiserror::Error;

#[derive(Debug, PartialEq, Eq, Error)]
#[error("value {value} exceeds the maximum value {max_value}")]
pub struct UpperBoundExceededError {
    value: usize,
    max_value: usize,
}

/// A minimal implementation of a 4-bit integer.
/// Supports only the operations needed in this crate.
/// Need not actually use only 4-bits in memory.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, AsRef, Into, Display)]
#[repr(transparent)]
pub struct U4(u8);

#[derive(Debug)]
#[repr(u8)]
pub enum U8Nibble {
    Lo = 0,
    Hi = 1,
}

impl U4 {
    pub const MIN: Self = Self(0);
    pub const MAX: Self = Self(0b1111);

    pub const fn into_u8(self) -> u8 {
        self.0
    }

    pub const fn from_u8(val: u8, nibble: U8Nibble) -> Self {
        U4((val >> (4 * (nibble as u8))) & 0b1111)
    }

    pub const unsafe fn from_u8_unchecked(val: u8) -> Self {
        U4(val)
    }
}

impl TryFrom<u8> for U4 {
    type Error = UpperBoundExceededError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value <= U4::MAX.into() {
            Ok(U4(value))
        } else {
            Err(UpperBoundExceededError {
                value: value as usize,
                max_value: u8::from(U4::MAX) as usize,
            })
        }
    }
}

/// A minimal implementation of a 12-bit integer.
/// Supports only the operations needed in this crate.
/// Need not actually use only 12-bits in memory.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, AsRef, Into, Display)]
#[repr(transparent)]
pub struct U12(u16);

impl U12 {
    pub const MIN: Self = Self(0);
    pub const MAX: Self = Self(0b1111_1111_1111);

    // const into for u16
    pub const fn into_u16(self) -> u16 {
        self.0
    }

    pub const unsafe fn from_u16_unchecked(val: u16) -> Self {
        U12(val)
    }
}

impl TryFrom<u16> for U12 {
    type Error = UpperBoundExceededError;

    fn try_from(value: u16) -> Result<Self, Self::Error> {
        if value <= U12::MAX.into() {
            Ok(U12(value))
        } else {
            Err(UpperBoundExceededError {
                value: value as usize,
                max_value: u16::from(U12::MAX) as usize,
            })
        }
    }
}
