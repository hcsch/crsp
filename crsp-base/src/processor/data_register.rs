use std::{convert::TryFrom, iter::Step};

use num_enum::{IntoPrimitive, TryFromPrimitive, UnsafeFromPrimitive};
use static_assertions::const_assert;

use crate::nibble_ints::U4;

/// Data register of the CHIP-8 processor.
#[derive(
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    TryFromPrimitive,
    IntoPrimitive,
    UnsafeFromPrimitive,
)]
#[repr(u8)]
pub enum DataRegister {
    /// Used as the offset in [`Instruction::JumpOffset`].
    V0,
    V1,
    V2,
    V3,
    V4,
    V5,
    V6,
    V7,
    V8,
    V9,
    VA,
    VB,
    VC,
    VD,
    VE,
    /// Used for carry/borrow flags and set to the shifted-out bit after bit shifts.
    /// See [`Instruction::AddAssign`], [`Instruction::SubAssign`],
    /// [`Instruction::RevSubAssign`], [`Instruction::ShrAssign`]
    /// and [`Instruction::ShlAssign`].
    VF,
}

const_assert!(std::mem::variant_count::<DataRegister>() == U4::MAX.into_u8() as usize + 1);

impl From<DataRegister> for U4 {
    fn from(reg: DataRegister) -> Self {
        // SAFETY: DataRegister has exactly U4::MAX + 1 variants, i.e the discriminant fits in the low nibble.
        unsafe { U4::from_u8_unchecked(reg as u8) }
    }
}

impl From<U4> for DataRegister {
    fn from(val: U4) -> Self {
        // SAFETY: DataRegister has exactly U4::MAX + 1 variants.
        unsafe { DataRegister::from_unchecked(u8::from(val)) }
    }
}

impl Step for DataRegister {
    fn steps_between(start: &Self, end: &Self) -> Option<usize> {
        (*end as u8 as usize).checked_sub(*start as u8 as usize)
    }

    fn forward_checked(start: Self, count: usize) -> Option<Self> {
        u8::try_from(count)
            .ok()
            .and_then(|count| (start as u8).checked_add(count))
            .and_then(|i| Self::try_from(i).ok())
    }

    fn backward_checked(start: Self, count: usize) -> Option<Self> {
        u8::try_from(count)
            .ok()
            .and_then(|count| (start as u8).checked_sub(count))
            .and_then(|i| Self::try_from(i).ok())
    }
}
