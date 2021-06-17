use num_enum::{IntoPrimitive, TryFromPrimitive, UnsafeFromPrimitive};
use static_assertions::const_assert;

use crate::nibble_ints::U4;

/// A key as recognized by the CHIP-8 processor.
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
pub enum Key {
    K0,
    K1,
    K2,
    K3,
    K4,
    K5,
    K6,
    K7,
    K8,
    K9,
    KA,
    KB,
    KC,
    KD,
    KE,
    KF,
}

const_assert!(std::mem::variant_count::<Key>() == U4::MAX.into_u8() as usize + 1);

impl From<Key> for U4 {
    fn from(reg: Key) -> Self {
        // SAFETY: Key has exactly U4::MAX + 1 variants, i.e the discriminant fits in the low nibble.
        unsafe { U4::from_u8_unchecked(reg as u8) }
    }
}

impl From<U4> for Key {
    fn from(val: U4) -> Self {
        // SAFETY: Key has exactly U4::MAX + 1 variants.
        unsafe { Key::from_unchecked(u8::from(val)) }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KeyState {
    Pressed,
    NotPressed,
}
