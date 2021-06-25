use std::convert::TryFrom;

use static_assertions::const_assert;
use thiserror::Error;

use crate::{
    nibble_ints::{U8Nibble, U12, U4},
    processor::DataRegister,
};

/// Extract the correct nibble(s) from the instruction bytes
/// and assign them to the variable with the given identifier.
/// If given a constant instead of an identifier, do nothing.
macro_rules! maybe_extract_instruction_nibbles_into_var {
    ($instruction:ident, $target:ident, byte: $byte:literal, $nibble:expr) => {
        // SAFETY: bit-masked to be below U4::MAX (0b1111)
        let $target: U4 = U4::from_u8($instruction[$byte], $nibble);
    };
    ($instruction:ident, $constant:literal, byte: $_byte:literal, $_nibble:expr) => {};
    ($instruction:ident, byte_constant: $target:ident) => {
        let $target: u8 = $instruction[1];
    };
    ($instruction:ident, address: $target:ident) => {
        // SAFETY: bit-masked to be below U12::MAX (0b1111_1111_1111)
        let $target: U12 = unsafe {
            U12::from_u16_unchecked(
                (($instruction[0] & 0b1111) as u16) << (2 * 4) | $instruction[1] as u16,
            )
        };
    };
}

/// Expands to a pattern that matches a nibble constant in a match expression.
macro_rules! nibble_pattern_part_match_pattern {
    ($var:ident) => {
        _
    };
    ($constant:literal) => {
        $constant
    };
}

/// Expands to a pattern that matches all nibble constants in a given nibble pattern.
macro_rules! instruction_from_u8x2_match_arm_pattern {
    (($n0:literal, $n1:tt, $n2:tt, $n3:tt)) => {
        (
            $n0,
            nibble_pattern_part_match_pattern!($n1),
            nibble_pattern_part_match_pattern!($n2),
            nibble_pattern_part_match_pattern!($n3),
        )
    };
    (($n0:literal, $n1:tt, $byte_constant:ident)) => {
        ($n0, nibble_pattern_part_match_pattern!($n1), _, _)
    };
    (($n0:literal, $address:ident)) => {
        ($n0, _, _, _)
    };
}

/// If given a literal, `const_assert!`s that the literal is smaller than `0b1111`.
/// Does nothing if given an identifier.
macro_rules! nibble_literal_assertion {
    ($var:ident) => {};
    ($constant:literal) => {
        const_assert!($constant <= 0b1111);
    };
}

/// For all given literals, `const_assert!`s that the literals are smaller than `0b1111`.
/// Identifiers are ignored.
macro_rules! nibble_literals_assertions {
    (($n0:literal, $n1:tt, $n2:tt, $n3:tt)) => {
        nibble_literal_assertion!($n0);
        nibble_literal_assertion!($n1);
        nibble_literal_assertion!($n2);
        nibble_literal_assertion!($n3);
    };
    (($n0:literal, $n1:tt, $_byte_constant:ident)) => {
        nibble_literal_assertion!($n0);
        nibble_literal_assertion!($n1);
    };
    (($n0:literal, $_address:ident)) => {
        nibble_literal_assertion!($n0);
    };
}

macro_rules! instruction_from_u8x2_match_arm_code {
    ($instruction:ident, ($n0:literal, $n1:tt, $n2:tt, $n3:tt), $code:expr) => {{
        maybe_extract_instruction_nibbles_into_var!($instruction, $n1, byte: 0, U8Nibble::Lo);
        maybe_extract_instruction_nibbles_into_var!($instruction, $n2, byte: 1, U8Nibble::Hi);
        maybe_extract_instruction_nibbles_into_var!($instruction, $n3, byte: 1, U8Nibble::Lo);
        $code
    }};
    ($instruction:ident, ($n0:literal, $n1:tt, $byte_constant:ident), $code:expr) => {{
        maybe_extract_instruction_nibbles_into_var!($instruction, $n1, byte: 0, U8Nibble::Lo);
        maybe_extract_instruction_nibbles_into_var!($instruction, byte_constant: $byte_constant);
        $code
    }};
    ($instruction:ident, ($n0:literal, $address:ident), $code:expr) => {{
        maybe_extract_instruction_nibbles_into_var!($instruction, address: $address);
        $code
    }};
}

/// Checks if a u8 nibble variable is greater than the maximum value of a nibble (0b1111).
/// Returns an error if the variable's value exceeds tha maximum, otherwise does nothing.
macro_rules! u4_var_or_literal_to_u8 {
    ($nibble:literal) => {
        $nibble as u8
    };
    ($nibble:ident) => {
        u8::from(U4::from($nibble))
    };
}

macro_rules! instruction_to_u8x2_match_arm_code {
    ($instruction:ident, ($n0:literal, $n1:tt, $n2:tt, $n3:tt)) => {{
        [
            (u4_var_or_literal_to_u8!($n0) << 4) | u4_var_or_literal_to_u8!($n1),
            (u4_var_or_literal_to_u8!($n2) << 4) | u4_var_or_literal_to_u8!($n3),
        ]
    }};
    ($instruction:ident, ($n0:literal, $n1:tt, $byte_constant:ident)) => {{
        [
            (u4_var_or_literal_to_u8!($n0) << 4) | u4_var_or_literal_to_u8!($n1),
            $byte_constant,
        ]
    }};
    ($instruction:ident, ($n0:literal, $address:ident)) => {{
        [
            (u4_var_or_literal_to_u8!($n0) << 4) | ((u16::from($address as U12) >> (2 * 4)) as u8),
            u16::from($address as U12) as u8,
        ]
    }};
}

#[derive(Debug, PartialEq, Eq, Error)]
#[error("invalid instruction nibbles `{0:X?}`")]
pub struct InvalidInstructionNibblesError([u8; 2]);

#[derive(Debug, PartialEq, Eq, Error)]
#[error("out of bounds field `{field_name}` in instruction `{instruction:?}`, must be smaller than {max_value}")]
pub struct OOBInstructionFieldError {
    instruction: Instruction,
    field_name: &'static str,
    max_value: usize,
}

macro_rules! define_instruction {
    (
        $(#[$enum_attribute:meta])*
        pub enum $enum_name:ident {
            $(
                $(#[$field_attribute:meta])*
                $instruction_name:ident $( {
                    $(
                        $(#[$param_attribute:meta])*
                        $param:ident : $param_type:ty
                    ),*
                    $(,)?
                } )?
                =
                $nibble_pattern:tt
            ),*
            $(,)?
        }
    ) => {
        $(#[$enum_attribute])*
        pub enum $enum_name {
            $(
                $(#[$field_attribute])*
                $instruction_name $({
                    $($param: $param_type),*
                })?
            ),*
        }

        $(
            nibble_literals_assertions!($nibble_pattern);
        )*

        impl TryFrom<[u8; 2]> for Instruction {
            type Error = InvalidInstructionNibblesError;

            fn try_from(instruction: [u8; 2]) -> Result<Self, Self::Error> {
                let n0 = instruction[0] >> 4 & 0b1111;
                let n1 = instruction[0] & 0b1111;
                let n2 = instruction[1] >> 4 & 0b1111;
                let n3 = instruction[1] & 0b1111;

                match (n0, n1, n2, n3) {
                    $(
                        instruction_from_u8x2_match_arm_pattern!($nibble_pattern) => {
                            Ok(instruction_from_u8x2_match_arm_code!(instruction, $nibble_pattern, {
                                // TODO: allow for compile time checking of conversion from u8/u16 to $param_type
                                Self::$instruction_name $({ $($param: <$param_type>::try_from($param).unwrap() ),* })?
                            }))
                        },
                    )*
                    (_, _, _, _) => Err(InvalidInstructionNibblesError(instruction))
                }
            }
        }

        impl From<Instruction> for [u8; 2] {
            fn from(instruction: Instruction) -> Self {
                match instruction {
                    $(
                        Instruction::$instruction_name $({ $($param),* })? => {
                            instruction_to_u8x2_match_arm_code!(instruction, $nibble_pattern)
                        },
                    )*
                }
            }
        }
    };
}

define_instruction! {
    /// A CHIP-8 instruction
    ///
    /// References used are
    /// <https://github.com/mattmikolay/chip-8/wiki/CHIP%E2%80%908-Instruction-Set> (CC-BY-SA 4.0, Matthew Mikolay)
    /// and <https://en.wikipedia.org/wiki/CHIP-8#Opcode_table> (CC-BY-SA 3.0, Wikipedia Authors).
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum Instruction {
        /// Clear the display.
        ClearDisplay = (0x0, 0x0, 0xE, 0x0),
        /// Return from a subroutine.
        Return = (0x0, 0x0, 0xE, 0xE),
        /// Jump to the `target_address`.
        Jump { target_address: U12 } = (0x1, target_address),
        /// Call the subroutine at the `target_address`.
        CallSubroutine { target_address: U12 } = (0x2, target_address),
        /// Skip the next instruction if the value in `register`
        /// is equal to `constant`.
        SkipIfEqConst { register: DataRegister, constant: u8 } = (0x3, register, constant),
        /// Skip the next instruction if the value in `register`
        /// is not equal to `constant`.
        SkipIfNeqConst { register: DataRegister, constant: u8 } = (0x4, register, constant),
        /// Skip the next instruction if the value in `register1`
        /// is equal to the value in `register2`.
        SkipIfEq {
            register1: DataRegister,
            register2: DataRegister,
        } = (0x5, register1, register2, 0x0),
        /// Assign `constant` to `target_register`.
        AssignConst {
            target_register: DataRegister,
            constant: u8,
        } = (0x6, target_register, constant),
        /// Add `constant` to the value in `target_register`
        /// and assign the result to `target_register`.
        ///
        /// [`DataRegister::VF`] is not altered.
        AddAssignConst {
            target_register: DataRegister,
            constant: u8,
        } = (0x7, target_register, constant),
        /// Assign the value in `source_register` to `target_register`.
        Assign {
            target_register: DataRegister,
            source_register: DataRegister,
        } = (0x8, target_register, source_register, 0x0),
        /// Bitwise-OR the value in `source_register`
        /// and the value in `target_register`,
        /// and assign the result to `target_register`.
        OrAssign {
            target_register: DataRegister,
            source_register: DataRegister,
        } = (0x8, target_register, source_register, 0x1),
        /// Bitwise-AND the value in `source_register`
        /// and the value in `target_register`,
        /// and assign the result to `target_register`.
        AndAssign {
            target_register: DataRegister,
            source_register: DataRegister,
        } = (0x8, target_register, source_register, 0x2),
        /// Bitwise-XOR the value in `source_register`
        /// and the value in `target_register`,
        /// and assign the result to `target_register`.
        XorAssign {
            target_register: DataRegister,
            source_register: DataRegister,
        } = (0x8, target_register, source_register, 0x3),
        /// Add the value in `source_register` to the value in `target_register`
        /// and assign the result to `target_register`.
        ///
        /// If a carry occurs [`DataRegister::VF`] is set to `1`,
        /// if not it is set to `0`.
        AddAssign {
            target_register: DataRegister,
            source_register: DataRegister,
        } = (0x8, target_register, source_register, 0x4),
        /// Subtract the value in `source_register`
        /// from the value in `target_register`
        /// and assign the result to `target_register`.
        ///
        /// If a borrow occurs [`DataRegister::VF`] is set to `0`,
        /// if not it is set to `1`.
        SubAssign {
            target_register: DataRegister,
            source_register: DataRegister,
        } = (0x8, target_register, source_register, 0x5),
        /// Shift the value in `source_register` one bit to the right
        /// and assign the result to `target_register`.
        ///
        /// [`DataRegister::VF`] is set to the least significant bit of
        /// `source_register` prior to the shift, i.e. the bit that is shifted out.
        ShrAssign {
            target_register: DataRegister,
            source_register: DataRegister,
        } = (0x8, target_register, source_register, 0x6),
        /// Subtract the value in `target_register`
        /// from the value in `source_register`
        /// and assign the result to `target_register`.
        ///
        /// If a borrow occurs [`DataRegister::VF`] is set to `0`,
        /// if not it is set to `1`.
        RevSubAssign {
            target_register: DataRegister,
            source_register: DataRegister,
        } = (0x8, target_register, source_register, 0x7),
        /// Shift the value in `source_register` one bit to the left
        /// and assign the result to `target_register`.
        ///
        /// [`DataRegister::VF`] is set to the most significant bit of
        /// `source_register` prior to the shift, i.e. the bit that is shifted out.
        ShlAssign {
            target_register: DataRegister,
            source_register: DataRegister,
        } = (0x8, target_register, source_register, 0xE),
        /// Skip the next instruction if the value in `register1`
        /// is not equal to the value in `register2`.
        SkipIfNeq {
            register1: DataRegister,
            register2: DataRegister,
        } = (0x9, register1, register2, 0x0),
        /// Assign `address` to the special address register `I`.
        AssignAddrToI { address: U12 } = (0xA, address),
        /// Jump to the sum of `address` and the value in [`DataRegister::V0`].
        JumpOffset { address: U12 } = (0xB, address),
        /// Assign `target_register` random bits in the positions indicated by `mask`.
        AssignRandomMasked {
            target_register: DataRegister,
            mask: u8,
        } = (0xC, target_register, mask),
        /// Draw a sprite at the position given by the values
        /// in `position_x_register` and `position_y_register`.
        /// For this `last_sprite_byte_offset`+1 bytes of sprite data are read from the address
        /// stored in the special address register `I`.
        ///
        /// If the position for the sprite to be drawn is offscreen,
        /// the position will have the modulo of the screen size in each dimension applied to it.
        DrawSprite {
            position_x_register: DataRegister,
            position_y_register: DataRegister,
            last_sprite_byte_offset: U4,
        } = (0xD, position_x_register, position_y_register, last_sprite_byte_offset),
        /// Skip the next instruction if the key corresponding
        /// to the value set in `key_register` is pressed.
        SkipIfKeyPressed { key_register: DataRegister } = (0xE, key_register, 0x9, 0xE),
        /// Skip the next instruction if the key corresponding
        /// to the value set in `key_register` is not pressed.
        SkipIfKeyNotPressed { key_register: DataRegister } = (0xE, key_register, 0xA, 0x1),
        /// Assign the current value of the delay timer to `target_register`.
        AssignDelayTimerVal { target_register: DataRegister } = (0xF, target_register, 0x0, 0x7),
        /// Wait until a key is pressed and store the value
        /// corresponding the key in `target_register`
        WaitForKeyPress { target_register: DataRegister } = (0xF, target_register, 0x0, 0xA),
        /// Set the value of the delay timer to the value in `source_register`.
        SetDelayTimer { source_register: DataRegister } = (0xF, source_register, 0x1, 0x5),
        /// Set the value of the sound timer to the value in `source_register`.
        SetSoundTimer { source_register: DataRegister } = (0xF, source_register, 0x1, 0x8),
        /// Add the value in `source_register` to the value
        /// in the special address register `I` and store the result in `I`.
        ///
        /// [`DataRegister::VF`] is not altered.
        AddAssignI { source_register: DataRegister } = (0xF, source_register, 0x1, 0xE),
        /// Assign the address of the built-in hex char sprite
        /// corresponding to the value in `sprite_register`
        /// to the special address register `I`.
        /// See [`SPRITE_4X5_FONT`][`crate::graphics::font_4x5::SPRITE_4X5_FONT`].
        ///
        /// For any value of `hex_char_register` that is greater than `0xF`
        /// a runtime error will be emitted.
        AssignHexCharSpriteAddrToI { hex_char_register: DataRegister } = (0xF, hex_char_register, 0x2, 0x9),
        /// Store the three digit binary-coded decimal equivalent
        /// to the value in `source_register`
        /// in the three consecutive bytes of memory
        /// beginning at the address in the special address register `I`.
        /// The digits are stored in order of significance,
        /// e.g. the digit for hundreds is stored at the address in `I`.
        StoreBCD { source_register: DataRegister } = (0xF, source_register, 0x3, 0x3),
        /// Store the values from registers [`DataRegister::V0`] to `last_register`
        /// in consecutive bytes of memory
        /// beginning at the address in the special address register `I`.
        ///
        /// The special address register `I` is assigned the sum of its old value
        /// and the number of registers stored.
        StoreRegisterValues { last_register: DataRegister } = (0xF, last_register, 0x5, 0x5),
        /// Load the values of consecutive bytes of memory
        /// beginning at the address in the special address register `I`
        /// into the registers from [`DataRegister::V0`] to `last_register`.
        ///
        /// The special address register `I` is assigned the sum of its old value
        /// and the number of registers stored.
        LoadRegisterValues { last_register: DataRegister } = (0xF, last_register, 0x6, 0x5),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    mod instruction_try_from_u8x2 {
        use super::*;

        #[test]
        fn case_ok() {
            let instr = Instruction::AssignConst {
                target_register: DataRegister::V4,
                constant: 7,
            };

            let instr_bytes = [0x64_u8, 0x07];

            assert_eq!(
                Instruction::try_from(instr_bytes),
                Ok(instr) as Result<_, InvalidInstructionNibblesError>
            );
        }

        #[test]
        fn case_err() {
            let instr_bytes = [0x00_u8, 0x00];

            assert_eq!(
                Instruction::try_from(instr_bytes),
                Err(InvalidInstructionNibblesError(instr_bytes)) as Result<Instruction, _>
            );
        }
    }

    #[test]
    fn u8x2_from_instruction() {
        let instr = Instruction::DrawSprite {
            position_x_register: DataRegister::V9,
            position_y_register: DataRegister::V3,
            last_sprite_byte_offset: U4::try_from(5).unwrap(),
        };

        let instr_bytes = [0xD9_u8, 0x35];

        assert_eq!(<[u8; 2]>::from(instr), instr_bytes);
    }
}
