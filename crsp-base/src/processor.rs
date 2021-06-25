use std::convert::TryFrom;

use rand::random;
use thiserror::Error;

use crate::{
    graphics::font_4x5::Font,
    instruction::{Instruction, InvalidInstructionNibblesError},
};

mod data_register;
mod key;
#[cfg(test)]
mod test;

pub use data_register::DataRegister;
pub use key::{Key, KeyState};

#[derive(Debug, PartialEq, Eq, Error)]
pub enum ProcessorError {
    #[error("an out of bounds memory access was requested at {program_counter:X}")]
    OutOfBoundsMemoryAccess { program_counter: u16 },
    #[error("the call request at {program_counter:X} exceeds the maximum call stack size")]
    MaxCallStackSizeExceeded { program_counter: u16 },
    #[error("return was requested at {program_counter:X} with an empty call stack")]
    ReturnWithEmptyCallStack { program_counter: u16 },
    #[error("the hex char sprite address was requested for a non-hex-char (greater than 0xF) id {requested_sprite_id:X} at {program_counter:X}")]
    NotAHexChar {
        program_counter: u16,
        requested_sprite_id: u8,
    },
    #[error("a key with an invalid (greater than 0xF) key id {requested_key_id:X} was referenced at {program_counter:X}")]
    NotAValidKey {
        program_counter: u16,
        requested_key_id: u8,
    },
    #[error(transparent)]
    InvalidInstructionNibblesError(#[from] InvalidInstructionNibblesError),
}

#[derive(Debug, PartialEq, Eq)]
pub struct CallStack {
    vec: Vec<u16>,
    max_len: usize,
}

impl CallStack {
    pub fn new_with_max_len(max_len: usize) -> Self {
        Self {
            vec: Vec::with_capacity(max_len),
            max_len,
        }
    }

    pub fn len(&self) -> usize {
        self.vec.len()
    }

    pub fn pop(&mut self) -> Option<u16> {
        self.vec.pop()
    }

    #[must_use]
    pub fn push(&mut self, address: u16) -> bool {
        if self.vec.len() < self.max_len {
            self.vec.push(address);
            true
        } else {
            false
        }
    }
}

impl From<Vec<u16>> for CallStack {
    fn from(vec: Vec<u16>) -> Self {
        let max_len = vec.capacity();
        Self { vec, max_len }
    }
}

impl Default for CallStack {
    fn default() -> Self {
        Self::new_with_max_len(128)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum KeyWaitingState {
    NotWaiting,
    Waiting { target_register: DataRegister },
}

impl Default for KeyWaitingState {
    fn default() -> Self {
        Self::NotWaiting
    }
}

/// Drawing behavior for sprites that are partially offscreen.
///
/// Sprites that are drawn at coordinates fully offscreen will *always*
/// have the modulo of the screen size applied to their coordinates.
/// The partial offscreen drawing behavior will be applied after this.
/// See also [`Instruction::DrawSprite`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PartialOffscreenDrawing {
    /// Clip offscreen parts of sprites in both X and Y.
    ClipXY,
    /// Clip offscreen parts of sprites in X, wrap in Y.
    ClipXWrapY,
    /// Wrap offscreen parts of sprites in X, clip in Y.
    WrapXClipY,
    /// Wrap offscreen parts of sprites in both X and Y.
    WrapXY,
}

impl Default for PartialOffscreenDrawing {
    fn default() -> Self {
        Self::ClipXY
    }
}

impl PartialOffscreenDrawing {
    pub fn wrap_x(self) -> bool {
        match self {
            Self::WrapXY | Self::WrapXClipY => true,
            _ => false,
        }
    }

    pub fn wrap_y(self) -> bool {
        match self {
            Self::WrapXY | Self::ClipXWrapY => true,
            _ => false,
        }
    }
}

// TODO: add screen and sprite handling
// TODO: add delay and sound timer handling
// TODO: add sound handling
// TODO: consider supporting S-CHIP as well
#[derive(Debug, PartialEq, Eq)]
pub struct Processor {
    data_registers: [u8; std::mem::variant_count::<DataRegister>()],
    address_register: u16,
    memory: [u8; Self::MAX_USABLE_MEMORY_LEN],
    program_counter: u16,
    call_stack: CallStack,
    delay_timer: u8,
    sound_timer: u8,
    screen: [u8; Self::SCREEN_WIDTH_BYTES as usize * Self::SCREEN_HEIGHT as usize],
    key_states: [KeyState; std::mem::variant_count::<Key>()],
    waiting_for_keypress: KeyWaitingState,
    partial_offscreen_drawing: PartialOffscreenDrawing,
}

impl Default for Processor {
    fn default() -> Self {
        ProcessorBuilder::new().build()
    }
}

impl Processor {
    /// The maximum length of memory that can be addressed with CHIP-8 instructions, [`u16::MAX`]+1.
    ///
    /// See also [`Self::MAX_ADDRESS`]
    pub const MAX_USABLE_MEMORY_LEN: usize = Self::MAX_ADDRESS as usize + 1;

    /// The maximum address that can be represented with CHIP-8 instructions, [`u16::MAX`]+1.
    ///
    /// [`Instruction::StoreRegisterValues`] and [`Instruction::LoadRegisterValues`]
    /// don't allow access outside of this and will cause a runtime error when run
    /// with the sum of the address in special address register `I`
    /// and the number of the `last_register` greater than this.
    /// The same goes for [`Instruction::DrawSprite`] and the `last_sprite_byte_offset`.
    pub const MAX_ADDRESS: u16 = u16::MAX;

    /// Screen width in bytes.
    pub const SCREEN_WIDTH_BYTES: u8 = 8;
    /// Screen width in pixels.
    pub const SCREEN_WIDTH: u8 = Self::SCREEN_WIDTH_BYTES * 8;
    /// Screen height in pixels.
    pub const SCREEN_HEIGHT: u8 = 32;

    pub fn builder() -> ProcessorBuilder {
        ProcessorBuilder::new()
    }

    /// Get the value of a data register.
    const fn get_register(&self, register: DataRegister) -> u8 {
        self.data_registers[register as u8 as usize]
    }

    /// Set the value of a data register.
    fn set_register(&mut self, register: DataRegister, val: u8) {
        self.data_registers[register as u8 as usize] = val;
    }

    /// Get the state of a key.
    pub const fn get_key_state(&self, key: Key) -> KeyState {
        self.key_states[key as u8 as usize]
    }

    /// Set the state of a key.
    pub fn set_key_state(&mut self, key: Key, state: KeyState) {
        // TODO: possibly replace with if let chain once let_chains (eRFC 2497) work
        match self.waiting_for_keypress {
            KeyWaitingState::Waiting { target_register } if state == KeyState::Pressed => {
                self.waiting_for_keypress = KeyWaitingState::NotWaiting;
                self.set_register(target_register, key as u8);
            }
            _ => (),
        }
        self.key_states[key as u8 as usize] = state;
    }

    /// Draw byte to `screen` at position `byte_x*8` and `y`.
    /// Does not take `&mut self` so it can be called while iterating over a sprite in `self.memory`.
    ///
    /// Returns `true` if a set pixel has been unset, `false` otherwise.
    fn draw_byte_to_screen(
        screen: &mut [u8; Self::SCREEN_WIDTH_BYTES as usize * Self::SCREEN_HEIGHT as usize],
        byte_x: usize,
        y: usize,
        byte: u8,
    ) -> bool {
        // A one in the original byte and the shifted sprite byte's bits
        // will result in a set pixel being unset.
        let set_pixel_unset = (screen[byte_x + y * Self::SCREEN_WIDTH_BYTES as usize] & byte) > 0;

        screen[byte_x + y * Self::SCREEN_WIDTH_BYTES as usize] ^= byte;

        set_pixel_unset
    }

    pub fn step(&mut self) -> Result<(), ProcessorError> {
        if self.program_counter >= Self::MAX_ADDRESS {
            return Err(ProcessorError::OutOfBoundsMemoryAccess {
                program_counter: self.program_counter,
            });
        }
        // SAFETY: This can't produce an OOB accesses,
        //         as we checked that the address in self.program_counter
        //         and the one after that are in bounds above.
        let instruction_nibbles = [
            self.memory[self.program_counter as usize],
            self.memory[self.program_counter as usize + 1],
        ];

        let instruction = Instruction::try_from(instruction_nibbles)?;

        let mut was_control_flow_instr = false;

        match instruction {
            Instruction::ClearDisplay => todo!(),
            Instruction::Return => {
                self.program_counter =
                    self.call_stack
                        .pop()
                        .ok_or(ProcessorError::ReturnWithEmptyCallStack {
                            program_counter: self.program_counter,
                        })?;

                was_control_flow_instr = true;
            }
            Instruction::Jump { target_address } => {
                self.program_counter = target_address.into();

                was_control_flow_instr = true;
            }
            Instruction::CallSubroutine { target_address } => {
                if !self.call_stack.push(
                    self.program_counter
                        .wrapping_add(std::mem::size_of::<u16>() as u16),
                ) {
                    return Err(ProcessorError::MaxCallStackSizeExceeded {
                        program_counter: self.program_counter,
                    });
                };
                self.program_counter = target_address.into();

                was_control_flow_instr = true;
            }
            Instruction::SkipIfEqConst { register, constant } => {
                if self.get_register(register) == constant {
                    self.program_counter = self
                        .program_counter
                        .wrapping_add(2 * std::mem::size_of::<u16>() as u16);

                    was_control_flow_instr = true;
                }
            }
            Instruction::SkipIfNeqConst { register, constant } => {
                if self.get_register(register) != constant {
                    self.program_counter = self
                        .program_counter
                        .wrapping_add(2 * std::mem::size_of::<u16>() as u16);

                    was_control_flow_instr = true;
                }
            }
            Instruction::SkipIfEq {
                register1,
                register2,
            } => {
                if self.get_register(register1) == self.get_register(register2) {
                    self.program_counter = self
                        .program_counter
                        .wrapping_add(2 * std::mem::size_of::<u16>() as u16);

                    was_control_flow_instr = true;
                }
            }
            Instruction::AssignConst {
                target_register,
                constant,
            } => self.set_register(target_register, constant),
            Instruction::AddAssignConst {
                target_register,
                constant,
            } => self.set_register(
                target_register,
                self.get_register(target_register).wrapping_add(constant),
            ),
            Instruction::Assign {
                target_register,
                source_register,
            } => self.set_register(target_register, self.get_register(source_register)),
            Instruction::OrAssign {
                target_register,
                source_register,
            } => self.set_register(
                target_register,
                self.get_register(target_register) | self.get_register(source_register),
            ),
            Instruction::AndAssign {
                target_register,
                source_register,
            } => self.set_register(
                target_register,
                self.get_register(target_register) & self.get_register(source_register),
            ),
            Instruction::XorAssign {
                target_register,
                source_register,
            } => self.set_register(
                target_register,
                self.get_register(target_register) ^ self.get_register(source_register),
            ),
            Instruction::AddAssign {
                target_register,
                source_register,
            } => {
                let (res, carry) = self
                    .get_register(target_register)
                    .overflowing_add(self.get_register(source_register));
                self.set_register(DataRegister::VF, carry as u8);
                self.set_register(target_register, res);
            }
            Instruction::SubAssign {
                target_register,
                source_register,
            } => {
                let (res, borrow) = self
                    .get_register(target_register)
                    .overflowing_sub(self.get_register(source_register));
                self.set_register(DataRegister::VF, 1 - borrow as u8);
                self.set_register(target_register, res);
            }
            Instruction::ShrAssign {
                target_register,
                source_register,
            } => {
                let old_lsb = self.get_register(source_register) & 0b1;
                self.set_register(DataRegister::VF, old_lsb);
                self.set_register(target_register, self.get_register(source_register) >> 1);
            }
            Instruction::RevSubAssign {
                target_register,
                source_register,
            } => {
                let (res, borrow) = self
                    .get_register(source_register)
                    .overflowing_sub(self.get_register(target_register));
                self.set_register(DataRegister::VF, 1 - borrow as u8);
                self.set_register(target_register, res);
            }
            Instruction::ShlAssign {
                target_register,
                source_register,
            } => {
                let old_msb = (self.get_register(source_register) >> 7) & 0b1;
                self.set_register(DataRegister::VF, old_msb);
                self.set_register(target_register, self.get_register(source_register) << 1);
            }
            Instruction::SkipIfNeq {
                register1,
                register2,
            } => {
                if self.get_register(register1) != self.get_register(register2) {
                    self.program_counter = self
                        .program_counter
                        .wrapping_add(2 * std::mem::size_of::<u16>() as u16);

                    was_control_flow_instr = true;
                }
            }
            Instruction::AssignAddrToI { address } => self.address_register = address.into(),
            Instruction::JumpOffset { address } => {
                self.program_counter =
                    u16::from(address).wrapping_add(self.get_register(DataRegister::V0) as u16);

                was_control_flow_instr = true;
            }
            Instruction::AssignRandomMasked {
                target_register,
                mask,
            } => self.set_register(
                target_register,
                (self.get_register(target_register) & !mask) | (random::<u8>() & mask),
            ),
            Instruction::DrawSprite {
                position_x_register,
                position_y_register,
                last_sprite_byte_offset,
            } => {
                if self.address_register
                    > Self::MAX_ADDRESS - u8::from(last_sprite_byte_offset) as u16
                {
                    return Err(ProcessorError::OutOfBoundsMemoryAccess {
                        program_counter: self.program_counter,
                    });
                }
                let x = (self.get_register(position_x_register) % Self::SCREEN_WIDTH) as usize;
                let y = (self.get_register(position_y_register) % Self::SCREEN_HEIGHT) as usize;
                let mut set_pixel_unset = false;

                for (i, sprite_byte) in self.memory[self.address_register as usize
                    ..=(self.address_register as usize
                        + u8::from(last_sprite_byte_offset) as usize)]
                    .iter()
                    .copied()
                    .enumerate()
                {
                    // Wrap y if we should, else we're done for the entire sprite.
                    let y = if y + i < Self::SCREEN_HEIGHT as usize
                        || (y + i >= Self::SCREEN_HEIGHT as usize
                            && self.partial_offscreen_drawing.wrap_y())
                    {
                        (y + i) % Self::SCREEN_HEIGHT as usize
                    } else {
                        break;
                    };

                    set_pixel_unset |= Self::draw_byte_to_screen(
                        &mut self.screen,
                        x / 8,
                        y,
                        sprite_byte >> (x % 8),
                    );

                    // If x is exactly at the start of a screen byte, we're done.
                    // We're also done if the next byte is offscreen and we shouldn't wrap in X.
                    if x % 8 == 0
                        || (x + 7 >= Self::SCREEN_WIDTH as usize
                            && !self.partial_offscreen_drawing.wrap_x())
                    {
                        continue;
                    }

                    // Draw remaining bits into next byte (possibly wrapping around in X)

                    let rem_sprite_byte = sprite_byte << (8 - (x % 8));
                    let rem_x = (x + (8 - (x % 8))) % Self::SCREEN_WIDTH as usize;

                    set_pixel_unset |=
                        Self::draw_byte_to_screen(&mut self.screen, rem_x / 8, y, rem_sprite_byte);
                }

                self.set_register(DataRegister::VF, set_pixel_unset as u8);
            }
            Instruction::SkipIfKeyPressed { key_register } => {
                let key_id = self.get_register(key_register);
                if let Ok(key) = Key::try_from(key_id) {
                    if self.get_key_state(key) == KeyState::Pressed {
                        self.program_counter = self
                            .program_counter
                            .wrapping_add(2 * std::mem::size_of::<u16>() as u16);

                        was_control_flow_instr = true;
                    }
                } else {
                    return Err(ProcessorError::NotAValidKey {
                        program_counter: self.program_counter,
                        requested_key_id: key_id,
                    });
                }
            }
            Instruction::SkipIfKeyNotPressed { key_register } => {
                let key_id = self.get_register(key_register);
                if let Ok(key) = Key::try_from(key_id) {
                    if self.get_key_state(key) == KeyState::NotPressed {
                        self.program_counter = self
                            .program_counter
                            .wrapping_add(2 * std::mem::size_of::<u16>() as u16);

                        was_control_flow_instr = true;
                    }
                } else {
                    return Err(ProcessorError::NotAValidKey {
                        program_counter: self.program_counter,
                        requested_key_id: key_id,
                    });
                }
            }
            Instruction::AssignDelayTimerVal { target_register } => {
                self.set_register(target_register, self.delay_timer)
            }
            Instruction::WaitForKeyPress { target_register } => {
                self.waiting_for_keypress = KeyWaitingState::Waiting { target_register };
                todo!()
            }
            Instruction::SetDelayTimer { source_register } => {
                self.delay_timer = self.get_register(source_register)
            }
            Instruction::SetSoundTimer { source_register } => {
                self.sound_timer = self.get_register(source_register)
            }
            Instruction::AddAssignI { source_register } => {
                self.address_register = self
                    .address_register
                    .wrapping_add(self.get_register(source_register) as u16)
            }
            Instruction::AssignHexCharSpriteAddrToI { hex_char_register } => {
                if self.get_register(hex_char_register) > 0xF {
                    return Err(ProcessorError::NotAHexChar {
                        program_counter: self.program_counter,
                        requested_sprite_id: self.get_register(hex_char_register),
                    });
                }
                // Hex char sprites start at 0x0 in self.memory and are each 5 bytes in length
                self.address_register = self.get_register(hex_char_register) as u16 * 5;
            }
            Instruction::StoreBCD { source_register } => {
                let val = self.get_register(source_register);

                // SAFETY: this can't produce an OOB accesses,
                //         as self.memory.len() is strictly greater than
                //         the maximum value of (self.address_register + 2)
                self.memory[self.address_register as usize] = val / 100;
                self.memory[self.address_register as usize + 1] = val / 10 % 10;
                self.memory[self.address_register as usize + 2] = val % 10;
            }
            Instruction::StoreRegisterValues { last_register } => {
                if self.address_register > Self::MAX_ADDRESS - (last_register as u8) as u16 {
                    return Err(ProcessorError::OutOfBoundsMemoryAccess {
                        program_counter: self.program_counter,
                    });
                }
                for register in DataRegister::V0..=last_register {
                    self.memory[self.address_register as usize + register as u8 as usize] =
                        self.get_register(register);
                }
                self.address_register = self
                    .address_register
                    .wrapping_add(last_register as u8 as u16 + 1);
            }
            Instruction::LoadRegisterValues { last_register } => {
                if self.address_register > Self::MAX_ADDRESS - (last_register as u8) as u16 {
                    return Err(ProcessorError::OutOfBoundsMemoryAccess {
                        program_counter: self.program_counter,
                    });
                }
                for register in DataRegister::V0..=last_register {
                    self.set_register(
                        register,
                        self.memory[self.address_register as usize + register as u8 as usize],
                    );
                }
                self.address_register = self
                    .address_register
                    .wrapping_add(last_register as u8 as u16 + 1);
            }
        }

        if !was_control_flow_instr {
            self.program_counter = self
                .program_counter
                .wrapping_add(std::mem::size_of::<u16>() as u16);
        }

        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq, Error)]
pub enum ProcessorBuilderError {
    #[error(
        "a program with a length ({program_len:X}) greater than the usable length of memory ({:X}) was supplied",
        Processor::MAX_USABLE_MEMORY_LEN
    )]
    ProgramExceedsUsableMemoryLen { program_len: usize },
}

pub struct ProcessorBuilder {
    /// The partially initialized processor
    processor: Processor,
    font: Font,
}

impl ProcessorBuilder {
    pub fn new() -> Self {
        Self {
            processor: Processor {
                data_registers: [0; 16],
                address_register: 0,
                memory: [0; Processor::MAX_USABLE_MEMORY_LEN],
                program_counter: 0x200,
                call_stack: CallStack::default(),
                delay_timer: 0,
                sound_timer: 0,
                screen: [0; 8 * 32],
                key_states: [KeyState::default(); 16],
                waiting_for_keypress: KeyWaitingState::default(),
                partial_offscreen_drawing: PartialOffscreenDrawing::default(),
            },
            font: Font::default(),
        }
    }

    // TODO: consider taking an iterator as input
    /// Copies the program into the processors memory
    /// in such that the first element is at address 0x0.
    /// This way the index of bytes in the program represents the address in memory.
    /// IMPORTANT: The first [`Font::LEN`] elements are overwritten with sprite font data
    ///            and are therefore not usable for program data.
    pub fn program(mut self, program: &[u8]) -> Result<Self, ProcessorBuilderError> {
        if program.len() > Processor::MAX_USABLE_MEMORY_LEN {
            return Err(ProcessorBuilderError::ProgramExceedsUsableMemoryLen {
                program_len: program.len(),
            });
        }

        self.processor.memory[Font::LEN..program.len()].copy_from_slice(program);

        Ok(self)
    }

    /// Set the font the processor should use.
    /// The font will be stored in processor memory starting at address 0x0.
    /// See also [`Font`].
    pub fn font(mut self, font: Font) -> Self {
        self.font = font;
        self
    }

    /// Set the partial offscreen drawing behavior for sprites.
    /// See also [`PartialOffscreenDrawing`].
    pub fn partial_offscreen_drawing(
        mut self,
        partial_offscreen_drawing: PartialOffscreenDrawing,
    ) -> Self {
        self.processor.partial_offscreen_drawing = partial_offscreen_drawing;
        self
    }

    pub fn build(mut self) -> Processor {
        self.processor.memory[0..Font::LEN].copy_from_slice(self.font.bytes());
        self.processor
    }
}
