use std::convert::TryFrom;

use rand::random;
use thiserror::Error;

use crate::{
    graphics::font_4x5::SPRITE_4X5_FONT_ROUND,
    instruction::{Instruction, InvalidInstructionNibblesError},
};

mod data_register;
#[cfg(test)]
mod test;

pub use data_register::DataRegister;

#[derive(Debug, PartialEq, Eq, Error)]
pub enum ProcessorInitError {
    #[error(
        "a program with a length ({program_len:X}) greater than the usable length of memory ({:X}) was supplied",
        Processor::MAX_USABLE_MEMORY_LEN
    )]
    ProgramExceedsUsableMemoryLen { program_len: usize },
}

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

impl Default for CallStack {
    fn default() -> Self {
        Self::new_with_max_len(128)
    }
}

// TODO: add screen and sprite handling
// TODO: add delay and sound timer handling
// TODO: add sound handling
// TODO: add font selection
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
    screen: [u8; 64 * 23],
}

impl Default for Processor {
    fn default() -> Self {
        Self {
            data_registers: [0; 16],
            address_register: 0,
            memory: Self::init_memory(None).unwrap(),
            program_counter: 0x200,
            call_stack: CallStack::default(),
            delay_timer: 0,
            sound_timer: 0,
            screen: [0; 64 * 23],
        }
    }
}

impl Processor {
    /// The maximum length of memory that can be addressed with CHIP-8 instructions, [`u16::MAX`]+1.
    ///
    /// [`Instruction::StoreRegisterValues`] and [`Instruction::LoadRegisterValues`]
    /// don't allow access outside of this and will cause a runtime error when run
    /// with the sum of the address in special address register `I`
    /// and the number of the `last_register` greater than [`u16::MAX`].
    pub const MAX_USABLE_MEMORY_LEN: usize = u16::MAX as usize + 1;

    fn init_memory(
        program: Option<&[u8]>,
    ) -> Result<[u8; Self::MAX_USABLE_MEMORY_LEN], ProcessorInitError> {
        let mut memory = [0; Self::MAX_USABLE_MEMORY_LEN];
        memory[0..SPRITE_4X5_FONT_ROUND.len()].copy_from_slice(&SPRITE_4X5_FONT_ROUND);

        if let Some(program) = program {
            if program.len() > Self::MAX_USABLE_MEMORY_LEN {
                return Err(ProcessorInitError::ProgramExceedsUsableMemoryLen {
                    program_len: program.len(),
                });
            }

            memory[SPRITE_4X5_FONT_ROUND.len()..program.len()].copy_from_slice(program);
        }

        Ok(memory)
    }

    // TODO: consider taking an iterator as input
    /// Constructs a new [`Processor`] with the program in its memory.
    ///
    /// The program is copied in such that the first element is at address 0x0,
    /// but the first 80 elements are overwritten with sprite font data.
    /// This way the index of bytes in the program represents the address in memory.
    pub fn new_with_program(program: &[u8]) -> Result<Self, ProcessorInitError> {
        return Ok(Self {
            memory: Self::init_memory(Some(program))?,
            ..Self::default()
        });
    }

    /// Get the value of a data register
    const fn get_register(&self, register: DataRegister) -> u8 {
        self.data_registers[register as u8 as usize]
    }

    fn set_register(&mut self, register: DataRegister, val: u8) {
        self.data_registers[register as u8 as usize] = val;
    }

    pub fn step(&mut self) -> Result<(), ProcessorError> {
        if self.program_counter as usize >= Self::MAX_USABLE_MEMORY_LEN - 1 {
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
                last_sprite_byte,
            } => todo!(),
            Instruction::SkipIfKeyPressed { key_register } => todo!(),
            Instruction::SkipIfKeyNotPressed { key_register } => todo!(),
            Instruction::AssignDelayTimerVal { target_register } => todo!(),
            Instruction::WaitForKeyPress { target_register } => todo!(),
            Instruction::SetDelayTimer { source_register } => todo!(),
            Instruction::SetSoundTimer { source_register } => todo!(),
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
                if self.address_register as usize
                    >= Self::MAX_USABLE_MEMORY_LEN - (last_register as u8) as usize
                {
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
                if self.address_register as usize
                    >= Self::MAX_USABLE_MEMORY_LEN - (last_register as u8) as usize
                {
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
