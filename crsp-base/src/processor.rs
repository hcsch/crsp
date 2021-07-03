use std::{
    convert::TryFrom,
    thread::{self, JoinHandle},
    time::{Duration, Instant},
};

use flume::{Receiver, Sender};
use rand::random;
use thiserror::Error;
use tracing::{debug, error, trace, trace_span, warn, Level};

use crate::{
    builtin_sprites::font_4x5::Font,
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
    #[error("call to machine subroutine requested at {program_counter:X}, this is unsupported")]
    CallMachineSubroutineUnsupported { program_counter: u16 },
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
    pub fn should_wrap_x(self) -> bool {
        match self {
            Self::WrapXY | Self::WrapXClipY => true,
            _ => false,
        }
    }

    pub fn should_wrap_y(self) -> bool {
        match self {
            Self::WrapXY | Self::ClipXWrapY => true,
            _ => false,
        }
    }
}

/// Skipping behavior for the processor.
///
/// Unsupported instructions that are not skipped will lead to an error being returned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Skipping {
    // Skip no unsupported instructions.
    None,
    // Skip [`Instruction::CallMachineSubroutine`].
    CallMachineSubroutine,
    // Skip unknown instructions
    // (i.e. ones not specified as variants of [`Instruction`]).
    Unknown,
    // Skip all unsupported instructions.
    // This skips both [`Instruction::CallMachineSubroutine`] and unknown ones.
    AllUnsupported,
}

impl Default for Skipping {
    fn default() -> Self {
        Self::CallMachineSubroutine
    }
}

impl Skipping {
    pub fn should_skip_call_machine_subroutine(self) -> bool {
        match self {
            Self::CallMachineSubroutine | Self::AllUnsupported => true,
            _ => false,
        }
    }

    pub fn should_skip_unknown(self) -> bool {
        match self {
            Self::Unknown | Self::AllUnsupported => true,
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum InstructionTiming {
    TotalTime { duration: Duration },
    WaitForKeyPress,
}

impl From<Duration> for InstructionTiming {
    fn from(duration: Duration) -> Self {
        Self::TotalTime { duration }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct StepOutcome {
    instruction_timing: InstructionTiming,
    screen_updated: bool,
    sound_timer_updated: bool,
    delay_timer_updated: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ProcessorEvent {
    ScreenUpdate {
        new_screen:
            [u8; Processor::SCREEN_WIDTH_BYTES as usize * Processor::SCREEN_HEIGHT as usize],
    },
    SoundRequest {
        duration: Duration,
    },
    WaitForKeyPress,
    ErrorEncountered {
        error: ProcessorError,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub enum ControlEvent {
    KeyStateChange { key: Key, new_state: KeyState },
}

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
    skipping: Skipping,
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
    /// The same goes for [`Instruction::DrawSprite`] and the `sprite_byte_len`.
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

    // TODO: add option for time scaling
    #[tracing::instrument(skip(self, processor_event_sender, control_event_receiver))]
    fn run(
        mut self,
        processor_event_sender: Sender<ProcessorEvent>,
        control_event_receiver: Receiver<ControlEvent>,
    ) -> Result<Processor, ProcessorError> {
        let mut delay_duration = Duration::from_secs(0);
        let mut last_delay_update = Instant::now();
        loop {
            let span = trace_span!("run loop iteration");
            let _guard = span.enter();

            let start = Instant::now();

            let control_event = match control_event_receiver.try_recv() {
                Ok(control_event) => Some(control_event),
                Err(flume::TryRecvError::Empty) => None,
                Err(flume::TryRecvError::Disconnected) => {
                    debug!("control_event_sender dropped, stopping processor::run");
                    break;
                } // ProcessorHandle dropped, stop
            };
            if let Some(control_event) = control_event {
                match control_event {
                    ControlEvent::KeyStateChange { key, new_state } => {
                        self.set_key_state(key, new_state)
                    }
                }
            }

            self.delay_timer = (delay_duration
                .saturating_sub(last_delay_update.elapsed())
                .as_secs_f64()
                * 60.0) as u8;

            let outcome = match self.step() {
                Ok(outcome) => outcome,
                Err(error) => {
                    error!(?error, "error stepping processor");
                    if let Err(_) =
                        processor_event_sender.send(ProcessorEvent::ErrorEncountered { error })
                    {
                        debug!("processor_event_receiver dropped, stopping processor::run");
                    }
                    break;
                }
            };

            if outcome.screen_updated {
                if let Err(_) = processor_event_sender.send(ProcessorEvent::ScreenUpdate {
                    new_screen: self.screen.clone(),
                }) {
                    debug!("processor_event_receiver dropped, stopping processor::run");
                    break;
                }
            }

            if outcome.sound_timer_updated {
                if let Err(_) = processor_event_sender.send(ProcessorEvent::SoundRequest {
                    duration: Duration::from_secs_f64(self.sound_timer as f64 / 60.0),
                }) {
                    debug!("processor_event_receiver dropped, stopping processor::run");
                    break;
                }
            }

            if outcome.delay_timer_updated {
                delay_duration = Duration::from_secs_f64(self.delay_timer as f64 / 60.0); // / 500;
                last_delay_update = Instant::now();
            }

            match outcome.instruction_timing {
                InstructionTiming::TotalTime { duration } => {
                    // let duration = duration / 500;

                    let elapsed = start.elapsed();
                    let delta = duration.checked_sub(elapsed);
                    if let Some(delta) = delta {
                        spin_sleep::sleep(delta);
                    } else {
                        warn!(
                            target_duration = ?duration,
                            actual = ?elapsed,
                            delta = ?(elapsed - duration),
                            "instruction processing took longer than target duration",
                        );
                    }
                }
                InstructionTiming::WaitForKeyPress => {
                    if let Err(_) = processor_event_sender.send(ProcessorEvent::WaitForKeyPress) {
                        debug!("processor_event_receiver dropped, stopping processor::run");
                        break;
                    }

                    let control_event = match control_event_receiver.recv() {
                        Ok(control_event) => Some(control_event),
                        Err(flume::RecvError::Disconnected) => break, // ProcessorHandle dropped, stop
                    };
                    if let Some(control_event) = control_event {
                        match control_event {
                            ControlEvent::KeyStateChange { key, new_state } => {
                                self.set_key_state(key, new_state)
                            }
                        }
                    }
                }
            }
        }

        Ok(self)
    }

    // TODO: add tests for this
    #[tracing::instrument(skip(self))]
    pub fn start(
        self,
    ) -> (
        Sender<ControlEvent>,
        Receiver<ProcessorEvent>,
        JoinHandle<Result<Processor, ProcessorError>>,
    ) {
        let (processor_event_sender, processor_event_receiver) = flume::bounded(2);
        let (control_event_sender, control_event_receiver) = flume::bounded(2);

        let join_handle = thread::Builder::new()
            .name("processor runner".to_owned())
            .spawn(move || self.run(processor_event_sender, control_event_receiver))
            .expect("failed to create thread for processor runner");

        (control_event_sender, processor_event_receiver, join_handle)
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
        debug!(?key, ?state, "key state update");
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

    pub const fn screen(
        &self,
    ) -> &[u8; Self::SCREEN_WIDTH_BYTES as usize * Self::SCREEN_HEIGHT as usize] {
        &self.screen
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

    /// Return decimal digits of a u8 value.
    /// The hundreds digit is the first element in the array,
    /// followed by the tens and single digits.
    ///
    /// 3 digits are always enough, since the maximum value of a u8 is 255.
    fn decimal_digits_of_u8(num: u8) -> [u8; 3] {
        [num / 100, num / 10 % 10, num % 10]
    }

    #[tracing::instrument(level = Level::TRACE, skip(self))]
    pub fn step(&mut self) -> Result<StepOutcome, ProcessorError> {
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

        let instruction = match Instruction::try_from(instruction_nibbles) {
            Ok(instruction) => instruction,
            Err(error) => {
                if !self.skipping.should_skip_unknown() {
                    return Err(error.into());
                } else {
                    self.program_counter = self
                        .program_counter
                        .wrapping_add(std::mem::size_of::<u16>() as u16);

                    return Ok(StepOutcome {
                        instruction_timing: Duration::from_micros(0).into(),
                        screen_updated: false,
                        sound_timer_updated: false,
                        delay_timer_updated: false,
                    });
                }
            }
        };

        trace!(program_counter = ?self.program_counter, ?instruction, "executing instruction");

        let mut was_control_flow_instr = false;
        let mut screen_updated = false;
        let mut sound_timer_updated = false;
        let mut delay_timer_updated = false;

        match instruction {
            Instruction::ClearDisplay => {
                self.screen.fill(0);

                screen_updated = true;
            }
            Instruction::Return => {
                self.program_counter =
                    self.call_stack
                        .pop()
                        .ok_or(ProcessorError::ReturnWithEmptyCallStack {
                            program_counter: self.program_counter,
                        })?;

                was_control_flow_instr = true;
            }
            Instruction::CallMachineSubroutine { .. } => {
                if !self.skipping.should_skip_call_machine_subroutine() {
                    return Err(ProcessorError::CallMachineSubroutineUnsupported {
                        program_counter: self.program_counter,
                    });
                }
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
                self.set_register(target_register, res);
                self.set_register(DataRegister::VF, carry as u8);
            }
            Instruction::SubAssign {
                target_register,
                source_register,
            } => {
                let (res, borrow) = self
                    .get_register(target_register)
                    .overflowing_sub(self.get_register(source_register));
                self.set_register(target_register, res);
                self.set_register(DataRegister::VF, 1 - borrow as u8);
            }
            Instruction::ShrAssign {
                target_register,
                source_register,
            } => {
                let old_lsb = self.get_register(source_register) & 0b1;
                self.set_register(target_register, self.get_register(source_register) >> 1);
                self.set_register(DataRegister::VF, old_lsb);
            }
            Instruction::RevSubAssign {
                target_register,
                source_register,
            } => {
                let (res, borrow) = self
                    .get_register(source_register)
                    .overflowing_sub(self.get_register(target_register));
                self.set_register(target_register, res);
                self.set_register(DataRegister::VF, 1 - borrow as u8);
            }
            Instruction::ShlAssign {
                target_register,
                source_register,
            } => {
                let old_msb = (self.get_register(source_register) >> 7) & 0b1;
                self.set_register(target_register, self.get_register(source_register) << 1);
                self.set_register(DataRegister::VF, old_msb);
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
                sprite_byte_len,
            } => {
                if self.address_register > Self::MAX_ADDRESS - u8::from(sprite_byte_len) as u16 + 1
                {
                    return Err(ProcessorError::OutOfBoundsMemoryAccess {
                        program_counter: self.program_counter,
                    });
                }
                let x = (self.get_register(position_x_register) % Self::SCREEN_WIDTH) as usize;
                let y = (self.get_register(position_y_register) % Self::SCREEN_HEIGHT) as usize;
                let mut set_pixel_unset = false;

                for (i, sprite_byte) in self.memory[self.address_register as usize
                    ..(self.address_register as usize + u8::from(sprite_byte_len) as usize)]
                    .iter()
                    .copied()
                    .enumerate()
                {
                    // Wrap y if we should, else we're done for the entire sprite.
                    let y = if y + i < Self::SCREEN_HEIGHT as usize
                        || (y + i >= Self::SCREEN_HEIGHT as usize
                            && self.partial_offscreen_drawing.should_wrap_y())
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
                            && !self.partial_offscreen_drawing.should_wrap_x())
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

                screen_updated = true;
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
                // actual waiting is done by the caller of step()
                // and is signaled by the instruction_timing of the StepOutcome
            }
            Instruction::SetDelayTimer { source_register } => {
                self.delay_timer = self.get_register(source_register);

                delay_timer_updated = true;
            }
            Instruction::SetSoundTimer { source_register } => {
                self.sound_timer = self.get_register(source_register);

                sound_timer_updated = true;
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
                if self.address_register > Self::MAX_ADDRESS - 2 as u16 {
                    return Err(ProcessorError::OutOfBoundsMemoryAccess {
                        program_counter: self.program_counter,
                    });
                }

                let val = self.get_register(source_register);

                self.memory[self.address_register as usize..=(self.address_register as usize + 2)]
                    .copy_from_slice(&Self::decimal_digits_of_u8(val));
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

        Ok(StepOutcome {
            instruction_timing: self.instruction_timing(instruction),
            screen_updated,
            sound_timer_updated,
            delay_timer_updated,
        })
    }

    /// Return the average total amount of time an instruction should take,
    /// or an event to wait for.
    /// See [`InstructionTiming`].
    ///
    /// If an instruction is unsupported or would produce an error,
    /// a Duration of 0µs is returned.
    ///
    /// Information taken from
    /// <https://jackson-s.me/2019/07/13/Chip-8-Instruction-Scheduling-and-Frequency.html>
    /// ([archived](https://web.archive.org/web/20210626163444/https://jackson-s.me/2019/07/13/Chip-8-Instruction-Scheduling-and-Frequency.html))
    /// and also
    /// <https://web.archive.org/web/20170224084655/http://laurencescotford.co.uk/?p=405>
    /// from which the former source derives its information.
    fn instruction_timing(&self, instruction: Instruction) -> InstructionTiming {
        match instruction {
            Instruction::CallMachineSubroutine { .. } => Duration::from_micros(0).into(), // unsupported
            Instruction::ClearDisplay => Duration::from_micros(109).into(),
            Instruction::Return
            | Instruction::Jump { .. }
            | Instruction::CallSubroutine { .. }
            | Instruction::JumpOffset { .. } => {
                Duration::from_micros(105).into() // ignores page boundaries of original chip
            }
            Instruction::SkipIfEqConst { register, constant } => {
                if self.get_register(register) == constant {
                    Duration::from_micros(55 - 9)
                } else {
                    Duration::from_micros(55 + 9)
                }
                .into()
            }
            Instruction::SkipIfNeqConst { register, constant } => {
                if self.get_register(register) != constant {
                    Duration::from_micros(55 - 9)
                } else {
                    Duration::from_micros(55 + 9)
                }
                .into()
            }
            Instruction::SkipIfEq {
                register1,
                register2,
            } => if self.get_register(register1) == self.get_register(register2) {
                Duration::from_micros(73 - 9)
            } else {
                Duration::from_micros(73 + 9)
            }
            .into(),
            Instruction::SkipIfNeq {
                register1,
                register2,
            } => if self.get_register(register1) != self.get_register(register2) {
                Duration::from_micros(73 - 9)
            } else {
                Duration::from_micros(73 + 9)
            }
            .into(),
            Instruction::SkipIfKeyPressed { key_register } => {
                let key_id = self.get_register(key_register);
                if let Ok(key) = Key::try_from(key_id) {
                    if self.get_key_state(key) == KeyState::Pressed {
                        Duration::from_micros(73 - 9)
                    } else {
                        Duration::from_micros(73 + 9)
                    }
                } else {
                    Duration::from_micros(0)
                }
                .into()
            }
            Instruction::SkipIfKeyNotPressed { key_register } => {
                let key_id = self.get_register(key_register);
                if let Ok(key) = Key::try_from(key_id) {
                    if self.get_key_state(key) == KeyState::NotPressed {
                        Duration::from_micros(73 - 9)
                    } else {
                        Duration::from_micros(73 + 9)
                    }
                } else {
                    Duration::from_micros(0)
                }
                .into()
            }
            Instruction::AssignConst { .. } => Duration::from_micros(27).into(),
            Instruction::AddAssignConst { .. }
            | Instruction::AssignDelayTimerVal { .. }
            | Instruction::SetDelayTimer { .. }
            | Instruction::SetSoundTimer { .. } => Duration::from_micros(45).into(),
            Instruction::Assign { .. }
            | Instruction::OrAssign { .. }
            | Instruction::AndAssign { .. }
            | Instruction::XorAssign { .. }
            | Instruction::AddAssign { .. }
            | Instruction::SubAssign { .. }
            | Instruction::ShrAssign { .. }
            | Instruction::RevSubAssign { .. }
            | Instruction::ShlAssign { .. } => Duration::from_micros(200).into(),
            Instruction::AssignAddrToI { .. } => Duration::from_micros(55).into(),
            Instruction::AssignRandomMasked { .. } => Duration::from_micros(164).into(),
            Instruction::DrawSprite { .. } => Duration::from_micros(22_734).into(), // ignores intricacies, simply the average time
            Instruction::WaitForKeyPress { .. } => InstructionTiming::WaitForKeyPress,
            Instruction::AddAssignI { .. } => Duration::from_micros(86).into(), // ignores page boundaries of original chip
            Instruction::AssignHexCharSpriteAddrToI { .. } => Duration::from_micros(91).into(),
            Instruction::StoreBCD { source_register } => {
                let val = self.get_register(source_register);
                let digit_sum = Self::decimal_digits_of_u8(val).iter().sum::<u8>() as u64;
                Duration::from_micros(364 + digit_sum * 73).into()
            }
            Instruction::StoreRegisterValues { last_register }
            | Instruction::LoadRegisterValues { last_register } => {
                let num_registers = last_register as u8 + 1;
                Duration::from_micros(605 + num_registers as u64 * 64).into()
            }
        }
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
                skipping: Skipping::default(),
            },
            font: Font::default(),
        }
    }

    // TODO: consider taking an iterator as input
    /// Copies the program into the processors memory
    /// in such that the first byte is at address 0x200.
    pub fn program(mut self, program: &[u8]) -> Result<Self, ProcessorBuilderError> {
        if program.len() > Processor::MAX_USABLE_MEMORY_LEN - 0x200 {
            return Err(ProcessorBuilderError::ProgramExceedsUsableMemoryLen {
                program_len: program.len(),
            });
        }

        self.processor.memory[0x200..(0x200 + program.len())].copy_from_slice(&program);

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

    /// Set the processor's skipping behavior of unsupported instructions.
    /// Unsupported instructions that are not skipped cause an error to be returned.
    /// See also [`Skipping`].
    pub fn skipping(mut self, skipping: Skipping) -> Self {
        self.processor.skipping = skipping;
        self
    }

    pub fn build(mut self) -> Processor {
        self.processor.memory[0..Font::LEN].copy_from_slice(self.font.bytes());
        self.processor
    }
}
