use super::*;

mod step {
    use super::*;
    use crate::nibble_ints::{U12, U4};

    #[test]
    fn oob_program_counter() {
        let mut processor = Processor {
            // The program counter is set to the last address of the memory.
            // An instruction is two bytes wide, so the second byte is OOB.
            program_counter: (Processor::MAX_USABLE_MEMORY_LEN - 1) as u16,
            ..Processor::default()
        };

        assert_eq!(
            processor.step(),
            Err(ProcessorError::OutOfBoundsMemoryAccess {
                program_counter: (Processor::MAX_USABLE_MEMORY_LEN - 1) as u16
            }) as Result<InstructionTiming, _>
        );
    }

    macro_rules! callstack {
        ($($val:expr),*$(,)?) => {
            {
                let vec = vec![$($val),*];
                CallStack {
                    vec,
                    ..CallStack::default()
                }
            }
        };
    }

    mod instr_call_machine_subroutine {
        use super::*;

        #[test]
        fn case_skip() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::CallMachineSubroutine {
                target_address: U12::try_from(0x000).unwrap(),
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let mut processor = Processor {
                memory: program.clone(),
                program_counter: 0x200,
                skip_call_machine_subroutine: true,
                ..Processor::default()
            };

            processor.step().unwrap();

            assert_eq!(
                processor,
                Processor {
                    memory: program,
                    program_counter: 0x202,
                    skip_call_machine_subroutine: true,
                    ..Processor::default()
                }
            );
        }

        #[test]
        fn case_err() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::CallMachineSubroutine {
                target_address: U12::try_from(0x000).unwrap(),
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let mut processor = Processor {
                memory: program.clone(),
                program_counter: 0x200,
                skip_call_machine_subroutine: false,
                ..Processor::default()
            };

            assert_eq!(
                processor.step(),
                Err(ProcessorError::CallMachineSubroutineUnsupported {
                    program_counter: 0x200
                }) as Result<InstructionTiming, _>
            );
        }
    }

    mod instr_return {
        use super::*;

        #[test]
        fn case_ok() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::Return);
            program[0x204..=0x205].copy_from_slice(&instruction_bytes);

            let mut processor = Processor {
                memory: program.clone(),
                program_counter: 0x204,
                call_stack: callstack![0x202],
                ..Processor::default()
            };

            processor.step().unwrap();

            assert_eq!(
                processor,
                Processor {
                    memory: program,
                    program_counter: 0x202,
                    ..Processor::default()
                }
            );
        }

        #[test]
        fn case_err() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::Return);
            program[0x204..=0x205].copy_from_slice(&instruction_bytes);

            let mut processor = Processor {
                memory: program.clone(),
                program_counter: 0x204,
                ..Processor::default()
            };

            assert_eq!(
                processor.step(),
                Err(ProcessorError::ReturnWithEmptyCallStack {
                    program_counter: 0x204
                }) as Result<InstructionTiming, _>
            );
        }
    }

    #[test]
    fn instr_jump() {
        let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
        let instruction_bytes = <[u8; 2]>::from(Instruction::Jump {
            target_address: U12::try_from(0x420).unwrap(),
        });
        program[0x200..=0x201].copy_from_slice(&instruction_bytes);

        let mut processor = Processor {
            memory: program.clone(),
            ..Processor::default()
        };

        processor.step().unwrap();

        assert_eq!(
            processor,
            Processor {
                memory: program,
                program_counter: 0x420,
                ..Processor::default()
            }
        );
    }

    mod instr_call_subroutine {
        use super::*;

        #[test]
        fn case_ok() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::CallSubroutine {
                target_address: U12::try_from(0x208).unwrap(),
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let mut processor = Processor {
                memory: program.clone(),
                ..Processor::default()
            };

            processor.step().unwrap();

            assert_eq!(
                processor,
                Processor {
                    memory: program,
                    program_counter: 0x208,
                    call_stack: callstack![0x202],
                    ..Processor::default()
                }
            );
        }

        #[test]
        fn case_err() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::CallSubroutine {
                target_address: U12::try_from(0x208).unwrap(),
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let mut processor = Processor {
                memory: program.clone(),
                call_stack: CallStack::new_with_max_len(0),
                ..Processor::default()
            };

            assert_eq!(
                processor.step(),
                Err(ProcessorError::MaxCallStackSizeExceeded {
                    program_counter: 0x200,
                }) as Result<InstructionTiming, _>,
            );
        }
    }

    mod instrs_skip_if {
        use super::*;

        macro_rules! generate_instr {
            ($instr_name:ident, with_const) => {
                Instruction::$instr_name {
                    register: DataRegister::V3,
                    constant: 0,
                }
            };
            ($instr_name:ident, with_register) => {
                Instruction::$instr_name {
                    register1: DataRegister::V3,
                    register2: DataRegister::V5,
                }
            };
        }

        macro_rules! generate_test {
            ($mod_name:ident, $instr_name:ident, is_eq: $is_eq:literal, $const_str:ident) => {
                mod $mod_name {
                    use super::*;

                    #[test]
                    fn case_neq() {
                        let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
                        let instruction_bytes =
                            <[u8; 2]>::from(generate_instr!($instr_name, $const_str));
                        program[0x200..=0x201].copy_from_slice(&instruction_bytes);

                        let mut data_registers = [0; 16];
                        data_registers[DataRegister::V3 as u8 as usize] = 0x2A;

                        let mut processor = Processor {
                            data_registers,
                            memory: program.clone(),
                            ..Processor::default()
                        };

                        processor.step().unwrap();

                        assert_eq!(
                            processor,
                            Processor {
                                data_registers,
                                memory: program,
                                program_counter: if $is_eq { 0x202 } else { 0x204 },
                                ..Processor::default()
                            }
                        );
                    }

                    #[test]
                    fn case_eq() {
                        let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
                        let instruction_bytes =
                            <[u8; 2]>::from(generate_instr!($instr_name, $const_str));
                        program[0x200..=0x201].copy_from_slice(&instruction_bytes);

                        let mut processor = Processor {
                            memory: program.clone(),
                            ..Processor::default()
                        };

                        processor.step().unwrap();

                        assert_eq!(
                            processor,
                            Processor {
                                memory: program,
                                program_counter: if $is_eq { 0x204 } else { 0x202 },
                                ..Processor::default()
                            }
                        );
                    }
                }
            };
        }

        generate_test!(eq_const, SkipIfEqConst, is_eq: true, with_const);
        generate_test!(neq_const, SkipIfNeqConst, is_eq: false, with_const);
        generate_test!(eq, SkipIfEq, is_eq: true, with_register);
        generate_test!(neq, SkipIfNeq, is_eq: false, with_register);
    }

    #[test]
    fn instr_assign_const() {
        let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
        let instruction_bytes = <[u8; 2]>::from(Instruction::AssignConst {
            target_register: DataRegister::V4,
            constant: 0x2A,
        });
        program[0x200..=0x201].copy_from_slice(&instruction_bytes);

        let mut processor = Processor {
            memory: program.clone(),
            ..Processor::default()
        };

        processor.step().unwrap();

        let mut expected_data_registers = [0; 16];
        expected_data_registers[DataRegister::V4 as u8 as usize] = 0x2A;

        assert_eq!(
            processor,
            Processor {
                data_registers: expected_data_registers,
                memory: program,
                program_counter: 0x202,
                ..Processor::default()
            }
        );
    }

    mod instr_add_assign_const {
        use super::*;

        #[test]
        fn case_carry() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::AddAssignConst {
                target_register: DataRegister::V4,
                constant: u8::MAX - 0x2A + 2, // cause overflow to 0x01 on addition of 0x2A
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let mut data_registers = [0; 16];
            data_registers[DataRegister::V4 as u8 as usize] = 0x2A;

            let mut processor = Processor {
                data_registers,
                memory: program.clone(),
                ..Processor::default()
            };

            processor.step().unwrap();

            let mut expected_data_registers = [0; 16];
            expected_data_registers[DataRegister::V4 as u8 as usize] = 0x01;

            // DataRegister::VF must still be 0 here

            assert_eq!(
                processor,
                Processor {
                    data_registers: expected_data_registers,
                    memory: program,
                    program_counter: 0x202,
                    ..Processor::default()
                }
            );
        }

        #[test]
        fn case_no_carry() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::AddAssignConst {
                target_register: DataRegister::V4,
                constant: 0x31,
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let mut data_registers = [0; 16];
            data_registers[DataRegister::V4 as u8 as usize] = 0x2A;

            let mut processor = Processor {
                data_registers,
                memory: program.clone(),
                ..Processor::default()
            };

            processor.step().unwrap();

            let mut expected_data_registers = [0; 16];
            expected_data_registers[DataRegister::V4 as u8 as usize] = 0x5B;

            // DataRegister::VF must still be 0 here

            assert_eq!(
                processor,
                Processor {
                    data_registers: expected_data_registers,
                    memory: program,
                    program_counter: 0x202,
                    ..Processor::default()
                }
            );
        }
    }

    #[test]
    fn instr_assign() {
        let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
        let instruction_bytes = <[u8; 2]>::from(Instruction::Assign {
            target_register: DataRegister::V4,
            source_register: DataRegister::V8,
        });
        program[0x200..=0x201].copy_from_slice(&instruction_bytes);

        let mut data_registers = [0; 16];
        data_registers[DataRegister::V8 as u8 as usize] = 0x2A;

        let mut processor = Processor {
            data_registers,
            memory: program.clone(),
            ..Processor::default()
        };

        processor.step().unwrap();

        let mut expected_data_registers = [0; 16];
        expected_data_registers[DataRegister::V4 as u8 as usize] = 0x2A;
        expected_data_registers[DataRegister::V8 as u8 as usize] = 0x2A;

        assert_eq!(
            processor,
            Processor {
                data_registers: expected_data_registers,
                memory: program,
                program_counter: 0x202,
                ..Processor::default()
            }
        );
    }

    mod instrs_op_assign {
        use super::*;

        macro_rules! generate_test {
            (
                $test_name:ident,
                $instr_name:ident,
                target_val: $target_val:expr,
                source_val: $source_val:expr,
                result: $result:expr,
                vf: $vf:literal
            ) => {
                #[test]
                fn $test_name() {
                    let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
                    let instruction_bytes = <[u8; 2]>::from(Instruction::$instr_name {
                        target_register: DataRegister::V3,
                        source_register: DataRegister::V9,
                    });
                    program[0x200..=0x201].copy_from_slice(&instruction_bytes);

                    let mut data_registers = [0; 16];
                    data_registers[DataRegister::V3 as u8 as usize] = $target_val;
                    data_registers[DataRegister::V9 as u8 as usize] = $source_val;

                    let mut processor = Processor {
                        data_registers,
                        memory: program.clone(),
                        ..Processor::default()
                    };

                    processor.step().unwrap();

                    let mut expected_data_registers = [0; 16];
                    expected_data_registers[DataRegister::V3 as u8 as usize] = $result;
                    expected_data_registers[DataRegister::V9 as u8 as usize] = $source_val;
                    expected_data_registers[DataRegister::VF as u8 as usize] = $vf;

                    assert_eq!(
                        processor,
                        Processor {
                            data_registers: expected_data_registers,
                            memory: program,
                            program_counter: 0x202,
                            ..Processor::default()
                        }
                    );
                }
            };
        }

        generate_test!(or, OrAssign, target_val: 0b10101010, source_val: 0b11001010, result: 0b11101010, vf: 0);
        generate_test!(and, AndAssign, target_val: 0b10101010, source_val: 0b11001010, result: 0b10001010, vf: 0);
        generate_test!(xor, XorAssign, target_val: 0b10101010, source_val: 0b11001010, result: 0b01100000, vf: 0);

        mod add {
            use super::*;

            generate_test!(case_carry, AddAssign, target_val: !0, source_val: 1, result: 0, vf: 1);
            generate_test!(case_no_carry, AddAssign, target_val: 3, source_val: 4, result: 7, vf: 0);
        }

        mod sub {
            use super::*;

            generate_test!(case_borrow, SubAssign, target_val: 0, source_val: 1, result: !0, vf: 0);
            generate_test!(case_no_borrow, SubAssign, target_val: 7, source_val: 3, result: 4, vf: 1);
        }

        mod rev_sub {
            use super::*;

            generate_test!(case_borrow, RevSubAssign, target_val: 1, source_val: 0, result: !0, vf: 0);
            generate_test!(case_no_borrow, RevSubAssign, target_val: 3, source_val: 7, result: 4, vf: 1);
        }

        mod shr {
            use super::*;

            generate_test!(case_old_lsb_set, ShrAssign, target_val: 0b111, source_val: 0b101, result: 0b10, vf: 1);
            generate_test!(case_old_lsb_unset, ShrAssign, target_val: 0b111, source_val: 0b100, result: 0b10, vf: 0);
        }

        mod shl {
            use super::*;

            generate_test!(case_old_msb_set, ShlAssign, target_val: 0b1110_0000, source_val: 0b1010_0000, result: 0b0100_0000, vf: 1);
            generate_test!(case_old_msb_unset, ShlAssign, target_val: 0b1110_0000, source_val: 0b0010_0000, result: 0b0100_0000, vf: 0);
        }
    }

    #[test]
    fn instr_assign_addr_to_i() {
        let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
        let instruction_bytes = <[u8; 2]>::from(Instruction::AssignAddrToI {
            address: U12::try_from(1337).unwrap(),
        });
        program[0x200..=0x201].copy_from_slice(&instruction_bytes);

        let mut processor = Processor {
            memory: program.clone(),
            ..Processor::default()
        };

        processor.step().unwrap();

        assert_eq!(
            processor,
            Processor {
                address_register: 1337,
                memory: program,
                program_counter: 0x202,
                ..Processor::default()
            }
        );
    }

    #[test]
    fn instr_jump_offset() {
        let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
        let instruction_bytes = <[u8; 2]>::from(Instruction::JumpOffset {
            address: U12::try_from(1337).unwrap(),
        });
        program[0x200..=0x201].copy_from_slice(&instruction_bytes);

        let mut data_registers = [0; 16];
        data_registers[DataRegister::V0 as u8 as usize] = 42;

        let mut processor = Processor {
            data_registers,
            memory: program.clone(),
            ..Processor::default()
        };

        processor.step().unwrap();

        assert_eq!(
            processor,
            Processor {
                data_registers,
                memory: program,
                program_counter: 1337 + 42,
                ..Processor::default()
            }
        );
    }

    // TODO: figure out a good way to unit test Instruction::AssignRandomMasked

    mod instr_draw_sprite {
        use super::*;

        #[rustfmt::skip]
        const INITIAL_SCREEN: [u8; Processor::SCREEN_WIDTH_BYTES as usize
            * Processor::SCREEN_HEIGHT as usize] = [
            0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
            0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
        ];

        /// 8x8 sprite with 2x1 checkered pattern
        const SPRITE_BYTES: [u8; 8] = [
            0b1100_1100,
            0b0011_0011,
            0b1100_1100,
            0b0011_0011,
            0b1100_1100,
            0b0011_0011,
            0b1100_1100,
            0b0011_0011,
        ];

        #[test]
        fn case_clip_xy() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::DrawSprite {
                position_x_register: DataRegister::V0,
                position_y_register: DataRegister::V1,
                last_sprite_byte_offset: U4::try_from(7).unwrap(), // 8x8 sprite
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);
            program[0x300..=0x307].copy_from_slice(&SPRITE_BYTES);

            // Set positions to lower right corner of screen (after modulo),
            // with the sprite half offscreen in both dimensions.
            let mut data_registers = [0; 16];
            data_registers[DataRegister::V0 as u8 as usize] = 2 * Processor::SCREEN_WIDTH - 4;
            data_registers[DataRegister::V1 as u8 as usize] = 2 * Processor::SCREEN_HEIGHT - 4;

            let mut processor = Processor {
                data_registers,
                address_register: 0x300,
                memory: program,
                screen: INITIAL_SCREEN.clone(),
                partial_offscreen_drawing: PartialOffscreenDrawing::ClipXY,
                ..Processor::default()
            };

            processor.step().unwrap();

            let mut expected_data_registers = data_registers.clone();
            expected_data_registers[DataRegister::VF as u8 as usize] = 0; // pixels in upper left corner were *not* unset

            assert_eq!(
                processor,
                Processor {
                    data_registers: expected_data_registers,
                    address_register: 0x300,
                    memory: program,
                    program_counter: 0x202,
                    #[rustfmt::skip]
                    screen: [
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_1100,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0011,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_1100,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0011,
                    ],
                    partial_offscreen_drawing: PartialOffscreenDrawing::ClipXY,
                    ..Processor::default()
                },
            );
        }

        #[test]
        fn case_clip_x_wrap_y() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::DrawSprite {
                position_x_register: DataRegister::V0,
                position_y_register: DataRegister::V1,
                last_sprite_byte_offset: U4::try_from(7).unwrap(), // 8x8 sprite
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);
            program[0x300..=0x307].copy_from_slice(&SPRITE_BYTES);

            // Set positions to lower right corner of screen (after modulo),
            // with the sprite half offscreen in both dimensions.
            let mut data_registers = [0; 16];
            data_registers[DataRegister::V0 as u8 as usize] = 2 * Processor::SCREEN_WIDTH - 4;
            data_registers[DataRegister::V1 as u8 as usize] = 2 * Processor::SCREEN_HEIGHT - 4;

            let mut processor = Processor {
                data_registers,
                address_register: 0x300,
                memory: program,
                screen: INITIAL_SCREEN.clone(),
                partial_offscreen_drawing: PartialOffscreenDrawing::ClipXWrapY,
                ..Processor::default()
            };

            processor.step().unwrap();

            let mut expected_data_registers = data_registers.clone();
            expected_data_registers[DataRegister::VF as u8 as usize] = 0; // pixels in upper left corner were *not* unset

            assert_eq!(
                processor,
                Processor {
                    data_registers: expected_data_registers,
                    address_register: 0x300,
                    memory: program,
                    program_counter: 0x202,
                    #[rustfmt::skip]
                    screen: [
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_1100,
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0011,
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_1100,
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0011,
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_1100,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0011,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_1100,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0011,
                    ],
                    partial_offscreen_drawing: PartialOffscreenDrawing::ClipXWrapY,
                    ..Processor::default()
                },
            );
        }

        #[test]
        fn case_wrap_x_clip_y() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::DrawSprite {
                position_x_register: DataRegister::V0,
                position_y_register: DataRegister::V1,
                last_sprite_byte_offset: U4::try_from(7).unwrap(), // 8x8 sprite
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);
            program[0x300..=0x307].copy_from_slice(&SPRITE_BYTES);

            // Set positions to lower right corner of screen (after modulo),
            // with the sprite half offscreen in both dimensions.
            let mut data_registers = [0; 16];
            data_registers[DataRegister::V0 as u8 as usize] = 2 * Processor::SCREEN_WIDTH - 4;
            data_registers[DataRegister::V1 as u8 as usize] = 2 * Processor::SCREEN_HEIGHT - 4;

            let mut processor = Processor {
                data_registers,
                address_register: 0x300,
                memory: program,
                screen: INITIAL_SCREEN.clone(),
                partial_offscreen_drawing: PartialOffscreenDrawing::WrapXClipY,
                ..Processor::default()
            };

            processor.step().unwrap();

            let mut expected_data_registers = data_registers.clone();
            expected_data_registers[DataRegister::VF as u8 as usize] = 0; // pixels in upper left corner were *not* unset

            assert_eq!(
                processor,
                Processor {
                    data_registers: expected_data_registers,
                    address_register: 0x300,
                    memory: program,
                    program_counter: 0x202,
                    #[rustfmt::skip]
                    screen: [
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b1100_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_1100,
                        0b0011_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0011,
                        0b1100_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_1100,
                        0b0011_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0011,
                    ],
                    partial_offscreen_drawing: PartialOffscreenDrawing::WrapXClipY,
                    ..Processor::default()
                },
            );
        }

        #[test]
        fn case_wrap_xy() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::DrawSprite {
                position_x_register: DataRegister::V0,
                position_y_register: DataRegister::V1,
                last_sprite_byte_offset: U4::try_from(7).unwrap(), // 8x8 sprite
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);
            program[0x300..=0x307].copy_from_slice(&SPRITE_BYTES);

            // Set positions to lower right corner of screen (after modulo),
            // with the sprite half offscreen in both dimensions.
            let mut data_registers = [0; 16];
            data_registers[DataRegister::V0 as u8 as usize] = 2 * Processor::SCREEN_WIDTH - 4;
            data_registers[DataRegister::V1 as u8 as usize] = 2 * Processor::SCREEN_HEIGHT - 4;

            let mut processor = Processor {
                data_registers,
                address_register: 0x300,
                memory: program,
                screen: INITIAL_SCREEN.clone(),
                partial_offscreen_drawing: PartialOffscreenDrawing::WrapXY,
                ..Processor::default()
            };

            processor.step().unwrap();

            let mut expected_data_registers = data_registers.clone();
            expected_data_registers[DataRegister::VF as u8 as usize] = 1; // pixels in upper left corner *were* unset

            assert_eq!(
                processor,
                Processor {
                    data_registers: expected_data_registers,
                    address_register: 0x300,
                    memory: program,
                    program_counter: 0x202,
                    #[rustfmt::skip]
                    screen: [
                        0b0011_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_1100,
                        0b1100_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0011,
                        0b0011_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_1100,
                        0b1100_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0011,
                        0b1111_1000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000,
                        0b1100_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_1100,
                        0b0011_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0011,
                        0b1100_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_1100,
                        0b0011_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0000, 0b0000_0011,
                    ],
                    partial_offscreen_drawing: PartialOffscreenDrawing::WrapXY,
                    ..Processor::default()
                },
            );
        }

        #[test]
        fn case_out_of_bounds() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::DrawSprite {
                position_x_register: DataRegister::V0,
                position_y_register: DataRegister::V1,
                last_sprite_byte_offset: U4::try_from(1).unwrap(),
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let data_registers = [0; 16];

            let mut processor = Processor {
                data_registers,
                address_register: u16::MAX, // make the load of the last sprite byte an OOB access
                memory: program,
                ..Processor::default()
            };

            assert_eq!(
                processor.step(),
                Err(ProcessorError::OutOfBoundsMemoryAccess {
                    program_counter: 0x200
                }) as Result<InstructionTiming, _>
            );
        }
    }

    mod instrs_skip_if_key {
        use super::*;

        macro_rules! generate_test {
            ($mod_name:ident, $instr_name:ident, negated: $negated:literal) => {
                mod $mod_name {
                    use super::*;

                    #[test]
                    fn case_not_pressed() {
                        let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
                        let instruction_bytes = <[u8; 2]>::from(Instruction::$instr_name {
                            key_register: DataRegister::V3,
                        });
                        program[0x200..=0x201].copy_from_slice(&instruction_bytes);

                        let mut data_registers = [0; 16];
                        data_registers[DataRegister::V3 as u8 as usize] = 0x0B;

                        let mut processor = Processor {
                            data_registers,
                            memory: program.clone(),
                            ..Processor::default()
                        };

                        processor.step().unwrap();

                        assert_eq!(
                            processor,
                            Processor {
                                data_registers,
                                memory: program,
                                program_counter: if $negated { 0x204 } else { 0x202 },
                                ..Processor::default()
                            }
                        );
                    }

                    #[test]
                    fn case_pressed() {
                        let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
                        let instruction_bytes = <[u8; 2]>::from(Instruction::$instr_name {
                            key_register: DataRegister::V3,
                        });
                        program[0x200..=0x201].copy_from_slice(&instruction_bytes);

                        let mut data_registers = [0; 16];
                        data_registers[DataRegister::V3 as u8 as usize] = Key::KB as u8;

                        let mut key_states = [KeyState::NotPressed; 16];
                        key_states[Key::KB as u8 as usize] = KeyState::Pressed;

                        let mut processor = Processor {
                            data_registers,
                            memory: program.clone(),
                            key_states: key_states,
                            ..Processor::default()
                        };

                        processor.step().unwrap();

                        assert_eq!(
                            processor,
                            Processor {
                                data_registers,
                                memory: program,
                                program_counter: if $negated { 0x202 } else { 0x204 },
                                key_states: key_states,
                                ..Processor::default()
                            }
                        );
                    }

                    #[test]
                    fn case_not_a_valid_key() {
                        let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
                        let instruction_bytes = <[u8; 2]>::from(Instruction::$instr_name {
                            key_register: DataRegister::V3,
                        });
                        program[0x200..=0x201].copy_from_slice(&instruction_bytes);

                        let mut data_registers = [0; 16];
                        data_registers[DataRegister::V3 as u8 as usize] = 0x10;

                        let mut processor = Processor {
                            data_registers,
                            memory: program.clone(),
                            ..Processor::default()
                        };

                        assert_eq!(
                            processor.step(),
                            Err(ProcessorError::NotAValidKey {
                                program_counter: 0x200,
                                requested_key_id: 0x10,
                            })
                        );
                    }
                }
            };
        }

        generate_test!(pressed, SkipIfKeyPressed, negated: false);
        generate_test!(not_pressed, SkipIfKeyNotPressed, negated: true);
    }

    #[test]
    fn instr_assign_delay_timer_val() {
        let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
        let instruction_bytes = <[u8; 2]>::from(Instruction::AssignDelayTimerVal {
            target_register: DataRegister::V4,
        });
        program[0x200..=0x201].copy_from_slice(&instruction_bytes);

        let mut processor = Processor {
            memory: program.clone(),
            delay_timer: 0x2A,
            ..Processor::default()
        };

        processor.step().unwrap();

        let mut expected_data_registers = [0; 16];
        expected_data_registers[DataRegister::V4 as u8 as usize] = 0x2A;

        assert_eq!(
            processor,
            Processor {
                data_registers: expected_data_registers,
                memory: program,
                program_counter: 0x202,
                delay_timer: 0x2A,
                ..Processor::default()
            }
        );
    }

    #[test]
    fn instr_set_delay_timer() {
        let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
        let instruction_bytes = <[u8; 2]>::from(Instruction::SetDelayTimer {
            source_register: DataRegister::V8,
        });
        program[0x200..=0x201].copy_from_slice(&instruction_bytes);

        let mut data_registers = [0; 16];
        data_registers[DataRegister::V8 as u8 as usize] = 0x2A;

        let mut processor = Processor {
            data_registers,
            memory: program.clone(),
            ..Processor::default()
        };

        processor.step().unwrap();

        assert_eq!(
            processor,
            Processor {
                data_registers,
                memory: program,
                program_counter: 0x202,
                delay_timer: 0x2A,
                ..Processor::default()
            }
        );
    }

    #[test]
    fn instr_set_sound_timer() {
        let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
        let instruction_bytes = <[u8; 2]>::from(Instruction::SetSoundTimer {
            source_register: DataRegister::V8,
        });
        program[0x200..=0x201].copy_from_slice(&instruction_bytes);

        let mut data_registers = [0; 16];
        data_registers[DataRegister::V8 as u8 as usize] = 0x2A;

        let mut processor = Processor {
            data_registers,
            memory: program.clone(),
            ..Processor::default()
        };

        processor.step().unwrap();

        assert_eq!(
            processor,
            Processor {
                data_registers,
                memory: program,
                program_counter: 0x202,
                sound_timer: 0x2A,
                ..Processor::default()
            }
        );
    }

    mod instr_add_assign_i {
        use super::*;

        #[test]
        fn case_carry() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::AddAssignI {
                source_register: DataRegister::V0,
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let mut data_registers = [0; 16];
            data_registers[DataRegister::V0 as u8 as usize] = 0x2A;

            let mut processor = Processor {
                data_registers,
                address_register: u16::MAX - 0x2A + 2, // cause overflow to 0x01 on addition of 0x2A
                memory: program.clone(),
                ..Processor::default()
            };

            processor.step().unwrap();

            // DataRegister::VF must still be 0 here

            assert_eq!(
                processor,
                Processor {
                    data_registers,
                    address_register: 0x01,
                    memory: program,
                    program_counter: 0x202,
                    ..Processor::default()
                }
            );
        }

        #[test]
        fn case_no_carry() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::AddAssignI {
                source_register: DataRegister::V0,
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let mut data_registers = [0; 16];
            data_registers[DataRegister::V0 as u8 as usize] = 0x2A;

            let mut processor = Processor {
                data_registers,
                address_register: 0x31,
                memory: program.clone(),
                ..Processor::default()
            };

            processor.step().unwrap();

            // DataRegister::VF must still be 0 here

            assert_eq!(
                processor,
                Processor {
                    data_registers,
                    address_register: 0x5B,
                    memory: program,
                    program_counter: 0x202,
                    ..Processor::default()
                }
            );
        }
    }

    mod instr_assign_hex_char_sprite_addr_to_i {
        use super::*;

        #[test]
        fn case_ok() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::AssignHexCharSpriteAddrToI {
                hex_char_register: DataRegister::V3,
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let mut data_registers = [0; 16];
            data_registers[DataRegister::V3 as u8 as usize] = 0xB;

            let mut processor = Processor {
                data_registers,
                memory: program.clone(),
                ..Processor::default()
            };

            processor.step().unwrap();

            assert_eq!(
                processor,
                Processor {
                    data_registers,
                    // Hex char sprites start at 0x0 in self.memory and are each 5 bytes in length
                    address_register: 0xB * 5,
                    memory: program,
                    program_counter: 0x202,
                    ..Processor::default()
                }
            );
        }

        #[test]
        fn case_err() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::AssignHexCharSpriteAddrToI {
                hex_char_register: DataRegister::V3,
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let mut data_registers = [0; 16];
            data_registers[DataRegister::V3 as u8 as usize] = 0xF2;

            let mut processor = Processor {
                data_registers,
                memory: program.clone(),
                ..Processor::default()
            };

            assert_eq!(
                processor.step(),
                Err(ProcessorError::NotAHexChar {
                    program_counter: 0x200,
                    requested_sprite_id: 0xF2,
                })
            );
        }
    }

    mod instr_store_bcd {
        use super::*;

        #[test]
        fn case_ok() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::StoreBCD {
                source_register: DataRegister::V0,
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let mut data_registers = [0; 16];
            data_registers[DataRegister::V0 as u8 as usize] = 123;

            let mut processor = Processor {
                data_registers,
                address_register: Processor::MAX_ADDRESS - 2,
                memory: program.clone(),
                ..Processor::default()
            };

            processor.step().unwrap();

            let mut expected_memory = program;
            expected_memory[Processor::MAX_ADDRESS as usize - 2] = 1;
            expected_memory[Processor::MAX_ADDRESS as usize - 1] = 2;
            expected_memory[Processor::MAX_ADDRESS as usize] = 3;

            assert_eq!(
                processor,
                Processor {
                    data_registers,
                    address_register: Processor::MAX_ADDRESS - 2,
                    memory: expected_memory,
                    program_counter: 0x202,
                    ..Processor::default()
                }
            );
        }

        #[test]
        fn case_err() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::StoreBCD {
                source_register: DataRegister::V0,
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let mut data_registers = [0; 16];
            data_registers[DataRegister::V0 as u8 as usize] = 123;

            let mut processor = Processor {
                data_registers,
                address_register: Processor::MAX_ADDRESS - 1,
                memory: program.clone(),
                ..Processor::default()
            };

            assert_eq!(
                processor.step(),
                Err(ProcessorError::OutOfBoundsMemoryAccess {
                    program_counter: 0x200
                }),
            );
        }
    }

    mod instr_store_register_values {
        use super::*;

        #[test]
        fn case_ok() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::StoreRegisterValues {
                last_register: DataRegister::V8,
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let mut data_registers = [0; 16];
            for (i, reg) in data_registers.iter_mut().enumerate() {
                *reg = i as u8;
            }

            let mut processor = Processor {
                data_registers,
                address_register: u16::MAX - 8,
                memory: program.clone(),
                ..Processor::default()
            };

            let mut expected_memory = program;
            for i in 0x0..=0x8 {
                expected_memory[u16::MAX as usize - 8 + i] = i as u8;
            }

            processor.step().unwrap();

            assert_eq!(
                processor,
                Processor {
                    data_registers,
                    address_register: 0, // (u16::MAX - 8) + 8 + 1
                    memory: expected_memory,
                    program_counter: 0x202,
                    ..Processor::default()
                }
            );
        }

        #[test]
        fn case_err() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::StoreRegisterValues {
                last_register: DataRegister::V8,
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let mut data_registers = [0; 16];
            for (i, reg) in data_registers.iter_mut().enumerate() {
                *reg = i as u8;
            }

            let mut processor = Processor {
                data_registers,
                address_register: u16::MAX - (8 - 1), // make the store of the last register an OOB access
                memory: program,
                ..Processor::default()
            };

            assert_eq!(
                processor.step(),
                Err(ProcessorError::OutOfBoundsMemoryAccess {
                    program_counter: 0x200
                }) as Result<InstructionTiming, _>
            );
        }
    }

    mod instr_load_register_values {
        use super::*;

        #[test]
        fn case_ok() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::LoadRegisterValues {
                last_register: DataRegister::V8,
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);
            for i in 0x0..=0x8 {
                program[u16::MAX as usize - 8 + i] = i as u8;
            }

            let data_registers = [0; 16];

            let mut processor = Processor {
                data_registers,
                address_register: u16::MAX - 8,
                memory: program.clone(),
                ..Processor::default()
            };

            let mut expected_data_registers = [0; 16];
            for i in 0x0..=0x8 {
                expected_data_registers[i] = i as u8;
            }

            processor.step().unwrap();

            assert_eq!(
                processor,
                Processor {
                    data_registers: expected_data_registers,
                    address_register: 0, // (u16::MAX - 8) + 8 + 1
                    memory: program,
                    program_counter: 0x202,
                    ..Processor::default()
                }
            );
        }

        #[test]
        fn case_err() {
            let mut program = [0; Processor::MAX_USABLE_MEMORY_LEN];
            let instruction_bytes = <[u8; 2]>::from(Instruction::LoadRegisterValues {
                last_register: DataRegister::V8,
            });
            program[0x200..=0x201].copy_from_slice(&instruction_bytes);

            let data_registers = [0; 16];

            let mut processor = Processor {
                data_registers,
                address_register: u16::MAX - (8 - 1), // make the store of the last register an OOB access
                memory: program,
                ..Processor::default()
            };

            assert_eq!(
                processor.step(),
                Err(ProcessorError::OutOfBoundsMemoryAccess {
                    program_counter: 0x200
                }) as Result<InstructionTiming, _>
            );
        }
    }
}
