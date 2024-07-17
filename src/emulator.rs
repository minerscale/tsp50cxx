//! # Emulator
//!
//! This software is based on the TSP50C0X/1X spec from https://www.ti.com/lit/ml/spss011d/spss011d.pdf

#![allow(dead_code)]
#![allow(clippy::upper_case_acronyms)]

use arbitrary_int::{u12, u14};
use bitflags::bitflags;
use std::{
    fmt::{self, Debug},
    ops::{Index, IndexMut},
};

use crate::{
    instruction::{Instruction, I},
    uninit::Uninit,
};

bitflags! {
    #[derive(Debug, Default, Copy, Clone, PartialEq)]
    struct Mode: u8 {
        const ENA1 = 0x01;
        const LPC = 0x02;
        const PCM = 0x04;
        const ENA2 = 0x08;
        const EXTROM = 0x10;
        const RAMROM = 0x20;
        const MASTER = 0x40;
        const UNV = 0x80;
    }
}

#[derive(Copy, Clone, PartialEq, Default)]
enum IntegerMode {
    #[default]
    ExtSign = 0,
    Integer = 1,
}

impl Debug for IntegerMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntegerMode::ExtSign => f.write_str("Ext"),
            IntegerMode::Integer => f.write_str("Int"),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Debug, Default)]
enum StackPointer {
    #[default]
    Bottom = 0,
    Middle = 1,
    Top = 2,
}

impl<T> Index<StackPointer> for [T] {
    type Output = T;
    fn index(&self, idx: StackPointer) -> &Self::Output {
        &self[idx as usize]
    }
}

impl<T> IndexMut<StackPointer> for [T] {
    fn index_mut(&mut self, idx: StackPointer) -> &mut Self::Output {
        &mut self[idx as usize]
    }
}

#[derive(Debug, Default)]
struct Stack {
    stack: [Uninit<u14>; 3],
    sp: StackPointer,
}

impl Stack {
    fn push(&mut self, addr: u14) {
        type S = StackPointer;

        self.sp = match self.sp {
            S::Bottom => S::Middle,
            S::Middle => S::Top,
            S::Top => {
                self.stack[S::Bottom] = self.stack[S::Middle];
                self.stack[S::Middle] = self.stack[S::Top];
                S::Top
            }
        };

        self.stack[self.sp] = Uninit::Some(addr);
    }

    fn pop(&mut self) -> u14 {
        type S = StackPointer;

        let addr = self.stack[self.sp].unwrap();
        self.sp = match self.sp {
            S::Top => S::Middle,
            S::Middle => S::Bottom,
            S::Bottom => panic!("Stack underflow!"),
        };

        addr
    }
}

trait Num<T> {
    const ZERO: T;
    const ONE: T;
}

impl Num<u14> for u14 {
    const ZERO: u14 = u14::new(0);
    const ONE: u14 = u14::new(1);
}

#[derive(Debug, PartialEq)]
enum Status {
    Continue,
    Halt,
}

#[derive(Debug, Default)]
enum Interrupt {
    #[default]
    Inactive,
    Requested,
    Active,
}

#[derive(Debug, Default)]
struct Interrupt1 {
    state: Interrupt,
    a: Uninit<u14>,
    x: Uninit<u8>,
    b: Uninit<u14>,
    status: Uninit<bool>,
    integer_mode: Uninit<IntegerMode>,
}

#[derive(Debug, Default)]
struct Interrupt2 {
    state: Interrupt,
    status: Uninit<bool>,
    integer_mode: Uninit<IntegerMode>,
}

pub struct TSP50 {
    num_cycles: usize,
    stack: Stack,
    pc: u14,
    a: Uninit<u14>,
    x: Uninit<u8>,
    b: Uninit<u14>,
    status: Uninit<bool>,
    integer_mode: Uninit<IntegerMode>,
    timer: Uninit<u8>,
    timer_prescale: Uninit<u8>,
    timer_prescale_count: Uninit<u8>,
    timer_begun: bool,
    pitch: Uninit<u14>,
    dac: Uninit<i16>,
    excitation: Uninit<u14>,
    sar: Uninit<u14>,
    ps: Uninit<u8>,
    ps_buf: Uninit<Option<u8>>,
    ps_bits_left: Uninit<u8>,
    mode: Mode,
    random: u16,

    interrupt_1: Interrupt1,
    interrupt_2: Interrupt2,

    synthesis_mem: [Uninit<u12>; 16],
    mem: [Uninit<u8>; 120],
    rom: [u8; 16384],
    excitation_rom: [u8; 384],
}

impl fmt::Debug for TSP50 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("pc: {:04x} | a: {:04x} | b: {:04x} | x: {:02x} | s: {:x} | mode: {:?} | stack: [{:04x}|{:04x}|{:04x}] | sp: {:3?}",
            &self.pc, &self.a.unwrap_or_default(), &self.b.unwrap_or_default(), &self.x.unwrap_or_default(), &(self.status.unwrap_or_default() as u8), &self.integer_mode, &self.stack.stack[0].unwrap_or_default(), &self.stack.stack[1].unwrap_or_default(), &self.stack.stack[2].unwrap_or_default(), &self.stack.sp))
    }
}

impl Default for TSP50 {
    fn default() -> Self {
        TSP50 {
            pc: Default::default(),
            stack: Default::default(),
            interrupt_1: Default::default(),
            interrupt_2: Default::default(),
            a: Default::default(),
            x: Default::default(),
            b: Default::default(),
            status: Default::default(),
            integer_mode: Default::default(),
            timer: Default::default(),
            timer_prescale: Default::default(),
            timer_prescale_count: Default::default(),
            timer_begun: Default::default(),
            pitch: Default::default(),
            dac: Default::default(),
            excitation: Default::default(),
            sar: Default::default(),
            ps: Default::default(),
            ps_buf: Default::default(),
            ps_bits_left: Default::default(),
            mode: Default::default(),
            random: Default::default(),
            num_cycles: Default::default(),
            synthesis_mem: [Default::default(); 16],
            mem: [Default::default(); 120],
            rom: [Default::default(); 16384],
            excitation_rom: [Default::default(); 384],
        }
    }
}

impl TSP50 {
    pub fn new() -> TSP50 {
        Default::default()
    }

    pub fn run(&mut self) {
        while self.step() == Status::Continue {
            println!("{:?}", self);
        }
    }

    pub fn rom_mut(&mut self) -> &mut [u8] {
        return &mut self.rom;
    }

    pub fn rom(&mut self) -> &[u8] {
        return &self.rom;
    }

    fn handle_interrupts(&mut self) {
        /* From the spec:
         * Interrupts are not taken in the middle of double-byte instructions, during
         * branch or call instructions, or during the subroutine or interrupt returns (RETN
         * or RETI).
         */
        if matches!(self.rom[self.pc.value() as usize], 0x00..=0x0f | 0x1f | 0x3d | 0x3e | 0x40..=0x5f | 0x80..)
        {
            return;
        }

        match (
            self.mode.contains(Mode::ENA1),
            &self.interrupt_1.state,
            self.mode.contains(Mode::ENA2),
            &self.interrupt_2.state,
        ) {
            // Activate interrupt-1
            (true, Interrupt::Requested, _, _) => {
                self.interrupt_1 = Interrupt1 {
                    state: Interrupt::Active,
                    a: self.a,
                    x: self.x,
                    b: self.b,
                    status: self.status,
                    integer_mode: self.integer_mode,
                };

                self.stack.push(self.pc);

                self.pc = match (self.mode.contains(Mode::PCM), self.mode.contains(Mode::LPC)) {
                    (false, true) => u14::new(0x18),
                    (false, false) => u14::new(0x1a),
                    (true, true) => u14::new(0x1c),
                    (true, false) => u14::new(0x1e),
                };

                if self.rom[self.pc.value() as usize] == 0x3e {
                    panic!("from the spec: If a level-1 interrupt is followed immediately by a RETI, then the potential exists with some single-byte instructions to corrupt the A register upon return.")
                }
            }
            // Prevent interrput-2 from activating if interrupt 1 is active
            (_, Interrupt::Active, _, _) => (),
            // Activate interrput-2
            (_, Interrupt::Inactive, true, Interrupt::Requested) => {
                self.interrupt_2 = Interrupt2 {
                    state: Interrupt::Active,
                    status: self.status,
                    integer_mode: self.integer_mode,
                };

                self.stack.push(self.pc);

                self.pc = match (self.mode.contains(Mode::PCM), self.mode.contains(Mode::LPC)) {
                    (false, true) => u14::new(0x10),
                    (false, false) => u14::new(0x12),
                    (true, true) => u14::new(0x14),
                    (true, false) => u14::new(0x16),
                }
            }
            _ => (),
        }
    }

    fn step(&mut self) -> Status {
        self.handle_interrupts();
        let instruction = self.fetch();
        self.execute(instruction)
    }

    fn fetch(&mut self) -> Instruction {
        let opcode: u8 = self.rom[self.pc.value() as usize];
        let next_idx = self.pc.wrapping_add(u14::ONE);

        match Instruction::has_operand_byte(opcode) {
            true => {
                self.pc = next_idx.wrapping_add(u14::ONE);
                Instruction::opcode_to_instruction_with_operand_byte(
                    opcode,
                    self.rom[next_idx.value() as usize],
                )
            }
            false => {
                self.pc = next_idx;
                Instruction::opcode_to_instruction(opcode)
            }
        }
    }

    fn sign_extend_8_to_14_if_extended_sign(&self, a: u8) -> u14 {
        let a = a as u16;
        u14::new(match self.integer_mode.unwrap() {
            IntegerMode::ExtSign => match a >= 0x80 {
                true => a | 0x3F00,
                false => a,
            },
            IntegerMode::Integer => a,
        })
    }

    fn sign_extend_12_to_14_if_extended_sign(&self, a: u12) -> u14 {
        let a = a.value();
        u14::new(match self.integer_mode.unwrap() {
            IntegerMode::ExtSign => match a >= 0x800 {
                true => a | 0x3000,
                false => a,
            },
            IntegerMode::Integer => a,
        })
    }

    fn read_mem_sign_extend(&mut self, addr: u8) -> u14 {
        let addr = addr as usize;
        match addr {
            0x00..=0x0F => {
                let a = self.synthesis_mem[addr].unwrap();
                self.sign_extend_12_to_14_if_extended_sign(a)
            }
            0x10..=0x7F => {
                let a = self.mem[addr - 0x10].unwrap();

                self.sign_extend_8_to_14_if_extended_sign(a)
            }
            _ => panic!("Attempt to access unmapped memory"),
        }
    }

    fn read_mem(&mut self, addr: u8) -> u14 {
        let addr = addr as usize;
        u14::new(match addr {
            0x00..=0x0F => self.synthesis_mem[addr].unwrap().value(),
            0x10..=0x7F => self.mem[addr - 0x10].unwrap() as u16,
            _ => panic!("Attempt to access unmapped memory"),
        })
    }

    // Read bottom 8 bits of address
    fn read_mem_8(&mut self, addr: u8) -> u8 {
        let addr = addr as usize;
        match addr {
            0x00..=0x0F => self.synthesis_mem[addr].unwrap().value() as u8,
            0x10..=0x7F => self.mem[addr - 0x10].unwrap(),
            _ => panic!("Attempt to read unmapped memory"),
        }
    }

    // Write bottom 8 bits of address, leaving top bits alone
    fn write_mem_8(&mut self, val: u8, addr: u8) {
        let addr = addr as usize;
        match addr {
            0x00..=0x0F => {
                self.synthesis_mem[addr] = Uninit::Some(
                    (self.synthesis_mem[addr].unwrap() & u12::new(0x0F00)) | u12::new(val as u16),
                )
            }

            0x10..=0x7F | 0x81..=0x83 | 0x85..=0x87 => self.mem[addr - 0x10] = Uninit::Some(val),

            0x80 | 0x84 => panic!("Attempt to write to read only Data Input Register"),
            _ => panic!("Attempt to write to unmapped memory"),
        }
    }

    fn write_mem(&mut self, val: u14, addr: u8) {
        let val = val.value() & 0x0FFF;
        match addr {
            0x00..=0x0F => self.synthesis_mem[addr as usize] = Uninit::Some(u12::new(val)),
            _ => self.write_mem_8(val as u8, addr),
        }
    }

    fn set_status(&mut self, status: bool) {
        self.status = Uninit::Some(status);
    }

    fn get_fetch_into_ps_buf(&mut self) {
        if self.mode.contains(Mode::RAMROM) {
            self.ps_buf = Uninit::Some(Some(self.read_mem_8(self.x.unwrap())));
        } else if self.mode.contains(Mode::EXTROM) {
            todo!("EXTROM is not yet supported");
        } else {
            self.ps_buf = Uninit::Some(Some(self.rom[self.sar.unwrap().value() as usize]));
            self.sar = Uninit::Some(self.sar.unwrap() + u14::ONE);
        }
    }

    fn execute(&mut self, instruction: Instruction) -> Status {
        fn signed_shift_multiply(a: u14, b: u8) -> u14 {
            let a = a.value();
            assert!(a != 0x2000,
                "from the spec: When the A register contains the value 2000h, the results of the AXCA instruction are not reliable"
            );

            // is 'a' negative?
            let a = if a >= 0x2000 {
                // Sign extend and convert to 32 bit
                (a as u32 | 0xFFFFC000) as i32
            } else {
                // Positive. No sign extension necessary
                a as i32
            };

            // Sign extend operand to 32 bits
            let operand = b as i8 as i32;

            // Multiply, shift right and truncate to 14 bits.
            u14::new(((((a * operand) / 128) as u32) & 0x3FFF) as u16)
        }

        match instruction {
            I::ABAAC => {
                let a = self.a.unwrap();
                let b = self.b.unwrap();
                self.set_status((a.value() as u8).overflowing_add(b.value() as u8).1);
                self.a = Uninit::Some(a.wrapping_add(b));
            }
            I::ACAAC(Some(operand)) => {
                let a = self.a.unwrap();
                let operand = self.sign_extend_12_to_14_if_extended_sign(u12::new(operand));
                self.set_status((a.value() as u8).overflowing_add(operand.value() as u8).1);
                self.a = Uninit::Some(a.wrapping_add(operand));
            }
            I::AGEC(Some(operand)) => self.set_status((self.a.unwrap().value() as u8) >= operand),
            I::AMAAC => {
                let mem = self.read_mem_sign_extend(self.x.unwrap());
                self.set_status(
                    (self.a.unwrap().value() as u8)
                        .overflowing_add(mem.value() as u8)
                        .1,
                );
                self.a = Uninit::Some(self.a.unwrap().wrapping_add(mem));
            }
            I::ANDCM(Some(operand)) => {
                self.set_status(true);
                let addr = self.x.unwrap();
                let mem = self.read_mem_8(addr);
                self.write_mem_8(mem & operand, addr);
            }
            I::ANEC(Some(operand)) => {
                self.set_status((self.a.unwrap().value() as u8) != operand);
            }
            I::AXCA(Some(operand)) => {
                self.set_status(true);
                self.a = Uninit::Some(signed_shift_multiply(self.a.unwrap(), operand));
            }
            I::AXMA => {
                self.set_status(true);
                self.a = Uninit::Some(signed_shift_multiply(self.a.unwrap(), self.x.unwrap()));
            }
            I::AXTM => {
                self.set_status(true);
                self.a =
                    Uninit::Some(signed_shift_multiply(self.a.unwrap(), self.timer.unwrap()));
            }
            I::BR(Some(operand)) => {
                if self.status.unwrap() {
                    self.pc = u14::new(operand);
                }
                self.set_status(true);
            }
            I::BRA => {
                self.set_status(true);
                self.pc = self.a.unwrap();
            }
            I::CALL(Some(operand)) => {
                if self.status.unwrap() {
                    self.stack.push(self.pc);
                    self.pc = u14::new(operand);
                }

                self.set_status(true);
            }
            I::CLA => {
                self.set_status(true);
                self.a = Uninit::Some(u14::ZERO);
            }
            I::CLB => {
                self.set_status(true);
                self.b = Uninit::Some(u14::ZERO);
            }
            I::CLX => {
                self.set_status(true);
                self.x = Uninit::Some(0);
            }
            I::DECMN => {
                let addr = self.x.unwrap();
                self.set_status(addr == 0);
                let mem = self.read_mem(addr) + u14::new(0xFF);
                self.write_mem(mem, addr)
            }
            I::DECXN => {
                let (x, carry) = self.x.unwrap().overflowing_sub(1);
                self.x = Uninit::Some(x);
                self.set_status(carry);
            }
            I::EXTSG => {
                self.integer_mode = Uninit::Some(IntegerMode::ExtSign);
                self.set_status(true);
            }
            I::GET(Some(operand)) => {
                assert!((1..=8).contains(&operand));
                let bits_left = self.ps_bits_left.unwrap();

                if self.ps_buf.unwrap().is_none() {
                    self.get_fetch_into_ps_buf();
                }

                let take_bits = |this: &mut Self, n: u8| {
                    this.a = Uninit::Some(
                        (this.a.unwrap() << n)
                            + (this.ps.unwrap().reverse_bits() >> (8 - n)).into(),
                    );
                };

                if bits_left <= operand {
                    // Drain the parallel to serial register into A
                    if bits_left > 0 {
                        take_bits(self, bits_left);
                    }

                    // Drain P/S buffer to P/S register
                    self.ps = Uninit::Some(self.ps_buf.unwrap().unwrap());
                    self.ps_bits_left = Uninit::Some(8);
                    self.ps_buf = Uninit::Some(None);
                    self.set_status(true);
                } else {
                    self.set_status(false);
                }

                let bits_left = operand - bits_left;
                if bits_left > 0 {
                    take_bits(self, bits_left);
                    self.ps = Uninit::Some(self.ps.unwrap() - bits_left);
                }

                /* From the spec:
                 * The status flag after either a GET 7 or a GET 8 is not reliable. If the state
                 * of the status flag following the GET instruction is important to the applica-
                 * tion, a GET 7 or a GET 8 should be avoided. */
                if operand >= 7 {
                    self.status = Default::default();
                }
            }
            I::IAC => {
                let a = self.a.unwrap();
                self.set_status(a.value() & 0xFF == 0xFF);
                self.a = Uninit::Some(a.wrapping_add(u14::ONE));
            }
            I::IBC => {
                let b = self.b.unwrap();
                self.set_status(b.value() & 0xFF == 0xFF);
                self.b = Uninit::Some(b.wrapping_add(u14::ONE));
            }
            I::INCMC => {
                let addr = self.x.unwrap();
                let mem = self.read_mem(addr);
                self.set_status(mem.value() & 0xFF == 0xFF);
                self.write_mem(mem.wrapping_add(u14::ONE), addr);
            }
            I::INTGR => {
                self.integer_mode = Uninit::Some(IntegerMode::Integer);
                self.set_status(true);
            }
            I::IXC => {
                let x = self.x.unwrap();
                let (val, flag) = x.overflowing_add(1);
                self.set_status(flag);
                self.x = Uninit::Some(val);
            }
            I::LUAA => {
                let val = self.rom[self.a.unwrap().value() as usize];
                self.a = Uninit::Some(self.sign_extend_8_to_14_if_extended_sign(val));
                self.set_status(true);
            }
            I::LUAB => {
                let val = self.rom[self.a.unwrap().value() as usize];
                self.b = Uninit::Some(self.sign_extend_8_to_14_if_extended_sign(val));
                self.set_status(true);
            }
            I::LUAPS => {
                self.ps_bits_left = Uninit::Some(0);
                self.sar = self.a;
                self.get_fetch_into_ps_buf();
                self.set_status(true);
            }
            I::ORCM(Some(operand)) => {
                self.set_status(true);
                let addr = self.x.unwrap();
                let mem = self.read_mem_8(addr);
                self.write_mem_8(mem | operand, addr);
            }
            I::RETI => {
                match (self.mode.contains(Mode::ENA1), self.mode.contains(Mode::ENA2), &self.interrupt_1.state, &self.interrupt_2.state) {
                    // Return from interrupt 1
                    (_, _, Interrupt::Active, _) => {
                        self.a = self.interrupt_1.a;
                        self.x = self.interrupt_1.x;
                        self.b = self.interrupt_1.b;
                        self.status = self.interrupt_1.status;
                        self.integer_mode = self.interrupt_1.integer_mode;
                        self.pc = self.stack.pop();
                    },
                    // Return from interrupt 2
                    (_, _, _, Interrupt::Active) => {
                        self.status = self.interrupt_2.status;
                        self.integer_mode = self.interrupt_2.integer_mode;
                    },
                    // If a RETI is executed with interrupts disabled, any interrupt pending flag is cleared.
                    (false, false, _, _) => {
                        self.interrupt_1.state = Interrupt::Inactive;
                        self.interrupt_2.state = Interrupt::Inactive;
                    },
                    _ => panic!("From the spec: If a RETI instruction is executed with interrupts enabled and without an interrupt first occurring, the stack control can be corrupted.")
                }
            }
            I::RETN => {
                self.set_status(true);
                if self.stack.sp != StackPointer::Bottom {
                    self.pc = self.stack.pop();
                }
            }
            I::SALA => {
                self.set_status((self.a.unwrap().value() & 0x80) != 0);
                self.a = Uninit::Some(self.a.unwrap() << 1);
            }
            I::SALA4 => {
                self.set_status(true);
                self.a = Uninit::Some(self.a.unwrap() << 4);
            }
            I::SARA => {
                self.set_status(true);
                self.a = Uninit::Some(self.a.unwrap() >> 1);
            }
            I::SBAAN => {
                self.set_status((self.a.unwrap().value() as u8) < (self.b.unwrap().value() as u8));
                self.a = Uninit::Some(self.a.unwrap().wrapping_sub(self.b.unwrap()));
            }
            I::SBR(Some(operand)) => {
                self.set_status(true);

                const PAGE_MASK: u14 = u14::new(0b11_1111_1000_0000);
                if self.status.unwrap() {
                    self.pc = u14::new(operand as u16) | self.pc & PAGE_MASK;
                } else {
                    /* from the docs:
                     * An SBR instruction executed at XX7Fh or XXFFh with status cleared
                     * (branch not taken) goes to XX00h or XX80h, respectively.
                     */

                    /* As far as I can tell this means that once the fetch increments the
                     * pc if it ends in 0x00 or 0x80 it needs have 0x80 subtracted from it
                     * since XXFFh -> X(X+1)00h. Only God knows why this happens.
                     */

                    if self.pc & PAGE_MASK == u14::ZERO {
                        self.pc -= u14::new(0x80);
                    }
                }
            }
            I::SETOFF => return Status::Halt,
            I::SMAAN => {
                let a = self.a.unwrap();
                let mem = self.read_mem_sign_extend(self.x.unwrap());
                self.set_status((a.value() as u8) < (mem.value() as u8));
                self.a = Uninit::Some(a.wrapping_sub(mem));
            }
            I::TAB => {
                self.set_status(true);
                self.b = self.a;
            }
            I::TAM => {
                self.set_status(true);
                self.write_mem(self.a.unwrap(), self.x.unwrap());
            }
            I::TAMD(Some(operand)) => {
                self.set_status(true);
                self.write_mem(self.a.unwrap(), operand);
            }
            I::TAMIX => {
                self.set_status(true);
                self.write_mem(self.a.unwrap(), self.x.unwrap());
                self.x = Uninit::Some(self.x.unwrap().wrapping_add(1));
            }
            I::TAMODE => {
                self.set_status(true);
                self.mode = Mode::from_bits(self.a.unwrap().value() as u8).unwrap();
            }
            I::TAPSC => {
                self.set_status(true);
                self.timer_prescale = Uninit::Some(self.a.unwrap().value() as u8);
            }
            I::TASYN => {
                self.set_status(true);
                let a = self.a.unwrap();
                match (self.mode.contains(Mode::LPC), self.mode.contains(Mode::PCM)) {
                    (false, true) => {
                        // See section 6.10 of the spec as for why this algorithm is insane
                        let dac = a.value() >> 2;
                        self.dac = Uninit::Some(
                            ((if dac & 0xC00 == 0xC00 { -1 } else { 1 })
                                * (((dac & 1) + ((dac & 0xFF) >> 1)) as i16))
                                .clamp(-480, 480),
                        );
                    }
                    (true, false) | (false, false) => {
                        assert!(a.value() & 0b10_0000_0000_0001 == 0, "From the spec: When in LPC mode, MSB and LSB of A register must be set to zero upon TASYN");
                        self.pitch = self.a;
                    }
                    (true, true) => self.excitation = self.a,
                }
            }
            I::TATM => {
                self.set_status(true);
                self.timer = Uninit::Some(self.a.unwrap().value() as u8);
            }
            I::TAX => {
                self.set_status(true);
                self.x = Uninit::Some(self.a.unwrap().value() as u8);
            }
            I::TBM => {
                self.set_status(true);
                self.write_mem(self.b.unwrap(), self.x.unwrap());
            }
            I::TCA(Some(operand)) => {
                self.set_status(true);
                self.a = Uninit::Some(self.sign_extend_8_to_14_if_extended_sign(operand));
            }
            I::TCX(Some(operand)) => {
                self.set_status(true);
                self.x = Uninit::Some(operand);
            }
            I::TMA => {
                self.set_status(true);
                self.a = Uninit::Some(self.read_mem_sign_extend(self.x.unwrap()));
            }
            I::TMAD(Some(operand)) => {
                self.set_status(true);
                self.a = Uninit::Some(self.read_mem_sign_extend(operand));
            }
            I::TMAIX => {
                self.set_status(true);
                self.a = Uninit::Some(self.read_mem_sign_extend(self.x.unwrap()));
                self.x = Uninit::Some(self.x.unwrap().wrapping_add(1));
            }
            I::TMXD(Some(operand)) => {
                self.set_status(true);
                self.x = Uninit::Some(self.read_mem_8(operand));
            }
            I::TRNDA => {
                self.set_status(true);
                self.a = Uninit::Some(u14::new(self.random & 0xFF))
            }
            I::TSTCA(Some(operand)) => {
                self.set_status(self.a.unwrap().value() as u8 & operand == operand)
            }
            I::TSTCM(Some(operand)) => {
                let status = self.read_mem_8(self.x.unwrap()) & operand == operand;
                self.set_status(status)
            }
            I::TTMA => {
                self.set_status(true);
                self.a =
                    Uninit::Some(self.sign_extend_8_to_14_if_extended_sign(self.timer.unwrap()));
            }
            I::TXA => {
                self.set_status(true);
                self.a =
                    Uninit::Some(self.sign_extend_8_to_14_if_extended_sign(self.x.unwrap()));
            }
            I::XBA => {
                self.set_status(true);
                std::mem::swap(&mut self.a, &mut self.b);
            }
            I::XBX => {
                self.set_status(true);
                let b = self.b.unwrap();
                let x = self.x.unwrap();

                self.x = Uninit::Some(b.value() as u8);
                self.b = Uninit::Some(self.sign_extend_8_to_14_if_extended_sign(x));
            }
            I::XGEC(Some(operand)) => {
                self.set_status(self.x.unwrap() > operand);
            }
            _ => panic!("attempt to use opcode with None operand"),
        };

        let cycles = instruction.cycles();
        self.num_cycles += cycles;

        if self.timer_begun {
            let timer_prescale = self.timer_prescale.unwrap() as usize;
            let (timer_prescale_count, overflow) = (self.timer_prescale_count.unwrap() as usize
                + cycles)
                .overflowing_rem(timer_prescale + 1);

            self.timer_prescale_count = Uninit::Some(timer_prescale_count as u8);

            if overflow {
                let (timer, interrupt) = self.timer.unwrap().overflowing_sub(1);
                self.timer = Uninit::Some(timer);
                if interrupt {
                    self.interrupt_2.state = Interrupt::Requested;
                }
            }
        }

        for _ in 0..cycles {
            // update random number generator once for each clock cycle
            self.random =
                (self.random << 1) | (self.random & 0x4000 == self.random & 0x2000) as u16;
        }

        Status::Continue
    }
}
