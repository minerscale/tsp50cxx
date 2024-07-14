#![allow(dead_code)]
#![allow(clippy::upper_case_acronyms)]

use arbitrary_int::{u12, u14};
use bitflags::bitflags;
use std::{
    fmt::{self, Debug},
    ops::{Index, IndexMut},
};

#[derive(Debug)]
enum Instruction {
    ABAAC,
    ACAAC(u12),
    AGEC(u8),
    AMAAC,
    ANDCM(u8),
    ANEC(u8),
    AXCA(u8),
    AXMA,
    AXTM,
    BR(u16),
    BRA,
    CALL(u14),
    CLA,
    CLB,
    CLX,
    DECMN,
    DECXN,
    EXTSG,
    GET(u8),
    IAC,
    IBC,
    INCMC,
    INTGR,
    IXC,
    LUAA,
    LUAB,
    LUAPS,
    ORCM(u8),
    RETI,
    RETN,
    SALA,
    SALA4,
    SARA,
    SBAAN,
    SBR(u8),
    SETOFF,
    SMAAN,
    TAB,
    TAM,
    TAMD(u8),
    TAMIX,
    TAMODE,
    TAPSC,
    TASYN,
    TATM,
    TAX,
    TBM,
    TCA(u8),
    TCX(u8),
    TMA,
    TMAD(u8),
    TMAIX,
    TMXD(u8),
    TRNDA,
    TSTCA(u8),
    TSTCM(u8),
    TTMA,
    TXA,
    XBA,
    XBX,
    XGEC(u8),
}

impl Instruction {
    pub fn has_operand_byte(opcode: u8) -> bool {
        matches!(opcode, 0x00..=0x0F | 0x40..=0x6A | 0x6E..=0x7F)
    }

    pub fn opcode_to_instruction(opcode: u8) -> Instruction {
        type I = Instruction;
        match opcode {
            0x6B => I::LUAA,
            0x6C => I::LUAPS,
            0x6D => I::LUAB,
            0x10 => I::TXA,
            0x11 => I::TMA,
            0x12 => I::XBA,
            0x13 => I::TAMIX,
            0x14 => I::TMAIX,
            0x15 => I::SARA,
            0x16 => I::TAM,
            0x17 => I::TTMA,
            0x18 => I::TAX,
            0x19 => I::TAPSC,
            0x1A => I::TAB,
            0x1B => I::SALA4,
            0x1C => I::TASYN,
            0x1D => I::TAMODE,
            0x1E => I::TATM,
            0x1F => I::BRA,
            0x20 => I::CLX,
            0x21 => I::IXC,
            0x22 => I::DECXN,
            0x23 => I::XBX,
            0x24 => I::CLB,
            0x25 => I::IBC,
            0x26 => I::INCMC,
            0x27 => I::DECMN,
            0x28 => I::AMAAC,
            0x29 => I::SMAAN,
            0x2A => I::TBM,
            0x2B => I::TRNDA,
            0x2C => I::ABAAC,
            0x2D => I::SBAAN,
            0x2E => I::SALA,
            0x2F => I::CLA,
            0x30..=0x37 => I::GET(opcode & 0b0111),
            0x38 => I::AXTM,
            0x39 => I::AXMA,
            0x3A => I::IAC,
            0x3B => I::INTGR,
            0x3C => I::EXTSG,
            0x3D => I::RETN,
            0x3E => I::RETI,
            0x3F => I::SETOFF,
            0x80..=0xFF => I::SBR(opcode & 0b0111_1111),
            _ => unreachable!("Opcode with operand called without operand byte."),
        }
    }

    pub fn opcode_to_instruction_with_operand_byte(opcode: u8, operand: u8) -> Instruction {
        type I = Instruction;
        match opcode {
            0x00..=0x0F => I::CALL(u14::new((opcode as u16) << 8 | operand as u16)),
            0x40..=0x5F => I::BR(((opcode & 0b0001_1111) as u16) << 8 | operand as u16),
            0x60 => I::ANEC(operand),
            0x61 => I::XGEC(operand),
            0x62 => I::TCX(operand),
            0x63 => I::AGEC(operand),
            0x64 => I::ORCM(operand),
            0x65 => I::ANDCM(operand),
            0x66 => I::TSTCM(operand),
            0x67 => I::TSTCA(operand),
            0x68 => I::AXCA(operand),
            0x69 => I::TMAD(operand),
            0x6A => I::TAMD(operand),
            0x6E => I::TCA(operand),
            0x6F => I::TMXD(operand),
            0x70..=0x7F => I::ACAAC(u12::new(((opcode & 0b1111) as u16) << 8 | operand as u16)),
            _ => unreachable!("Opcode without operand called with operand byte."),
        }
    }
}

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

#[cfg(debug_assertions)]
#[derive(Copy, Clone, Default)]
enum OptUninit<T> {
    Some(T),
    #[default]
    None,
}

#[cfg(debug_assertions)]
impl<T> OptUninit<T> {
    pub fn unwrap(self) -> T {
        match self {
            OptUninit::Some(val) => val,
            OptUninit::None => panic!("attempt to access uninitialised value"),
        }
    }
}

#[cfg(debug_assertions)]
impl<T: Default> OptUninit<T> {
    pub fn unwrap_or_default(self) -> T {
        match self {
            OptUninit::Some(val) => val,
            OptUninit::None => Default::default(),
        }
    }
}

#[cfg(debug_assertions)]
impl<T: Clone + Debug + Default> fmt::Debug for OptUninit<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            OptUninit::Some(x) => f.write_fmt(format_args!("{:?}", x)),
            OptUninit::None => f.write_str("---"),
        }
    }
}

#[cfg(not(debug_assertions))]
#[derive(Copy, Clone)]
enum OptUninit<T> {
    Some(T),
}

#[cfg(not(debug_assertions))]
impl<T: Default> Default for OptUninit<T> {
    fn default() -> Self {
        Self::Some(T::default())
    }
}

#[cfg(not(debug_assertions))]
impl<T> OptUninit<T> {
    pub fn unwrap(self) -> T {
        match self {
            OptUninit::Some(val) => val,
        }
    }
}

#[cfg(not(debug_assertions))]
impl<T: Default> OptUninit<T> {
    pub fn unwrap_or_default(self) -> T {
        match self {
            OptUninit::Some(val) => val,
        }
    }
}

#[cfg(not(debug_assertions))]
impl<T: Clone + Debug> fmt::Debug for OptUninit<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{:?}",
            &<OptUninit<T> as Clone>::clone(self).unwrap()
        ))
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
    stack: [OptUninit<u14>; 3],
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

        self.stack[self.sp] = OptUninit::Some(addr);
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

struct TSP50 {
    pc: u14,
    stack: Stack,
    a: OptUninit<u14>,
    x: OptUninit<u8>,
    b: OptUninit<u14>,
    status: OptUninit<bool>,
    integer_mode: OptUninit<IntegerMode>,
    timer: OptUninit<u8>,
    timer_prescale: OptUninit<u8>,
    pitch: OptUninit<u14>,
    sar: OptUninit<u14>,
    ps: OptUninit<u8>,
    ps_buf: OptUninit<Option<u8>>,
    ps_bits_left: OptUninit<u8>,
    mode: OptUninit<Mode>,

    synthesis_mem: [OptUninit<u12>; 16],
    mem: [OptUninit<u8>; 120],
    rom: [u8; 16384],
    excitation_rom: [u8; 384],
}

impl fmt::Debug for TSP50 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("pc: {:04x} | a: {:04x} | b: {:04x} | x: {:02x} | status: {:x} | mode: {:?} | stack: [{:04x}|{:04x}|{:04x}] | sp: {:3?}",
            &self.pc, &self.a.unwrap_or_default(), &self.b.unwrap_or_default(), &self.x.unwrap_or_default(), &(self.status.unwrap_or_default() as u8), &self.integer_mode, &self.stack.stack[0].unwrap_or_default(), &self.stack.stack[1].unwrap_or_default(), &self.stack.stack[2].unwrap_or_default(), &self.stack.sp))
    }
}

impl TSP50 {
    pub fn new() -> TSP50 {
        TSP50 {
            pc: Default::default(),
            stack: Default::default(),
            a: Default::default(),
            x: Default::default(),
            b: Default::default(),
            status: Default::default(),
            integer_mode: Default::default(),
            timer: Default::default(),
            timer_prescale: Default::default(),
            pitch: Default::default(),
            sar: Default::default(),
            ps: Default::default(),
            ps_buf: Default::default(),
            ps_bits_left: Default::default(),
            mode: Default::default(),
            synthesis_mem: [Default::default(); 16],
            mem: [Default::default(); 120],
            rom: [Default::default(); 16384],
            excitation_rom: [Default::default(); 384],
        }
    }

    pub fn step(&mut self) -> bool {
        let instruction = self.fetch();
        print!("{:10} ", format!("{:02x?}", instruction));
        self.execute(instruction)
    }

    fn fetch(&mut self) -> Instruction {
        let opcode: u8 = self.rom[self.pc.value() as usize];
        let next_idx = self.pc.wrapping_add(u14::ONE);
        print!(" {:#02x} | ", opcode);

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
                self.synthesis_mem[addr] = OptUninit::Some(
                    (self.synthesis_mem[addr].unwrap() & u12::new(0x0F00)) | u12::new(val as u16),
                )
            }

            0x10..=0x7F | 0x81..=0x83 | 0x85..=0x87 => self.mem[addr - 0x10] = OptUninit::Some(val),

            0x80 | 0x84 => panic!("Attempt to write to read only Data Input Register"),
            _ => panic!("Attempt to write to unmapped memory"),
        }
    }

    fn write_mem(&mut self, val: u14, addr: u8) {
        let val = val.value() & 0x0FFF;
        match addr {
            0x00..=0x0F => self.synthesis_mem[addr as usize] = OptUninit::Some(u12::new(val)),
            _ => self.write_mem_8(val as u8, addr),
        }
    }

    fn set_status(&mut self, status: bool) {
        self.status = OptUninit::Some(status);
    }

    fn get_fetch_into_ps_buf(&mut self) {
        let mode = self.mode.unwrap();
        if mode.contains(Mode::RAMROM) {
            self.ps_buf = OptUninit::Some(Some(self.read_mem_8(self.x.unwrap())));
        } else if mode.contains(Mode::EXTROM) { 
            todo!("EXTROM is not yet supported");
        } else {
            self.ps_buf = OptUninit::Some(Some(self.rom[self.sar.unwrap().value() as usize]));
            self.sar = OptUninit::Some(self.sar.unwrap() + u14::ONE);
        }
    }

    fn execute(&mut self, instruction: Instruction) -> bool {
        type I = Instruction;

        fn signed_shift_multiply(a: u14, b: u8) -> u14 {
            let a = a.value();
            assert!(a != 0x2000,
                "When the A register contains the value 2000h, the results of the AXCA instruction are not reliable"
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
                self.a = OptUninit::Some(a.wrapping_add(b));
            }
            I::ACAAC(operand) => {
                let a = self.a.unwrap();
                let operand = self.sign_extend_12_to_14_if_extended_sign(operand);
                self.set_status((a.value() as u8).overflowing_add(operand.value() as u8).1);
                self.a = OptUninit::Some(a.wrapping_add(operand));
            }
            I::AGEC(operand) => self.set_status((self.a.unwrap().value() as u8) >= operand),
            I::AMAAC => {
                let mem = self.read_mem_sign_extend(self.x.unwrap());
                self.set_status(
                    (self.a.unwrap().value() as u8)
                        .overflowing_add(mem.value() as u8)
                        .1,
                );
                self.a = OptUninit::Some(self.a.unwrap().wrapping_add(mem));
            }
            I::ANDCM(operand) => {
                self.set_status(true);
                let addr = self.x.unwrap();
                let mem = self.read_mem_8(addr);
                self.write_mem_8(mem & operand, addr);
            }
            I::ANEC(operand) => {
                self.set_status((self.a.unwrap().value() as u8) != operand);
            }
            I::AXCA(operand) => {
                self.set_status(true);
                self.a = OptUninit::Some(signed_shift_multiply(self.a.unwrap(), operand));
            }
            I::AXMA => {
                self.set_status(true);
                self.a = OptUninit::Some(signed_shift_multiply(self.a.unwrap(), self.x.unwrap()));
            }
            I::AXTM => {
                self.set_status(true);
                self.a =
                    OptUninit::Some(signed_shift_multiply(self.a.unwrap(), self.timer.unwrap()));
            }
            I::BR(operand) => {
                if self.status.unwrap() {
                    self.pc = u14::new(operand);
                }
                self.set_status(true);
            }
            I::BRA => {
                self.set_status(true);
                self.pc = self.a.unwrap();
            }
            I::CALL(operand) => {
                if self.status.unwrap() {
                    self.stack.push(self.pc);
                    self.pc = operand;
                }

                self.set_status(true);
            }
            I::CLA => {
                self.set_status(true);
                self.a = OptUninit::Some(u14::ZERO);
            }
            I::CLB => {
                self.set_status(true);
                self.b = OptUninit::Some(u14::ZERO);
            }
            I::CLX => {
                self.set_status(true);
                self.x = OptUninit::Some(0);
            }
            I::DECMN => {
                let addr = self.x.unwrap();
                self.set_status(addr == 0);
                let mem = self.read_mem(addr) + u14::new(0xFF);
                self.write_mem(mem, addr)
            }
            I::DECXN => {
                let (x, carry) = self.x.unwrap().overflowing_sub(1);
                self.x = OptUninit::Some(x);
                self.set_status(carry);
            }
            I::EXTSG => {
                self.integer_mode = OptUninit::Some(IntegerMode::ExtSign);
                self.set_status(true);
            }
            I::GET(operand) => {
                assert!((1..=8).contains(&operand));
                let bits_left = self.ps_bits_left.unwrap();

                if self.ps_buf.unwrap().is_none() {
                    self.get_fetch_into_ps_buf();
                }

                let take_bits = |this: &mut Self, n: u8| {
                    this.a = OptUninit::Some(
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
                    self.ps = OptUninit::Some(self.ps_buf.unwrap().unwrap());
                    self.ps_bits_left = OptUninit::Some(8);
                    self.ps_buf = OptUninit::Some(None);
                    self.set_status(true);
                } else {
                    self.set_status(false);
                }

                let bits_left = operand - bits_left;
                if bits_left > 0 {
                    take_bits(self, bits_left);
                    self.ps = OptUninit::Some(self.ps.unwrap() - bits_left);
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
                self.a = OptUninit::Some(a.wrapping_add(u14::ONE));
            }
            I::IBC => {
                let b = self.b.unwrap();
                self.set_status(b.value() & 0xFF == 0xFF);
                self.b = OptUninit::Some(b.wrapping_add(u14::ONE));
            }
            I::INCMC => {
                let addr = self.x.unwrap();
                let mem = self.read_mem(addr);
                self.set_status(mem.value() & 0xFF == 0xFF);
                self.write_mem(mem.wrapping_add(u14::ONE), addr);
            }
            I::INTGR => {
                self.integer_mode = OptUninit::Some(IntegerMode::Integer);
                self.set_status(true);
            }
            I::IXC => {
                let x = self.x.unwrap();
                let (val, flag) = x.overflowing_add(1);
                self.set_status(flag);
                self.x = OptUninit::Some(val);
            }
            I::LUAA => {
                let val = self.rom[self.a.unwrap().value() as usize];
                self.a = OptUninit::Some(self.sign_extend_8_to_14_if_extended_sign(val));
                self.set_status(true);
            }
            I::LUAB => {
                let val = self.rom[self.a.unwrap().value() as usize];
                self.b = OptUninit::Some(self.sign_extend_8_to_14_if_extended_sign(val));
                self.set_status(true);
            }
            I::LUAPS => {
                self.ps_bits_left = OptUninit::Some(0);
                self.sar = self.a;
                self.get_fetch_into_ps_buf();
                self.set_status(true);
            }
            I::ORCM(operand) => {
                self.set_status(true);
                let addr = self.x.unwrap();
                let mem = self.read_mem_8(addr);
                self.write_mem_8(mem | operand, addr);
            }
            I::RETI => todo!(),
            I::RETN => {
                self.set_status(true);
                if self.stack.sp != StackPointer::Bottom {
                    self.pc = self.stack.pop();
                }
            }
            I::SALA => {
                self.set_status((self.a.unwrap().value() & 0x80) != 0);
                self.a = OptUninit::Some(self.a.unwrap() << 1);
            },
            I::SALA4 => {
                self.set_status(true);
                self.a = OptUninit::Some(self.a.unwrap() << 4);
            },
            I::SARA => {
                self.set_status(true);
                self.a = OptUninit::Some(self.a.unwrap() >> 1);
            },
            I::SBAAN => {
                self.set_status((self.a.unwrap().value() as u8) < (self.b.unwrap().value() as u8));
                self.a = OptUninit::Some(self.a.unwrap().wrapping_sub(self.b.unwrap()));
            },
            I::SBR(operand) => {
                self.set_status(true);

                const PAGE_MASK: u14 = u14::new(0b11_1111_1000_0000);
                if self.status.unwrap() {
                    self.pc = u14::new(operand as u16) | self.pc & PAGE_MASK;
                } else {
                   /* from the docs:
                    * An SBR instruction executed at XX7Fh or XXFFh with status cleared
                    * (branch not taken) goes to XX00h or XX80h, respectively.
                    *
                    * As far as I can tell this means that once the fetch increments the 
                    * pc if it ends in 0x00 or 0x80 it needs have 0x80 subtracted from it
                    * since XXFFh -> X(X+1)00h. Only God knows why this happens.
                    */

                    if self.pc & PAGE_MASK == u14::ZERO {
                        self.pc -= u14::new(0x80);
                    }
                }
                
            },
            I::SETOFF => return true,
            I::SMAAN => todo!(),
            I::TAB => todo!(),
            I::TAM => todo!(),
            I::TAMD(_) => todo!(),
            I::TAMIX => todo!(),
            I::TAMODE => {
                self.set_status(true);
                self.mode = OptUninit::Some(Mode::from_bits(self.a.unwrap().value() as u8).unwrap());
            },
            I::TAPSC => todo!(),
            I::TASYN => todo!(),
            I::TATM => todo!(),
            I::TAX => todo!(),
            I::TBM => todo!(),
            I::TCA(_) => todo!(),
            I::TCX(_) => todo!(),
            I::TMA => todo!(),
            I::TMAD(_) => todo!(),
            I::TMAIX => todo!(),
            I::TMXD(_) => todo!(),
            I::TRNDA => todo!(),
            I::TSTCA(_) => todo!(),
            I::TSTCM(_) => todo!(),
            I::TTMA => todo!(),
            I::TXA => todo!(),
            I::XBA => todo!(),
            I::XBX => todo!(),
            I::XGEC(_) => todo!(),
        }
        false
    }
}

fn main() {
    let mut emulator = TSP50::new();
    emulator.rom[0] = 0x2F;
    emulator.rom[1] = 0x3B;
    emulator.rom[2] = 0x70;
    emulator.rom[3] = 0xFE;
    emulator.rom[4] = 0x3A;
    emulator.rom[5] = 0x40;
    emulator.rom[6] = 0x09;
    emulator.rom[7] = 0x40;
    emulator.rom[8] = 0x04;
    emulator.rom[9] = 0x3F;

    while !emulator.step() {
        println!("{:?}", emulator);
    }

    println!();
}
