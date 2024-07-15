/*
 * This software is based on the TSP50C0X/1X spec from https://www.ti.com/lit/ml/spss011d/spss011d.pdf
 */

#![allow(dead_code)]
#![allow(clippy::upper_case_acronyms)]

use arbitrary_int::{u12, u14};
use bitflags::bitflags;
use slicevec::SliceVec;
use std::{
    collections::HashMap,
    fmt::{self, Debug},
    fs::File,
    io::Read,
    ops::{Index, IndexMut},
    str::FromStr,
};

#[derive(Debug, Copy, Clone)]
enum Instruction {
    CALL(Option<u16>),
    TXA,
    TMA,
    XBA,
    TAMIX,
    TMAIX,
    SARA,
    TAM,
    TTMA,
    TAX,
    TAPSC,
    TAB,
    SALA4,
    TASYN,
    TAMODE,
    TATM,
    BRA,
    CLX,
    IXC,
    DECXN,
    XBX,
    CLB,
    IBC,
    INCMC,
    DECMN,
    AMAAC,
    SMAAN,
    TBM,
    TRNDA,
    ABAAC,
    SBAAN,
    SALA,
    CLA,
    GET(Option<u8>),
    AXTM,
    AXMA,
    IAC,
    INTGR,
    EXTSG,
    RETN,
    RETI,
    SETOFF,
    BR(Option<u16>),
    ANEC(Option<u8>),
    XGEC(Option<u8>),
    TCX(Option<u8>),
    AGEC(Option<u8>),
    ORCM(Option<u8>),
    ANDCM(Option<u8>),
    TSTCM(Option<u8>),
    TSTCA(Option<u8>),
    AXCA(Option<u8>),
    TMAD(Option<u8>),
    TAMD(Option<u8>),
    LUAA,
    LUAPS,
    LUAB,
    TCA(Option<u8>),
    TMXD(Option<u8>),
    ACAAC(Option<u16>),
    SBR(Option<u8>),
}

#[derive(Debug, Copy, Clone)]
enum Directive<'a> {
    I(Instruction),
    Br(Option<&'a str>),
}

type I = Instruction;
type D<'a> = Directive<'a>;

impl TryFrom<&str> for Directive<'_> {
    type Error = ();

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "CALL" => Ok(D::I(I::CALL(None))),
            "TXA" => Ok(D::I(I::TXA)),
            "TMA" => Ok(D::I(I::TMA)),
            "XBA" => Ok(D::I(I::XBA)),
            "TAMIX" => Ok(D::I(I::TAMIX)),
            "TMAIX" => Ok(D::I(I::TMAIX)),
            "SARA" => Ok(D::I(I::SARA)),
            "TAM" => Ok(D::I(I::TAM)),
            "TTMA" => Ok(D::I(I::TTMA)),
            "TAX" => Ok(D::I(I::TAX)),
            "TAPSC" => Ok(D::I(I::TAPSC)),
            "TAB" => Ok(D::I(I::TAB)),
            "SALA4" => Ok(D::I(I::SALA4)),
            "TASYN" => Ok(D::I(I::TASYN)),
            "TAMODE" => Ok(D::I(I::TAMODE)),
            "TATM" => Ok(D::I(I::TATM)),
            "BRA" => Ok(D::I(I::BRA)),
            "CLX" => Ok(D::I(I::CLX)),
            "IXC" => Ok(D::I(I::IXC)),
            "DECXN" => Ok(D::I(I::DECXN)),
            "XBX" => Ok(D::I(I::XBX)),
            "CLB" => Ok(D::I(I::CLB)),
            "IBC" => Ok(D::I(I::IBC)),
            "INCMC" => Ok(D::I(I::INCMC)),
            "DECMN" => Ok(D::I(I::DECMN)),
            "AMAAC" => Ok(D::I(I::AMAAC)),
            "SMAAN" => Ok(D::I(I::SMAAN)),
            "TBM" => Ok(D::I(I::TBM)),
            "TRNDA" => Ok(D::I(I::TRNDA)),
            "ABAAC" => Ok(D::I(I::ABAAC)),
            "SBAAN" => Ok(D::I(I::SBAAN)),
            "SALA" => Ok(D::I(I::SALA)),
            "CLA" => Ok(D::I(I::CLA)),
            "GET" => Ok(D::I(I::GET(None))),
            "AXTM" => Ok(D::I(I::AXTM)),
            "AXMA" => Ok(D::I(I::AXMA)),
            "IAC" => Ok(D::I(I::IAC)),
            "INTGR" => Ok(D::I(I::INTGR)),
            "EXTSG" => Ok(D::I(I::EXTSG)),
            "RETN" => Ok(D::I(I::RETN)),
            "RETI" => Ok(D::I(I::RETI)),
            "SETOFF" => Ok(D::I(I::SETOFF)),
            "BR" => Ok(D::I(I::BR(None))),
            "ANEC" => Ok(D::I(I::ANEC(None))),
            "XGEC" => Ok(D::I(I::XGEC(None))),
            "TCX" => Ok(D::I(I::TCX(None))),
            "AGEC" => Ok(D::I(I::AGEC(None))),
            "ORCM" => Ok(D::I(I::ORCM(None))),
            "ANDCM" => Ok(D::I(I::ANDCM(None))),
            "TSTCM" => Ok(D::I(I::TSTCM(None))),
            "TSTCA" => Ok(D::I(I::TSTCA(None))),
            "AXCA" => Ok(D::I(I::AXCA(None))),
            "TMAD" => Ok(D::I(I::TMAD(None))),
            "TAMD" => Ok(D::I(I::TAMD(None))),
            "LUAA" => Ok(D::I(I::LUAA)),
            "LUAPS" => Ok(D::I(I::LUAPS)),
            "LUAB" => Ok(D::I(I::LUAB)),
            "TCA" => Ok(D::I(I::TCA(None))),
            "TMXD" => Ok(D::I(I::TMXD(None))),
            "ACAAC" => Ok(D::I(I::ACAAC(None))),
            "SBR" => Ok(D::I(I::SBR(None))),
            "Br" => Ok(D::Br(None)),
            _ => Err(()),
        }
    }
}

impl Instruction {
    pub fn has_operand_byte(opcode: u8) -> bool {
        matches!(opcode, 0x00..=0x0F | 0x40..=0x6A | 0x6E..=0x7F)
    }

    pub fn set_operand_value(self, value: usize) -> Self {
        match self {
            I::CALL(_) => I::CALL(Some(value.try_into().unwrap())),
            I::GET(_) => I::GET(Some(value.try_into().unwrap())),
            I::BR(_) => I::BR(Some(value.try_into().unwrap())),
            I::ANEC(_) => I::ANEC(Some(value.try_into().unwrap())),
            I::XGEC(_) => I::XGEC(Some(value.try_into().unwrap())),
            I::TCX(_) => I::TCX(Some(value.try_into().unwrap())),
            I::AGEC(_) => I::AGEC(Some(value.try_into().unwrap())),
            I::ORCM(_) => I::ORCM(Some(value.try_into().unwrap())),
            I::ANDCM(_) => I::ANDCM(Some(value.try_into().unwrap())),
            I::TSTCM(_) => I::TSTCM(Some(value.try_into().unwrap())),
            I::TSTCA(_) => I::TSTCA(Some(value.try_into().unwrap())),
            I::AXCA(_) => I::AXCA(Some(value.try_into().unwrap())),
            I::TMAD(_) => I::TMAD(Some(value.try_into().unwrap())),
            I::TAMD(_) => I::TAMD(Some(value.try_into().unwrap())),
            I::TCA(_) => I::TCA(Some(value.try_into().unwrap())),
            I::TMXD(_) => I::TMXD(Some(value.try_into().unwrap())),
            I::ACAAC(_) => I::ACAAC(Some(value.try_into().unwrap())),
            I::SBR(_) => I::SBR(Some(value.try_into().unwrap())),
            x => panic!("{x:?} has no operand"),
        }
    }

    pub fn to_opcode(self) -> (u8, Option<u8>) {
        match self {
            I::CALL(Some(x)) => ((x >> 8) as u8, Some(x as u8)),
            I::TXA => (0x10, None),
            I::TMA => (0x11, None),
            I::XBA => (0x12, None),
            I::TAMIX => (0x13, None),
            I::TMAIX => (0x14, None),
            I::SARA => (0x15, None),
            I::TAM => (0x16, None),
            I::TTMA => (0x17, None),
            I::TAX => (0x18, None),
            I::TAPSC => (0x19, None),
            I::TAB => (0x1a, None),
            I::SALA4 => (0x1b, None),
            I::TASYN => (0x1c, None),
            I::TAMODE => (0x1d, None),
            I::TATM => (0x1e, None),
            I::BRA => (0x1f, None),
            I::CLX => (0x20, None),
            I::IXC => (0x21, None),
            I::DECXN => (0x22, None),
            I::XBX => (0x23, None),
            I::CLB => (0x24, None),
            I::IBC => (0x25, None),
            I::INCMC => (0x26, None),
            I::DECMN => (0x27, None),
            I::AMAAC => (0x28, None),
            I::SMAAN => (0x29, None),
            I::TBM => (0x2a, None),
            I::TRNDA => (0x2b, None),
            I::ABAAC => (0x2c, None),
            I::SBAAN => (0x2d, None),
            I::SALA => (0x2e, None),
            I::CLA => (0x2f, None),
            I::GET(Some(x)) => (0x30 | x, None),
            I::AXTM => (0x38, None),
            I::AXMA => (0x39, None),
            I::IAC => (0x3a, None),
            I::INTGR => (0x3b, None),
            I::EXTSG => (0x3c, None),
            I::RETN => (0x3d, None),
            I::RETI => (0x3e, None),
            I::SETOFF => (0x3f, None),
            I::BR(Some(x)) => (0x40 | ((x >> 8) as u8), Some(x as u8)),
            I::ANEC(Some(x)) => (0x60, Some(x)),
            I::XGEC(Some(x)) => (0x61, Some(x)),
            I::TCX(Some(x)) => (0x62, Some(x)),
            I::AGEC(Some(x)) => (0x63, Some(x)),
            I::ORCM(Some(x)) => (0x64, Some(x)),
            I::ANDCM(Some(x)) => (0x65, Some(x)),
            I::TSTCM(Some(x)) => (0x66, Some(x)),
            I::TSTCA(Some(x)) => (0x67, Some(x)),
            I::AXCA(Some(x)) => (0x68, Some(x)),
            I::TMAD(Some(x)) => (0x69, Some(x)),
            I::TAMD(Some(x)) => (0x6a, Some(x)),
            I::LUAA => (0x6b, None),
            I::LUAPS => (0x6c, None),
            I::LUAB => (0x6d, None),
            I::TCA(Some(x)) => (0x6e, Some(x)),
            I::TMXD(Some(x)) => (0x6f, Some(x)),
            I::ACAAC(Some(x)) => (0x70 | ((x >> 8) as u8), Some(x as u8)),
            I::SBR(Some(x)) => (0x80 | x, None),
            _ => panic!("attempt to use opcode with None operand"),
        }
    }

    pub fn opcode_to_instruction(opcode: u8) -> Self {
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
            0x30..=0x37 => I::GET(Some(opcode & 0b0111)),
            0x38 => I::AXTM,
            0x39 => I::AXMA,
            0x3A => I::IAC,
            0x3B => I::INTGR,
            0x3C => I::EXTSG,
            0x3D => I::RETN,
            0x3E => I::RETI,
            0x3F => I::SETOFF,
            0x80..=0xFF => I::SBR(Some(opcode & 0b0111_1111)),
            _ => unreachable!("Opcode with operand called without operand byte."),
        }
    }

    pub fn opcode_to_instruction_with_operand_byte(opcode: u8, operand: u8) -> Self {
        match opcode {
            0x00..=0x0F => I::CALL(Some((opcode as u16) << 8 | operand as u16)),
            0x40..=0x5F => I::BR(Some(((opcode & 0b0001_1111) as u16) << 8 | operand as u16)),
            0x60 => I::ANEC(Some(operand)),
            0x61 => I::XGEC(Some(operand)),
            0x62 => I::TCX(Some(operand)),
            0x63 => I::AGEC(Some(operand)),
            0x64 => I::ORCM(Some(operand)),
            0x65 => I::ANDCM(Some(operand)),
            0x66 => I::TSTCM(Some(operand)),
            0x67 => I::TSTCA(Some(operand)),
            0x68 => I::AXCA(Some(operand)),
            0x69 => I::TMAD(Some(operand)),
            0x6A => I::TAMD(Some(operand)),
            0x6E => I::TCA(Some(operand)),
            0x6F => I::TMXD(Some(operand)),
            0x70..=0x7F => I::ACAAC(Some(((opcode & 0b1111) as u16) << 8 | operand as u16)),
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
        f.write_fmt(format_args!("pc: {:04x} | a: {:04x} | b: {:04x} | x: {:02x} | s: {:x} | mode: {:?} | stack: [{:04x}|{:04x}|{:04x}] | sp: {:3?}",
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

    pub fn assemble(&mut self, program: &str) {
        // step 1: create AST
        // todo: ugly and bad tokeniser might want to clean up
        let ast: Vec<(Option<&str>, Directive)> = program
            .lines()
            .filter_map(|line| {
                // Comment delimiter
                let line = match line.split_once('%') {
                    Some(x) => x.0,
                    None => line,
                };

                let mut words = line.split_whitespace();

                let first_word = match words.next() {
                    Some(x) => x,
                    None => return None,
                };

                fn attatch_operand_to_directive<'a>(
                    directive: Directive<'a>,
                    operand: &'a str,
                ) -> Directive<'a> {
                    match directive {
                        D::I(i) => {
                            let operand: usize = if operand.starts_with('#') {
                                usize::from_str_radix(&operand[1..], 16)
                            } else {
                                usize::from_str(operand)
                            }
                            .expect("failed to parse literal");
                            D::I(i.set_operand_value(operand))
                        }
                        D::Br(_) => D::Br(Some(operand)),
                    }
                }

                Some(match Directive::try_from(first_word) {
                    Ok(directive) => (
                        None,
                        match words.next() {
                            Some(operand) => attatch_operand_to_directive(directive, operand),
                            None => directive,
                        },
                    ),
                    Err(_) => {
                        match Directive::try_from(words.next().expect("label with no opcode")) {
                            Ok(directive) => (
                                Some(
                                    first_word
                                        .rsplit_once(':')
                                        .expect("labels must have colons")
                                        .0,
                                ),
                                match words.next() {
                                    Some(operand) => {
                                        attatch_operand_to_directive(directive, operand)
                                    }
                                    None => directive,
                                },
                            ),
                            Err(_) => {
                                panic!("a directive needs to immediately follow a label")
                            }
                        }
                    }
                })
            })
            .collect();

        // Using a slicevec allows us to construct our assembled program in place.
        let mut assembled = SliceVec::new(&mut self.rom);
        let mut labels: HashMap<&str, u16> = HashMap::new();
        let mut references: Vec<(&str, usize)> = Vec::new();

        for (label, directive) in ast {
            if let Some(l) = label {
                if let Some(v) = labels.insert(l, assembled.len().try_into().unwrap()) {
                    panic!("label {v} used twice");
                }
            }

            let instruction = match directive {
                Directive::I(i) => i,
                Directive::Br(Some(i)) => {
                    references.push((i, assembled.len()));
                    I::BR(Some(0x00))
                }
                _ => panic!("attempt to use directive with None label"),
            };

            match instruction.to_opcode() {
                (i, None) => assembled.push(i).unwrap(),
                (i, Some(o)) => {
                    assembled.push(i).unwrap();
                    assembled.push(o).unwrap()
                }
            }
        }

        // Fix addresses
        for reference in references {
            let opcode = I::BR(Some(labels[reference.0])).to_opcode();
            assembled[reference.1] = opcode.0;
            assembled[reference.1 + 1] = opcode.1.unwrap();
        }
    }

    pub fn run(&mut self) {
        while !self.step() {
            println!("{:?}", self);
        }
    }

    fn step(&mut self) -> bool {
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
            I::ACAAC(Some(operand)) => {
                let a = self.a.unwrap();
                let operand = self.sign_extend_12_to_14_if_extended_sign(u12::new(operand));
                self.set_status((a.value() as u8).overflowing_add(operand.value() as u8).1);
                self.a = OptUninit::Some(a.wrapping_add(operand));
            }
            I::AGEC(Some(operand)) => self.set_status((self.a.unwrap().value() as u8) >= operand),
            I::AMAAC => {
                let mem = self.read_mem_sign_extend(self.x.unwrap());
                self.set_status(
                    (self.a.unwrap().value() as u8)
                        .overflowing_add(mem.value() as u8)
                        .1,
                );
                self.a = OptUninit::Some(self.a.unwrap().wrapping_add(mem));
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
            I::GET(Some(operand)) => {
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
            I::ORCM(Some(operand)) => {
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
            }
            I::SALA4 => {
                self.set_status(true);
                self.a = OptUninit::Some(self.a.unwrap() << 4);
            }
            I::SARA => {
                self.set_status(true);
                self.a = OptUninit::Some(self.a.unwrap() >> 1);
            }
            I::SBAAN => {
                self.set_status((self.a.unwrap().value() as u8) < (self.b.unwrap().value() as u8));
                self.a = OptUninit::Some(self.a.unwrap().wrapping_sub(self.b.unwrap()));
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
            I::SETOFF => return true,
            I::SMAAN => todo!(),
            I::TAB => todo!(),
            I::TAM => todo!(),
            I::TAMD(_) => todo!(),
            I::TAMIX => todo!(),
            I::TAMODE => {
                self.set_status(true);
                self.mode =
                    OptUninit::Some(Mode::from_bits(self.a.unwrap().value() as u8).unwrap());
            }
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
            _ => panic!("attempt to use opcode with None operand"),
        }
        false
    }
}

fn main() {
    let mut emulator = TSP50::new();

    let mut program = String::new();
    File::open("src/test.asm")
        .unwrap()
        .read_to_string(&mut program)
        .unwrap();
    emulator.assemble(&program);

    emulator.run();
}
