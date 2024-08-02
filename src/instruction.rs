//! # Instruction info
//!
//! instruction.rs is responsible for all the info and tables required to
//! represent all the opcodes for the assembler and directives for the assembler
//! macros could possibly make this smaller, but it's not too big of a deal.

#![allow(clippy::upper_case_acronyms)]

#[derive(Debug, Copy, Clone)]
pub enum Instruction {
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

#[derive(Debug, Clone)]
pub struct Expr<'a> {
    pub expr: Expression<'a>,
    pub debug: Option<&'a str>,
}

impl<'a> Expr<'a> {
    pub fn new(expr: Expression<'a>, debug: Option<&'a str>) -> Expr<'a> {
        Expr { expr, debug }
    }
}

#[derive(Debug, Clone)]
pub struct BinaryOp<'a> {
    pub operation: BinaryOpType,
    pub operands: Box<(Expr<'a>, Expr<'a>)>,
}

#[derive(Debug, Clone)]
pub struct UnaryOp<'a> {
    pub operation: UnaryOpType,
    pub operand: Box<Expr<'a>>,
}

#[derive(Debug, Clone)]
pub enum BinaryOpType {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug, Clone)]
pub enum UnaryOpType {
    BitNot,
}

#[derive(Debug, Clone)]
pub enum Op<'a> {
    UnaryOp(UnaryOp<'a>),
    BinaryOp(BinaryOp<'a>),
}

#[derive(Debug, Clone)]
pub enum Expression<'a> {
    Symbol(&'a str),
    Literal(usize),
    Op(Op<'a>),
}

#[derive(Debug, Clone)]
pub enum Directive<'a> {
    I((Instruction, Option<Expr<'a>>)),
    Aorg(Option<Expr<'a>>),
    Byte(Option<Vec<Expr<'a>>>),
    Data(Option<Vec<Expr<'a>>>),
    Text(Option<&'a str>),
    Equ(Option<Expr<'a>>),
}

pub type I = Instruction;
pub type D<'a> = Directive<'a>;

impl<'a> Directive<'a> {
    pub fn to_str(&self) -> &'static str {
        match self {
            D::I((i, _)) => i.as_str(),
            D::Aorg(_) => "AORG",
            D::Byte(_) => "BYTE",
            D::Data(_) => "DATA",
            D::Text(_) => "TEXT",
            D::Equ(_) => "EQU",
        }
    }
}

impl TryFrom<&str> for Directive<'_> {
    type Error = ();

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Ok(match value {
            "AORG" => D::Aorg(None),
            "BYTE" => D::Byte(None),
            "DATA" => D::Data(None),
            "TEXT" => D::Text(None),
            "EQU" => D::Equ(None),
            _ => D::I((value.try_into()?, None)),
        })
    }
}

impl TryFrom<&str> for Instruction {
    type Error = ();

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Ok(match value {
            "call" => I::CALL(None),
            "txa" => I::TXA,
            "tma" => I::TMA,
            "xba" => I::XBA,
            "tamix" => I::TAMIX,
            "tmaix" => I::TMAIX,
            "sara" => I::SARA,
            "tam" => I::TAM,
            "ttma" => I::TTMA,
            "tax" => I::TAX,
            "tapsc" => I::TAPSC,
            "tab" => I::TAB,
            "sala4" => I::SALA4,
            "tasyn" => I::TASYN,
            "tamode" => I::TAMODE,
            "tatm" => I::TATM,
            "bra" => I::BRA,
            "clx" => I::CLX,
            "ixc" => I::IXC,
            "decxn" => I::DECXN,
            "xbx" => I::XBX,
            "clb" => I::CLB,
            "ibc" => I::IBC,
            "incmc" => I::INCMC,
            "decmn" => I::DECMN,
            "amaac" => I::AMAAC,
            "smaan" => I::SMAAN,
            "tbm" => I::TBM,
            "trnda" => I::TRNDA,
            "abaac" => I::ABAAC,
            "sbaan" => I::SBAAN,
            "sala" => I::SALA,
            "cla" => I::CLA,
            "get" => I::GET(None),
            "axtm" => I::AXTM,
            "axma" => I::AXMA,
            "iac" => I::IAC,
            "intgr" => I::INTGR,
            "extsg" => I::EXTSG,
            "retn" => I::RETN,
            "reti" => I::RETI,
            "setoff" => I::SETOFF,
            "br" => I::BR(None),
            "anec" => I::ANEC(None),
            "xgec" => I::XGEC(None),
            "tcx" => I::TCX(None),
            "agec" => I::AGEC(None),
            "orcm" => I::ORCM(None),
            "andcm" => I::ANDCM(None),
            "tstcm" => I::TSTCM(None),
            "tstca" => I::TSTCA(None),
            "axca" => I::AXCA(None),
            "tmad" => I::TMAD(None),
            "tamd" => I::TAMD(None),
            "luaa" => I::LUAA,
            "luaps" => I::LUAPS,
            "luab" => I::LUAB,
            "tca" => I::TCA(None),
            "tmxd" => I::TMXD(None),
            "acaac" => I::ACAAC(None),
            "sbr" => I::SBR(None),
            _ => Err(())?,
        })
    }
}

impl Instruction {
    pub fn has_operand_byte(opcode: u8) -> bool {
        matches!(opcode, 0x00..=0x0F | 0x40..=0x6A | 0x6E..=0x7F)
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            I::CALL(_) => "call",
            I::TXA => "txa",
            I::TMA => "tma",
            I::XBA => "xba",
            I::TAMIX => "tamix",
            I::TMAIX => "tmaix",
            I::SARA => "sara",
            I::TAM => "tam",
            I::TTMA => "ttma",
            I::TAX => "tax",
            I::TAPSC => "tapsc",
            I::TAB => "tab",
            I::SALA4 => "sala4",
            I::TASYN => "tasyn",
            I::TAMODE => "tamode",
            I::TATM => "tatm",
            I::BRA => "bra",
            I::CLX => "clx",
            I::IXC => "ixc",
            I::DECXN => "decxn",
            I::XBX => "xbx",
            I::CLB => "clb",
            I::IBC => "ibc",
            I::INCMC => "incmc",
            I::DECMN => "decmn",
            I::AMAAC => "amaac",
            I::SMAAN => "smaan",
            I::TBM => "tbm",
            I::TRNDA => "trnda",
            I::ABAAC => "abaac",
            I::SBAAN => "sbaan",
            I::SALA => "sala",
            I::CLA => "cla",
            I::GET(_) => "get",
            I::AXTM => "axtm",
            I::AXMA => "axma",
            I::IAC => "iac",
            I::INTGR => "intgr",
            I::EXTSG => "extsg",
            I::RETN => "retn",
            I::RETI => "reti",
            I::SETOFF => "setoff",
            I::BR(_) => "br",
            I::ANEC(_) => "anec",
            I::XGEC(_) => "xgec",
            I::TCX(_) => "tcx",
            I::AGEC(_) => "agec",
            I::ORCM(_) => "orcm",
            I::ANDCM(_) => "andcm",
            I::TSTCM(_) => "tstcm",
            I::TSTCA(_) => "tstca",
            I::AXCA(_) => "axca",
            I::TMAD(_) => "tmad",
            I::TAMD(_) => "tamd",
            I::LUAA => "luaa",
            I::LUAPS => "luaps",
            I::LUAB => "luab",
            I::TCA(_) => "tca",
            I::TMXD(_) => "tmxd",
            I::ACAAC(_) => "acaac",
            I::SBR(_) => "sbr",
        }
    }

    pub fn set_operand_value<'a>(self, value: usize) -> Result<Self, &'a str> {
        Ok(match self {
            I::CALL(_) => I::CALL(Some(value as u16)),
            I::GET(_) => I::GET(Some(value as u8)),
            I::BR(_) => I::BR(Some(value as u16)),
            I::ANEC(_) => I::ANEC(Some(value as u8)),
            I::XGEC(_) => I::XGEC(Some(value as u8)),
            I::TCX(_) => I::TCX(Some(value as u8)),
            I::AGEC(_) => I::AGEC(Some(value as u8)),
            I::ORCM(_) => I::ORCM(Some(value as u8)),
            I::ANDCM(_) => I::ANDCM(Some(value as u8)),
            I::TSTCM(_) => I::TSTCM(Some(value as u8)),
            I::TSTCA(_) => I::TSTCA(Some(value as u8)),
            I::AXCA(_) => I::AXCA(Some(value as u8)),
            I::TMAD(_) => I::TMAD(Some(value as u8)),
            I::TAMD(_) => I::TAMD(Some(value as u8)),
            I::TCA(_) => I::TCA(Some(value as u8)),
            I::TMXD(_) => I::TMXD(Some(value as u8)),
            I::ACAAC(_) => I::ACAAC(Some(value as u16)),
            I::SBR(_) => I::SBR(Some(value as u8)),
            _ => Err("instruction has no operand")?,
        })
    }

    pub fn to_opcode(self) -> Result<(u8, Option<u8>), String> {
        Ok(match self {
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
            I::GET(Some(x)) => (0x30 | (x - 1), None),
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
            _ => Err(format!(
                "instruction '{}' must have an argument",
                self.as_str()
            ))?,
        })
    }

    pub fn cycles(&self) -> usize {
        if matches!(
            self,
            I::ACAAC(_)
                | I::AGEC(_)
                | I::ANDCM(_)
                | I::ANEC(_)
                | I::AXCA(_)
                | I::BR(_)
                | I::CALL(_)
                | I::GET(_)
                | I::LUAA
                | I::LUAB
                | I::LUAPS
                | I::ORCM(_)
                | I::TAMD(_)
                | I::TCA(_)
                | I::TCX(_)
                | I::TMAD(_)
                | I::TMXD(_)
                | I::TSTCA(_)
                | I::TSTCM(_)
                | I::XGEC(_)
        ) {
            2
        } else {
            1
        }
    }

    pub fn num_bytes(&self) -> usize {
        if matches!(
            self,
            I::ACAAC(_)
                | I::AGEC(_)
                | I::ANDCM(_)
                | I::ANEC(_)
                | I::AXCA(_)
                | I::BR(_)
                | I::CALL(_)
                | I::ORCM(_)
                | I::TAMD(_)
                | I::TCA(_)
                | I::TCX(_)
                | I::TMAD(_)
                | I::TMXD(_)
                | I::TSTCA(_)
                | I::TSTCM(_)
                | I::XGEC(_)
        ) {
            2
        } else {
            1
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
            0x30..=0x37 => I::GET(Some((opcode & 0b0111) + 1)),
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
