//! # Instruction info
//!
//! instruction.rs is responsible for all the info and tables required to
//! represent all the opcodes for the assembler and directives for the assembler
//! macros could possibly make this smaller, but it's not too big of a deal.

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
pub enum Directive<'a> {
    I(Instruction),
    Br(Option<&'a str>),
    Aorg(Option<usize>),
    Byte(Option<Vec<u8>>),
    Data(Option<Vec<u16>>),
    Text(Option<&'a str>),
}

pub type I = Instruction;
pub type D<'a> = Directive<'a>;

impl<'a> Directive<'a> {
    pub fn to_str(&self) -> &'static str {
        match self {
            D::I(I::CALL(_)) => "call",
            D::I(I::TXA) => "txa",
            D::I(I::TMA) => "tma",
            D::I(I::XBA) => "xba",
            D::I(I::TAMIX) => "tamix",
            D::I(I::TMAIX) => "tmaix",
            D::I(I::SARA) => "sara",
            D::I(I::TAM) => "tam",
            D::I(I::TTMA) => "ttma",
            D::I(I::TAX) => "tax",
            D::I(I::TAPSC) => "tapsc",
            D::I(I::TAB) => "tab",
            D::I(I::SALA4) => "sala4",
            D::I(I::TASYN) => "tasyn",
            D::I(I::TAMODE) => "tamode",
            D::I(I::TATM) => "tatm",
            D::I(I::BRA) => "bra",
            D::I(I::CLX) => "clx",
            D::I(I::IXC) => "ixc",
            D::I(I::DECXN) => "decxn",
            D::I(I::XBX) => "xbx",
            D::I(I::CLB) => "clb",
            D::I(I::IBC) => "ibc",
            D::I(I::INCMC) => "incmc",
            D::I(I::DECMN) => "decmn",
            D::I(I::AMAAC) => "amaac",
            D::I(I::SMAAN) => "smaan",
            D::I(I::TBM) => "tbm",
            D::I(I::TRNDA) => "trnda",
            D::I(I::ABAAC) => "abaac",
            D::I(I::SBAAN) => "sbaan",
            D::I(I::SALA) => "sala",
            D::I(I::CLA) => "cla",
            D::I(I::GET(_)) => "get",
            D::I(I::AXTM) => "axtm",
            D::I(I::AXMA) => "axma",
            D::I(I::IAC) => "iac",
            D::I(I::INTGR) => "intgr",
            D::I(I::EXTSG) => "extsg",
            D::I(I::RETN) => "retn",
            D::I(I::RETI) => "reti",
            D::I(I::SETOFF) => "setoff",
            D::I(I::BR(_)) => "br",
            D::I(I::ANEC(_)) => "anec",
            D::I(I::XGEC(_)) => "xgec",
            D::I(I::TCX(_)) => "tcx",
            D::I(I::AGEC(_)) => "agec",
            D::I(I::ORCM(_)) => "orcm",
            D::I(I::ANDCM(_)) => "andcm",
            D::I(I::TSTCM(_)) => "tstcm",
            D::I(I::TSTCA(_)) => "tstca",
            D::I(I::AXCA(_)) => "axca",
            D::I(I::TMAD(_)) => "tmad",
            D::I(I::TAMD(_)) => "tamd",
            D::I(I::LUAA) => "luaa",
            D::I(I::LUAPS) => "luaps",
            D::I(I::LUAB) => "luab",
            D::I(I::TCA(_)) => "tca",
            D::I(I::TMXD(_)) => "tmxd",
            D::I(I::ACAAC(_)) => "acaac",
            D::I(I::SBR(_)) => "sbr",
            D::Br(_) => "BR",
            D::Aorg(_) => "AORG",
            D::Byte(_) => "BYTE",
            D::Data(_) => "DATA",
            D::Text(_) => "TEXT",
        }
    }
}

impl TryFrom<&str> for Directive<'_> {
    type Error = ();

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Ok(match value {
            "call" => D::I(I::CALL(None)),
            "txa" => D::I(I::TXA),
            "tma" => D::I(I::TMA),
            "xba" => D::I(I::XBA),
            "tamix" => D::I(I::TAMIX),
            "tmaix" => D::I(I::TMAIX),
            "sara" => D::I(I::SARA),
            "tam" => D::I(I::TAM),
            "ttma" => D::I(I::TTMA),
            "tax" => D::I(I::TAX),
            "tapsc" => D::I(I::TAPSC),
            "tab" => D::I(I::TAB),
            "sala4" => D::I(I::SALA4),
            "tasyn" => D::I(I::TASYN),
            "tamode" => D::I(I::TAMODE),
            "tatm" => D::I(I::TATM),
            "bra" => D::I(I::BRA),
            "clx" => D::I(I::CLX),
            "ixc" => D::I(I::IXC),
            "decxn" => D::I(I::DECXN),
            "xbx" => D::I(I::XBX),
            "clb" => D::I(I::CLB),
            "ibc" => D::I(I::IBC),
            "incmc" => D::I(I::INCMC),
            "decmn" => D::I(I::DECMN),
            "amaac" => D::I(I::AMAAC),
            "smaan" => D::I(I::SMAAN),
            "tbm" => D::I(I::TBM),
            "trnda" => D::I(I::TRNDA),
            "abaac" => D::I(I::ABAAC),
            "sbaan" => D::I(I::SBAAN),
            "sala" => D::I(I::SALA),
            "cla" => D::I(I::CLA),
            "get" => D::I(I::GET(None)),
            "axtm" => D::I(I::AXTM),
            "axma" => D::I(I::AXMA),
            "iac" => D::I(I::IAC),
            "intgr" => D::I(I::INTGR),
            "extsg" => D::I(I::EXTSG),
            "retn" => D::I(I::RETN),
            "reti" => D::I(I::RETI),
            "setoff" => D::I(I::SETOFF),
            "br" => D::I(I::BR(None)),
            "anec" => D::I(I::ANEC(None)),
            "xgec" => D::I(I::XGEC(None)),
            "tcx" => D::I(I::TCX(None)),
            "agec" => D::I(I::AGEC(None)),
            "orcm" => D::I(I::ORCM(None)),
            "andcm" => D::I(I::ANDCM(None)),
            "tstcm" => D::I(I::TSTCM(None)),
            "tstca" => D::I(I::TSTCA(None)),
            "axca" => D::I(I::AXCA(None)),
            "tmad" => D::I(I::TMAD(None)),
            "tamd" => D::I(I::TAMD(None)),
            "luaa" => D::I(I::LUAA),
            "luaps" => D::I(I::LUAPS),
            "luab" => D::I(I::LUAB),
            "tca" => D::I(I::TCA(None)),
            "tmxd" => D::I(I::TMXD(None)),
            "acaac" => D::I(I::ACAAC(None)),
            "sbr" => D::I(I::SBR(None)),
            "BR" => D::Br(None),
            "AORG" => D::Aorg(None),
            "BYTE" => D::Byte(None),
            "DATA" => D::Data(None),
            "TEXT" => D::Text(None),
            _ => Err(())?,
        })
    }
}

impl Instruction {
    pub fn has_operand_byte(opcode: u8) -> bool {
        matches!(opcode, 0x00..=0x0F | 0x40..=0x6A | 0x6E..=0x7F)
    }

    pub fn set_operand_value(self, value: usize) -> Result<Self, ()> {
        Ok(match self {
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
            _ => Err(())?,
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
            _ => Err(format!(
                "instruction '{}' must have an argument",
                D::I(self).to_str()
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
