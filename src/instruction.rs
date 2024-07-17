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

impl TryFrom<&str> for Directive<'_> {
    type Error = ();

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "call" => Ok(D::I(I::CALL(None))),
            "txa" => Ok(D::I(I::TXA)),
            "tma" => Ok(D::I(I::TMA)),
            "xba" => Ok(D::I(I::XBA)),
            "tamix" => Ok(D::I(I::TAMIX)),
            "tmaix" => Ok(D::I(I::TMAIX)),
            "sara" => Ok(D::I(I::SARA)),
            "tam" => Ok(D::I(I::TAM)),
            "ttma" => Ok(D::I(I::TTMA)),
            "tax" => Ok(D::I(I::TAX)),
            "tapsc" => Ok(D::I(I::TAPSC)),
            "tab" => Ok(D::I(I::TAB)),
            "sala4" => Ok(D::I(I::SALA4)),
            "tasyn" => Ok(D::I(I::TASYN)),
            "tamode" => Ok(D::I(I::TAMODE)),
            "tatm" => Ok(D::I(I::TATM)),
            "bra" => Ok(D::I(I::BRA)),
            "clx" => Ok(D::I(I::CLX)),
            "ixc" => Ok(D::I(I::IXC)),
            "decxn" => Ok(D::I(I::DECXN)),
            "xbx" => Ok(D::I(I::XBX)),
            "clb" => Ok(D::I(I::CLB)),
            "ibc" => Ok(D::I(I::IBC)),
            "incmc" => Ok(D::I(I::INCMC)),
            "decmn" => Ok(D::I(I::DECMN)),
            "amaac" => Ok(D::I(I::AMAAC)),
            "smaan" => Ok(D::I(I::SMAAN)),
            "tbm" => Ok(D::I(I::TBM)),
            "trnda" => Ok(D::I(I::TRNDA)),
            "abaac" => Ok(D::I(I::ABAAC)),
            "sbaan" => Ok(D::I(I::SBAAN)),
            "sala" => Ok(D::I(I::SALA)),
            "cla" => Ok(D::I(I::CLA)),
            "get" => Ok(D::I(I::GET(None))),
            "axtm" => Ok(D::I(I::AXTM)),
            "axma" => Ok(D::I(I::AXMA)),
            "iac" => Ok(D::I(I::IAC)),
            "intgr" => Ok(D::I(I::INTGR)),
            "extsg" => Ok(D::I(I::EXTSG)),
            "retn" => Ok(D::I(I::RETN)),
            "reti" => Ok(D::I(I::RETI)),
            "setoff" => Ok(D::I(I::SETOFF)),
            "br" => Ok(D::I(I::BR(None))),
            "anec" => Ok(D::I(I::ANEC(None))),
            "xgec" => Ok(D::I(I::XGEC(None))),
            "tcx" => Ok(D::I(I::TCX(None))),
            "agec" => Ok(D::I(I::AGEC(None))),
            "orcm" => Ok(D::I(I::ORCM(None))),
            "andcm" => Ok(D::I(I::ANDCM(None))),
            "tstcm" => Ok(D::I(I::TSTCM(None))),
            "tstca" => Ok(D::I(I::TSTCA(None))),
            "axca" => Ok(D::I(I::AXCA(None))),
            "tmad" => Ok(D::I(I::TMAD(None))),
            "tamd" => Ok(D::I(I::TAMD(None))),
            "luaa" => Ok(D::I(I::LUAA)),
            "luaps" => Ok(D::I(I::LUAPS)),
            "luab" => Ok(D::I(I::LUAB)),
            "tca" => Ok(D::I(I::TCA(None))),
            "tmxd" => Ok(D::I(I::TMXD(None))),
            "acaac" => Ok(D::I(I::ACAAC(None))),
            "sbr" => Ok(D::I(I::SBR(None))),
            "BR" => Ok(D::Br(None)),
            "AORG" => Ok(D::Aorg(None)),
            "BYTE" => Ok(D::Byte(None)),
            "DATA" => Ok(D::Data(None)),
            "TEXT" => Ok(D::Text(None)),
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
