//! # Assembler
//!
//! This assembler has full unicode support and a syntax highlighting file.

use std::fmt::Write;
use std::ops::Range;
use std::str::FromStr;
use std::{borrow::Borrow, collections::HashMap};
use unicode_width::UnicodeWidthStr;

use crate::instruction::{
    BinaryOp, BinaryOpType, Directive, Expr, Expression, Instruction, Op, UnaryOp, UnaryOpType, D,
};
use inline_colorization::*;

#[derive(Debug)]
pub struct SyntaxError<'a> {
    pub msg: Vec<&'a str>,
    pub slice: &'a str,
}

fn lstrip_whitespace(value: &str) -> Option<&str> {
    value
        .find(|c: char| !c.is_whitespace())
        .map(|x| &value[x..])
}

fn rstrip_whitespace(value: &str) -> Option<&str> {
    value
        .rfind(|c: char| !c.is_whitespace())
        .map(|idx| match value[idx..].char_indices().nth(1) {
            Some((next_idx, _)) => &value[..idx + next_idx],
            None => value,
        })
}

pub fn strip_whitespace(value: &str) -> Option<&str> {
    lstrip_whitespace(value).and_then(|x| rstrip_whitespace(x))
}

fn segment_ptr_to_str(value: usize) -> &'static str {
    match value {
        0 => "__segment_0",
        1 => "__segment_1",
        2 => "__segment_2",
        3 => "__segment_3",
        4 => "__segment_4",
        5 => "__segment_5",
        6 => "__segment_6",
        7 => "__segment_7",
        8 => "__segment_8",
        9 => "__segment_9",
        10 => "__segment_10",
        11 => "__segment_11",
        12 => "__segment_12",
        13 => "__segment_13",
        14 => "__segment_14",
        15 => "__segment_15",
        _ => panic!("uh oh I ran out of segment names.. add more please"),
    }
}

pub fn parse_expression(literal: &str) -> Result<Expr, SyntaxError> {
    match parse_order_of_operations(literal)? {
        Some(op) => Ok(Expr::new(Expression::Op(op), Some(literal))),
        None => match if let Some(hex) = literal.strip_prefix('#') {
            usize::from_str_radix(hex, 16)
        } else {
            usize::from_str(literal)
        } {
            Ok(v) => Ok(Expr::new(Expression::Literal(v), Some(literal))),
            Err(_) => Ok(Expr::new(Expression::Symbol(literal.into()), Some(literal))),
        },
    }
}

fn parse_order_of_operations(value: &str) -> Result<Option<Op>, SyntaxError> {
    fn to_op_binary(
        op_type: BinaryOpType,
        value: &str,
        idx: usize,
    ) -> Result<Option<Op>, SyntaxError> {
        let (left, right) = (
            &value[..idx],
            value
                .char_indices()
                .nth(1)
                .map(|(i, _)| &value[idx + i..])
                .unwrap_or(&value[idx..idx]),
        );
        Ok(Some(Op::BinaryOp(BinaryOp {
            operation: op_type,
            operands: Box::new((
                parse_expression(strip_whitespace(left).ok_or_else(|| SyntaxError {
                    msg: vec!["must have expression to the left of a binary operator"],
                    slice: left,
                })?)?,
                parse_expression(strip_whitespace(right).ok_or_else(|| SyntaxError {
                    msg: vec!["must have expression the right of a binary operator"],
                    slice: right,
                })?)?,
            )),
        })))
    }

    fn to_op_unary(
        op_type: UnaryOpType,
        value: &str,
        idx: usize,
    ) -> Result<Option<Op>, SyntaxError> {
        let right = value
            .char_indices()
            .nth(1)
            .map(|(i, _)| &value[idx + i..])
            .unwrap_or(&value[idx..idx]);

        Ok(Some(Op::UnaryOp(UnaryOp {
            operation: op_type,
            operand: Box::new(parse_expression(strip_whitespace(right).ok_or_else(
                || SyntaxError {
                    msg: vec!["must have expression right of a unary operator"],
                    slice: right,
                },
            )?)?),
        })))
    }

    match value.char_indices().rfind(|(_, c)| matches!(c, '+' | '-')) {
        Some((idx, c)) => match c {
            '+' => to_op_binary(BinaryOpType::Add, value, idx),
            '-' => to_op_binary(BinaryOpType::Sub, value, idx),
            _ => unreachable!(),
        },
        None => match value.char_indices().rfind(|(_, c)| matches!(c, '*' | '/')) {
            Some((idx, c)) => match c {
                '*' => to_op_binary(BinaryOpType::Mul, value, idx),
                '/' => to_op_binary(BinaryOpType::Div, value, idx),
                _ => unreachable!(),
            },
            None => match value.char_indices().rfind(|(_, c)| matches!(c, '~')) {
                Some((idx, c)) => match c {
                    '~' => to_op_unary(UnaryOpType::BitNot, value, idx),
                    _ => unreachable!(),
                },
                None => Ok(None),
            },
        },
    }
}

pub fn resolve_expression<'a>(
    expression: &'a Expr<'a>,
    symbols: &'a HashMap<&'a str, Expr<'a>>,
) -> Result<usize, (&'a str, &'a str)> {
    match &expression.expr {
        Expression::Literal(x) => Ok(*x),
        Expression::Symbol(s) => match symbols.get(s) {
            Some(sym) => resolve_expression(sym, symbols),
            None => Err(("symbol not found", expression.debug.expect("no debug info"))),
        },
        Expression::Op(op) => match op {
            Op::UnaryOp(op) => {
                let right = resolve_expression(&op.operand, symbols)?;
                Ok(match op.operation {
                    UnaryOpType::BitNot => !right,
                })
            }
            Op::BinaryOp(op) => {
                let (left, right) = op.operands.borrow();
                let left: usize = resolve_expression(left, symbols)?;
                let right = resolve_expression(right, symbols)?;
                Ok(match op.operation {
                    BinaryOpType::Add => left + right,
                    BinaryOpType::Sub => left - right,
                    BinaryOpType::Mul => left * right,
                    BinaryOpType::Div => left / right,
                })
            }
        },
    }
}

type AstFrame<'a> = (Option<&'a str>, Option<Directive<'a>>, &'a str);

fn make_ast(source: &str) -> Result<Vec<AstFrame>, SyntaxError> {
    fn parse_expression_list(line: &str) -> Result<Vec<Expr>, SyntaxError> {
        line.split(',')
            .map(parse_expression)
            .collect::<Result<Vec<_>, _>>()
    }

    fn parse_argument<'a>(
        label: Option<&'a str>,
        directive: Directive<'a>,
        line: &'a str,
    ) -> Result<(Option<&'a str>, Option<Directive<'a>>), SyntaxError<'a>> {
        match match line
            .char_indices()
            .find(|(_, c)| !c.is_whitespace())
            .map_or(Ok(None), |(idx, c)| match c {
                '"' => {
                    let err = || {
                        Err(SyntaxError {
                            msg: vec!["no closing double quote"],
                            slice: &line[idx..],
                        })
                    };
                    line[idx..]
                        .char_indices()
                        .nth(1)
                        .map_or(err(), |(next_idx, _)| {
                            line[(idx + next_idx)..].find('"').map_or(err(), |end| {
                                Ok(Some(&line[(idx + next_idx)..(idx + next_idx + end)]))
                            })
                        })
                }
                '%' => Ok(None),
                _ => {
                    let end_idx = line[idx..]
                        .find('%')
                        .map_or(&line[idx..], |x| &line[idx..(idx + x)])
                        .rfind(|c: char| !c.is_whitespace())
                        .unwrap();

                    Ok(Some(
                        line[idx + end_idx..]
                            .char_indices()
                            .nth(1)
                            .map_or(&line[idx..], |(next_idx, _)| {
                                &line[idx..(idx + end_idx + next_idx)]
                            }),
                    ))
                }
            }) {
            Ok(Some(arg)) => match directive {
                D::I((i, _)) => parse_expression(arg).map(|x| D::I((i, Some(x)))),
                D::Aorg(_) => parse_expression(arg).map(|x| D::Aorg(Some(x))),
                D::Byte(_) => parse_expression_list(arg).map(|x| D::Byte(Some(x))),
                D::Data(_) => parse_expression_list(arg).map(|x| D::Data(Some(x))),
                D::Text(_) => Ok(D::Text(Some(arg))),
                D::Equ(_) => parse_expression(arg).map(|x| D::Equ(Some(x))),
            },
            Ok(None) => Ok(directive),
            Err(e) => Err(e),
        } {
            Ok(directive) => Ok((label, Some(directive))),
            Err(e) => Err(e),
        }
    }

    fn parse_keyword_or_label<'a>(
        label: Option<&'a str>,
        line: &'a str,
    ) -> Result<(Option<&'a str>, Option<Directive<'a>>), SyntaxError<'a>> {
        let get_directive = |s| match Directive::try_from(s) {
            Ok(d) => Ok((label, Some(d))),
            Err(_) => Err(SyntaxError {
                msg: vec!["directive not recognised"],
                slice: s,
            }),
        };

        match line
            .char_indices()
            .find(|(_, c)| c.is_whitespace() || matches!(c, ':' | '%'))
        {
            Some((idx, c)) => {
                match c {
                    // Label
                    ':' => line[idx..].char_indices().nth(1).map_or(
                        Ok((Some(&line[..idx]), None)),
                        |(after_colon, _)| {
                            parse_line(Some(&line[..idx]), &line[(idx + after_colon)..])
                        },
                    ),
                    // Comment delimiter
                    '%' => get_directive(&line[..idx]),
                    // Keyword, get operand and strip whitespace on both sides
                    _ => match Directive::try_from(&line[..idx]) {
                        Ok(d) => parse_argument(label, d, &line[idx..]),
                        Err(_) => Err(SyntaxError {
                            msg: vec!["directive not recognised"],
                            slice: &line[..idx],
                        }),
                    },
                }
            }
            None => get_directive(line),
        }
    }

    fn parse_line<'a>(
        label: Option<&'a str>,
        line: &'a str,
    ) -> Result<(Option<&'a str>, Option<Directive<'a>>), SyntaxError<'a>> {
        line.char_indices()
            .find(|(_, c)| !c.is_whitespace())
            .map(|(idx, c)| match c {
                '%' => Ok((label, None)),
                _ => parse_keyword_or_label(label, &line[idx..]),
            })
            .unwrap_or(Ok((label, None)))
    }

    source
        .lines()
        .filter_map(|line| match parse_line(None, line) {
            Ok((None, None)) => None,
            Ok((label, directive)) => Some(Ok((label, directive, line))),
            Err(e) => Some(Err(e)),
        })
        .collect()
}

enum SquigglyColor {
    Red,
    Green,
}

fn draw_line(
    msg: &mut String,
    source: &str,
    filename: &str,
    squiggly: &str,
    squiggly_color: SquigglyColor,
) {
    let line_number = source[..(squiggly.as_bytes().as_ptr() as usize - source.as_ptr() as usize)]
        .chars()
        .fold(0usize, |count, c| if c == '\n' { count + 1 } else { count });

    let line = source.lines().nth(line_number).unwrap();
    let line_number = line_number + 1; // Stupid humans start their line numbers at 1
    let padding = " ".repeat(line_number.to_string().len());

    {
        let column = squiggly.as_bytes().as_ptr_range().start as usize - line.as_ptr() as usize;

        writeln!(
            msg,
            "{padding}{color_blue}-->{color_reset}{style_reset} {filename}:{line_number}:{column}"
        )
        .unwrap();

        writeln!(msg, " {padding}{style_bold}{color_blue}|").unwrap();
        writeln!(msg, "{line_number} |{color_reset}{style_reset} {line}").unwrap();
        write!(
            msg,
            " {padding}{color_blue}{style_bold}|{color_reset}{style_reset}"
        )
        .unwrap();

        match squiggly_color {
            SquigglyColor::Red => write!(
                msg,
                " {color_red}{}{color_reset}{style_reset}",
                " ".repeat(line[..column].width()) + &("^".repeat(squiggly.width()))
            )
            .unwrap(),
            SquigglyColor::Green => write!(
                msg,
                " {color_green}{}{color_reset}{style_reset}",
                " ".repeat(line[..column].width()) + &("^".repeat(squiggly.width()))
            )
            .unwrap(),
        }
    }
}

pub fn assemble<'a>(
    filename: &str,
    source: &'a str,
    rom: (&mut [u8], &mut [u8]),
) -> Result<(HashMap<usize, &'a str>, HashMap<&'a str, Expr<'a>>), String> {
    let ast: Vec<(Option<&str>, Option<Directive>, &str)> = make_ast(source).map_err(|e| {
        let mut msg = String::new();
        writeln!(
            msg,
            "{style_bold}{color_red}error{color_reset}: {}",
            e.msg.concat()
        )
        .unwrap();
        draw_line(&mut msg, source, filename, e.slice, SquigglyColor::Red);

        msg
    })?;

    #[derive(Debug)]
    struct Reference<'a> {
        segment: usize,
        byte: usize,
        directive: Directive<'a>,
    }

    #[derive(Debug)]
    struct Segment<'a> {
        start: Expr<'a>,
        label: &'a str,
        assembled: Vec<u8>,
    }

    let mut segments: Vec<Segment> = Vec::new();

    segments.push(Segment {
        start: Expr::new(Expression::Literal(0), None),
        label: "__segment_0".into(),
        assembled: Vec::new(),
    });

    let mut segment_ptr = 0;

    let mut symbols: HashMap<&str, Expr> = HashMap::new();
    let mut references: Vec<Reference> = Vec::new();

    fn used_twice_err(
        source: &str,
        filename: &str,
        error_squiggly: &str,
        warning_squiggly: &str,
    ) -> String {
        let mut err = String::new();
        writeln!(err, "{style_bold}{color_red}error{color_reset}: label '{error_squiggly}' used twice{style_reset}").unwrap();

        draw_line(
            &mut err,
            source,
            filename,
            error_squiggly,
            SquigglyColor::Red,
        );

        writeln!(
            err,
            "\n{style_bold}{color_green}note{color_reset}: previously used here",
        )
        .unwrap();
        draw_line(
            &mut err,
            source,
            filename,
            warning_squiggly,
            SquigglyColor::Green,
        );
        err
    }

    let mut debug_symbols: Vec<Expr> = Vec::new();

    for (label, directive, line) in ast {
        if !matches!(directive, Some(D::Equ(_))) {
            if let Some(l) = label {
                if let Some(e) = symbols.insert(
                    l,
                    Expr::new(
                        Expression::Op(Op::BinaryOp(BinaryOp {
                            operation: BinaryOpType::Add,
                            operands: Box::new((
                                Expr::new(
                                    Expression::Symbol(segments.last().unwrap().label),
                                    Some(l),
                                ),
                                Expr::new(
                                    Expression::Literal(segments.last().unwrap().assembled.len()),
                                    Some(l),
                                ),
                            )),
                        })),
                        Some(l),
                    ),
                ) {
                    Err(used_twice_err(
                        source,
                        filename,
                        l,
                        e.debug.expect("no debug info"),
                    ))?;
                }
            }
        }

        fn write_opcode(instruction: &Instruction, assembled: &mut Vec<u8>) -> Result<(), String> {
            match instruction.to_opcode()? {
                (i, None) => {
                    assembled.push(i);
                }
                (i, Some(o)) => {
                    assembled.push(i);
                    assembled.push(o);
                }
            };

            Ok(())
        }

        let segment = segments.last_mut().unwrap();

        let mut push_debug_symbol = || {
            debug_symbols.push(Expr {
                expr: Expression::Op(Op::BinaryOp(BinaryOp {
                    operation: BinaryOpType::Add,
                    operands: Box::new((
                        Expr::new(Expression::Symbol(segment.label), None),
                        Expr::new(Expression::Literal(segment.assembled.len()), None),
                    )),
                })),
                debug: Some(line),
            });
        };

        if let Some(d) = directive {
            match d {
                Directive::I((instruction, None)) => {
                    push_debug_symbol();
                    write_opcode(&instruction, &mut segment.assembled)
                }
                Directive::I((instruction, Some(_))) => {
                    push_debug_symbol();
                    references.push(Reference {
                        segment: segment_ptr,
                        byte: segment.assembled.len(),
                        directive: d,
                    }); // Add expression to refrence list

                    // Ensure offset correct by filling out reigon with zeros
                    match instruction.num_bytes() {
                        2 => {
                            segment.assembled.push(Default::default());
                            segment.assembled.push(Default::default());
                        }
                        1 => {
                            segment.assembled.push(Default::default());
                        }
                        _ => unreachable!(),
                    }

                    Ok(())
                }
                Directive::Aorg(Some(i)) => {
                    if segment.assembled.is_empty() {
                        segment.start = i
                    } else {
                        segment_ptr += 1;
                        segments.push(Segment {
                            start: i,
                            label: segment_ptr_to_str(segment_ptr),
                            assembled: Vec::new(),
                        });
                    }

                    Ok(())
                }
                Directive::Byte(Some(ref expr_list)) => {
                    push_debug_symbol();
                    let old_len = segment.assembled.len();

                    for _ in expr_list {
                        segment.assembled.push(Default::default());
                    }

                    references.push(Reference {
                        segment: segment_ptr,
                        byte: old_len,
                        directive: d,
                    });

                    Ok(())
                }
                Directive::Data(Some(ref expr_list)) => {
                    push_debug_symbol();
                    let old_len = segment.assembled.len();

                    for _ in expr_list {
                        segment.assembled.push(Default::default());
                        segment.assembled.push(Default::default());
                    }

                    references.push(Reference {
                        segment: segment_ptr,
                        byte: old_len,
                        directive: d,
                    });

                    Ok(())
                }
                Directive::Text(Some(i)) => {
                    push_debug_symbol();
                    for &byte in i.as_bytes() {
                        segment.assembled.push(byte);
                    }

                    Ok(())
                }
                Directive::Equ(Some(expr)) => label
                    .ok_or("EQU directive must have symbol to define".to_string())
                    .and_then(|l| match symbols.insert(l, expr) {
                        Some(x) => Err(used_twice_err(
                            source,
                            filename,
                            l,
                            x.debug.expect("no debug info"),
                        )),
                        None => Ok(()),
                    }),
                _ => Err(format!("directive {} must have an argument", d.to_str())),
            }?
        }
    }

    fn make_error_msg(msg: &str, squiggly: &str, source: &str, filename: &str) -> String {
        let mut err = String::new();
        writeln!(
            err,
            "{style_bold}{color_red}error{color_reset}: {msg}{style_reset}"
        )
        .unwrap();

        draw_line(&mut err, source, filename, squiggly, SquigglyColor::Red);
        err
    }

    enum RomLocation {
        Rom,
        ExcitationRom,
    }

    let mut segment_layout: Vec<(RomLocation, usize, Range<*const u8>)> = Vec::new();
    // resolve segments
    for (idx, segment) in segments.iter().enumerate() {
        let lower = resolve_expression(&segment.start, &symbols)
            .map_err(|(msg, squiggly)| make_error_msg(msg, squiggly, source, filename))?;
        symbols.insert(&segment.label, Expr::new(Expression::Literal(lower), None));
        let upper = lower + segment.assembled.len();

        if lower >= 0x4000 {
            let lower = lower - 0x4000;
            let upper = upper - 0x4000;

            let a = rom.1[lower..upper].as_ptr_range();
            for (_, _, b) in &segment_layout {
                if (b.start <= a.start && a.start < b.end) || (b.start <= a.end && a.end < b.end) {
                    panic!("uh oh spaghettio AORG clobbo'd your data")
                }
            }
            segment_layout.push((
                RomLocation::ExcitationRom,
                idx,
                rom.1[lower..upper].as_ptr_range(),
            ));

            rom.1[lower..upper].copy_from_slice(&segment.assembled);
        } else {
            let a = rom.0[lower..upper].as_ptr_range();
            for (_, _, b) in &segment_layout {
                if (b.start <= a.start && a.start < b.end) || (b.start <= a.end && a.end < b.end) {
                    panic!("uh oh spaghettio AORG clobbo'd your data")
                }
            }
            segment_layout.push((RomLocation::Rom, idx, rom.0[lower..upper].as_ptr_range()));

            rom.0[lower..upper].copy_from_slice(&segment.assembled);
        }
    }

    for r in references {
        let (location, _, range) = segment_layout
            .iter()
            .find(|(_, s, _)| *s == r.segment)
            .unwrap();

        let (buf, write_idx) = match location {
            RomLocation::Rom => {
                let idx = range.start as usize - rom.0.as_ptr() as usize + r.byte;
                (&mut *rom.0, idx)
            }
            RomLocation::ExcitationRom => {
                let idx = range.start as usize - rom.1.as_ptr() as usize + r.byte;
                (&mut *rom.1, idx)
            }
        };

        match r.directive {
            Directive::I((i, expr)) => {
                match i
                    .set_operand_value(
                        resolve_expression(expr.as_ref().unwrap(), &symbols).map_err(
                            |(msg, squiggly)| make_error_msg(msg, squiggly, source, filename),
                        )?,
                    )
                    .map_err(|msg| {
                        make_error_msg(msg, expr.as_ref().unwrap().debug.unwrap(), source, filename)
                    })?
                    .to_opcode()
                    .unwrap()
                {
                    (x, None) => {
                        buf[write_idx] = x;
                    }
                    (x, Some(y)) => {
                        buf[write_idx] = x;
                        buf[write_idx + 1] = y;
                    }
                }
            }
            Directive::Byte(x) => {
                for (idx, e) in x.unwrap().iter().enumerate() {
                    buf[write_idx + idx] = resolve_expression(e, &symbols)
                        .map_err(|(msg, squiggly)| make_error_msg(msg, squiggly, source, filename))?
                        .try_into()
                        .unwrap();
                }
            }
            Directive::Data(x) => {
                for (idx, e) in x.unwrap().iter().enumerate() {
                    let val: u16 = resolve_expression(e, &symbols)
                        .map_err(|(msg, squiggly)| make_error_msg(msg, squiggly, source, filename))?
                        .try_into()
                        .unwrap();
                    buf[write_idx + 2 * idx] = (val >> 8) as u8;
                    buf[write_idx + 2 * idx + 1] = val as u8;
                }
            }
            Directive::Aorg(_) => unreachable!(),
            Directive::Text(_) => unreachable!(),
            Directive::Equ(_) => unreachable!(),
        }
    }

    let mut resolved_debug_symbols: HashMap<usize, &str> = HashMap::new();

    for expr in debug_symbols {
        resolved_debug_symbols.insert(
            resolve_expression(&expr, &symbols).unwrap(),
            expr.debug.unwrap(),
        );
    }

    Ok((resolved_debug_symbols, symbols))
}
