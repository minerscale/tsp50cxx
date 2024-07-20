//! # Assembler
//!
//! This assembler has full unicode support and a syntax highlighting file.

use std::fmt::Write;
use std::fs::File;
use std::io::Read;
use std::ops::Range;
use std::rc::Rc;
use std::str::FromStr;
use std::{borrow::Borrow, collections::HashMap};
use unicode_width::UnicodeWidthStr;

use crate::instruction::{BinaryOpType, Directive, Expr, Expression, Instruction, D};
use inline_colorization::*;

#[derive(Debug)]
struct SyntaxError<'a> {
    msg: Vec<&'a str>,
    slice: &'a str,
}

fn lstrip_whitespace<'a>(value: &'a str) -> Option<&'a str> {
    value
        .find(|c: char| !c.is_whitespace())
        .map(|x| &value[x..])
}

fn rstrip_whitespace<'a>(value: &'a str) -> Option<&'a str> {
    value.rfind(|c: char| !c.is_whitespace()).and_then(|idx| {
        match value[idx..].char_indices().nth(1) {
            Some((next_idx, _)) => Some(&value[..idx + next_idx]),
            None => Some(&value),
        }
    })
}

fn strip_whitespace<'a>(value: &'a str) -> Option<&'a str> {
    lstrip_whitespace(value).and_then(|x| rstrip_whitespace(x))
}

fn split_order_of_operations<'a>(value: &'a str) -> Option<(BinaryOpType, (&'a str, &'a str))> {
    value
        .split_once('*')
        .map(|x| (BinaryOpType::Mul, x))
        .or(value
            .split_once('/')
            .map(|x| (BinaryOpType::Div, x))
            .or(value
                .split_once('+')
                .map(|x| (BinaryOpType::Add, x))
                .or(value.split_once('-').map(|x| (BinaryOpType::Sub, x)))))
}

fn make_ast<'a>(
    source: &'a [&'a str],
) -> Result<Vec<(Option<&'a str>, Option<Directive<'a>>)>, SyntaxError<'a>> {
    fn parse_expression(literal: &str) -> Result<Expr, SyntaxError> {
        match split_order_of_operations(literal) {
            Some((op, (left, right))) => Ok(Expr::new(
                Expression::BinaryOp((
                    op,
                    Box::new((
                        parse_expression(strip_whitespace(left).ok_or_else(|| SyntaxError {
                            msg: vec!["must have expression left of '+' operator"],
                            slice: left,
                        })?)?,
                        parse_expression(strip_whitespace(right).ok_or_else(|| SyntaxError {
                            msg: vec!["must have expression right of '+' operator"],
                            slice: right,
                        })?)?,
                    )),
                )),
                Some(literal),
            )),
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

    fn parse_expression_list(line: &str) -> Result<Vec<Expr>, SyntaxError> {
        line.split(',')
            .map(|s| parse_expression(s))
            .collect::<Result<Vec<_>, _>>()
    }

    fn parse_argument<'a>(
        label: Option<&'a str>,
        directive: Directive<'a>,
        line: &'a str,
    ) -> Option<Result<(Option<&'a str>, Option<Directive<'a>>), SyntaxError<'a>>> {
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
            Ok(directive) => Some(Ok((label, Some(directive)))),
            Err(e) => Some(Err(e)),
        }
    }

    fn parse_keyword_or_label<'a>(
        label: Option<&'a str>,
        line: &'a str,
    ) -> Option<Result<(Option<&'a str>, Option<Directive<'a>>), SyntaxError<'a>>> {
        let get_directive = |s| match Directive::try_from(s) {
            Ok(d) => Some(Ok((label, Some(d)))),
            Err(_) => Some(Err(SyntaxError {
                msg: vec!["directive not recognised"],
                slice: s,
            })),
        };

        match line
            .char_indices()
            .find(|(_, c)| c.is_whitespace() || matches!(c, ':' | '%'))
        {
            Some((idx, c)) => {
                match c {
                    // Label
                    ':' => line[idx..].char_indices().nth(1).map_or(
                        Some(Ok((Some(&line[..idx]), None))),
                        |(after_colon, _)| {
                            parse_line(Some(&line[..idx]), &line[(idx + after_colon)..])
                        },
                    ),
                    // Comment delimiter
                    '%' => get_directive(&line[..idx]),
                    // Keyword, get operand and strip whitespace on both sides
                    _ => match Directive::try_from(&line[..idx]) {
                        Ok(d) => parse_argument(label, d, &line[idx..]),
                        Err(_) => Some(Err(SyntaxError {
                            msg: vec!["directive not recognised"],
                            slice: &line[..idx],
                        })),
                    },
                }
            }
            None => get_directive(line),
        }
    }

    fn parse_line<'a>(
        label: Option<&'a str>,
        line: &'a str,
    ) -> Option<Result<(Option<&'a str>, Option<Directive<'a>>), SyntaxError<'a>>> {
        line.char_indices()
            .find(|(_, c)| !c.is_whitespace())
            .and_then(|(idx, c)| match c {
                '%' => None,
                _ => parse_keyword_or_label(label, &line[idx..]),
            })
    }

    source
        .into_iter()
        .filter_map(|&line| {
            parse_line(None, line).map(|x| match x {
                Ok((label, directive)) => Ok((label, directive)),
                Err(e) => Err(e),
            })
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

    // In any other language this wouldn't be hacky
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

pub fn assemble(filename: &str, memory: &mut [u8]) -> Result<(), String> {
    let mut source = String::new();
    File::open(filename)
        .map_err(|_| format!("{style_bold}{color_red}error{color_reset}: unable to open source file '{filename}'{style_reset}"))?
        .read_to_string(&mut source)
        .map_err(|_| format!("{style_bold}{color_red}error{color_reset}: unable to read source file '{filename}'{style_reset}"))?;

    let source_lines = source.lines().collect::<Vec<_>>();
    let ast: Vec<(Option<&str>, Option<Directive>)> = make_ast(&source_lines).map_err(|e| {
        let mut msg = String::new();
        writeln!(
            msg,
            "{style_bold}{color_red}error{color_reset}: {}",
            e.msg.concat()
        )
        .unwrap();
        draw_line(&mut msg, &source, filename, e.slice, SquigglyColor::Red);

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
        label: Rc<str>,
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
            &source,
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
            &source,
            filename,
            warning_squiggly,
            SquigglyColor::Green,
        );
        err
    }

    for (label, directive) in ast {
        if !matches!(directive, Some(D::Equ(_))) {
            if let Some(l) = label {
                if let Some(e) = symbols.insert(
                    l,
                    Expr::new(
                        Expression::BinaryOp((
                            BinaryOpType::Add,
                            Box::new((
                                Expr::new(
                                    Expression::Symbol(segments.last().unwrap().label.clone()),
                                    Some(l),
                                ),
                                Expr::new(
                                    Expression::Literal(segments.last().unwrap().assembled.len()),
                                    Some(l),
                                ),
                            )),
                        )),
                        None,
                    ),
                ) {
                    Err(used_twice_err(
                        &source,
                        filename,
                        l,
                        e.debug.expect("no debug info"),
                    ))?;
                }
            }
        }

        fn write_opcode(instruction: &Instruction, assembled: &mut Vec<u8>) -> Result<(), String> {
            Ok(match instruction.to_opcode()? {
                (i, None) => {
                    assembled.push(i);
                }
                (i, Some(o)) => {
                    assembled.push(i);
                    assembled.push(o);
                }
            })
        }

        let segment = segments.last_mut().unwrap();

        match directive {
            Some(d) => match d {
                Directive::I((instruction, None)) => {
                    write_opcode(&instruction, &mut segment.assembled)
                }
                Directive::I((instruction, Some(_))) => {
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
                            label: ("__segment_".to_owned() + &segment_ptr.to_string()).into(),
                            assembled: Vec::new(),
                        });
                    }

                    Ok(())
                }
                Directive::Byte(Some(ref expr_list)) => {
                    for _ in expr_list {
                        segment.assembled.push(Default::default());
                    }

                    references.push(Reference {
                        segment: segment_ptr,
                        byte: segment.assembled.len(),
                        directive: d,
                    });

                    Ok(())
                }
                Directive::Data(Some(ref expr_list)) => {
                    for _ in expr_list {
                        segment.assembled.push(Default::default());
                        segment.assembled.push(Default::default());
                    }

                    references.push(Reference {
                        segment: segment_ptr,
                        byte: segment.assembled.len(),
                        directive: d,
                    });

                    Ok(())
                }
                Directive::Text(Some(i)) => {
                    for &byte in i.as_bytes() {
                        segment.assembled.push(byte);
                    }

                    Ok(())
                }
                Directive::Equ(Some(expr)) => label
                    .ok_or("EQU directive must have symbol to define".to_string())
                    .and_then(|l| match symbols.insert(l, expr) {
                        Some(x) => Err(used_twice_err(
                            &source,
                            filename,
                            l,
                            x.debug.expect("no debug info"),
                        )),
                        None => Ok(()),
                    }),
                _ => Err(format!("directive {} must have an argument", d.to_str())),
            }?,
            None => (),
        }
    }

    fn resolve_expression<'a>(
        expression: &'a Expr<'a>,
        symbols: &'a HashMap<&'a str, Expr<'a>>,
    ) -> Result<usize, (&'a str, &'a str)> {
        match &expression.expr {
            Expression::Literal(x) => Ok(*x),
            Expression::Symbol(s) => match symbols.get(s.as_ref()) {
                Some(ref sym) => resolve_expression(&sym, symbols),
                None => Err(("symbol not found", expression.debug.expect("no debug info"))),
            },
            Expression::BinaryOp(x) => {
                let (op, (left, right)) = (&x.0, x.1.borrow());

                let left: usize = resolve_expression(&left, symbols)?;
                let right = resolve_expression(&right, symbols)?;

                Ok(match op {
                    BinaryOpType::Add => left + right,
                    BinaryOpType::Sub => left - right,
                    BinaryOpType::Mul => left * right,
                    BinaryOpType::Div => left / right,
                })
            }
        }
    }

    fn make_error_msg(msg: &str, squiggly: &str, source: &str, filename: &str) -> String {
        let mut err = String::new();
        writeln!(
            err,
            "{style_bold}{color_red}error{color_reset}: {msg}{style_reset}"
        )
        .unwrap();

        draw_line(&mut err, &source, filename, squiggly, SquigglyColor::Red);
        err
    }

    let mut segment_layout: Vec<(usize, Range<*const u8>)> = Vec::new();
    // resolve segments
    for (idx, segment) in segments.iter().enumerate() {
        let lower = resolve_expression(&segment.start, &symbols)
            .map_err(|(msg, squiggly)| make_error_msg(msg, squiggly, &source, filename))?;
        symbols.insert(&segment.label, Expr::new(Expression::Literal(lower), None));

        let upper = lower + segment.assembled.len();

        let a = memory[lower..upper].as_ptr_range();
        for (_, b) in &segment_layout {
            if (b.start <= a.start && a.start < b.end) || (b.start <= a.end && a.end < b.end) {
                panic!("uh oh spaghettio AORG clobbo'd your data")
            }
        }
        segment_layout.push((idx, memory[lower..upper].as_ptr_range()));

        memory[lower..upper].copy_from_slice(&segment.assembled);
    }

    for r in references {
        let write_idx = (segment_layout
            .iter()
            .find(|(s, _)| *s == r.segment)
            .unwrap()
            .1
            .start as usize
            - memory.as_ptr() as usize)
            + r.byte;

        match r.directive {
            Directive::I((i, expr)) => {
                match i
                    .set_operand_value(resolve_expression(&expr.unwrap(), &symbols).map_err(
                        |(msg, squiggly)| make_error_msg(msg, squiggly, &source, filename),
                    )?)
                    .unwrap()
                    .to_opcode()
                    .unwrap()
                {
                    (x, None) => {
                        memory[write_idx] = x;
                    }
                    (x, Some(y)) => {
                        memory[write_idx] = x;
                        memory[write_idx + 1] = y;
                    }
                }
            }
            Directive::Byte(x) => {
                for (idx, e) in x.unwrap().iter().enumerate() {
                    memory[write_idx + idx] = resolve_expression(&e, &symbols)
                        .map_err(|(msg, squiggly)| {
                            make_error_msg(msg, squiggly, &source, filename)
                        })?
                        .try_into()
                        .unwrap();
                }
            }
            Directive::Data(x) => {
                for (idx, e) in x.unwrap().iter().enumerate() {
                    let val: u16 = resolve_expression(&e, &symbols)
                        .map_err(|(msg, squiggly)| {
                            make_error_msg(msg, squiggly, &source, filename)
                        })?
                        .try_into()
                        .unwrap();
                    memory[write_idx + 2 * idx] = (val >> 8) as u8;
                    memory[write_idx + 2 * idx + 1] = val as u8;
                }
            }
            Directive::Aorg(_) => unreachable!(),
            Directive::Text(_) => unreachable!(),
            Directive::Equ(_) => unreachable!(),
        }
    }

    for s in &symbols {
        println!("{s:?}");
    }

    Ok(())
}
