//! # Assembler
//!
//! This assembler has full unicode support and a syntax highlighting file.

use std::collections::HashMap;
use std::fmt::Write;
use std::fs::File;
use std::io::Read;
use std::str::FromStr;
use unicode_width::UnicodeWidthStr;

use crate::instruction::{Directive, Instruction, D, I};
use inline_colorization::*;
use slicevec::SliceVec;

#[derive(Debug)]
struct SyntaxError<'a> {
    msg: Vec<&'a str>,
    slice: &'a str,
}

fn make_ast<'a>(
    program: &'a [&'a str],
) -> Result<Vec<(Option<&'a str>, Directive<'a>)>, (&'a str, usize, SyntaxError<'a>)> {
    fn parse_number(literal: &str) -> Result<usize, SyntaxError> {
        if let Some(hex) = literal.strip_prefix('#') {
            usize::from_str_radix(hex, 16)
        } else {
            usize::from_str(literal)
        }
        .map_err(|_| SyntaxError {
            msg: vec!["failed to parse number"],
            slice: literal,
        })
    }

    fn parse_argument<'a>(
        label: Option<&'a str>,
        directive: Directive<'a>,
        line: &'a str,
    ) -> Option<Result<(Option<&'a str>, Directive<'a>), SyntaxError<'a>>> {
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
                        .nth(2)
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
                            .nth(2)
                            .map_or(&line[idx..], |(next_idx, _)| {
                                &line[idx..(idx + end_idx + next_idx - 1)]
                            }),
                    ))
                }
            }) {
            Ok(Some(arg)) => match directive {
                D::I(i) => match parse_number(arg) {
                    Ok(x) => match i.set_operand_value(x) {
                        Ok(x) => Ok(D::I(x)),
                        Err(_) => Err(SyntaxError {
                            msg: vec!["instruction '", directive.to_str(), "' has no operand"],
                            slice: arg,
                        }),
                    },
                    Err(e) => Err(e),
                },
                D::Br(_) => Ok(D::Br(Some(arg))),
                D::Aorg(_) => parse_number(arg).map(|x| D::Aorg(Some(x))),
                D::Byte(_) => arg
                    .split(',')
                    .map(|s| match parse_number(s) {
                        Ok(x) => u8::try_from(x).map_err(|_| SyntaxError {
                            msg: vec!["BYTE must be between #00 and #FF"],
                            slice: arg,
                        }),
                        Err(e) => Err(e),
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .map(|x| D::Byte(Some(x))),
                D::Data(_) => arg
                    .split(',')
                    .map(|s| match parse_number(s) {
                        Ok(x) => u16::try_from(x).map_err(|_| SyntaxError {
                            msg: vec!["DATA must be between #0000 and #FFFF"],
                            slice: arg,
                        }),
                        Err(e) => Err(e),
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .map(|x| D::Data(Some(x))),
                D::Text(_) => Ok(D::Text(Some(arg))),
            },
            Ok(None) => Ok(directive),
            Err(e) => Err(e),
        } {
            Ok(directive) => Some(Ok((label, directive))),
            Err(e) => Some(Err(e)),
        }
    }

    fn parse_keyword_or_label<'a>(
        label: Option<&'a str>,
        line: &'a str,
    ) -> Option<Result<(Option<&'a str>, Directive<'a>), SyntaxError<'a>>> {
        let get_directive = |s| match Directive::try_from(s) {
            Ok(d) => Some(Ok((label, d))),
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
                        Some(Err(SyntaxError {
                            msg: vec!["expected directive after label"],
                            slice: &line[idx..],
                        })),
                        |(after_colon, _)| {
                            parse_main(Some(&line[..idx]), &line[(idx + after_colon)..])
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

    fn parse_main<'a>(
        label: Option<&'a str>,
        line: &'a str,
    ) -> Option<Result<(Option<&'a str>, Directive<'a>), SyntaxError<'a>>> {
        match line.find(|c: char| !c.is_whitespace()) {
            Some(idx) => parse_keyword_or_label(label, &line[idx..]),
            None => None,
        }
    }

    program
        .into_iter()
        .enumerate()
        .filter_map(|(line_number, &line)| {
            parse_main(None, line).map(|x| x.map_err(|e| (line, line_number, e)))
        })
        .collect()
}

fn draw_line(
    msg: &mut String,
    line: &str,
    filename: &str,
    line_number: usize,
    column: Option<usize>,
) {
    let line_number = line_number + 1; // Stupid humans start their line numbers at 1
    let padding = " ".repeat(line_number.to_string().len());

    match column {
        Some(column) => writeln!(
            msg,
            "{padding}{color_blue}-->{color_reset}{style_reset} {filename}:{line_number}:{column}"
        ),
        None => writeln!(
            msg,
            "{padding}{color_blue}-->{color_reset}{style_reset} {filename}:{line_number}"
        ),
    }
    .unwrap();

    writeln!(msg, " {padding}{style_bold}{color_blue}|").unwrap();
    writeln!(msg, "{line_number} |{color_reset}{style_reset}{line}").unwrap();
    write!(
        msg,
        " {padding}{color_blue}{style_bold}|{color_reset}{style_reset}"
    )
    .unwrap();
}

pub fn assemble(filename: &str, memory: &mut [u8]) -> Result<(), String> {
    let mut source = String::new();
    File::open(filename)
        .map_err(|_| format!("{style_bold}{color_red}error{color_reset}: unable to open source file '{filename}'{style_reset}"))?
        .read_to_string(&mut source)
        .map_err(|_| format!("{style_bold}{color_red}error{color_reset}: unable to read source file '{filename}'{style_reset}"))?;

    let source = source.lines().collect::<Vec<_>>();
    let ast: Vec<(Option<&str>, Directive)> =
        make_ast(&source).map_err(|(line, line_number, e)| {
            // In any other language this wouldn't be hacky
            let column: usize =
                e.slice.as_bytes().as_ptr_range().start as usize - line.as_ptr() as usize;

            let mut msg = String::new();
            writeln!(
                msg,
                "{style_bold}{color_red}error{color_reset}: {}",
                e.msg.concat()
            )
            .unwrap();
            draw_line(&mut msg, line, filename, line_number, Some(column));
            write!(
                msg,
                "{color_red}{}{color_reset}{style_reset}",
                " ".repeat(line[..column].width()) + &("^".repeat(e.slice.width()))
            )
            .unwrap();
            msg
        })?;

    // Using a slicevec allows us to construct our assembled program in place.
    let mut assembled = SliceVec::new(memory);
    let mut labels: HashMap<&str, (u16, usize)> = HashMap::new();
    let mut references: Vec<(&str, usize, usize)> = Vec::new();

    for (line_number, (label, directive)) in ast.into_iter().enumerate() {
        if let Some(l) = label {
            if let Some((_, old_line_number)) =
                labels.insert(l, (assembled.len() as u16, line_number))
            {
                let mut err = String::new();
                writeln!(err, "{style_bold}{color_red}error{color_reset}: label '{l}' used twice{style_reset}").unwrap();

                draw_line(&mut err, source[line_number], filename, line_number, None);

                writeln!(
                    err,
                    "\n{style_bold}{color_green}note{color_reset}: previously used here",
                )
                .unwrap();

                draw_line(
                    &mut err,
                    source[old_line_number],
                    filename,
                    old_line_number,
                    None,
                );
                Err(err)?;
            }
        }

        fn write_opcode(
            instruction: &Instruction,
            assembled: &mut SliceVec<u8>,
        ) -> Result<(), String> {
            match instruction.to_opcode()? {
                (i, None) => {
                    assembled.push(i).unwrap();
                }
                (i, Some(o)) => {
                    assembled.push(i).unwrap();
                    assembled.push(o).unwrap();
                }
            };

            Ok(())
        }

        match directive {
            Directive::I(i) => write_opcode(&i, &mut assembled),
            Directive::Br(Some(i)) => {
                references.push((i, assembled.len(), line_number));

                write_opcode(&I::BR(Some(0)), &mut assembled)
            }
            Directive::Aorg(Some(i)) => {
                if assembled.len() <= i {
                    for _ in assembled.len()..i {
                        assembled.push(0).unwrap();
                    }
                    Ok(())
                } else {
                    Err("AORG directive must leave rom strictly increasing".to_string())
                }
            }
            Directive::Byte(Some(i)) => {
                for byte in i {
                    assembled.push(byte).unwrap();
                }

                Ok(())
            }
            Directive::Data(Some(i)) => {
                for word in i {
                    assembled.push((word >> 8) as u8).unwrap();
                    assembled.push(word as u8).unwrap();
                }

                Ok(())
            }
            Directive::Text(Some(i)) => {
                for &byte in i.as_bytes() {
                    assembled.push(byte).unwrap();
                }

                Ok(())
            }
            _ => Err(format!(
                "directive {} must have an argument",
                directive.to_str()
            )),
        }
        .map_err(|e| {
            let mut err = String::new();

            writeln!(
                err,
                "{style_bold}{color_red}error{color_reset}: {e}{style_reset}"
            )
            .unwrap();
            draw_line(&mut err, source[line_number], filename, line_number, None);
            err
        })?
    }

    // Fix addresses
    for reference in references {
        let opcode = I::BR(Some(match labels.get(reference.0) {
            Some((byte, _)) => *byte,
            None => {
                let mut err = String::new();
                writeln!(err, "{style_bold}{color_red}error{color_reset}: no corresponding label for '{}' {style_reset}",reference.0).unwrap();
                draw_line(&mut err, source[reference.2], filename, reference.2, None);
                Err(err)?
            },
        })).to_opcode().unwrap();
        assembled[reference.1] = opcode.0;
        assembled[reference.1 + 1] = opcode.1.unwrap();
    }

    Ok(())
}
