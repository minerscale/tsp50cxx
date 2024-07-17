//! # Assembler
//!
//! This assembler has full unicode support and a syntax highlighting file.

use std::str::FromStr;
use std::{collections::HashMap, process::exit};
use unicode_width::UnicodeWidthStr;

use crate::instruction::{Directive, Instruction, D, I};
use inline_colorization::*;
use slicevec::SliceVec;

fn make_ast(program: &str) -> Vec<(Option<&str>, Directive)> {
    #[derive(Debug)]
    struct SyntaxError<'a> {
        msg: &'a str,
        slice: &'a str,
    }

    fn parse_number(literal: &str) -> Result<usize, SyntaxError> {
        if let Some(hex) = literal.strip_prefix('#') {
            usize::from_str_radix(hex, 16)
        } else {
            usize::from_str(literal)
        }
        .map_err(|_| SyntaxError {
            msg: "failed to parse number",
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
                            msg: "no closing double quote",
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
                D::I(i) => parse_number(arg).map(|x| D::I(i.set_operand_value(x))),
                D::Br(_) => Ok(D::Br(Some(arg))),
                D::Aorg(_) => parse_number(arg).map(|x| D::Aorg(Some(x))),
                D::Byte(_) => arg
                    .split(',')
                    .map(|s| match parse_number(s) {
                        Ok(x) => u8::try_from(x).map_err(|_| SyntaxError {
                            msg: "BYTE must be between #00 and #FF",
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
                            msg: "DATA must be between #0000 and #FFFF",
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
                msg: "directive not recognised",
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
                            msg: "expected directive after label",
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
                            msg: "directive not recognised",
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
        .lines()
        .enumerate()
        .filter_map(|(line_number, line)| {
            parse_main(None, line).map(|x| x.map_err(|e| (line, line_number, e)))
        })
        .collect::<Result<Vec<_>, _>>()
        .unwrap_or_else(|(line, line_number, e)| {
            // In any other language this wouldn't be hacky
            let column: usize =
                e.slice.as_bytes().as_ptr_range().start as usize - line.as_ptr() as usize;

            let padding = line_number.to_string().len();
            let pad_str = " ".repeat(padding);

            println!("{style_bold}{color_red}error{color_reset}: {}", e.msg);
            println!("{pad_str}{color_blue}-->{color_reset}{style_reset} {line_number}:{column}");
            println!(" {pad_str}{style_bold}{color_blue}|");
            println!("{line_number} |{color_reset}{style_reset}{line}");
            println!(
                " {pad_str}{style_bold}{color_blue}|{color_red}{}{color_reset}{style_reset}",
                " ".repeat(line[..column].width()) + &("^".repeat(e.slice.width()))
            );

            exit(1)
        })
}

pub fn assemble(program: &str, memory: &mut [u8]) {
    // step 1: create AST
    // todo: ugly and bad tokeniser might want to clean up
    let ast: Vec<(Option<&str>, Directive)> = make_ast(program);

    // Using a slicevec allows us to construct our assembled program in place.
    let mut assembled = SliceVec::new(memory);
    let mut labels: HashMap<&str, u16> = HashMap::new();
    let mut references: Vec<(&str, usize)> = Vec::new();

    for (label, directive) in ast {
        if let Some(l) = label {
            if let Some(v) = labels.insert(l, assembled.len() as u16) {
                panic!("label {v} used twice");
            }
        }

        fn write_opcode(instruction: &Instruction, assembled: &mut SliceVec<u8>) {
            match instruction.to_opcode() {
                (i, None) => {
                    assembled.push(i).unwrap();
                }
                (i, Some(o)) => {
                    assembled.push(i).unwrap();
                    assembled.push(o).unwrap();
                }
            }
        }

        match directive {
            Directive::I(i) => write_opcode(&i, &mut assembled),
            Directive::Br(Some(i)) => {
                references.push((i, assembled.len()));

                write_opcode(&I::BR(Some(0)), &mut assembled);
            }
            Directive::Aorg(Some(i)) => {
                assert!(
                    assembled.len() <= i,
                    "AORG directive must leave rom strictly increasing"
                );
                // gross, fix later
                for _ in assembled.len()..i {
                    assembled.push(0).unwrap();
                }
            }
            Directive::Byte(Some(i)) => {
                for byte in i {
                    assembled.push(byte).unwrap();
                }
            }
            Directive::Data(Some(i)) => {
                for word in i {
                    assembled.push((word >> 8) as u8).unwrap();
                    assembled.push(word as u8).unwrap();
                }
            }
            Directive::Text(Some(i)) => {
                for &byte in i.as_bytes() {
                    assembled.push(byte).unwrap();
                }
            }
            _ => panic!("attempt to use directive with None label"),
        }
    }

    // Fix addresses
    for reference in references {
        let opcode = I::BR(Some(labels[reference.0])).to_opcode();
        assembled[reference.1] = opcode.0;
        assembled[reference.1 + 1] = opcode.1.unwrap();
    }
}
