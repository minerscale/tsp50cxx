use inline_colorization::*;

use std::{
    collections::HashMap,
    io::{stdin, stdout, Write},
};
use terminal_size::terminal_size;

use crate::{
    assembler::{parse_expression, resolve_expression, strip_whitespace},
    emulator::{Status, TSP50},
    instruction::Expr,
};

pub fn debug_loop(
    source: &str,
    debug_syms: HashMap<usize, &str>,
    symbol_map: HashMap<&str, Expr>,
    emulator: &mut TSP50,
) -> Result<(), ()> {
    let mut debug_lines_sorted_vec: Vec<(usize, &str)> =
        debug_syms.iter().map(|(x, y)| (*x, *y)).collect();

    debug_lines_sorted_vec.sort_unstable_by(|a, b| a.1.as_ptr().cmp(&b.1.as_ptr()));

    let mut previous_input: Box<str> = "n".into();
    let mut input_string = String::new();
    let mut breakpoints: Vec<usize> = Vec::new();
    let mut error: String = "".into();
    let mut show_prompt = true;
    let mut error_red = false;
    loop {
        for b in &breakpoints {
            if emulator.pc().value() as usize == *b {
                show_prompt = true;
            }
        }

        if show_prompt {
            loop {
                let sym = debug_syms[&(emulator.pc().value() as usize)];

                let lines: Vec<&str> = source.lines().collect();

                let line_number = source
                    [..(sym.as_bytes().as_ptr() as usize - source.as_ptr() as usize)]
                    .chars()
                    .fold(0usize, |count, c| if c == '\n' { count + 1 } else { count });

                let height: usize = terminal_size().unwrap().1 .0.into();

                let page_size = height - 9;
                let lower_line = (line_number / page_size) * page_size;
                let upper_line = (lower_line + page_size).clamp(0, lines.len());

                //print!("{esc}[2J{esc}[1;1H", esc = 27 as char);
                println!();
                for (n, l) in lines[lower_line..upper_line].iter().enumerate() {
                    if l.as_ptr() == sym.as_ptr() {
                        println!("  {style_bold}{color_blue}{color_blue}{:04}:  {l}{style_reset}{color_reset}", lower_line + n + 1);
                    } else {
                        println!("  {color_green}{:04}:{color_reset}  {l}", lower_line + n);
                    }
                }
                println!();
                println!("  {emulator:?}");

                if error_red {
                    println!("{color_red}{error}{color_reset}");
                } else {
                    println!("{error}");
                }

                input_string.clear();
                error.clear();

                print!(": ");
                stdout().flush().unwrap();
                stdin().read_line(&mut input_string).unwrap();

                if input_string.is_empty() {
                    println!();
                    return Ok(());
                }

                let input = match input_string.find(|c: char| !c.is_whitespace()) {
                    Some(x) => {
                        let input = if input_string.chars().last().unwrap() == '\n' {
                            &input_string[x..(input_string.len() - 1)]
                        } else {
                            &input_string[x..]
                        };

                        previous_input = input.into();
                        input
                    }
                    None => &previous_input,
                };

                match input.chars().next().unwrap() {
                    'n' => break,
                    'r' => {
                        show_prompt = false;
                        break;
                    }
                    'b' => match (|| {
                        let input = strip_whitespace(
                            &input[input
                                .char_indices()
                                .nth(1)
                                .ok_or("b: requires an argument")?
                                .0..],
                        )
                        .ok_or("b: requires an argument")?;

                        let mut line_mode = false;
                        let input = strip_whitespace(
                            match input.char_indices().find(|(_, c)| !c.is_whitespace()) {
                                Some((_, ':')) => {
                                    line_mode = true;
                                    &input[input
                                        .char_indices()
                                        .nth(1)
                                        .ok_or("b: an expression must follow ':'")?
                                        .0..]
                                }
                                _ => input,
                            },
                        )
                        .ok_or("an expression must follow ':'")?;

                        breakpoints.push({
                            let arg = resolve_expression(
                                &parse_expression(input).map_err(|x| {
                                    x.msg.iter().fold(String::new(), |acc, &s| acc + s)
                                })?,
                                &symbol_map,
                            )
                            .map_err(|e| e.1.to_string() + ": " + e.0)?;

                            if line_mode {
                                let arg = arg - 1;
                                if arg >= lines.len() {
                                    Err("line number out of range")?
                                }
                                debug_lines_sorted_vec[match debug_lines_sorted_vec
                                    .binary_search_by(|probe| {
                                        probe.1.as_ptr().cmp(&lines[arg].as_ptr())
                                    }) {
                                    Ok(x) => x,
                                    Err(x) => x,
                                }]
                                .0
                            } else {
                                arg
                            }
                        });
                        Ok(format!(
                            "breakpoint {} set at #{:04x}",
                            breakpoints.len(),
                            breakpoints.last().unwrap()
                        ))
                    })() {
                        Ok(s) => {
                            error_red = false;
                            error = s
                        }
                        Err(e) => {
                            error_red = true;
                            error = e
                        }
                    },
                    _ => (),
                }
            }
        }

        if emulator.step() == Status::Halt {
            break;
        }
    }

    Ok(())
}
