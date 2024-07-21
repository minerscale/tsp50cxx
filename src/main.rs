use inline_colorization::*;
use std::{fmt::Write, fs::File, io::Read, process::ExitCode};
mod assembler;
mod emulator;
mod instruction;
mod uninit;

use assembler::assemble;

use crate::emulator::TSP50;

fn main() -> ExitCode {
    let mut emulator = TSP50::new();

    let filename = "src/test.tsp";
    let mut source = String::new();

    if let Err(e) = File::open(filename)
        .map_err(|_| format!("{style_bold}{color_red}error{color_reset}: unable to open source file '{filename}'{style_reset}"))
        .and_then(|mut f| f.read_to_string(&mut source)
                                       .map_err(|_|
                                        format!("{style_bold}{color_red}error{color_reset}: unable to read source file '{filename}'{style_reset}")))
    {
        println!("{e}");
        return ExitCode::from(1);
    }

    if let Err(e) = assemble(filename, &source, emulator.rom_mut()) {
        println!("{e}");
        return ExitCode::from(1);
    }

    for i in 0..0xa0 {
        println!(
            "{}",
            &emulator.rom()[0x10 * i..(0x10 * (i + 1))]
                .iter()
                .fold(String::new(), |mut s, x| {
                    let _ = write!(s, "{x:02x} ");
                    s
                })
        );
    }

    emulator.run();

    ExitCode::SUCCESS
}
