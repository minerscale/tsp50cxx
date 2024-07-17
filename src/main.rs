use std::{fmt::Write, process::ExitCode};
mod assembler;
mod emulator;
mod instruction;
mod uninit;

use assembler::assemble;

use crate::emulator::TSP50;

fn main() -> ExitCode {
    let mut emulator = TSP50::new();

    match assemble("src/test.tsp", emulator.rom_mut()) {
        Err(s) => {
            println!("{s}");
            return ExitCode::from(1);
        }
        _ => (),
    }

    for i in 0..8 {
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
