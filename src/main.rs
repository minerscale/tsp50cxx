use std::fmt::Write;
mod assembler;
mod emulator;
mod instruction;
mod uninit;

use assembler::assemble;
use std::{fs::File, io::Read};

use crate::emulator::TSP50;

fn main() {
    let mut emulator = TSP50::new();

    let mut program = String::new();
    File::open("src/test.tsp")
        .unwrap()
        .read_to_string(&mut program)
        .unwrap();
    assemble(&program, emulator.rom_mut());

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
}
