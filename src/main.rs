use debugger::debug_loop;
//use debugger::debug_loop;
use inline_colorization::*;
use std::{
    env::args,
    fs::File,
    io::{BufWriter, Read, Write},
};

mod assembler;
mod debugger;
mod emulator;
mod instruction;
mod uninit;

use assembler::assemble;

use crate::emulator::TSP50;

fn main() -> Result<(), ()> {
    let mut emulator = TSP50::new();

    emulator.set_pcm_file(BufWriter::new(File::create("trace").unwrap()));

    let filename = "src/test.tsp";
    let mut source = String::new();

    if let Err(e) = File::open(filename)
        .map_err(|_| format!("{style_bold}{color_red}error{color_reset}: unable to open source file '{filename}'{style_reset}"))
        .and_then(|mut f| f.read_to_string(&mut source)
                                       .map_err(|_|
                                        format!("{style_bold}{color_red}error{color_reset}: unable to read source file '{filename}'{style_reset}")))
    {
        println!("{e}");
        Err(())?
    }

    let (debug_syms, symbol_map) =
        assemble(filename, &source, emulator.rom_mut()).map_err(|e| println!("{e}"))?;

    let limit = emulator
        .rom()
        .0
        .iter()
        .enumerate()
        .rfind(|(_, &x)| x != 0x00)
        .unwrap()
        .0
        + 1;
    File::create("test.bin")
        .unwrap()
        .write_all(&emulator.rom().0[0..limit])
        .unwrap();

    match args().find(|x| x == "dbg") {
        Some(_) => debug_loop(&source, debug_syms, symbol_map, &mut emulator)?,
        None => emulator.run(),
    };

    Ok(())
}
