use debugger::debug_loop;
use inline_colorization::*;
use std::{fs::File, io::Read};

mod assembler;
mod debugger;
mod emulator;
mod instruction;
mod uninit;

use assembler::assemble;

use crate::emulator::TSP50;

fn main() -> Result<(), ()> {
    let mut emulator = TSP50::new();

    emulator.set_pcm_file(File::create("out.pcm").unwrap());

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

    debug_loop(&source, debug_syms, symbol_map, &mut emulator)?;

    println!("{}", emulator.num_cycles);

    Ok(())
}
