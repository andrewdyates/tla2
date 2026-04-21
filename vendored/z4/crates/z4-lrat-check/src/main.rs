// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Standalone LRAT proof checker for SAT Competition.
//!
//! Reads a DIMACS CNF file and an LRAT proof file, verifies the proof,
//! and outputs `s VERIFIED` (exit 0) or `s NOT VERIFIED` (exit 1).
//!
//! Depends on z4-proof-common for shared types (Literal, DIMACS parser, LEB128).

use std::io::Write;
use std::{env, fs, process};

use z4_lrat_check::checker::LratChecker;
use z4_lrat_check::{dimacs, lrat_parser};

fn print_usage() {
    let _ = writeln!(
        std::io::stdout(),
        "Usage: z4-lrat-check <cnf-file> <proof-file> [OPTIONS]"
    );
    let _ = writeln!(std::io::stdout());
    let _ = writeln!(std::io::stdout(), "Options:");
    let _ = writeln!(
        std::io::stdout(),
        "  -h, --help     Print this help message"
    );
    let _ = writeln!(
        std::io::stdout(),
        "  -V, --version  Print version information"
    );
}

fn print_version() {
    let _ = writeln!(
        std::io::stdout(),
        "z4-lrat-check {}",
        env!("CARGO_PKG_VERSION")
    );
}

fn run() -> Result<bool, String> {
    let args: Vec<String> = env::args().collect();
    if args.len() == 2 {
        match args[1].as_str() {
            "-h" | "--help" => {
                print_usage();
                process::exit(0);
            }
            "-V" | "--version" => {
                print_version();
                process::exit(0);
            }
            _ => {}
        }
    }
    if args.len() != 3 {
        print_usage();
        process::exit(2);
    }

    let cnf_path = &args[1];
    let proof_path = &args[2];

    let cnf_data =
        fs::read(cnf_path).map_err(|e| format!("error reading CNF file {cnf_path}: {e}"))?;

    let cnf = dimacs::parse_cnf_with_ids(&cnf_data[..]).map_err(|e| e.to_string())?;

    let proof_data =
        fs::read(proof_path).map_err(|e| format!("error reading proof file {proof_path}: {e}"))?;

    let is_binary = lrat_parser::is_binary_lrat(&proof_data);
    let steps = if is_binary {
        lrat_parser::parse_binary_lrat(&proof_data).map_err(|e| e.to_string())?
    } else {
        let proof_text = std::str::from_utf8(&proof_data)
            .map_err(|e| format!("proof file is not valid UTF-8: {e}"))?;
        lrat_parser::parse_text_lrat(proof_text).map_err(|e| e.to_string())?
    };

    let mut chk = LratChecker::new(cnf.num_vars);
    for (id, clause) in &cnf.clauses {
        if !chk.add_original(*id, clause) {
            let _ = writeln!(std::io::stderr(), "c {}", chk.stats_summary());
            return Ok(false);
        }
    }

    let result = chk.verify_proof(&steps);
    let _ = writeln!(std::io::stderr(), "c {}", chk.stats_summary());
    Ok(result)
}

fn main() {
    match run() {
        Ok(true) => {
            let _ = writeln!(std::io::stdout(), "s VERIFIED");
            process::exit(0);
        }
        Ok(false) => {
            let _ = writeln!(std::io::stdout(), "s NOT VERIFIED");
            process::exit(1);
        }
        Err(e) => {
            let _ = writeln!(std::io::stderr(), "error: {e}");
            process::exit(2);
        }
    }
}
