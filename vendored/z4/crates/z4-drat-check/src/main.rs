// Copyright 2026 Andrew Yates
// z4-drat-check: standalone DRAT/DRUP proof checker.
//
// Usage: z4-drat-check <formula.cnf> <proof.drat> [--rup-only] [--backward]
//
// Exit 0 + "s VERIFIED" if the proof is valid.
// Exit 1 + "s NOT VERIFIED" if the proof is invalid.

use z4_drat_check::{checker, cnf_parser, drat_parser};

use std::io::{self, Write};
use std::process;
use std::time::Instant;

fn print_usage(out: &mut impl Write) -> io::Result<()> {
    writeln!(
        out,
        "Usage: z4-drat-check <formula.cnf> <proof.drat> [OPTIONS]"
    )?;
    writeln!(out)?;
    writeln!(
        out,
        "Verifies a DRAT/DRUP proof against a DIMACS CNF formula."
    )?;
    writeln!(out)?;
    writeln!(out, "Options:")?;
    writeln!(
        out,
        "  --rup-only  Restrict to RUP checking only (DRUP mode)"
    )?;
    writeln!(
        out,
        "  --backward  Use backward checking (verify only needed clauses)"
    )?;
    writeln!(out, "  --stats     Print verification statistics")?;
    writeln!(out, "  -h, --help  Print this help message")?;
    writeln!(out, "  -V, --version  Print version information")?;
    writeln!(out)?;
    writeln!(
        out,
        "RAT checking is enabled by default (full DRAT). Use --rup-only for DRUP."
    )
}

fn print_version(out: &mut impl Write) -> io::Result<()> {
    writeln!(out, "z4-drat-check {}", env!("CARGO_PKG_VERSION"))
}

fn print_stats(out: &mut impl Write, s: &checker::Stats, secs: f64) -> io::Result<()> {
    writeln!(out, "c original clauses:  {}", s.original)?;
    writeln!(out, "c proof additions:   {}", s.additions)?;
    writeln!(out, "c proof deletions:   {}", s.deletions)?;
    writeln!(out, "c RUP checks:        {}", s.checks)?;
    writeln!(out, "c RAT checks:        {}", s.rat_checks)?;
    writeln!(out, "c propagations:      {}", s.propagations)?;
    writeln!(out, "c failures:          {}", s.failures)?;
    writeln!(out, "c missed deletes:    {}", s.missed_deletes)?;
    writeln!(out, "c time:              {secs:.3}s")
}

fn run() -> Result<bool, String> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() == 2 {
        match args[1].as_str() {
            "-h" | "--help" => {
                print_usage(&mut io::stdout()).map_err(|e| e.to_string())?;
                process::exit(0);
            }
            "-V" | "--version" => {
                print_version(&mut io::stdout()).map_err(|e| e.to_string())?;
                process::exit(0);
            }
            _ => {}
        }
    }
    if args.len() < 3 {
        print_usage(&mut io::stderr()).map_err(|e| e.to_string())?;
        process::exit(2);
    }
    let cnf_path = &args[1];
    let proof_path = &args[2];
    // RAT checking enabled by default (full DRAT). --rup-only restricts to DRUP.
    let check_rat = !args.iter().any(|a| a == "--rup-only");
    let backward = args.iter().any(|a| a == "--backward");
    let show_stats = args.iter().any(|a| a == "--stats");
    let start = Instant::now();

    let cnf_data = std::fs::read(cnf_path).map_err(|e| format!("cannot read '{cnf_path}': {e}"))?;
    let cnf = cnf_parser::parse_cnf(&cnf_data[..]).map_err(|e| e.to_string())?;
    let proof_data =
        std::fs::read(proof_path).map_err(|e| format!("cannot read '{proof_path}': {e}"))?;
    let steps = drat_parser::parse_drat(&proof_data).map_err(|e| e.to_string())?;

    let (result, stats) = if backward {
        let mut chk = checker::backward::BackwardChecker::new(cnf.num_vars, check_rat);
        let r = chk.verify(&cnf.clauses, &steps).map_err(|e| e.to_string());
        (r, chk.stats().clone())
    } else {
        let mut chk = checker::DratChecker::new(cnf.num_vars, check_rat);
        let r = chk.verify(&cnf.clauses, &steps).map_err(|e| e.to_string());
        (r, chk.stats().clone())
    };

    let secs = start.elapsed().as_secs_f64();
    let mut out = io::stdout();
    let mut err = io::stderr();

    match result {
        Ok(()) => {
            writeln!(out, "s VERIFIED").map_err(|e| e.to_string())?;
            if show_stats {
                print_stats(&mut err, &stats, secs).map_err(|e| e.to_string())?;
            }
            Ok(true)
        }
        Err(msg) => {
            writeln!(out, "s NOT VERIFIED").map_err(|e| e.to_string())?;
            writeln!(err, "c verification failed: {msg}").map_err(|e| e.to_string())?;
            if show_stats {
                print_stats(&mut err, &stats, secs).map_err(|e| e.to_string())?;
            }
            Ok(false)
        }
    }
}

fn main() {
    match run() {
        Ok(true) => process::exit(0),
        Ok(false) => process::exit(1),
        Err(msg) => {
            let _ = writeln!(io::stderr(), "error: {msg}");
            process::exit(2);
        }
    }
}
