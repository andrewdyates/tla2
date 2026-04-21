// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

mod common;

use ntest::timeout;
use z4_sat::{parse_dimacs, SatResult};

/// Regression test: crn_11_99_u (1287 vars, 2332 clauses) is known UNSAT
/// (verified by CaDiCaL 3.0.0 in 0.41s with 53K conflicts).
///
/// With default preprocessing (BVE + factoring both enabled), z4 returns
/// UNKNOWN with `invalid_sat_model` reason after ~34K conflicts — the solver
/// declares SAT but model verification catches the invalid assignment.
///
/// Disabling BVE alone, factoring alone, or probing alone each fixes the
/// issue, indicating a preprocessing interaction bug between BVE and
/// factoring (probing changes state that affects BVE's elimination choices).
///
/// Related: #5543 (BVE-only UNKNOWN on manol-pipe-c9), #3864 (reconstruction
/// rollback gap).
#[test]
#[timeout(60_000)]
fn crn_11_99_u_default_preprocessing_must_be_unsat() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/crn_11_99_u.cnf");
    if !path.exists() {
        eprintln!(
            "crn_11_99_u: benchmark missing at {}, skipping",
            path.display()
        );
        return;
    }
    let content = std::fs::read_to_string(&path).expect("read crn_11_99_u.cnf");
    let formula = parse_dimacs(&content).expect("parse crn_11_99_u.cnf");
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();
    match result {
        SatResult::Unsat => {} // correct
        SatResult::Sat(_) => panic!("crn_11_99_u: known UNSAT returned SAT (soundness bug)"),
        SatResult::Unknown => panic!(
            "crn_11_99_u: known UNSAT returned Unknown — BVE+factor preprocessing \
             interaction bug (model verification caught invalid SAT assignment)"
        ),
        _ => unreachable!(),
    }
}

/// Workaround confirmation: disabling BVE allows the solver to find UNSAT.
#[test]
#[timeout(60_000)]
fn crn_11_99_u_no_bve_is_unsat() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/crn_11_99_u.cnf");
    if !path.exists() {
        eprintln!("crn_11_99_u: benchmark missing, skipping");
        return;
    }
    let content = std::fs::read_to_string(&path).expect("read");
    let formula = parse_dimacs(&content).expect("parse");
    let mut solver = formula.into_solver();
    solver.set_bve_enabled(false);
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat),
        "crn_11_99_u with BVE disabled must be UNSAT, got {result:?}"
    );
}

/// Workaround confirmation: disabling factoring allows the solver to find UNSAT.
#[test]
#[timeout(60_000)]
fn crn_11_99_u_no_factor_is_unsat() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/crn_11_99_u.cnf");
    if !path.exists() {
        eprintln!("crn_11_99_u: benchmark missing, skipping");
        return;
    }
    let content = std::fs::read_to_string(&path).expect("read");
    let formula = parse_dimacs(&content).expect("parse");
    let mut solver = formula.into_solver();
    solver.set_factor_enabled(false);
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat),
        "crn_11_99_u with factoring disabled must be UNSAT, got {result:?}"
    );
}
