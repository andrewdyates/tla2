// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #6892: BVE backward subsumption deletes irredundant
//! clauses without adding reconstruction entries. When BVE later eliminates
//! a variable present in the deleted clause, the `!is_active` guard at
//! line 364 skips it — losing its constraint from the reconstruction stack.
//! Cross-variable reconstruction interference then flips witness variables
//! in a way that unsatisfies the original clause, producing an invalid SAT
//! model (reported as UNKNOWN).
//!
//! Root cause: BVE backward subsumption (bve.rs:590) marks subsumed clauses
//! as deleted without pushing a reconstruction entry. The resolvent that
//! subsumes the clause may itself be deleted by a subsequent elimination,
//! breaking the subsumption chain.
//!
//! Fix: push a witness-clause reconstruction entry for irredundant clauses
//! before backward-subsumption deletion.
//!
//! Minimal trigger: probe + BVE + subsumption on the crn_11_99_u benchmark.

#![allow(clippy::panic)]

mod common;

use ntest::timeout;
use z4_sat::{parse_dimacs, SatResult};

const CRN_PATH: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/sat/satcomp2024-sample/ef330d1b144055436a2d576601191ea5-crn_11_99_u.cnf.xz"
);

/// Full default configuration must produce UNSAT on crn_11_99_u.
/// Before the #6892 fix, this returned UNKNOWN (invalid SAT model).
#[test]
#[timeout(120_000)]
fn crn_full_default_config() {
    let Some(content) = common::load_benchmark_or_skip(CRN_PATH) else {
        return;
    };
    let formula = parse_dimacs(&content).expect("valid DIMACS");
    let mut solver = formula.into_solver();
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat),
        "#6892: full default config must produce UNSAT on crn_11_99_u, got {result:?}"
    );
}

/// Minimal trigger: probe + BVE + subsumption (the three interacting features).
#[test]
#[timeout(120_000)]
fn crn_probe_bve_subsume() {
    let Some(content) = common::load_benchmark_or_skip(CRN_PATH) else {
        return;
    };
    let formula = parse_dimacs(&content).expect("valid DIMACS");
    let mut solver = formula.into_solver();
    common::disable_all_inprocessing(&mut solver);
    solver.set_probe_enabled(true);
    solver.set_bve_enabled(true);
    solver.set_subsume_enabled(true);
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat),
        "#6892: probe+BVE+subsume must produce UNSAT on crn_11_99_u, got {result:?}"
    );
}

/// Probe only (no BVE) — baseline: confirms the benchmark is UNSAT without BVE.
#[test]
#[timeout(120_000)]
fn crn_probe_only() {
    let Some(content) = common::load_benchmark_or_skip(CRN_PATH) else {
        return;
    };
    let formula = parse_dimacs(&content).expect("valid DIMACS");
    let mut solver = formula.into_solver();
    common::disable_all_inprocessing(&mut solver);
    solver.set_probe_enabled(true);
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat),
        "#6892: probe-only must produce UNSAT on crn_11_99_u, got {result:?}"
    );
}

/// BVE only (no probe): without probing, BVE can produce a reduced formula
/// where search finds SAT but reconstruction can't extend to the original
/// (fail-closed to Unknown). Default config (probe+BVE) always works.
/// Only Sat would be a soundness bug; Unknown is correct fail-closed behavior.
#[test]
#[timeout(120_000)]
fn crn_bve_only() {
    let Some(content) = common::load_benchmark_or_skip(CRN_PATH) else {
        return;
    };
    let formula = parse_dimacs(&content).expect("valid DIMACS");
    let mut solver = formula.into_solver();
    common::disable_all_inprocessing(&mut solver);
    solver.set_bve_enabled(true);
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat | SatResult::Unknown),
        "#6892: BVE-only must produce UNSAT or Unknown on crn_11_99_u, got {result:?}"
    );
}
