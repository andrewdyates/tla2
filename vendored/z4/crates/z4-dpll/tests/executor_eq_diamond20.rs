// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test for z4-dpll `--release` hangs (#1535).
//!
//! The eq_diamond20 benchmark triggers non-terminating behavior in SAT
//! subsumption preprocessing. This test uses a timeout wrapper to fail
//! fast instead of hanging indefinitely and orphaning cargo test processes.

use ntest::timeout;
use z4_dpll::Executor;
use z4_frontend::parse;

#[test]
#[timeout(10_000)]
fn test_executor_eq_diamond20_unsat() {
    // Release-time regression guard for eq_diamond20 performance.
    // Completes quickly in `--release` since the unified incremental EUF
    // path with or_eq_lemma shortcuts landed. If it regresses/hangs
    // (e.g. stuck in SAT preprocessing), the timeout fails the test.
    let mut path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("../../benchmarks/smtcomp/non-incremental/QF_UF/eq_diamond/eq_diamond20.smt2");
    let input = std::fs::read_to_string(path).expect("read eq_diamond20.smt2");

    let commands = parse(&input).expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
}
