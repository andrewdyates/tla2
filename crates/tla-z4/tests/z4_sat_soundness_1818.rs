// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use z4_dpll::Executor;
use z4_frontend::parse;

#[test]
#[timeout(30_000)]
fn z4_sat_soundness_regression_1708_order_dependent_is_unsat() {
    let mut path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("../../test_data/z4/regression_1708_order_dependent.smt2");
    let input = std::fs::read_to_string(&path).expect("read regression_1708_order_dependent.smt2");

    let commands = parse(&input).expect("parse smt2");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
}

#[test]
#[timeout(30_000)]
fn z4_sat_soundness_regression_1708_bv_ite_shared_vars_minimal_is_unsat() {
    let mut path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("../../test_data/z4/bv_ite_shared_vars_minimal.smt2");
    let input = std::fs::read_to_string(&path).expect("read bv_ite_shared_vars_minimal.smt2");

    let commands = parse(&input).expect("parse smt2");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all");

    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
}
