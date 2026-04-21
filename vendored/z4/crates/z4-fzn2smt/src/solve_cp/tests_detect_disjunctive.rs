// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Tests for detect_disjunctive: substitutive disjunctive scheduling detection.
// Verifies that int_lin_le_reif pairs encoding pairwise non-overlap constraints
// are detected and replaced by native Disjunctive propagators.

use z4_cp::engine::CpSolveResult;

use super::tests::{parse_and_solve, solve_cp_output};
use super::CpContext;

/// Helper: build a CpContext from FlatZinc and return the skip set size.
fn detect_and_count_skipped(fzn: &str) -> (CpContext, usize) {
    let model = z4_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let mut ctx = CpContext::new();
    // Register parameters and variables first.
    for par in &model.parameters {
        ctx.register_parameter(par);
    }
    for var in &model.variables {
        ctx.create_variable(var).expect("create var failed");
    }
    let skip = ctx.detect_disjunctive(&model);
    (ctx, skip.len())
}

// --- Detection tests (unit-level) ---

/// Two tasks, one machine: classic int_lin_le_reif pair.
/// s0 + 3 <= s1 when b01, s1 + 4 <= s0 when b10.
/// Detection should find 1 machine with 2 tasks, skip 2 reif constraints.
#[test]
fn test_detect_disjunctive_2_tasks_1_machine() {
    let fzn = "\
        var 0..20: s0 :: output_var;\n\
        var 0..20: s1 :: output_var;\n\
        var bool: b01;\n\
        var bool: b10;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], -3, b01);\n\
        constraint int_lin_le_reif([1, -1], [s1, s0], -4, b10);\n\
        constraint bool_or(b01, b10, true);\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(skipped, 2, "should skip 2 int_lin_le_reif constraints");
}

/// Three tasks on one machine (complete graph of 3 pairs).
/// Detection should find 1 machine with 3 tasks, skip 6 reif constraints.
#[test]
fn test_detect_disjunctive_3_tasks_1_machine() {
    let fzn = "\
        var 0..30: s0 :: output_var;\n\
        var 0..30: s1 :: output_var;\n\
        var 0..30: s2 :: output_var;\n\
        var bool: b01;\n\
        var bool: b10;\n\
        var bool: b02;\n\
        var bool: b20;\n\
        var bool: b12;\n\
        var bool: b21;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], -3, b01);\n\
        constraint int_lin_le_reif([1, -1], [s1, s0], -4, b10);\n\
        constraint int_lin_le_reif([1, -1], [s0, s2], -3, b02);\n\
        constraint int_lin_le_reif([1, -1], [s2, s0], -2, b20);\n\
        constraint int_lin_le_reif([1, -1], [s1, s2], -4, b12);\n\
        constraint int_lin_le_reif([1, -1], [s2, s1], -2, b21);\n\
        constraint bool_or(b01, b10, true);\n\
        constraint bool_or(b02, b20, true);\n\
        constraint bool_or(b12, b21, true);\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(
        skipped, 6,
        "should skip 6 int_lin_le_reif constraints (3 pairs)"
    );
}

/// No disjunctive pattern: int_lin_le_reif with wrong coefficients.
/// Detection should find nothing.
#[test]
fn test_detect_disjunctive_no_match_wrong_coeffs() {
    let fzn = "\
        var 0..10: s0 :: output_var;\n\
        var 0..10: s1 :: output_var;\n\
        var bool: b01;\n\
        constraint int_lin_le_reif([2, -1], [s0, s1], -3, b01);\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(skipped, 0, "wrong coefficients should not match");
}

/// No disjunctive pattern: positive rhs (not a precedence constraint).
#[test]
fn test_detect_disjunctive_no_match_positive_rhs() {
    let fzn = "\
        var 0..10: s0 :: output_var;\n\
        var 0..10: s1 :: output_var;\n\
        var bool: b01;\n\
        var bool: b10;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], 3, b01);\n\
        constraint int_lin_le_reif([1, -1], [s1, s0], 3, b10);\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(
        skipped, 0,
        "positive rhs should not match (not a precedence)"
    );
}

/// Unpaired half: only one direction. Should not create a disjunctive.
#[test]
fn test_detect_disjunctive_unpaired_half() {
    let fzn = "\
        var 0..10: s0 :: output_var;\n\
        var 0..10: s1 :: output_var;\n\
        var bool: b01;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], -3, b01);\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(skipped, 0, "unpaired half should not create disjunctive");
}

/// No constraints at all. Detection returns empty skip set.
#[test]
fn test_detect_disjunctive_empty_model() {
    let fzn = "\
        var 0..10: x :: output_var;\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(skipped, 0, "empty model should return 0 skipped");
}

// --- Integration tests (solve-level) ---

/// 2-task jobshop via int_lin_le_reif: SAT when horizon is wide enough.
/// After detection, a native Disjunctive propagator handles scheduling.
#[test]
fn test_detect_disjunctive_2_tasks_sat() {
    let fzn = "\
        var 0..10: s0 :: output_var;\n\
        var 0..10: s1 :: output_var;\n\
        var bool: b01;\n\
        var bool: b10;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], -3, b01);\n\
        constraint int_lin_le_reif([1, -1], [s1, s0], -2, b10);\n\
        constraint bool_or(b01, b10, true);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(assignment) => {
            assert!(assignment.len() >= 2, "should have at least 2 output vars");
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// 2-task jobshop via int_lin_le_reif: UNSAT when horizon is too tight.
/// Tasks with dur=6 and dur=6 on horizon [0,10]: need at least 12 time units.
#[test]
fn test_detect_disjunctive_2_tasks_unsat_tight_horizon() {
    let fzn = "\
        var 0..5: s0 :: output_var;\n\
        var 0..5: s1 :: output_var;\n\
        var bool: b01;\n\
        var bool: b10;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], -6, b01);\n\
        constraint int_lin_le_reif([1, -1], [s1, s0], -6, b10);\n\
        constraint bool_or(b01, b10, true);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat, got {other:?}"),
    }
}

/// 3-task 1-machine via int_lin_le_reif: verify no-overlap in solution.
#[test]
fn test_detect_disjunctive_3_tasks_solution_valid() {
    let fzn = "\
        var 0..20: s0 :: output_var;\n\
        var 0..20: s1 :: output_var;\n\
        var 0..20: s2 :: output_var;\n\
        var bool: b01;\n\
        var bool: b10;\n\
        var bool: b02;\n\
        var bool: b20;\n\
        var bool: b12;\n\
        var bool: b21;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], -3, b01);\n\
        constraint int_lin_le_reif([1, -1], [s1, s0], -4, b10);\n\
        constraint int_lin_le_reif([1, -1], [s0, s2], -3, b02);\n\
        constraint int_lin_le_reif([1, -1], [s2, s0], -2, b20);\n\
        constraint int_lin_le_reif([1, -1], [s1, s2], -4, b12);\n\
        constraint int_lin_le_reif([1, -1], [s2, s1], -2, b21);\n\
        constraint bool_or(b01, b10, true);\n\
        constraint bool_or(b02, b20, true);\n\
        constraint bool_or(b12, b21, true);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should find a solution: {output}"
    );
}

/// Two separate machines (2 tasks each, no cross-machine pairs).
/// Should detect 2 machines, skip 4 reif constraints total.
#[test]
fn test_detect_disjunctive_2_machines() {
    let fzn = "\
        var 0..20: a0 :: output_var;\n\
        var 0..20: a1 :: output_var;\n\
        var 0..20: b0 :: output_var;\n\
        var 0..20: b1 :: output_var;\n\
        var bool: ba01;\n\
        var bool: ba10;\n\
        var bool: bb01;\n\
        var bool: bb10;\n\
        constraint int_lin_le_reif([1, -1], [a0, a1], -3, ba01);\n\
        constraint int_lin_le_reif([1, -1], [a1, a0], -4, ba10);\n\
        constraint int_lin_le_reif([1, -1], [b0, b1], -2, bb01);\n\
        constraint int_lin_le_reif([1, -1], [b1, b0], -5, bb10);\n\
        constraint bool_or(ba01, ba10, true);\n\
        constraint bool_or(bb01, bb10, true);\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(
        skipped, 4,
        "should skip 4 int_lin_le_reif (2 machines x 2 halves)"
    );
}
