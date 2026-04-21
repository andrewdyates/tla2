// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! DieHard and Rich spec TIR parity and eval tests.

use crate::common::{parse_module, EnvVarGuard};
use crate::specs::{DIEHARD_SPEC, RICH_SPEC};
use tla_check::{check_module, CheckResult, Config};

/// DieHard water jug puzzle — parity canary against a real algorithmic spec.
///
/// Inline version of the classic DieHard spec (without EXTENDS Naturals).
/// 16 distinct states (full state space), TypeOK invariant holds.
/// Exercises: IF/THEN/ELSE, arithmetic (+, -, <), disjunction, conjunction,
/// set membership (\\in), explicit sets, multi-variable primed assignments.
#[test]
fn test_tir_parity_diehard() {
    let _guard = EnvVarGuard::set("TLA2_TIR_PARITY", Some("Init,Next,TypeOK"));
    let module = parse_module(DIEHARD_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT TypeOK\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            // Full state space: 16 distinct reachable states.
            // (TLC baseline shows 14 with NotSolved invariant, which halts early.)
            assert_eq!(
                stats.states_found, 16,
                "expected 16 reachable states (full DieHard state space)"
            );
        }
        other => panic!("expected successful parity-checked run, got: {other:?}"),
    }
}

/// TIR eval mode canary: DieHard with TypeOK invariant evaluated via TIR.
///
/// Unlike the parity tests above (which shadow-check TIR against AST),
/// this test uses `TLA2_TIR_EVAL` to make TIR the PRIMARY evaluator for
/// the TypeOK invariant. The invariant is evaluated via `eval_tir()` for
/// every state during BFS — compiled guards and AST eval are bypassed.
///
/// Part of #3194: proves TIR eval works as a production evaluation path.
#[test]
fn test_tir_eval_diehard_invariant() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("TypeOK"));
    let module = parse_module(DIEHARD_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT TypeOK\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 16,
                "expected 16 reachable states (full DieHard state space)"
            );
        }
        other => panic!("expected success with TIR eval invariant, got: {other:?}"),
    }
}

/// TIR eval mode canary: DieHard transitions accepted through TIR `Next`.
///
/// This exercises the real-spec successor path with `TLA2_TIR_EVAL=Next`,
/// making TIR the transition admission check for every generated successor.
#[test]
fn test_tir_eval_diehard_next() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Next"));
    let module = parse_module(DIEHARD_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 16,
                "expected 16 reachable states (full DieHard state space)"
            );
        }
        other => panic!("expected success with TIR-evaluated Next, got: {other:?}"),
    }
}

/// DieHard Init-only selection canary.
///
/// Part of #3288: the temporary AST-only init gate must preserve behavior on a
/// multi-variable init predicate as well.
#[test]
fn test_tir_eval_diehard_init_only() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Init"));
    let module = parse_module(DIEHARD_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT TypeOK\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 16,
                "expected 16 reachable states (full DieHard state space)"
            );
        }
        other => panic!("expected success with TIR eval on Init only (DieHard), got: {other:?}"),
    }
}

/// TIR eval canary: DieHard with BOTH Next (leaf eval) and TypeOK (invariant eval).
///
/// Part of #3194: exercises TIR leaf eval on a real algorithmic spec with
/// multiple actions, IF/THEN/ELSE guards, and arithmetic.
#[test]
fn test_tir_eval_diehard_next_and_typeok() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Next,TypeOK"));
    let module = parse_module(DIEHARD_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT TypeOK\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 16,
                "expected 16 reachable states (full DieHard state space)"
            );
        }
        other => panic!("expected success with TIR Next+TypeOK, got: {other:?}"),
    }
}

/// TIR eval mode canary: Rich spec with TIR-based invariant checking.
///
/// Exercises TIR eval for quantifiers, set membership, DOMAIN, SUBSETEQ,
/// set filter, LET — the full invariant expression coverage.
#[test]
fn test_tir_eval_rich_invariant() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Inv"));
    let module = parse_module(RICH_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT Inv\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected 1 initial state");
            assert!(
                stats.states_found >= 2,
                "expected at least 2 reachable states, got {}",
                stats.states_found
            );
        }
        other => panic!("expected success with TIR eval invariant, got: {other:?}"),
    }
}

/// Richer parity canary exercising quantifiers, sets, functions, CHOOSE, EXCEPT.
#[test]
fn test_tir_parity_rich_canary() {
    let _guard = EnvVarGuard::set("TLA2_TIR_PARITY", Some("Init,Next,Inv"));
    let module = parse_module(RICH_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT Inv\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected 1 initial state");
            // pos in {1,2}, flags in {[1|->F,2|->F],[1|->T,2|->F],[1|->F,2|->T],[1|->T,2|->T]}
            // = 2 * 4 = 8 max, but reachable subset is smaller
            assert!(
                stats.states_found >= 2,
                "expected at least 2 reachable states, got {}",
                stats.states_found
            );
        }
        other => panic!("expected successful parity-checked run, got: {other:?}"),
    }
}
