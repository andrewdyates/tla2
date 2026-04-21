// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Advanced TIR parity tests: constraints, lambda, parameterized LET,
//! multi-action EXCEPT regression, default probe, and SUBSET constrained.

use crate::common::{parse_module, EnvVarGuard};
use crate::specs::{
    check_multi_action_except, constraint_terminal_config, probe_delta, CONSTRAINT_TERMINAL_SPEC,
    COUNTER_SPEC, LAMBDA_SPEC, PARAMETERIZED_LET_SPEC, SUBSET_CONSTRAINED_SPEC,
};
use tla_check::{check_module, CheckResult, Config};
use tla_eval::tir::{enable_tir_eval_probe, tir_eval_probe_snapshot, TIR_CLOSURE_BODY_PROBE_LABEL};

// --- Constraint + Terminal ---

#[test]
fn test_tir_parity_constraints_action_constraints_and_terminal() {
    let _guard = EnvVarGuard::set("TLA2_TIR_PARITY", Some("Bound,ActionOk,Done"));
    let module = parse_module(CONSTRAINT_TERMINAL_SPEC);
    let config = constraint_terminal_config();

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 2,
                "expected constraint-limited terminal run to keep 2 states"
            );
        }
        other => panic!("expected success with TIR parity on constraints/terminal, got: {other:?}"),
    }
}

#[test]
fn test_tir_eval_constraints_action_constraints_and_terminal() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Bound,ActionOk,Done"));
    let module = parse_module(CONSTRAINT_TERMINAL_SPEC);
    let config = constraint_terminal_config();

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 2,
                "expected constraint-limited terminal run to keep 2 states"
            );
        }
        other => panic!("expected success with TIR eval on constraints/terminal, got: {other:?}"),
    }
}

// --- Lambda ---

/// Part of #3163: LAMBDA closure round-trip through TIR.
#[test]
fn test_tir_parity_lambda_round_trip() {
    let _guard = EnvVarGuard::set("TLA2_TIR_PARITY", Some("Init,Next,TypeOK"));
    tla_check::eval::clear_for_test_reset();
    tla_core::clear_global_name_interner();
    let module = parse_module(LAMBDA_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT TypeOK\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 3,
                "expected x in {{1,2,3}} = 3 reachable states"
            );
        }
        other => panic!("expected parity-checked LAMBDA spec to succeed, got: {other:?}"),
    }
}

#[test]
fn test_tir_eval_lambda_round_trip() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Init,Next,TypeOK"));
    tla_check::eval::clear_for_test_reset();
    tla_core::clear_global_name_interner();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();
    let module = parse_module(LAMBDA_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT TypeOK\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 3,
                "expected x in {{1,2,3}} = 3 reachable states"
            );
        }
        other => panic!("expected TIR-eval LAMBDA spec to succeed, got: {other:?}"),
    }

    let after = tir_eval_probe_snapshot();
    let delta = probe_delta(&before, &after, TIR_CLOSURE_BODY_PROBE_LABEL);
    assert!(
        delta.expr_evals > 0,
        "expected TIR-eval lambda spec to execute stored closure bodies through eval_tir, delta={delta:?}"
    );
    assert_eq!(
        delta.named_op_evals, 0,
        "closure-body probe should track only stored-body expr evals, delta={delta:?}"
    );
}

// --- Parameterized LET ---

/// Part of #3262: parameterized LET lowered to LAMBDA in TIR.
#[test]
fn test_tir_parity_parameterized_let() {
    let _guard = EnvVarGuard::set("TLA2_TIR_PARITY", Some("Init,Next,TypeOK"));
    tla_check::eval::clear_for_test_reset();
    tla_core::clear_global_name_interner();
    let module = parse_module(PARAMETERIZED_LET_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT TypeOK\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 4,
                "expected pos in {{0,1,2,3}} = 4 reachable states"
            );
        }
        other => {
            panic!("expected parity-checked parameterized LET spec to succeed, got: {other:?}")
        }
    }
}

#[test]
fn test_tir_eval_parameterized_let() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Init,Next,TypeOK"));
    tla_check::eval::clear_for_test_reset();
    tla_core::clear_global_name_interner();
    let module = parse_module(PARAMETERIZED_LET_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT TypeOK\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 4,
                "expected pos in {{0,1,2,3}} = 4 reachable states"
            );
        }
        other => panic!("expected TIR-eval parameterized LET spec to succeed, got: {other:?}"),
    }
}

// --- Multi-action EXCEPT regression (#3276) ---

#[test]
fn test_tir_eval_multi_action_except_regression_3276() {
    // First, get the baseline state count without TIR
    let baseline_states = {
        let _no_tir = EnvVarGuard::remove("TLA2_TIR_EVAL");
        let _no_parity = EnvVarGuard::remove("TLA2_TIR_PARITY");
        match check_multi_action_except(None) {
            CheckResult::Success(stats) => stats.states_found,
            other => panic!("expected AST baseline to succeed, got: {other:?}"),
        }
    };
    assert!(
        baseline_states > 8,
        "AST baseline should find more than 8 states, got {baseline_states}"
    );

    // Now test with TIR_EVAL=Next — this was broken before the #3276 fix
    {
        let _tir = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Next"));
        match check_multi_action_except(Some("Next")) {
            CheckResult::Success(stats) => {
                assert_eq!(
                    stats.states_found, baseline_states,
                    "TIR_EVAL=Next must match AST baseline state count \
                     (before #3276 fix: stale expr_cache produced 8 states)"
                );
            }
            other => panic!(
                "expected success with TIR_EVAL=Next on multi-action EXCEPT spec, got: {other:?}"
            ),
        }
    }

    // Also test TIR_EVAL=all
    {
        let _tir = EnvVarGuard::set("TLA2_TIR_EVAL", Some("all"));
        match check_multi_action_except(Some("all")) {
            CheckResult::Success(stats) => {
                assert_eq!(
                    stats.states_found, baseline_states,
                    "TIR_EVAL=all must match AST baseline state count"
                );
            }
            other => panic!(
                "expected success with TIR_EVAL=all on multi-action EXCEPT spec, got: {other:?}"
            ),
        }
    }
}

// --- Default probe + SUBSET constrained ---

/// Part of #3323: TIR is the default sequential evaluation path.
#[test]
fn test_tir_default_on_fires_probes_without_env_vars() {
    let _eval_guard = EnvVarGuard::remove("TLA2_TIR_EVAL");
    let _parity_guard = EnvVarGuard::remove("TLA2_TIR_PARITY");

    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();

    let module = parse_module(COUNTER_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT TypeOK\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
        }
        other => panic!("expected success with default TIR, got: {other:?}"),
    }

    let after = tir_eval_probe_snapshot();
    let next_delta = probe_delta(&before, &after, "Next");
    assert!(
        next_delta.expr_evals > 0,
        "default TIR (#3323) should exercise TIR leaf evaluation for Next"
    );
}

/// Part of #3394: TIR must produce correct state counts on specs with SUBSET quantification.
#[test]
fn test_tir_subset_constrained_produces_correct_states() {
    let module_src = SUBSET_CONSTRAINED_SPEC;
    let config_src = "INIT Init\nNEXT Next\nINVARIANT TypeOK\n";

    let _eval_guard = EnvVarGuard::remove("TLA2_TIR_EVAL");
    let _parity_guard = EnvVarGuard::remove("TLA2_TIR_PARITY");
    tla_check::eval::clear_for_test_reset();
    tla_core::clear_global_name_interner();
    let module = parse_module(module_src);
    let config = Config::parse(config_src).expect("config parse");
    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert!(
                stats.states_found > 1,
                "SUBSET constrained spec should have more than 1 reachable state, got {}",
                stats.states_found
            );
        }
        other => panic!("expected TIR eval success, got: {other:?}"),
    }
}

/// Part of #3354: TIR eval must produce known state counts for COUNTER_SPEC.
#[test]
fn test_tir_default_counter_produces_correct_state_counts() {
    let module_src = COUNTER_SPEC;
    let config_src = "INIT Init\nNEXT Next\nINVARIANT TypeOK\n";

    let _eval_guard = EnvVarGuard::remove("TLA2_TIR_EVAL");
    let _parity_guard = EnvVarGuard::remove("TLA2_TIR_PARITY");
    let module = parse_module(module_src);
    let config = Config::parse(config_src).expect("config parse");
    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
        }
        other => panic!("expected TIR eval success, got: {other:?}"),
    }
}
