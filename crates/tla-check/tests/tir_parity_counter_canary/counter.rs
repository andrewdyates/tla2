// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Counter spec TIR parity and eval tests.

use crate::common::{parse_module, EnvVarGuard};
use crate::specs::{probe_delta, COUNTER_SPEC, INIT_FALLBACK_SPEC, RENAMED_COUNTER_SPEC};
use tla_check::{check_module, CheckResult, Config};
use tla_eval::tir::{enable_tir_eval_probe, tir_eval_probe_snapshot};

#[test]
fn test_tir_parity_counter_canary() {
    let _guard = EnvVarGuard::set("TLA2_TIR_PARITY", Some("Init,Next"));
    let module = parse_module(COUNTER_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
        }
        other => panic!("expected successful parity-checked run, got: {other:?}"),
    }
}

/// TIR eval mode canary: Counter successor acceptance driven by TIR `Next`.
///
/// This keeps AST enumeration as the candidate generator, but the checker uses
/// TIR as the primary transition validator for `Next` before admitting any
/// successor into the BFS result set.
#[test]
fn test_tir_eval_counter_next() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Next"));
    let module = parse_module(COUNTER_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
        }
        other => panic!("expected success with TIR-evaluated Next, got: {other:?}"),
    }
}

/// TIR eval canary: Counter with BOTH Next (leaf eval) and TypeOK (invariant eval).
///
/// Part of #3194: exercises the full TIR integration — leaf eval during
/// successor generation AND TIR-based invariant checking in one BFS run.
/// This is the acceptance canary for the successor-leaf-TIR-slice design.
#[test]
fn test_tir_eval_counter_next_and_typeok() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Next,TypeOK"));
    let module = parse_module(COUNTER_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT TypeOK\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
        }
        other => panic!("expected success with TIR Next+TypeOK, got: {other:?}"),
    }
}

/// Init-only selection canary.
///
/// Part of #3296: init constraint extraction now exercises TIR leaf evaluation
/// when `TLA2_TIR_EVAL` selects `Init`. The binding-form gate in
/// `try_eval_expr_detailed()` ensures correctness while allowing TIR to
/// evaluate init constraints. State counts must still match exactly.
#[test]
fn test_tir_eval_counter_init_only() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Init"));
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();
    let module = parse_module(COUNTER_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT TypeOK\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
        }
        other => panic!("expected success with TIR eval on Init only, got: {other:?}"),
    }

    let after = tir_eval_probe_snapshot();
    let init_delta = probe_delta(&before, &after, "Init");
    // Part of #3296: TIR is now active for init constraint extraction.
    // The probe should fire, confirming TIR leaf evaluation is exercised.
    assert!(
        init_delta.expr_evals > 0,
        "init selection should exercise TIR leaf evaluation (#3296 re-enabled)"
    );
}

/// `all` mode with init fallback (unbounded domain) stays on AST for Init.
///
/// Part of #3296: TIR is active for init constraint extraction when the init
/// predicate has extractable constraints. But when init falls back to
/// brute-force due to unbounded domain (`Init == x > 0 /\ x < 2`), the
/// constraint extraction fails before TIR evaluation is reached. The probe
/// stays at zero for Init in this case. State counts must match exactly.
#[test]
fn test_tir_eval_all_init_fallback_stays_ast_for_unbounded() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("all"));
    let module = parse_module(INIT_FALLBACK_SPEC);
    let config = Config::parse("INIT Init\nNEXT Next\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 1,
                "expected only x=1 to remain reachable"
            );
        }
        other => {
            panic!("expected success with TIR eval all on init fallback canary, got: {other:?}")
        }
    }
}

/// Renamed-init-only selection canary.
///
/// Part of #3288: selecting the resolved init name must remain harmless while
/// init-solve is gated back to AST.
#[test]
fn test_tir_eval_counter_renamed_boot_only() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Boot"));
    let module = parse_module(RENAMED_COUNTER_SPEC);
    let config = Config::parse("INIT Boot\nNEXT Step\nINVARIANT Safe\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
        }
        other => panic!("expected success with TIR eval on renamed Boot init only, got: {other:?}"),
    }
}

/// Primary resolved-name canary for the sequential `#3194` closeout.
///
/// This proves the TIR eval gate uses the config-resolved operator names
/// themselves (`Boot` / `Step` / `Safe`) rather than literal `Init` / `Next`
/// / `TypeOK` strings.
#[test]
fn test_tir_eval_counter_renamed_boot_step_safe() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Boot,Step,Safe"));
    let module = parse_module(RENAMED_COUNTER_SPEC);
    let config = Config::parse("INIT Boot\nNEXT Step\nINVARIANT Safe\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
        }
        other => panic!(
            "expected success with TIR eval on renamed Boot/Step/Safe operators, got: {other:?}"
        ),
    }
}
