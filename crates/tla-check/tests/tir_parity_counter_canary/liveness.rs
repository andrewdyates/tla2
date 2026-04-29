// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Liveness and promoted property invariant TIR parity tests.

use crate::common::EnvVarGuard;
use crate::specs::{
    check_liveness_property_spec, check_promoted_property_invariant_spec, LIVENESS_COUNTER_SPEC,
    PROMOTED_PROPERTY_INVARIANT_SPEC,
};
use tla_check::CheckResult;

/// TIR eval canary: keep BFS on AST, but run liveness leaf evaluation through TIR.
///
/// Selecting `Live` enables TIR only for that liveness property. Because
/// `Next` is not selected here, successor admission stays on the AST path and
/// this test isolates the new `#3194` liveness wiring.
#[test]
fn test_tir_eval_liveness_state_leaf_matches_ast() {
    let _skip_guard = EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let (baseline_initial, baseline_states) = {
        let _parity_guard = EnvVarGuard::remove("TLA2_TIR_PARITY");
        let _eval_guard = EnvVarGuard::remove("TLA2_TIR_EVAL");
        match check_liveness_property_spec(LIVENESS_COUNTER_SPEC, "Live") {
            CheckResult::Success(stats) => (stats.initial_states, stats.states_found),
            other => panic!("expected AST liveness baseline success, got: {other:?}"),
        }
    };

    let _tir_guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Live"));
    match check_liveness_property_spec(LIVENESS_COUNTER_SPEC, "Live") {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.initial_states, baseline_initial,
                "TIR liveness path should keep the same initial-state count as AST"
            );
            assert_eq!(
                stats.states_found, baseline_states,
                "TIR liveness path should keep the same reachable-state count as AST"
            );
            assert_eq!(
                stats.states_found, 2,
                "expected x=0 and x=1 to be reachable"
            );
        }
        other => panic!("expected success with TIR-evaluated liveness leaves, got: {other:?}"),
    }
}

#[test]
fn test_tir_eval_promoted_property_invariant_still_violates() {
    let baseline_states = {
        let _eval_guard = EnvVarGuard::remove("TLA2_TIR_EVAL");
        let _parity_guard = EnvVarGuard::remove("TLA2_TIR_PARITY");
        match check_promoted_property_invariant_spec(PROMOTED_PROPERTY_INVARIANT_SPEC, "AlwaysSafe")
        {
            CheckResult::PropertyViolation {
                property,
                kind,
                trace,
                stats,
            } => {
                assert_eq!(property, "AlwaysSafe");
                assert_eq!(kind, tla_check::PropertyViolationKind::StateLevel);
                let last = trace
                    .states
                    .last()
                    .expect("violating trace must be non-empty");
                assert_eq!(
                    last.get("x"),
                    Some(&tla_check::Value::int(2)),
                    "baseline violation should occur at x=2"
                );
                stats.states_found
            }
            other => panic!("expected AST property violation baseline, got: {other:?}"),
        }
    };

    for tir_eval in ["AlwaysSafe", "all"] {
        let _eval_guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some(tir_eval));
        let _parity_guard = EnvVarGuard::remove("TLA2_TIR_PARITY");
        match check_promoted_property_invariant_spec(PROMOTED_PROPERTY_INVARIANT_SPEC, "AlwaysSafe")
        {
            CheckResult::PropertyViolation {
                property,
                kind,
                trace,
                stats,
            } => {
                assert_eq!(property, "AlwaysSafe");
                assert_eq!(kind, tla_check::PropertyViolationKind::StateLevel);
                let last = trace.states.last().expect("violating trace must be non-empty");
                assert_eq!(
                    last.get("x"),
                    Some(&tla_check::Value::int(2)),
                    "TIR_EVAL={tir_eval} should keep the same violating state"
                );
                assert_eq!(
                    stats.states_found, baseline_states,
                    "TIR_EVAL={tir_eval} should not suppress promoted property invariants"
                );
            }
            other => panic!(
                "expected property violation with TIR_EVAL={tir_eval} on promoted property invariant, got: {other:?}"
            ),
        }
    }
}
