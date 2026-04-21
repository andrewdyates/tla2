// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod common;

use std::collections::BTreeMap;

use common::{parse_module, EnvVarGuard};
use tla_check::eval::clear_for_test_reset;
use tla_check::{check_module, CheckResult, Config, ConstantValue};
use tla_core::clear_global_name_interner;
use tla_eval::tir::{enable_tir_eval_probe, tir_eval_probe_snapshot, TirEvalProbeCounts};

const REPLACED_INIT_PROBE_SPEC: &str = "\
---- MODULE TirResolvedInitReplacementProbe ----
VARIABLE x
Init == x = 99
BootResolved3296Impl == x = 0
Next ==
    IF x < 1
    THEN x' = x + 1
    ELSE x' = x
Safe == x \\in {0, 1}
====";

fn probe_counts(snapshot: &BTreeMap<String, TirEvalProbeCounts>, name: &str) -> TirEvalProbeCounts {
    snapshot.get(name).copied().unwrap_or_default()
}

fn probe_delta(
    before: &BTreeMap<String, TirEvalProbeCounts>,
    after: &BTreeMap<String, TirEvalProbeCounts>,
    name: &str,
) -> TirEvalProbeCounts {
    let before_counts = probe_counts(before, name);
    let after_counts = probe_counts(after, name);
    TirEvalProbeCounts {
        expr_evals: after_counts
            .expr_evals
            .saturating_sub(before_counts.expr_evals),
        named_op_evals: after_counts
            .named_op_evals
            .saturating_sub(before_counts.named_op_evals),
    }
}

/// Replacement-routed init probe canary for #3296.
///
/// The config keeps `INIT Init`, but a constant override rewires `Init` to a
/// different zero-arg operator. Selecting the raw config name must still
/// activate init leaf TIR evaluation and record probe hits under the resolved
/// implementation name.
#[test]
fn test_tir_eval_raw_init_selection_routes_to_resolved_replacement() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Init"));
    clear_for_test_reset();
    clear_global_name_interner();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();
    let module = parse_module(REPLACED_INIT_PROBE_SPEC);
    let mut config = Config::parse("INIT Init\nNEXT Next\nINVARIANT Safe\n").expect("config parse");
    config.constants.insert(
        "Init".to_string(),
        ConstantValue::Replacement("BootResolved3296Impl".to_string()),
    );

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 2,
                "expected replacement-routed Init to keep the counter in {{0, 1}}"
            );
        }
        other => {
            panic!("expected success with replacement-routed init-only TIR eval, got: {other:?}")
        }
    }

    let after = tir_eval_probe_snapshot();
    let delta = probe_delta(&before, &after, "BootResolved3296Impl");
    assert!(
        delta.expr_evals > 0,
        "expected resolved replacement init name to receive expr probe hits even when raw Init is selected, delta={delta:?}"
    );
    assert_eq!(
        delta.named_op_evals, 0,
        "init replacement routing should stay on the leaf-eval path, delta={delta:?}"
    );
}
