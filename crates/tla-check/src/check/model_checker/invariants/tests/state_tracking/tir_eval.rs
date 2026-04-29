// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for TIR-selected solve_predicate coverage.

use super::*;
use tla_eval::tir::{enable_tir_eval_probe, tir_eval_probe_snapshot};

fn sorted_solved_states(mc: &mut ModelChecker<'_>, pred_name: &str) -> Vec<State> {
    let mut states = mc
        .solve_predicate_for_states(pred_name)
        .expect("init solve should succeed");
    states.sort();
    states
}

fn tir_probe_expr_delta(
    before: &std::collections::BTreeMap<String, tla_eval::tir::TirEvalProbeCounts>,
    after: &std::collections::BTreeMap<String, tla_eval::tir::TirEvalProbeCounts>,
    label: &str,
) -> usize {
    let before = before.get(label).copied().unwrap_or_default();
    let after = after.get(label).copied().unwrap_or_default();
    after.expr_evals.saturating_sub(before.expr_evals)
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_solve_predicate_for_states_tir_eval_keeps_binding_form_init_on_ast_leaf_path() {
    enable_tir_eval_probe();
    let module = parse_module(
        r#"
---- MODULE InitTirBindingFallback ----
VARIABLE f, s, t
Peers == 1..2
Init ==
    \E node \in Peers:
        /\ f = [p \in Peers |-> IF p = node THEN 1 ELSE 0]
        /\ s = {m \in Peers : m = node}
        /\ t = {m + node : m \in Peers}
Next == FALSE
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut baseline = ModelChecker::new(&module, &config);
    baseline.tir_parity = None;
    let before_baseline = tir_eval_probe_snapshot();
    let baseline_states = sorted_solved_states(&mut baseline, "Init");
    let after_baseline = tir_eval_probe_snapshot();

    let mut tir = ModelChecker::new(&module, &config);
    tir.tir_parity = Some(
        super::super::super::super::tir_parity::TirParityState::test_eval_selected(
            module.clone(),
            Vec::new(),
            ["Init"],
        ),
    );
    let before_tir = tir_eval_probe_snapshot();
    let tir_states = sorted_solved_states(&mut tir, "Init");
    let after_tir = tir_eval_probe_snapshot();

    assert_eq!(
        baseline_states.len(),
        2,
        "baseline should enumerate both node bindings"
    );
    assert_eq!(
        tir_states, baseline_states,
        "binding-form init solving selected for TIR should still match the AST init path"
    );
    assert_eq!(
        tir_probe_expr_delta(&before_baseline, &after_baseline, "Init"),
        0,
        "baseline init solve should not touch the TIR probe"
    );
    assert!(
        tir_probe_expr_delta(&before_tir, &after_tir, "Init") > 0,
        "selected init solve should exercise TIR leaf evaluation, not silently stay on AST-only fallback"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_solve_predicate_for_states_tir_eval_keeps_binding_form_typeok_on_ast_leaf_path() {
    enable_tir_eval_probe();
    let module = parse_module(
        r#"
---- MODULE TypeOkTirBindingFallback ----
VARIABLE f, s, t
Peers == 1..2
TypeOK ==
    \E node \in Peers:
        /\ f = [p \in Peers |-> IF p = node THEN 1 ELSE 0]
        /\ s = {m \in Peers : m = node}
        /\ t = {m + node : m \in Peers}
Init ==
    /\ f[1] = 1
    /\ 1 \in s
    /\ ~(4 \in t)
Next == FALSE
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut baseline = ModelChecker::new(&module, &config);
    baseline.tir_parity = None;
    let before_baseline = tir_eval_probe_snapshot();
    let baseline_states = sorted_solved_states(&mut baseline, "Init");
    let after_baseline = tir_eval_probe_snapshot();

    let mut tir = ModelChecker::new(&module, &config);
    tir.tir_parity = Some(
        super::super::super::super::tir_parity::TirParityState::test_eval_selected(
            module.clone(),
            Vec::new(),
            ["TypeOK"],
        ),
    );
    let before_tir = tir_eval_probe_snapshot();
    let tir_states = sorted_solved_states(&mut tir, "Init");
    let after_tir = tir_eval_probe_snapshot();

    assert_eq!(
        baseline_states.len(),
        1,
        "baseline should keep exactly one TypeOK-generated state after Init filtering"
    );
    assert_eq!(
        tir_states, baseline_states,
        "binding-form TypeOK fallback selected for TIR should still match the AST init path"
    );
    assert_eq!(
        tir_probe_expr_delta(&before_baseline, &after_baseline, "TypeOK"),
        0,
        "baseline TypeOK solve should not touch the TIR probe"
    );
    assert!(
        tir_probe_expr_delta(&before_tir, &after_tir, "TypeOK") > 0,
        "selected TypeOK fallback should exercise TIR leaf evaluation, not silently stay on AST-only fallback"
    );
}
