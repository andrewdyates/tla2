// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use std::collections::BTreeMap;

use common::{parse_module, EnvVarGuard};
use tla_check::eval::clear_for_test_reset;
use tla_check::{check_module, CheckResult, Config, ConstantValue, ModelChecker};
use tla_core::clear_global_name_interner;
use tla_eval::tir::{enable_tir_eval_probe, tir_eval_probe_snapshot, TirEvalProbeCounts};

const RENAMED_COUNTER_SPEC: &str = "\
---- MODULE TirResolvedNameCounter ----
VARIABLE x
Boot == x = [a |-> 1, b |-> <<2, 3>>]
Step ==
    IF x.a < 2
    THEN x' = [x EXCEPT !.a = x.a + 1]
    ELSE x' = x
Safe == x.a \\in {1, 2}
====";

const PROBED_RENAMED_COUNTER_SPEC: &str = "\
---- MODULE TirResolvedNameCounterProbe ----
VARIABLE x
BootProbe3194Init == x = 0
StepProbe3194Next ==
    IF x < 1
    THEN x' = x + 1
    ELSE x' = x
SafeProbe3194Inv == x \\in {0, 1}
====";

const CONSTRAINED_RENAMED_NEXT_PROBE_SPEC: &str = "\
---- MODULE TirResolvedNameConstrainedProbe ----
VARIABLE x
BootProbe3294Init == x = 0
StepProbe3294Next ==
    IF x < 1
    THEN x' = x + 1
    ELSE x' = x
BoundProbe3294 == x <= 1
ActionOkProbe3294 == x' <= 1
SafeProbe3294Inv == x \\in {0, 1}
====";

const REPLACED_NEXT_PROBE_SPEC: &str = "\
---- MODULE TirResolvedReplacementProbe ----
VARIABLE x
Init == x = 0
Next == x' = 99
StepResolved3194Impl ==
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

/// Renamed-operator smoke canary for #3194.
///
/// The checker config uses `Boot`/`Step`/`Safe` instead of `Init`/`Next`/`TypeOK`.
/// This guards the end-to-end TIR path against regressing back to literal-name
/// activation.
fn assert_tir_eval_uses_renamed_operator_names() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Boot,Step,Safe"));
    clear_for_test_reset();
    clear_global_name_interner();
    let module = parse_module(RENAMED_COUNTER_SPEC);
    let config = Config::parse("INIT Boot\nNEXT Step\nINVARIANT Safe\n").expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
        }
        other => panic!("expected success with renamed TIR-selected operators, got: {other:?}"),
    }
}

/// Coverage collection uses a sequential fallback that must preserve resolved
/// operator names instead of hard-coding `Next`.
fn assert_tir_eval_uses_renamed_operator_names_with_coverage_enabled() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Boot,Step,Safe"));
    clear_for_test_reset();
    clear_global_name_interner();
    let module = parse_module(RENAMED_COUNTER_SPEC);
    let config = Config::parse("INIT Boot\nNEXT Step\nINVARIANT Safe\n").expect("config parse");
    let mut checker = ModelChecker::new(&module, &config);
    checker.set_collect_coverage(true);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
            let coverage = stats
                .coverage
                .as_ref()
                .expect("coverage stats should be present when collection is enabled");
            assert!(
                !coverage.action_order.is_empty(),
                "coverage should record at least one detected action"
            );
        }
        other => panic!(
            "expected success with renamed TIR-selected operators and coverage, got: {other:?}"
        ),
    }
}

/// Init-only probe canary for #3194.
///
/// This guards against a silent AST fallback in the renamed `INIT` path by
/// asserting that TIR leaf evaluation executed for the selected init operator.
/// The probed spec stays inside the bounded scalar counter subset so the test
/// proves routing rather than unsupported structured-value lowering.
fn assert_tir_eval_renamed_init_reports_probe_hit() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("BootProbe3194Init"));
    clear_for_test_reset();
    clear_global_name_interner();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();
    let module = parse_module(PROBED_RENAMED_COUNTER_SPEC);
    let config = Config::parse(
        "INIT BootProbe3194Init\nNEXT StepProbe3194Next\nINVARIANT SafeProbe3194Inv\n",
    )
    .expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
        }
        other => panic!("expected success with renamed init-only TIR eval, got: {other:?}"),
    }

    let after = tir_eval_probe_snapshot();
    let delta = probe_delta(&before, &after, "BootProbe3194Init");
    assert!(
        delta.expr_evals > 0,
        "expected init-only renamed TIR eval to hit the probe, delta={delta:?}"
    );
    assert_eq!(
        delta.named_op_evals, 0,
        "init-only renamed probe should not rely on named-op evaluation, delta={delta:?}"
    );
}

/// Next-only probe canary for #3194.
///
/// This guards the renamed successor leaf path specifically: the test fails if
/// `NEXT` falls back to AST-only evaluation because the TIR expr probe stays at
/// zero even though the state count still matches.
fn assert_tir_eval_renamed_next_reports_probe_hit() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("StepProbe3194Next"));
    clear_for_test_reset();
    clear_global_name_interner();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();
    let module = parse_module(PROBED_RENAMED_COUNTER_SPEC);
    let config = Config::parse(
        "INIT BootProbe3194Init\nNEXT StepProbe3194Next\nINVARIANT SafeProbe3194Inv\n",
    )
    .expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
        }
        other => panic!("expected success with renamed next-only TIR eval, got: {other:?}"),
    }

    let after = tir_eval_probe_snapshot();
    let delta = probe_delta(&before, &after, "StepProbe3194Next");
    assert!(
        delta.expr_evals > 0,
        "expected next-only renamed TIR eval to hit the expr probe, delta={delta:?}"
    );
    assert_eq!(
        delta.named_op_evals, 0,
        "successor-leaf TIR should not require a separate named-op replay for renamed Next, delta={delta:?}"
    );
}

/// `all`-mode probe canary for #3294.
///
/// The resolved renamed `NEXT` operator must still hit the successor-leaf TIR
/// probe when `TLA2_TIR_EVAL=all`. Before the streaming `tir_leaf` threading
/// fix, the state count could stay correct while the successor path silently
/// fell back to AST-only evaluation.
fn assert_tir_eval_all_mode_renamed_next_reports_probe_hit() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("all"));
    clear_for_test_reset();
    clear_global_name_interner();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();
    let module = parse_module(PROBED_RENAMED_COUNTER_SPEC);
    let config = Config::parse(
        "INIT BootProbe3194Init\nNEXT StepProbe3194Next\nINVARIANT SafeProbe3194Inv\n",
    )
    .expect("config parse");

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
        }
        other => {
            panic!("expected success with renamed next probe under TIR all mode, got: {other:?}")
        }
    }

    let after = tir_eval_probe_snapshot();
    let delta = probe_delta(&before, &after, "StepProbe3194Next");
    assert!(
        delta.expr_evals > 0,
        "expected TIR all mode to hit the renamed next expr probe, delta={delta:?}"
    );
    assert_eq!(
        delta.named_op_evals, 0,
        "successor-leaf TIR in all mode should not require a separate named-op replay for renamed Next, delta={delta:?}"
    );
}

/// Constrained batch-diff probe canary for #3294.
///
/// The presence of constraints forces the sequential checker onto the batch
/// diff successor lane. The renamed `NEXT` operator must still hit the TIR
/// expr probe there instead of silently falling back to the AST-only compiled
/// action path.
fn assert_tir_eval_renamed_next_reports_probe_hit_with_constraints() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("StepProbe3294Next"));
    clear_for_test_reset();
    clear_global_name_interner();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();
    let module = parse_module(CONSTRAINED_RENAMED_NEXT_PROBE_SPEC);
    let config = Config {
        init: Some("BootProbe3294Init".to_string()),
        next: Some("StepProbe3294Next".to_string()),
        invariants: vec!["SafeProbe3294Inv".to_string()],
        constraints: vec!["BoundProbe3294".to_string()],
        action_constraints: vec!["ActionOkProbe3294".to_string()],
        ..Default::default()
    };

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 2,
                "expected constrained batch-diff run to keep the counter in {{0, 1}}"
            );
        }
        other => {
            panic!("expected success with constrained renamed next-only TIR eval, got: {other:?}")
        }
    }

    let after = tir_eval_probe_snapshot();
    let delta = probe_delta(&before, &after, "StepProbe3294Next");
    assert!(
        delta.expr_evals > 0,
        "expected constrained batch-diff TIR eval to hit the renamed next expr probe, delta={delta:?}"
    );
    assert_eq!(
        delta.named_op_evals, 0,
        "constrained batch-diff TIR should not require a separate named-op replay for renamed Next, delta={delta:?}"
    );
}

/// Replacement-resolved probe canary for #3194.
///
/// The config keeps `NEXT Next`, but a constant override rewires `Next` to a
/// different zero-arg operator. Selecting the resolved replacement name must
/// still activate leaf TIR evaluation and record probe hits under that
/// resolved name.
fn assert_tir_eval_uses_resolved_replacement_name_for_next() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("StepResolved3194Impl"));
    clear_for_test_reset();
    clear_global_name_interner();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();
    let module = parse_module(REPLACED_NEXT_PROBE_SPEC);
    let mut config = Config::parse("INIT Init\nNEXT Next\nINVARIANT Safe\n").expect("config parse");
    config.constants.insert(
        "Next".to_string(),
        ConstantValue::Replacement("StepResolved3194Impl".to_string()),
    );

    match check_module(&module, &config) {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 2,
                "expected replacement-resolved Next to keep the counter in {{0, 1}}"
            );
        }
        other => {
            panic!("expected success with replacement-resolved next-only TIR eval, got: {other:?}")
        }
    }

    let after = tir_eval_probe_snapshot();
    let delta = probe_delta(&before, &after, "StepResolved3194Impl");
    assert!(
        delta.expr_evals > 0,
        "expected resolved replacement name to receive expr probe hits, delta={delta:?}"
    );
}

#[test]
fn test_tir_resolved_name_routing() {
    assert_tir_eval_uses_renamed_operator_names();
    assert_tir_eval_uses_renamed_operator_names_with_coverage_enabled();
    assert_tir_eval_renamed_init_reports_probe_hit();
    assert_tir_eval_renamed_next_reports_probe_hit();
    assert_tir_eval_all_mode_renamed_next_reports_probe_hit();
    assert_tir_eval_renamed_next_reports_probe_hit_with_constraints();
    assert_tir_eval_uses_resolved_replacement_name_for_next();
}
