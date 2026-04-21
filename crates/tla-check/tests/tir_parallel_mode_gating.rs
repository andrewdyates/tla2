// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;

use std::collections::BTreeMap;

use common::{parse_module, EnvVarGuard};
use tla_check::eval::clear_for_test_reset;
use tla_check::{
    AdaptiveChecker, CheckError, CheckResult, Config, ConfigCheckError, ConstantValue,
    ParallelChecker, Strategy,
};
use tla_core::clear_global_name_interner;
use tla_eval::tir::{enable_tir_eval_probe, tir_eval_probe_snapshot, TirEvalProbeCounts};

const LARGE_SPEC: &str = r#"
---- MODULE TirParallelModeGating ----
VARIABLE x, y, z
Init == x \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ y \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ z \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
Next == x' \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ y' \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ z' \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
Valid == TRUE
===="#;

const LARGE_RENAMED_SPEC: &str = r#"
---- MODULE TirParallelModeGatingRenamed ----
VARIABLE x, y, z
Boot == x \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ y \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ z \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
Step == x' \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ y' \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
     /\ z' \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
Safe == TRUE
===="#;

const SMALL_SPEC: &str = r#"
---- MODULE TirParallelModeDirect ----
VARIABLE x
Init == x = 0
Next == x' = x
Inv == TRUE
===="#;

const PARALLEL_RENAMED_NEXT_PROBE_SPEC: &str = r#"
---- MODULE TirParallelModeDirectProbe ----
VARIABLE x
BootProbe3285Init == x = 0
StepProbe3285Next ==
    IF x < 1
    THEN x' = x + 1
    ELSE x' = x
SafeProbe3285Inv == x \in {0, 1}
===="#;

const PARALLEL_CONSTRAINED_NEXT_PROBE_SPEC: &str = r#"
---- MODULE TirParallelModeDirectConstrainedProbe ----
VARIABLE x
BootProbe3285ConstrainedInit == x = 0
StepProbe3285ConstrainedNext ==
    IF x < 1
    THEN x' = x + 1
    ELSE x' = x
BoundProbe3285 == x <= 1
ActionOkProbe3285 == x' <= 1
SafeProbe3285ConstrainedInv == x \in {0, 1}
===="#;

const PARALLEL_RESOLVED_NEXT_PROBE_SPEC: &str = r#"
---- MODULE TirParallelModeResolvedProbe ----
VARIABLE x
Init == x = 0
Next == x' = 99
StepResolved3285Impl ==
    IF x < 1
    THEN x' = x + 1
    ELSE x' = x
Safe == x \in {0, 1}
===="#;

const PARALLEL_BINDING_FALLBACK_NEXT_PROBE_SPEC: &str = r#"
---- MODULE TirParallelModeBindingFallbackProbe ----
VARIABLE x
Init == x = 0
Next == x' = [i \in {0, 1} |-> 1 - i][x]
Inv == x \in {0, 1}
===="#;

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

fn assert_parallel_rejected_for_env(key: &'static str, value: &'static str, needle: &str) {
    let _guard = EnvVarGuard::set(key, Some(value));
    let module = parse_module(SMALL_SPEC);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    match checker.check() {
        CheckResult::Error {
            error: CheckError::Config(ConfigCheckError::Config(message)),
            ..
        } => {
            assert!(
                message.contains(needle),
                "expected rejection message containing {needle:?}, got: {message}"
            );
        }
        other => panic!("expected direct parallel rejection for {key}, got: {other:?}"),
    }
}

fn assert_parallel_next_only_tir_eval_reports_probe_hit() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("StepProbe3285Next"));
    clear_for_test_reset();
    clear_global_name_interner();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();
    let module = parse_module(PARALLEL_RENAMED_NEXT_PROBE_SPEC);
    let config = Config::parse(
        "INIT BootProbe3285Init\nNEXT StepProbe3285Next\nINVARIANT SafeProbe3285Inv\n",
    )
    .expect("config parse");

    let checker = ParallelChecker::new(&module, &config, 2);
    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
        }
        other => panic!("expected direct parallel next-only TIR eval to succeed, got: {other:?}"),
    }

    let after = tir_eval_probe_snapshot();
    let delta = probe_delta(&before, &after, "StepProbe3285Next");
    assert!(
        delta.expr_evals > 0,
        "expected direct parallel next-only TIR eval to hit the expr probe, delta={delta:?}"
    );
    assert_eq!(
        delta.named_op_evals, 0,
        "direct parallel leaf TIR should not require named-op replay, delta={delta:?}"
    );
}

fn assert_parallel_constrained_next_only_tir_eval_reports_probe_hit() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("StepProbe3285ConstrainedNext"));
    clear_for_test_reset();
    clear_global_name_interner();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();
    let module = parse_module(PARALLEL_CONSTRAINED_NEXT_PROBE_SPEC);
    let config = Config {
        init: Some("BootProbe3285ConstrainedInit".to_string()),
        next: Some("StepProbe3285ConstrainedNext".to_string()),
        invariants: vec!["SafeProbe3285ConstrainedInv".to_string()],
        constraints: vec!["BoundProbe3285".to_string()],
        action_constraints: vec!["ActionOkProbe3285".to_string()],
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 2,
                "expected constrained direct parallel run to keep the counter in {{0, 1}}"
            );
        }
        other => panic!(
            "expected constrained direct parallel next-only TIR eval to succeed, got: {other:?}"
        ),
    }

    let after = tir_eval_probe_snapshot();
    let delta = probe_delta(&before, &after, "StepProbe3285ConstrainedNext");
    assert!(
        delta.expr_evals > 0,
        "expected constrained direct parallel TIR eval to hit the expr probe, delta={delta:?}"
    );
    assert_eq!(
        delta.named_op_evals, 0,
        "constrained direct parallel leaf TIR should not require named-op replay, delta={delta:?}"
    );
}

fn assert_parallel_resolved_next_selection_reports_probe_hit() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("StepResolved3285Impl"));
    clear_for_test_reset();
    clear_global_name_interner();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();
    let module = parse_module(PARALLEL_RESOLVED_NEXT_PROBE_SPEC);
    let mut config = Config::parse("INIT Init\nNEXT Next\nINVARIANT Safe\n").expect("config parse");
    config.constants.insert(
        "Next".to_string(),
        ConstantValue::Replacement("StepResolved3285Impl".to_string()),
    );

    let checker = ParallelChecker::new(&module, &config, 2);
    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 2,
                "expected resolved replacement Next to keep the counter in {{0, 1}}"
            );
        }
        other => {
            panic!("expected resolved replacement next-only TIR eval to succeed, got: {other:?}")
        }
    }

    let after = tir_eval_probe_snapshot();
    let delta = probe_delta(&before, &after, "StepResolved3285Impl");
    assert!(
        delta.expr_evals > 0,
        "expected resolved replacement next name to receive expr probe hits, delta={delta:?}"
    );
    assert_eq!(
        delta.named_op_evals, 0,
        "resolved replacement direct parallel leaf TIR should not require named-op replay, delta={delta:?}"
    );
}

fn assert_parallel_all_tir_eval_reports_probe_hit() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("all"));
    clear_for_test_reset();
    clear_global_name_interner();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();
    let module = parse_module(PARALLEL_RENAMED_NEXT_PROBE_SPEC);
    let config = Config::parse(
        "INIT BootProbe3285Init\nNEXT StepProbe3285Next\nINVARIANT SafeProbe3285Inv\n",
    )
    .expect("config parse");

    let checker = ParallelChecker::new(&module, &config, 2);
    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(stats.states_found, 2, "expected two reachable states");
        }
        other => panic!("expected direct parallel TLA2_TIR_EVAL=all to succeed, got: {other:?}"),
    }

    let after = tir_eval_probe_snapshot();
    let delta = probe_delta(&before, &after, "StepProbe3285Next");
    assert!(
        delta.expr_evals > 0,
        "expected direct parallel TLA2_TIR_EVAL=all to hit the expr probe, delta={delta:?}"
    );
    assert_eq!(
        delta.named_op_evals, 0,
        "direct parallel TLA2_TIR_EVAL=all leaf TIR should not require named-op replay, delta={delta:?}"
    );
}

/// Part of #3350: binding-form operators (FuncDef in `[i \in {0,1} |-> 1-i][x]`)
/// are now evaluated through TIR instead of falling back to AST. The blanket
/// unsound-binding-form guard has been removed.
fn assert_parallel_binding_form_next_uses_tir() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Next"));
    clear_for_test_reset();
    clear_global_name_interner();
    enable_tir_eval_probe();
    let before = tir_eval_probe_snapshot();
    let module = parse_module(PARALLEL_BINDING_FALLBACK_NEXT_PROBE_SPEC);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1, "expected single initial state");
            assert_eq!(
                stats.states_found, 2,
                "expected the binding-form next probe to toggle between 0 and 1"
            );
        }
        other => panic!(
            "expected binding-form direct parallel next-only TIR eval to succeed, got: {other:?}"
        ),
    }

    // Part of #3350: After removing the blanket binding-form guard, TIR leaf
    // evaluation now fires for FuncDef-containing expressions. The probe
    // counter should be > 0 because TIR lowering succeeds for this expression.
    let after = tir_eval_probe_snapshot();
    let delta = probe_delta(&before, &after, "Next");
    assert!(
        delta.expr_evals > 0,
        "binding-form FuncDef should now use TIR; TIR probe should fire, delta={delta:?}"
    );
    assert_eq!(
        delta.named_op_evals, 0,
        "binding-form direct parallel leaf TIR should not require named-op replay, delta={delta:?}"
    );
}

#[test]
fn test_tir_modes_force_sequential_or_fail_closed() {
    {
        let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Valid"));
        let module = parse_module(LARGE_SPEC);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["Valid".to_string()],
            ..Default::default()
        };

        let mut checker = AdaptiveChecker::new(&module, &config);
        checker.set_deadlock_check(false);
        checker.set_max_states(100);

        let (result, analysis) = checker.check();
        let analysis = analysis.expect("adaptive check should return pilot analysis");

        assert!(
            matches!(analysis.strategy, Strategy::Sequential),
            "TIR mode must force sequential execution, got {:?}",
            analysis.strategy
        );
        assert!(
            !matches!(result, CheckResult::Error { .. }),
            "forcing sequential should avoid a parallel-only configuration error, got {result:?}"
        );
    }

    assert_parallel_rejected_for_env("TLA2_TIR_EVAL", "Inv", "next-only TLA2_TIR_EVAL");
    assert_parallel_rejected_for_env("TLA2_TIR_EVAL", "Next,Inv", "next-only TLA2_TIR_EVAL");
    assert_parallel_rejected_for_env("TLA2_TIR_PARITY", "Inv", "TLA2_TIR_PARITY");
    assert_parallel_all_tir_eval_reports_probe_hit();
    assert_parallel_next_only_tir_eval_reports_probe_hit();
    assert_parallel_constrained_next_only_tir_eval_reports_probe_hit();
    assert_parallel_resolved_next_selection_reports_probe_hit();
    assert_parallel_binding_form_next_uses_tir();

    // Adaptive still stays sequential for explicit TLA2_TIR_EVAL=all (#3324).
    {
        let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("all"));
        let module = parse_module(LARGE_SPEC);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["Valid".to_string()],
            ..Default::default()
        };

        let mut checker = AdaptiveChecker::new(&module, &config);
        checker.set_deadlock_check(false);
        checker.set_max_states(100);

        let (result, analysis) = checker.check();
        let analysis = analysis.expect("adaptive check should return pilot analysis");

        assert!(
            matches!(analysis.strategy, Strategy::Sequential),
            "TLA2_TIR_EVAL=all must still force sequential in adaptive mode, got {:?}",
            analysis.strategy
        );
        assert!(
            !matches!(result, CheckResult::Error { .. }),
            "adaptive TLA2_TIR_EVAL=all sequential forcing should succeed, got {result:?}"
        );
    }
}

#[test]
fn test_tir_eval_collect_coverage_keeps_adaptive_on_resolved_sequential_path() {
    let _guard = EnvVarGuard::set("TLA2_TIR_EVAL", Some("Boot,Step,Safe"));
    let module = parse_module(LARGE_RENAMED_SPEC);
    let config = Config::parse("INIT Boot\nNEXT Step\nINVARIANT Safe\n").expect("config parse");

    let mut checker = AdaptiveChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_collect_coverage(true);

    let (result, analysis) = checker.check();
    let analysis = analysis.expect("adaptive check should return pilot analysis");

    assert!(
        matches!(analysis.strategy, Strategy::Sequential),
        "TIR eval plus coverage must keep adaptive execution sequential, got {:?}",
        analysis.strategy
    );

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 1000, "expected full renamed init space");
            assert_eq!(
                stats.states_found, 1000,
                "expected the renamed large spec to stabilize at 1000 states"
            );
            let coverage = stats
                .coverage
                .as_ref()
                .expect("coverage should be present when adaptive routing keeps collection on");
            assert!(
                !coverage.action_order.is_empty(),
                "coverage should record actions on the resolved sequential path"
            );
        }
        other => panic!(
            "expected adaptive coverage run with renamed TIR-selected operators to succeed, got {other:?}"
        ),
    }
}
