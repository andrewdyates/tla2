// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TIR eval probe canary tests for split-action simulation.
//! Extracted from simulation.rs to keep that file under 500 lines.

use super::simulation::{SimulationConfig, SimulationResult, SimulationStats};
use super::ModelChecker;
use crate::{CheckError, ConfigCheckError};
use std::collections::{BTreeMap, HashMap};
use tla_eval::tir::{enable_tir_eval_probe, tir_eval_probe_snapshot, TirEvalProbeCounts};

fn tir_probe_expr_delta(
    before: &BTreeMap<String, TirEvalProbeCounts>,
    after: &BTreeMap<String, TirEvalProbeCounts>,
    label: &str,
) -> usize {
    let before = before.get(label).copied().unwrap_or_default();
    let after = after.get(label).copied().unwrap_or_default();
    after.expr_evals.saturating_sub(before.expr_evals)
}

fn split_action_replacement_probe_fixture() -> (tla_core::ast::Module, crate::Config) {
    let src = r#"
---- MODULE SimulationSplitActionTirReplacementProbe ----
VARIABLE x
Init == x = 0
Next == FALSE
Inc == /\ x = 0
       /\ x' = x + 1
Stay == /\ x \in {0, 1}
        /\ x' = x
SimNext == Inc \/ Stay
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("module should lower");
    let mut constants = HashMap::new();
    constants.insert(
        "Next".to_string(),
        crate::config::ConstantValue::Replacement("SimNext".to_string()),
    );
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constants,
        ..Default::default()
    };
    (module, config)
}

fn run_split_action_probe_with_selected_ops(
    module: &tla_core::ast::Module,
    config: &crate::Config,
    selected_ops: &[&str],
) -> (
    SimulationResult,
    BTreeMap<String, TirEvalProbeCounts>,
    BTreeMap<String, TirEvalProbeCounts>,
) {
    crate::eval::clear_for_test_reset();
    // Part of #4067: Use reset_global_state() instead of direct
    // clear_global_name_interner() to respect the active-run guard.
    crate::reset_global_state();
    enable_tir_eval_probe();

    let mut checker = ModelChecker::new(module, config);
    checker.tir_parity = Some(super::tir_parity::TirParityState::test_eval_selected(
        module.clone(),
        Vec::new(),
        selected_ops.iter().copied(),
    ));

    let before = tir_eval_probe_snapshot();
    let result = checker.simulate(&SimulationConfig {
        num_traces: 1,
        max_trace_length: 1,
        seed: Some(1),
        check_invariants: false,
        ..Default::default()
    });
    let after = tir_eval_probe_snapshot();

    (result, before, after)
}

#[test]
fn test_detect_simulation_actions_expands_parameterized_inline_next() {
    use crate::check::resolve_spec_from_config;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SimParameterizedNext ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
A(i) == x < 10 /\ x' = x + i
B(i) == x < 10 /\ x' = x + i + 1
Next(i) == A(i) \/ B(i)
Spec == Init /\ [][\E i \in {1, 2}: Next(i)]_x
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let unresolved = crate::Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved = resolve_spec_from_config(&unresolved, &tree)
        .expect("SPECIFICATION formula should resolve Init and inline Next");
    let config = crate::Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let mut checker = ModelChecker::new(&module, &config);
    checker
        .register_inline_next(&resolved)
        .expect("inline next registration should succeed");
    let (_, next_name) = checker
        .prepare_simulation(&SimulationConfig::default())
        .expect("simulation setup should resolve inline next");

    let actions = checker.detect_simulation_actions(&next_name);
    assert_eq!(
        actions.len(),
        4,
        "parameterized inline Next should split per witness and disjunct"
    );
    assert_eq!(
        actions
            .iter()
            .filter(|action| action.name.as_deref() == Some("A"))
            .count(),
        2
    );
    assert_eq!(
        actions
            .iter()
            .filter(|action| action.name.as_deref() == Some("B"))
            .count(),
        2
    );

    let mut i_values: Vec<i64> = actions
        .iter()
        .map(|action| {
            action
                .bindings
                .iter()
                .find_map(|(name, value)| (name.as_ref() == "i").then_some(value))
                .and_then(crate::Value::as_i64)
                .expect("split action should bind i to a concrete witness")
        })
        .collect();
    i_values.sort_unstable();
    assert_eq!(i_values, vec![1, 1, 2, 2]);
}

#[test]
fn test_simulation_config_defaults() {
    let config = SimulationConfig::default();
    assert_eq!(config.num_traces, 1000);
    assert_eq!(config.max_trace_length, 100);
    assert!(config.seed.is_none());
    assert!(config.check_invariants);
    assert!(config.action_constraints.is_empty());
}

#[test]
#[allow(clippy::float_cmp)]
fn test_simulation_stats_default_zeroed() {
    // Exact comparison is safe: Default for f64 is exactly 0.0, no computation involved.
    let stats = SimulationStats::default();
    assert_eq!(stats.traces_generated, 0);
    assert_eq!(stats.states_visited, 0);
    assert_eq!(stats.distinct_states, 0);
    assert_eq!(stats.transitions, 0);
    assert_eq!(stats.max_trace_length, 0);
    assert_eq!(stats.avg_trace_length, 0.0);
    assert_eq!(stats.deadlocked_traces, 0);
    assert_eq!(stats.truncated_traces, 0);
    assert_eq!(stats.elapsed_secs, 0.0);
}

#[test]
fn test_simulation_depth_overflow_uses_setup_error() {
    let err = crate::checker_ops::depth_to_tlc_level(usize::MAX)
        .expect_err("overflow depth should return SetupError");
    assert!(matches!(
        err,
        CheckError::Config(ConfigCheckError::Setup(_))
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_split_action_simulation_selected_tir_eval_hits_next_probe() {
    let src = r#"
---- MODULE SimulationSplitActionTirProbe ----
VARIABLE x
Init == x = 0
Inc == /\ x = 0
       /\ x' = x + 1
Stay == /\ x \in {0, 1}
        /\ x' = x
Next == Inc \/ Stay
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("module should lower");
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let (result, before, after) =
        run_split_action_probe_with_selected_ops(&module, &config, &["Next"]);

    match result {
        SimulationResult::Success(stats) => {
            assert_eq!(stats.traces_generated, 1, "expected one simulated trace");
            assert_eq!(stats.transitions, 1, "expected one simulated transition");
        }
        other => panic!("expected simulation success for TIR probe canary, got: {other:?}"),
    }

    assert!(
        tir_probe_expr_delta(&before, &after, "Next") > 0,
        "split-action simulation selected for TIR should hit the Next probe instead of silently staying on AST-only evaluation"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_split_action_simulation_selected_tir_eval_hits_raw_next_probe_through_replacement() {
    let (module, config) = split_action_replacement_probe_fixture();
    let (result, before, after) =
        run_split_action_probe_with_selected_ops(&module, &config, &["Next"]);

    match result {
        SimulationResult::Success(stats) => {
            assert_eq!(stats.traces_generated, 1, "expected one simulated trace");
            assert_eq!(stats.transitions, 1, "expected one simulated transition");
        }
        other => {
            panic!("expected simulation success for raw-name TIR probe canary, got: {other:?}")
        }
    }

    assert!(
        tir_probe_expr_delta(&before, &after, "Next") > 0,
        "split-action simulation selected for TIR via raw config Next should hit the raw-name probe even when NEXT resolves to SimNext"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_split_action_simulation_selected_tir_eval_hits_resolved_next_probe_through_replacement() {
    let (module, config) = split_action_replacement_probe_fixture();
    let (result, before, after) =
        run_split_action_probe_with_selected_ops(&module, &config, &["SimNext"]);

    match result {
        SimulationResult::Success(stats) => {
            assert_eq!(stats.traces_generated, 1, "expected one simulated trace");
            assert_eq!(stats.transitions, 1, "expected one simulated transition");
        }
        other => {
            panic!("expected simulation success for resolved-name TIR probe canary, got: {other:?}")
        }
    }

    assert!(
        tir_probe_expr_delta(&before, &after, "SimNext") > 0,
        "split-action simulation selected for TIR via resolved SimNext should hit the resolved-name probe when config Next is replacement-mapped"
    );
}
