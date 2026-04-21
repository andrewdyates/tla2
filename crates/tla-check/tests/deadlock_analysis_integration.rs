// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for the deadlock analysis engine.
//!
//! These tests run the full model checker pipeline, detect deadlocks,
//! and then invoke the deadlock analysis engine on the deadlocked state.

use std::sync::Arc;

use tla_check::{analyze_deadlock, check_module, CheckResult, Config, DeadlockAnalysis};
use tla_core::{lower, parse_to_syntax_tree, FileId};

fn parse_and_check(src: &str) -> (CheckResult, tla_core::ast::Module, Config) {
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: true,
        ..Default::default()
    };
    let result = check_module(&module, &config);
    (result, module, config)
}

fn run_deadlock_analysis(src: &str, var_names: &[&str]) -> (DeadlockAnalysis, tla_check::Trace) {
    let (result, module, config) = parse_and_check(src);
    match result {
        CheckResult::Deadlock { trace, .. } => {
            let deadlocked_state = trace.states.last().expect("trace should have states");

            // Create an EvalCtx and load the module (operators + stdlib).
            let mut ctx = tla_check::EvalCtx::new();
            ctx.load_module(&module);

            let next_name = config.next.as_deref().unwrap_or("Next");
            let next_def = ctx
                .get_op(next_name)
                .expect("Next should be defined")
                .clone();

            let var_arcs: Vec<Arc<str>> = var_names.iter().map(|&n| Arc::from(n)).collect();
            let analysis = analyze_deadlock(&mut ctx, &next_def, deadlocked_state, &var_arcs);
            (analysis, trace)
        }
        other => panic!("Expected Deadlock, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deadlock_analysis_single_action_simple_guard() {
    let src = r#"
---- MODULE DeadlockSingleGuard ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 5 /\ x' = x + 1
====
"#;
    let (analysis, trace) = run_deadlock_analysis(src, &["x"]);

    // Deadlocked state should be x=5.
    let deadlocked = trace.states.last().unwrap();
    let x_val = deadlocked.get("x").unwrap();
    assert_eq!(*x_val, tla_check::Value::int(5));

    // Analysis should find at least one action with false conjuncts.
    assert!(!analysis.actions.is_empty());
    let action = &analysis.actions[0];
    assert!(
        action.false_conjuncts > 0,
        "at least one conjunct should be false"
    );

    // There should be false conjuncts with x in the relevant variables.
    let false_conjuncts: Vec<_> = action.conjuncts.iter().filter(|c| !c.satisfied).collect();
    assert!(!false_conjuncts.is_empty());

    let has_x = false_conjuncts.iter().any(|c| {
        c.relevant_variables
            .iter()
            .any(|(name, val)| name == "x" && val == "5")
    });
    assert!(has_x, "should report x=5 in relevant variables");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deadlock_analysis_multiple_actions() {
    let src = r#"
---- MODULE DeadlockMultiAction ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
A == x < 3 /\ x' = x + 1
B == x > 10 /\ x' = x - 1
Next == A \/ B
====
"#;
    let (analysis, _trace) = run_deadlock_analysis(src, &["x"]);

    // Should have at least 2 action diagnostics (A and B).
    assert!(
        analysis.actions.len() >= 2,
        "expected at least 2 actions, got {}",
        analysis.actions.len()
    );

    // All actions should have at least one false conjunct.
    for action in &analysis.actions {
        assert!(
            action.false_conjuncts > 0,
            "action {} should have at least one false conjunct",
            action.name
        );
    }

    // Closest action should be meaningful.
    assert!(analysis.closest_action().is_some());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_deadlock_analysis_ranking() {
    let src = r#"
---- MODULE DeadlockRanking ----
EXTENDS Naturals
VARIABLE x, y
Init == x = 0 /\ y = 0
A == x < 3 /\ y >= 0 /\ x' = x + 1 /\ y' = y
B == x > 10 /\ y > 10 /\ x' = x - 1 /\ y' = y
Next == A \/ B
====
"#;
    let (analysis, _trace) = run_deadlock_analysis(src, &["x", "y"]);

    // Actions should be sorted by false_conjuncts (ascending).
    let false_counts: Vec<usize> = analysis.actions.iter().map(|a| a.false_conjuncts).collect();
    for window in false_counts.windows(2) {
        assert!(
            window[0] <= window[1],
            "actions should be sorted by false_conjuncts: {:?}",
            false_counts
        );
    }

    // The display format should contain expected markers.
    let display = format!("{}", analysis);
    assert!(display.contains("Deadlock Analysis"));
    assert!(display.contains("[FAIL]"));
    assert!(display.contains("Closest to enabled"));
}
