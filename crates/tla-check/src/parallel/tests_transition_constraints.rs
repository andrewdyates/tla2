// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::check::CheckResult;
use tla_core::{lower, parse_to_syntax_tree, FileId};

fn parse_module(src: &str) -> Result<Module, String> {
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    lower_result
        .module
        .ok_or_else(|| "Expected lowered module in transition parity regression".to_string())
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_transition_count_matches_sequential_with_action_constraint() -> Result<(), String>
{
    let _serial = crate::test_utils::acquire_interner_lock();
    // Regression for #2268: in the constraint path, parallel transition accounting
    // must count only successors that pass ACTION_CONSTRAINT filtering.
    let src = r#"
---- MODULE ConstraintTransitionParity ----
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' \in {x, x + 1}
OnlyForward == x' = x + 1
====
"#;
    let module = parse_module(src)?;

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        action_constraints: vec!["OnlyForward".to_string()],
        ..Default::default()
    };

    let mut seq_checker = crate::check::ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    let seq_stats = match seq_checker.check() {
        CheckResult::Success(stats) => stats,
        other => {
            return Err(format!(
                "Expected sequential success with action constraints, got {:?}",
                other
            ));
        }
    };

    let mut par_checker = ParallelChecker::new(&module, &config, 4);
    par_checker.set_deadlock_check(false);
    let par_stats = match par_checker.check() {
        CheckResult::Success(stats) => stats,
        other => {
            return Err(format!(
                "Expected parallel success with action constraints, got {:?}",
                other
            ));
        }
    };

    assert_eq!(seq_stats.states_found, 4);
    assert_eq!(par_stats.states_found, 4);
    assert_eq!(seq_stats.transitions, 3);
    assert_eq!(
        seq_stats.transitions, par_stats.transitions,
        "Transition count differs between sequential ({}) and parallel ({}) under ACTION_CONSTRAINT filtering",
        seq_stats.transitions, par_stats.transitions
    );
    Ok(())
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_transition_count_matches_sequential_with_state_constraint() -> Result<(), String> {
    let _serial = crate::test_utils::acquire_interner_lock();
    // Regression for #2268: in the constraint path, parallel transition accounting
    // must count only successors that pass CONSTRAINT filtering.
    let src = r#"
---- MODULE ConstraintTransitionParityState ----
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' \in {x, x + 1}
WithinBound == x <= 1
====
"#;
    let module = parse_module(src)?;

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constraints: vec!["WithinBound".to_string()],
        ..Default::default()
    };

    let mut seq_checker = crate::check::ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    let seq_stats = match seq_checker.check() {
        CheckResult::Success(stats) => stats,
        other => {
            return Err(format!(
                "Expected sequential success with constraints, got {:?}",
                other
            ));
        }
    };

    let mut par_checker = ParallelChecker::new(&module, &config, 4);
    par_checker.set_deadlock_check(false);
    let par_stats = match par_checker.check() {
        CheckResult::Success(stats) => stats,
        other => {
            return Err(format!(
                "Expected parallel success with constraints, got {:?}",
                other
            ));
        }
    };

    assert_eq!(seq_stats.states_found, 2);
    assert_eq!(par_stats.states_found, 2);
    assert_eq!(seq_stats.transitions, 3);
    assert_eq!(
        seq_stats.transitions, par_stats.transitions,
        "Transition count differs between sequential ({}) and parallel ({}) under CONSTRAINT filtering",
        seq_stats.transitions, par_stats.transitions
    );
    Ok(())
}
