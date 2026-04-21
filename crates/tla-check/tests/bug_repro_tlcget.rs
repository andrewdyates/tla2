// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLCGet level indexing - Part of #254
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::parse_module;
use tla_check::{check_module, CheckResult, Config, LimitType, ModelChecker};

// ============================================================================
// Part of #254: TLCGet("level") 1-based indexing verification
// ============================================================================

/// Discriminator test for TLCGet("level") 1-based indexing.
///
/// Part of #254: Animation specs like EWD840_anim use TLCGet("level") to
/// display the current BFS exploration depth in SVG output.
///
/// TLC uses 1-based indexing:
/// - Initial states are at level 1
/// - First successors are at level 2
/// - etc.
///
/// This test verifies TLA2 matches TLC's behavior by:
/// 1. Using TLCGet("level") in an invariant that would fail if level is wrong
/// 2. Creating a spec with known depth structure
///
/// WITHOUT the fix: Level might be 0-based, causing invariant violations
/// WITH the fix: Levels are 1-based, matching TLC behavior
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlcget_level_1_based_indexing() {
    // This spec verifies TLCGet("level") returns 1-based values.
    // We track depth explicitly and verify it matches TLCGet("level").
    // Depth goes 1 -> 2 -> 3 and then terminates (deadlock).
    let spec = r#"
---- MODULE TLCGetLevelTest ----
EXTENDS TLC, Naturals

VARIABLE depth

\* Invariant: TLCGet("level") should always equal depth
\* This catches any off-by-one errors in level indexing
LevelCorrect == TLCGet("level") = depth

\* Initial state at BFS depth 0, but TLC level = 1
Init == depth = 1

\* Each step increments depth up to 3, then no more transitions
Next == depth < 3 /\ depth' = depth + 1

====
"#;

    let module = parse_module(spec);
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["LevelCorrect".to_string()],
        ..Default::default()
    };
    config.check_deadlock = false; // Deadlock is expected at depth=3

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(stats) => {
            // Expected: 3 states (depth = 1, 2, 3) - all at correct levels
            assert_eq!(
                stats.states_found, 3,
                "TLCGet(\"level\") test: Expected 3 states, got {}",
                stats.states_found
            );
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "TLCGet(\"level\") off-by-one! Invariant {} violated. \
                 TLA2 level indexing doesn't match TLC's 1-based convention.",
                invariant
            );
        }
        other => panic!("TLCGet(\"level\") test unexpected result: {:?}", other),
    }
}

/// Regression for #1102: sequential store-states path must evaluate successor invariants
/// at succState level (not curState level).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlcget_level_1_based_indexing_store_states_mode() {
    let spec = r#"
---- MODULE TLCGetLevelStoreStatesTest ----
EXTENDS TLC, Naturals

VARIABLE depth

LevelCorrect == TLCGet("level") = depth

Init == depth = 1
Next == depth < 3 /\ depth' = depth + 1

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["LevelCorrect".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "store-states TLCGet(\"level\") test: expected 3 states, got {}",
                stats.states_found
            );
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!("store-states TLCGet(\"level\") off-by-one: invariant {invariant} violated");
        }
        other => panic!(
            "store-states TLCGet(\"level\") test unexpected result: {:?}",
            other
        ),
    }
}

/// Regression for #1102: sequential BFS must keep TLCGet("level") context split between:
/// - ACTION_CONSTRAINT evaluation in current-state context, and
/// - invariant/VIEW evaluation in successor-state context.
///
/// This explicitly exercises all 4 sequential BFS combinations:
/// 1. store_states=true,  VIEW disabled  (full-state + diff path)
/// 2. store_states=true,  VIEW enabled   (full-state + full successor path)
/// 3. store_states=false, VIEW disabled  (no-trace + diff path)
/// 4. store_states=false, VIEW enabled   (no-trace + full successor path)
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_tlcget_level_context_across_all_sequential_bfs_paths() {
    let spec = r#"
---- MODULE SequentialTLCGetLevelContext ----
EXTENDS TLC, Naturals

VARIABLE x

Init == x = 1
Next == /\ x < 3 /\ x' = x + 1

\* ACTION_CONSTRAINT is evaluated in current-state context.
CurLevelOk == TLCGet("level") = x

\* Invariant is evaluated in successor-state context.
SuccLevelOk == TLCGet("level") = x

\* Optional VIEW to force non-diff successor fingerprinting path.
LevelView == <<x, TLCGet("level")>>

====
"#;

    let module = parse_module(spec);

    for use_view in [false, true] {
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["SuccLevelOk".to_string()],
            action_constraints: vec!["CurLevelOk".to_string()],
            view: use_view.then_some("LevelView".to_string()),
            check_deadlock: false,
            ..Default::default()
        };

        for store_states in [false, true] {
            let mut checker = ModelChecker::new(&module, &config);
            checker.set_store_states(store_states);
            checker.set_auto_create_trace_file(false);

            let result = checker.check();
            match result {
                CheckResult::Success(stats) => {
                    assert_eq!(
                        stats.states_found, 3,
                        "sequential TLCGet context mismatch (store_states={}, use_view={})",
                        store_states, use_view
                    );
                }
                other => panic!(
                    "Expected Success for store_states={} use_view={}, got {:?}",
                    store_states, use_view, other
                ),
            }
        }
    }
}

/// Regression for #1102: successor VIEW fingerprinting must use succState level.
///
/// This spec stutters forever (`x' = x`). Distinct state discovery therefore depends entirely on
/// VIEW including `TLCGet("level")`. If successor fingerprinting uses curState level, each
/// successor aliases with its parent and exploration stalls at 1 state.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlcget_level_view_fingerprint_successor_level_in_both_storage_modes() {
    let spec = r#"
---- MODULE TLCGetLevelViewFingerprintTest ----
EXTENDS TLC

VARIABLE x

Init == x = 0
Next == x' = x
LevelView == TLCGet("level")

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        view: Some("LevelView".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    for store_states in [false, true] {
        let mut checker = ModelChecker::new(&module, &config);
        checker.set_store_states(store_states);
        checker.set_auto_create_trace_file(false);
        checker.set_max_depth(3);

        let result = checker.check();
        match result {
            CheckResult::LimitReached {
                limit_type: LimitType::Depth,
                stats,
            } => {
                assert_eq!(
                    stats.states_found, 4,
                    "view/TLCGet(\"level\") dedup mismatch in store_states={}: expected 4 states, got {}",
                    store_states, stats.states_found
                );
            }
            other => panic!(
                "view/TLCGet(\"level\") test unexpected result in store_states={}: {:?}",
                store_states, other
            ),
        }
    }
}

/// Test TLCGet("level") for TTrace-style trace replay.
///
/// TTrace specs use `TLCGet("level") = Len(_TETrace)` to verify
/// that the model checker is at the expected position in the trace.
/// This test verifies that pattern works correctly.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlcget_level_trace_replay_pattern() {
    // This mimics TTrace's usage: check that level matches trace position
    let spec = r#"
---- MODULE TLCGetLevelTracePattern ----
EXTENDS TLC, Naturals, Sequences

VARIABLE state

\* A hardcoded "trace" of 4 states
trace == <<1, 2, 3, 4>>

\* TTrace pattern: level should match trace length when we reach final state
\* Since we're doing BFS, we'll see states 1,2,3,4 at levels 1,2,3,4
TraceComplete == state = 4 => TLCGet("level") = 4

\* Initial state is trace[1]
Init == state = trace[1]

\* Next state follows trace sequence (i -> i+1)
Next ==
    /\ state < Len(trace)
    /\ state' = trace[state + 1]

====
"#;

    let module = parse_module(spec);
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TraceComplete".to_string()],
        ..Default::default()
    };
    config.check_deadlock = false; // Deadlock expected when state=4

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(stats) => {
            // Expected: 4 states (1, 2, 3, 4) following the trace
            assert_eq!(
                stats.states_found, 4,
                "TLCGet trace pattern: Expected 4 states, got {}",
                stats.states_found
            );
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "TLCGet trace pattern failed! Invariant {} violated. \
                 Level at state 4 should be 4 but wasn't.",
                invariant
            );
        }
        other => panic!("TLCGet trace pattern unexpected result: {:?}", other),
    }
}
