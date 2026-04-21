// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! POSTCONDITION evaluation - Part of #1102
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::parse_module;
use ntest::timeout;
use tla_check::RuntimeCheckError;
use tla_check::{check_module, check_module_parallel, CheckError, CheckResult, Config};

// ============================================================================
// POSTCONDITION evaluation (Part of #1102)
// ============================================================================

/// POSTCONDITION using TLCGet("level") to verify BFS depth is accessible.
/// Stronger than `PostCond == TRUE` because it catches wrong TLCGet("level")
/// values or premature evaluation (before BFS, when level would be 1).
/// Note: does NOT detect a dead postcondition feature — if postcondition
/// evaluation is silently skipped, the result is still Success. The companion
/// `postcondition_false_fails` test covers that case.
/// For spec x=0..3 (4 states across 4 BFS levels), TLC level > 1 after BFS.
/// Replaces the original trivially-true `PostCond == TRUE` test per #1299.
#[test]
#[timeout(30_000)]
fn postcondition_verifies_bfs_level() {
    let src = r#"
---- MODULE PostcondLevel ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = IF x < 3 THEN x + 1 ELSE x
\* After BFS, level should be > 1 (init states are at level 1).
\* A dead postcondition feature that never evaluates this would
\* produce Success without checking level — indistinguishable from no postcondition.
\* But if level evaluation produces an error or wrong value, this catches it.
PostCond == TLCGet("level") > 1
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        postcondition: Some("PostCond".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 4,
                "expected 4 states, got {}",
                stats.states_found
            );
        }
        other => panic!(
            "POSTCONDITION checking BFS level should succeed, got: {:?}",
            other
        ),
    }
}

/// POSTCONDITION that evaluates to FALSE should produce PostconditionFalse error.
#[test]
#[timeout(30_000)]
fn postcondition_false_fails() {
    let src = r#"
---- MODULE PostcondFalse ----
VARIABLE x
Init == x = 0
Next == x' = IF x < 3 THEN x + 1 ELSE x
PostCond == FALSE
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        postcondition: Some("PostCond".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Error {
            error: CheckError::Runtime(RuntimeCheckError::PostconditionFalse { operator }),
            ..
        } => {
            assert_eq!(operator, "PostCond");
        }
        other => panic!(
            "POSTCONDITION FALSE should produce PostconditionFalse error, got: {:?}",
            other
        ),
    }
}

/// POSTCONDITION using TLCGet("stats").diameter to check dynamic BFS depth.
/// TLCGet("stats").diameter returns ctx.tlc_level, which is the last BFS level.
/// For spec x=0..2 (3 states), the final BFS diameter is > 0.
/// This is stronger than the original TLCGet("config").mode = "bfs" per #1299:
/// - TLCGet("config").mode is a static constant, always "bfs"
/// - TLCGet("stats").diameter requires BFS to have actually run
#[test]
#[timeout(30_000)]
fn postcondition_with_tlcget_stats_diameter() {
    let src = r#"
---- MODULE PostcondTLCGetStats ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = IF x < 2 THEN x + 1 ELSE x
\* TLCGet("stats").diameter is set to the BFS depth after exploration.
\* This verifies that TLCGet("stats") returns a record with a numeric diameter
\* field that reflects actual BFS progress, not a stub.
PostCond == TLCGet("stats").diameter > 0
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        postcondition: Some("PostCond".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "expected 3 states, got {}",
                stats.states_found
            );
        }
        other => panic!(
            "POSTCONDITION checking stats.diameter should succeed, got: {:?}",
            other
        ),
    }
}

/// POSTCONDITION diameter must equal max BFS depth + 1 (TLC parity).
/// For spec x=0..4 (5 states, BFS depths 0-4), TLC diameter = 5.
/// TLCGet("stats").diameter should be 5, not 6 (successor level at last depth).
/// Regression test for #1102: POSTCONDITION was reading ctx.tlc_level which was
/// left at succ_level (off-by-one) instead of the correct BFS diameter.
/// Reference: TLC Worker.java:303, ConcurrentTLCTrace.java:77.
#[test]
#[timeout(30_000)]
fn postcondition_diameter_exact_value() {
    let src = r#"
---- MODULE PostcondDiameterExact ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = IF x < 4 THEN x + 1 ELSE x
\* TLC diameter = max successor level = 5 (states at depths 0,1,2,3,4).
\* BFS: init at depth 0 (level 1), deepest successor at depth 4 (level 5).
\* diameter - 1 = 4, which equals the number of Next transitions.
PostCond == TLCGet("stats").diameter = 5
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        postcondition: Some("PostCond".to_string()),
        ..Default::default()
    };

    let check_result = |mode: &str, result: CheckResult| match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 5,
                "{mode}: expected 5 states, got {}",
                stats.states_found
            );
        }
        other => panic!(
            "{mode}: POSTCONDITION diameter should be exactly 5, got: {:?}",
            other
        ),
    };

    check_result("sequential", check_module(&module, &config));
    check_result("parallel", check_module_parallel(&module, &config, 2));
}

/// POSTCONDITION must observe the final TLCGet("stats") snapshot after BFS.
/// Regression for #3414 follow-up audit: a stale per-state runtime snapshot
/// caused POSTCONDITION to see `generated=2` instead of the final `generated=3`
/// on a 2-state cycle, even though TLC reports the final counters.
#[test]
#[timeout(30_000)]
fn postcondition_stats_final_snapshot_exact_values() {
    let src = r#"
---- MODULE PostcondStatsFinalSnapshot ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = IF x = 0 THEN 1 ELSE 0
\* Final BFS stats:
\* - generated = 3 (1 initial + 2 transitions)
\* - distinct  = 2 (states x=0 and x=1)
\* - queue     = 0 after exhaustion
\* - diameter  = 2 (levels 1 and 2)
PostCond ==
    /\ TLCGet("stats").generated = 3
    /\ TLCGet("stats").distinct = 2
    /\ TLCGet("stats").queue = 0
    /\ TLCGet("stats").diameter = 2
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        postcondition: Some("PostCond".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    let check_result = |mode: &str, result: CheckResult| match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 2, "{mode}: expected 2 states");
            assert_eq!(stats.transitions, 2, "{mode}: expected 2 transitions");
        }
        other => panic!(
            "{mode}: POSTCONDITION should see final TLCGet(\"stats\") counters, got: {:?}",
            other
        ),
    };

    check_result("sequential", check_module(&module, &config));
    check_result("parallel", check_module_parallel(&module, &config, 2));
}
