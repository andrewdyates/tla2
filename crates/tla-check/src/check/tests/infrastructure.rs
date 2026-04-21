// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Part of #2696: TLC-matching trace text format.
///
/// TLC reference format:
/// ```text
/// 1: <Initial predicate>
/// x = 0
/// 2: <Action>
/// x = 1
/// ```
///
/// Single-variable states omit the `/\ ` prefix (TLC convention).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_display_single_var_tlc_format() {
    let s1 = State::from_pairs([("x", Value::int(0))]);
    let s2 = State::from_pairs([("x", Value::int(1))]);
    let trace = Trace::from_states(vec![s1, s2]);

    let display = format!("{}", trace);
    // TLC format: "N: <label>" header lines
    assert!(display.contains("1: <Initial predicate>"));
    assert!(display.contains("2: <Action>"));
    // Single-variable states: no "/\ " prefix
    assert!(display.contains("x = 0"));
    assert!(display.contains("x = 1"));
    // Fingerprint must NOT appear in output (TLC hides by default)
    assert!(
        !display.contains('('),
        "fingerprint should be hidden: {display}"
    );
}

/// Part of #2696: Multi-variable trace uses `/\ ` prefix per TLC convention.
///
/// TLC reference (DieHard):
/// ```text
/// 1: <Initial predicate>
/// /\ big = 0
/// /\ small = 0
/// 2: <Action>
/// /\ big = 5
/// /\ small = 0
/// ```
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_display_multi_var_tlc_format() {
    let s1 = State::from_pairs([("big", Value::int(0)), ("small", Value::int(0))]);
    let s2 = State::from_pairs([("big", Value::int(5)), ("small", Value::int(0))]);
    let trace = Trace::from_states(vec![s1, s2]);

    let display = format!("{}", trace);
    // Multi-variable states: "/\ " prefix on each variable line
    assert!(
        display.contains("/\\ big = 0"),
        "expected '/\\ big = 0' in: {display}"
    );
    assert!(
        display.contains("/\\ small = 0"),
        "expected '/\\ small = 0' in: {display}"
    );
    assert!(
        display.contains("/\\ big = 5"),
        "expected '/\\ big = 5' in: {display}"
    );
    // Verify header format (TLC 2.20: "State N:" prefix)
    assert!(
        display.contains("State 1: <Initial predicate>"),
        "expected 'State 1:' header in: {display}"
    );
    assert!(
        display.contains("State 2: <Action>"),
        "expected 'State 2:' header in: {display}"
    );
    // TLC emits a blank line after each state (Part of #2470 Step 6).
    assert!(
        display.contains("\n\n"),
        "expected blank lines between states (TLC parity): {display}"
    );
}

/// Part of #2696 Step 2: ActionLabel with source location produces TLC-matching format.
///
/// TLC reference:
/// ```text
/// 1: <Initial predicate>
/// /\ x = 0
/// /\ y = 1
/// 2: <Next line 10, col 3 to line 12, col 15 of module Spec>
/// /\ x = 1
/// /\ y = 0
/// ```
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_display_with_action_labels() {
    use crate::ActionLabel;

    let s1 = State::from_pairs([("x", Value::int(0)), ("y", Value::int(1))]);
    let s2 = State::from_pairs([("x", Value::int(1)), ("y", Value::int(0))]);
    let labels = vec![
        ActionLabel {
            name: "Initial predicate".to_string(),
            source_location: None,
        },
        ActionLabel {
            name: "Next".to_string(),
            source_location: Some("line 10, col 3 to line 12, col 15 of module Spec".to_string()),
        },
    ];
    let trace = Trace::from_states_with_labels(vec![s1, s2], labels);

    let display = format!("{}", trace);
    assert!(
        display.contains("1: <Initial predicate>"),
        "expected initial predicate header: {display}"
    );
    assert!(
        display.contains("2: <Next line 10, col 3 to line 12, col 15 of module Spec>"),
        "expected action label with source location: {display}"
    );
    assert!(
        display.contains("/\\ x = 0"),
        "expected variable: {display}"
    );
}

/// Part of #2696 Step 2: Traces without action labels fall back to placeholders.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_display_without_action_labels_uses_placeholders() {
    let s1 = State::from_pairs([("x", Value::int(0))]);
    let s2 = State::from_pairs([("x", Value::int(1))]);
    let trace = Trace::from_states(vec![s1, s2]);

    let display = format!("{}", trace);
    assert!(
        display.contains("1: <Initial predicate>"),
        "expected placeholder initial: {display}"
    );
    assert!(
        display.contains("2: <Action>"),
        "expected placeholder action: {display}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_stats_default() {
    let stats = CheckStats::default();
    assert_eq!(stats.states_found, 0);
    assert_eq!(stats.initial_states, 0);
    assert_eq!(stats.transitions, 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_error_display() {
    let err = ConfigCheckError::MissingInit;
    assert_eq!(format!("{}", err), "Missing INIT definition");

    let err = ConfigCheckError::MissingInvariant("Safety".to_string());
    assert!(format!("{}", err).contains("Safety"));
}

/// Part of #599: Verify fmt_tlc_fp produces correct format.
/// The decimal conversion must match Java's Long.toString() for TLC DOT compatibility.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fmt_tlc_fp_format() {
    // Test that hex formatting is correct (16 digits, zero-padded)
    let result = fmt_tlc_fp(0);
    assert!(result.starts_with("0000000000000000"));

    let result = fmt_tlc_fp(0xfedcba9876543210);
    assert!(result.starts_with("fedcba9876543210"));

    // Verify the signed decimal conversion formula matches Java Long.toString():
    // For values > i64::MAX, the signed interpretation should be negative.
    assert_eq!(0xfedcba9876543210u64 as i64, -81985529216486896i64);
    assert_eq!(u64::MAX as i64, -1i64);
    assert_eq!(0x8000000000000000u64 as i64, i64::MIN);

    // The actual fmt_tlc_fp output depends on TLA2_TLCFP_DECIMAL env var,
    // which is cached at first access. This test verifies the format logic.
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_missing_init() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE Test ----
VARIABLE x
Next == x' = x + 1
TypeOK == x \in Nat
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config without INIT
    let config = Config {
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    assert!(matches!(
        result,
        CheckResult::Error {
            error: CheckError::Config(ConfigCheckError::MissingInit),
            ..
        }
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_missing_next() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
TypeOK == x \in Nat
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config without NEXT
    let config = Config {
        init: Some("Init".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    assert!(matches!(
        result,
        CheckResult::Error {
            error: CheckError::Config(ConfigCheckError::MissingNext),
            ..
        }
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_assume_only_no_init_next() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE Test ----
ASSUME TRUE
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config without INIT/NEXT/SPECIFICATION, no variables, no properties/invariants.
    let config = Config::default();

    let result = check_module(&module, &config);
    assert!(matches!(result, CheckResult::Success(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_missing_invariant() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config with non-existent invariant
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["NonExistent".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    assert!(matches!(
        result,
        CheckResult::Error { error: CheckError::Config(ConfigCheckError::MissingInvariant(ref name)), .. } if name == "NonExistent"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_init_cannot_enumerate() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Init constrains x to an infinite set (Nat), which we cannot enumerate
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x \in Nat
Next == x' = x + 1
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    // This should fail because Nat is an infinite set that cannot be enumerated
    assert!(matches!(
        result,
        CheckResult::Error {
            error: CheckError::Config(ConfigCheckError::InitCannotEnumerate(_)),
            ..
        }
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_init_missing_variable_constraint() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Init only constrains one of two variables
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == x = 0
Next == x' = x + 1 /\ y' = y
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    // This should fail because y has no constraint
    assert!(matches!(
        result,
        CheckResult::Error {
            error: CheckError::Config(ConfigCheckError::InitCannotEnumerate(ref msg)),
            ..
        } if msg.contains('y')
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_model_checker_construction() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE Counter ----
VARIABLE count
Init == count = 0
Next == count' = count + 1
TypeOK == count \in Nat
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    let checker = ModelChecker::new(&module, &config);

    // Verify variable extraction
    let vars = checker.test_vars();
    assert_eq!(vars.len(), 1);
    assert_eq!(vars[0].as_ref(), "count");
}

/// Part of #2724: Verify that the model check lifecycle clears interned markers.
///
/// Previous version asserted `get_interner().len() == 0` which is racy under
/// concurrent test execution: `ACTIVE_MODEL_CHECK_RUNS` prevents clearing when
/// other `check_module` calls are active. Fix: insert unique marker values,
/// wait for all concurrent runs to finish, then verify markers were cleared.
/// This is race-free because once clearing occurs, a unique marker cannot
/// reappear (no other test inserts these specific values).
/// Part of #4067: Wait for global quiescence before testing interner
/// cleanup. The interner lock prevents parallel checker tests from
/// interfering, and wait_for_no_active_runs ensures no sequential
/// model check runs are in-flight. Timeout increased to 180s because
/// long-running sequential tests (e.g., real_disruptor ~100s) can
/// hold ACTIVE_MODEL_CHECK_RUNS elevated.
#[cfg_attr(test, ntest::timeout(180_000))]
#[test]
fn test_check_module_clears_value_interner_between_runs() {
    use crate::intern::{clear_global_value_interner, get_interner, wait_for_no_active_runs};
    use crate::state::value_fingerprint;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Part of #4067: Wait for ALL concurrent model check runs to finish
    // BEFORE acquiring the lock. This avoids holding PARALLEL_CHECK_LOCK
    // while waiting (which would block parallel tests and cause timeouts).
    wait_for_no_active_runs();

    let _serial = crate::test_utils::acquire_interner_lock();

    let src = r#"
---- MODULE InternerCleanupSequential ----
VARIABLE x
Init == x = 0
Next == x' = x
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    // Use unique marker values that no other test will insert.
    let marker1 = Value::int(777_777_001);
    let marker1_fp = value_fingerprint(&marker1);
    let marker2 = Value::int(777_777_002);
    let marker2_fp = value_fingerprint(&marker2);

    clear_global_value_interner();
    get_interner().intern(marker1);
    assert!(
        get_interner().contains_fp(marker1_fp),
        "precondition: marker1 should be in interner"
    );

    let first = check_module(&module, &config);
    assert!(matches!(first, CheckResult::Success(_)), "{first:?}");
    // Our check_module run should finish instantly (trivial spec). Since we
    // waited for quiescence above and hold the lock, no other runs started.
    wait_for_no_active_runs();
    assert!(
        !get_interner().contains_fp(marker1_fp),
        "marker1 should be cleared after all model check runs complete"
    );

    get_interner().intern(marker2);
    assert!(
        get_interner().contains_fp(marker2_fp),
        "precondition: marker2 should be in interner"
    );

    let second = check_module(&module, &config);
    assert!(matches!(second, CheckResult::Success(_)), "{second:?}");
    wait_for_no_active_runs();
    assert!(
        !get_interner().contains_fp(marker2_fp),
        "marker2 should be cleared after second run completes"
    );
}
