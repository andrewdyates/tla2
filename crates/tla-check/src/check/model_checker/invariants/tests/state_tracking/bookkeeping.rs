// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for basic state bookkeeping: counts, mark-seen, trace degradation.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_states_count_initially_zero() {
    let module = parse_module(
        r#"
---- MODULE Count0 ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mc = ModelChecker::new(&module, &config);
    assert_eq!(mc.states_count(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mark_trace_degraded_sets_flag_once() {
    let module = parse_module(
        r#"
---- MODULE TraceDegradedFlag ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    assert!(!mc.trace.trace_degraded);

    let first = std::io::Error::other("synthetic trace write error");
    mc.mark_trace_degraded(&first);
    assert!(mc.trace.trace_degraded);

    // Second error should be a no-op for the flag (warning already emitted once).
    let second = std::io::Error::other("synthetic trace write error 2");
    mc.mark_trace_degraded(&second);
    assert!(mc.trace.trace_degraded);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_state_seen_false_for_unseen() {
    let module = parse_module(
        r#"
---- MODULE Unseen ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mc = ModelChecker::new(&module, &config);
    assert!(!mc.is_state_seen_checked(Fingerprint(12345)).unwrap());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mark_state_seen_fp_only_then_is_seen() {
    let module = parse_module(
        r#"
---- MODULE MarkFp ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let fp = Fingerprint(99999);
    assert!(!mc.is_state_seen_checked(fp).unwrap());

    mc.mark_state_seen_fp_only_checked(fp, None, 0).unwrap();

    assert!(mc.is_state_seen_checked(fp).unwrap());
    assert_eq!(mc.states_count(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mark_multiple_states_counted() {
    let module = parse_module(
        r#"
---- MODULE MarkMulti ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    mc.mark_state_seen_fp_only_checked(Fingerprint(1), None, 0)
        .unwrap();
    mc.mark_state_seen_fp_only_checked(Fingerprint(2), Some(Fingerprint(1)), 1)
        .unwrap();
    mc.mark_state_seen_fp_only_checked(Fingerprint(3), Some(Fingerprint(2)), 2)
        .unwrap();
    assert_eq!(mc.states_count(), 3);
}
