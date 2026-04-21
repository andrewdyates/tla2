// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for O(1)-memory init invariant scan coverage (#3305).

use super::*;

/// Part of #3305: verify the streaming invariant scan catches violations with
/// O(1) memory (no states stored in BulkStateStorage). This is the path that
/// prevents Einstein-like specs from OOM-killing during Init enumeration.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scan_init_invariants_streaming_catches_violation() {
    let module = parse_module(
        r#"
---- MODULE InitStreamingScan ----
VARIABLE x, y, z
Init ==
    /\ x \in 0..9
    /\ y \in 0..9
    /\ z \in 0..9
Inv == x = 1
Next == FALSE
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);

    match mc.scan_init_invariants_streaming("Init") {
        Err(CheckResult::InvariantViolation {
            invariant, trace, ..
        }) => {
            assert_eq!(invariant, "Inv");
            assert_eq!(
                trace.states.len(),
                1,
                "streaming scan violation should report one state"
            );
            let state = &trace.states[0];
            assert_eq!(state.get("x"), Some(&Value::int(0)));
            assert_eq!(state.get("y"), Some(&Value::int(0)));
            assert_eq!(state.get("z"), Some(&Value::int(0)));
        }
        Ok(()) => panic!("expected invariant violation from streaming init scan"),
        Err(other) => {
            panic!("expected invariant violation from streaming init scan, got {other:?}")
        }
    }
}

/// Part of #3305: verify the streaming scan passes through cleanly when all
/// init states satisfy invariants.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scan_init_invariants_streaming_passes_when_all_satisfy() {
    let module = parse_module(
        r#"
---- MODULE InitStreamingScanPass ----
VARIABLE x
Init == x \in {0, 1}
Inv == x \in {0, 1}
Next == FALSE
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);

    mc.scan_init_invariants_streaming("Init")
        .expect("streaming scan should pass when all init states satisfy invariants");
}

/// Part of #3305: verify the streaming scan is a no-op when no invariants
/// are configured (guard condition).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scan_init_invariants_streaming_noop_without_invariants() {
    let module = parse_module(
        r#"
---- MODULE InitStreamingScanNoInv ----
VARIABLE x
Init == x \in {0, 1}
Next == FALSE
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);

    mc.scan_init_invariants_streaming("Init")
        .expect("streaming scan should be no-op without invariants");
}
