// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `check_state_constraints_array`: empty, satisfied, violated.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_state_constraints_empty_passes() {
    let module = parse_module(
        r#"
---- MODULE ConstEmpty ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constraints: vec![],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let state = State::from_pairs([("x", Value::int(5))]);
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);
    assert!(matches!(mc.check_state_constraints_array(&arr), Ok(true)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_state_constraints_satisfied() {
    let module = parse_module(
        r#"
---- MODULE ConstPass ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Bound == x < 10
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constraints: vec!["Bound".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let state = State::from_pairs([("x", Value::int(5))]);
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);
    assert!(matches!(mc.check_state_constraints_array(&arr), Ok(true)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_state_constraints_violated() {
    let module = parse_module(
        r#"
---- MODULE ConstFail ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Bound == x < 10
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constraints: vec!["Bound".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let state = State::from_pairs([("x", Value::int(15))]);
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);
    assert!(matches!(mc.check_state_constraints_array(&arr), Ok(false)));
}
