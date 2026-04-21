// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for `is_terminal_state_array`: no config, operator match, predicate match,
//! non-boolean errors, eval errors, unparseable predicate values.

use super::*;
use crate::{ConfigCheckError, EvalCheckError};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_terminal_state_no_terminal_config() {
    let module = parse_module(
        r#"
---- MODULE TermNone ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        terminal: None,
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let state = State::from_pairs([("x", Value::int(0))]);
    // Part of #2484 Phase 3: use ArrayState path
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);
    assert!(matches!(mc.is_terminal_state_array(&arr), Ok(false)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_terminal_state_operator_match() {
    let module = parse_module(
        r#"
---- MODULE TermOp ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
IsDone == x = 42
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        terminal: Some(TerminalSpec::Operator("IsDone".to_string())),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    // Part of #2484 Phase 3: use ArrayState path
    let registry = mc.ctx.var_registry().clone();

    let not_done = State::from_pairs([("x", Value::int(0))]);
    let arr = ArrayState::from_state(&not_done, &registry);
    assert!(matches!(mc.is_terminal_state_array(&arr), Ok(false)));

    let done = State::from_pairs([("x", Value::int(42))]);
    let arr = ArrayState::from_state(&done, &registry);
    assert!(matches!(mc.is_terminal_state_array(&arr), Ok(true)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_terminal_state_predicate_match() {
    let module = parse_module(
        r#"
---- MODULE TermPred ----
VARIABLE status
Init == status = "running"
Next == status' = "done"
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        terminal: Some(TerminalSpec::Predicates(vec![(
            "status".to_string(),
            "\"done\"".to_string(),
        )])),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    // Part of #2484 Phase 3: use ArrayState path
    let registry = mc.ctx.var_registry().clone();

    let running = State::from_pairs([("status", Value::string("running"))]);
    let arr = ArrayState::from_state(&running, &registry);
    assert!(matches!(mc.is_terminal_state_array(&arr), Ok(false)));

    let done = State::from_pairs([("status", Value::string("done"))]);
    let arr = ArrayState::from_state(&done, &registry);
    assert!(matches!(mc.is_terminal_state_array(&arr), Ok(true)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_terminal_state_operator_non_boolean_errors() {
    let module = parse_module(
        r#"
---- MODULE TermOpNonBool ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
IsDone == 42
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        terminal: Some(TerminalSpec::Operator("IsDone".to_string())),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let state = State::from_pairs([("x", Value::int(0))]);
    // Part of #2484 Phase 3: use ArrayState path
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);
    assert!(matches!(
        mc.is_terminal_state_array(&arr),
        Err(CheckError::Eval(EvalCheckError::ConstraintNotBoolean(ref name))) if name == "IsDone"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_terminal_state_operator_eval_error_errors() {
    let module = parse_module(
        r#"
---- MODULE TermOpEvalError ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x + 1
IsDone == (1 \div 0) = 0
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        terminal: Some(TerminalSpec::Operator("IsDone".to_string())),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let state = State::from_pairs([("x", Value::int(0))]);
    // Part of #2484 Phase 3: use ArrayState path
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);
    assert!(matches!(
        mc.is_terminal_state_array(&arr),
        Err(CheckError::Eval(EvalCheckError::Eval(_)))
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_terminal_state_predicate_unparseable_value_errors() {
    let module = parse_module(
        r#"
---- MODULE TermPredBadVal ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        terminal: Some(TerminalSpec::Predicates(vec![(
            "x".to_string(),
            "@#$bad".to_string(),
        )])),
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    let state = State::from_pairs([("x", Value::int(0))]);
    // Part of #2484 Phase 3: use ArrayState path
    let registry = mc.ctx.var_registry().clone();
    let arr = ArrayState::from_state(&state, &registry);
    let result = mc.is_terminal_state_array(&arr);
    assert!(
        matches!(&result, Err(CheckError::Config(ConfigCheckError::Config(msg))) if msg.contains("TERMINAL predicate")),
        "expected ConfigError for unparseable TERMINAL value, got: {:?}",
        result
    );
}
