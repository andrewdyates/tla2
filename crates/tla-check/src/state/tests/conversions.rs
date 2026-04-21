// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_values_complete_state() {
    let registry = VarRegistry::from_names(["x", "y"]);
    let state = State::from_pairs([("x", Value::int(1)), ("y", Value::int(2))]);
    let values = state.to_values(&registry);

    assert_eq!(values.len(), 2);
    let x_idx = registry.get("x").unwrap().as_usize();
    let y_idx = registry.get("y").unwrap().as_usize();
    assert_eq!(values[x_idx], Value::int(1));
    assert_eq!(values[y_idx], Value::int(2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[should_panic(expected = "State::to_values: variable")]
fn test_to_values_missing_variable_panics() {
    let registry = VarRegistry::from_names(["x", "y", "z"]);
    let state = State::from_pairs([("x", Value::int(1)), ("y", Value::int(2))]);
    let _values = state.to_values(&registry);
}
