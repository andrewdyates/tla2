// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for DOT graph output: basic trace, special characters, sets,
//! liveness cycle, empty trace, liveness prefix+cycle.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_to_dot_basic() {
    use crate::{State, Trace};

    // Create a simple 2-state trace using from_pairs
    let state1 = State::from_pairs([("x", Value::SmallInt(0)), ("y", Value::SmallInt(0))]);

    let state2 = State::from_pairs([("x", Value::SmallInt(1)), ("y", Value::SmallInt(0))]);

    let trace = Trace::from_states(vec![state1, state2]);
    let dot = trace_to_dot(&trace, None);

    // Verify basic DOT structure
    assert!(dot.starts_with("digraph trace {"), "DOT: {}", dot);
    assert!(dot.contains("rankdir=TB;"), "DOT: {}", dot);
    assert!(dot.contains("State 1"), "DOT: {}", dot);
    assert!(dot.contains("State 2"), "DOT: {}", dot);
    assert!(dot.contains("x = 0"), "DOT: {}", dot);
    assert!(dot.contains("x = 1"), "DOT: {}", dot);
    assert!(dot.contains("s0 -> s1"), "DOT: {}", dot);
    assert!(dot.ends_with("}\n"), "DOT: {}", dot);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_to_dot_with_special_chars() {
    use crate::{State, Trace};
    use std::sync::Arc;

    // Create state with values containing special DOT characters
    let state = State::from_pairs([("name", Value::String(Arc::from("test|value")))]);

    let trace = Trace::from_states(vec![state]);
    let dot = trace_to_dot(&trace, None);

    // Verify special characters are escaped
    assert!(
        dot.contains("test\\|value"),
        "Pipe should be escaped. DOT: {}",
        dot
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_to_dot_with_sets() {
    use crate::value::SortedSet;
    use crate::{State, Trace};
    use std::sync::Arc;

    // Create state with set value
    let state = State::from_pairs([(
        "s",
        Value::Set(Arc::new(SortedSet::from_iter([
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ]))),
    )]);

    let trace = Trace::from_states(vec![state]);
    let dot = trace_to_dot(&trace, None);

    // Set should be rendered with escaped braces
    assert!(
        dot.contains("s = \\{"),
        "Set braces should be escaped. DOT: {}",
        dot
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_to_dot_liveness_cycle() {
    use crate::{State, Trace};

    // Create a 4-state trace where states 2-3 form a cycle
    let states: Vec<State> = (0..4)
        .map(|i| State::from_pairs([("x", Value::SmallInt(i))]))
        .collect();

    let trace = Trace::from_states(states);
    let dot = trace_to_dot(&trace, Some(2)); // Cycle starts at index 2

    // Verify cycle styling
    assert!(
        dot.contains("color=blue"),
        "Cycle states should be blue. DOT: {}",
        dot
    );
    assert!(
        dot.contains("cycle"),
        "Should have cycle back-edge label. DOT: {}",
        dot
    );
    assert!(
        dot.contains("constraint=false"),
        "Cycle edge should have constraint=false. DOT: {}",
        dot
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_to_dot_empty_trace() {
    use crate::Trace;

    let trace = Trace::new();
    let dot = trace_to_dot(&trace, None);

    // Should still produce valid DOT, just with no nodes
    assert!(dot.starts_with("digraph trace {"), "DOT: {}", dot);
    assert!(dot.ends_with("}\n"), "DOT: {}", dot);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_liveness_trace_to_dot() {
    use crate::{State, Trace};

    // Create prefix (2 states)
    let prefix_states: Vec<State> = (0..2)
        .map(|i| State::from_pairs([("x", Value::SmallInt(i))]))
        .collect();
    let prefix = Trace::from_states(prefix_states);

    // Create cycle (2 states)
    let cycle_states: Vec<State> = (2..4)
        .map(|i| State::from_pairs([("x", Value::SmallInt(i))]))
        .collect();
    let cycle = Trace::from_states(cycle_states);

    let dot = liveness_trace_to_dot(&prefix, &cycle);

    // Should have 4 states total
    assert!(dot.contains("State 1"), "DOT: {}", dot);
    assert!(dot.contains("State 4"), "DOT: {}", dot);

    // Should have cycle back-edge
    assert!(
        dot.contains("cycle"),
        "Should have cycle label. DOT: {}",
        dot
    );
}
