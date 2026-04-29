// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TransitiveClosure module tests — TransitiveClosure, Warshall,
//! ConnectedNodes, ReflexiveTransitiveClosure.
//!
//! Extracted from property_tests.rs lines 3292-3412.
//! Part of #1371.

use tla_check::Value;
use tla_value::SortedSet;

use super::helpers::eval_str;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_transitive_closure_simple_chain() {
    // A chain 1->2->3 should produce closure with 1->2, 2->3, 1->3
    let result = eval_str(r#"TransitiveClosure({<<1, 2>>, <<2, 3>>})"#).unwrap();
    let expected = eval_str(r#"{<<1, 2>>, <<2, 3>>, <<1, 3>>}"#).unwrap();
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_transitive_closure_simple_two_edges() {
    // Two edges 1->2, 1->3 (no transitivity possible)
    let result = eval_str(r#"TransitiveClosure({<<1, 2>>, <<1, 3>>})"#).unwrap();
    let expected = eval_str(r#"{<<1, 2>>, <<1, 3>>}"#).unwrap();
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_transitive_closure_cycle() {
    // A cycle 1->2->1 should produce full connectivity
    let result = eval_str(r#"TransitiveClosure({<<1, 2>>, <<2, 1>>})"#).unwrap();
    let expected = eval_str(r#"{<<1, 2>>, <<2, 1>>, <<1, 1>>, <<2, 2>>}"#).unwrap();
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_transitive_closure_empty() {
    // Empty relation should produce empty closure
    let result = eval_str(r#"TransitiveClosure({})"#).unwrap();
    assert_eq!(result, Value::Set(Arc::new(SortedSet::new())));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_transitive_closure_single_edge() {
    // Single edge should stay the same
    let result = eval_str(r#"TransitiveClosure({<<1, 2>>})"#).unwrap();
    let expected = eval_str(r#"{<<1, 2>>}"#).unwrap();
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_transitive_closure_longer_chain() {
    // Chain 1->2->3->4 should produce all reachable pairs
    let result = eval_str(r#"TransitiveClosure({<<1, 2>>, <<2, 3>>, <<3, 4>>})"#).unwrap();
    let expected =
        eval_str(r#"{<<1, 2>>, <<1, 3>>, <<1, 4>>, <<2, 3>>, <<2, 4>>, <<3, 4>>}"#).unwrap();
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_warshall_alias() {
    // Warshall should be an alias for TransitiveClosure
    let tc = eval_str(r#"TransitiveClosure({<<1, 2>>, <<2, 3>>})"#).unwrap();
    let warshall = eval_str(r#"Warshall({<<1, 2>>, <<2, 3>>})"#).unwrap();
    assert_eq!(tc, warshall);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_connected_nodes_simple() {
    // ConnectedNodes extracts all nodes from the relation
    let result = eval_str(r#"ConnectedNodes({<<1, 2>>, <<2, 3>>})"#).unwrap();
    let expected = eval_str(r#"{1, 2, 3}"#).unwrap();
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_connected_nodes_empty() {
    // Empty relation should have no connected nodes
    let result = eval_str(r#"ConnectedNodes({})"#).unwrap();
    assert_eq!(result, Value::Set(Arc::new(SortedSet::new())));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_connected_nodes_with_strings() {
    // ConnectedNodes should work with string values
    let result = eval_str(r#"ConnectedNodes({<<"a", "b">>, <<"b", "c">>})"#).unwrap();
    let expected = eval_str(r#"{"a", "b", "c"}"#).unwrap();
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reflexive_transitive_closure_simple() {
    // ReflexiveTransitiveClosure adds reflexive edges
    let result = eval_str(r#"ReflexiveTransitiveClosure({<<1, 2>>}, {1, 2})"#).unwrap();
    let expected = eval_str(r#"{<<1, 1>>, <<1, 2>>, <<2, 2>>}"#).unwrap();
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reflexive_transitive_closure_chain() {
    // Chain with reflexive closure
    let result =
        eval_str(r#"ReflexiveTransitiveClosure({<<1, 2>>, <<2, 3>>}, {1, 2, 3})"#).unwrap();
    let expected =
        eval_str(r#"{<<1, 1>>, <<1, 2>>, <<1, 3>>, <<2, 2>>, <<2, 3>>, <<3, 3>>}"#).unwrap();
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reflexive_transitive_closure_empty_relation() {
    // Empty relation with domain should only have reflexive edges
    let result = eval_str(r#"ReflexiveTransitiveClosure({}, {1, 2})"#).unwrap();
    let expected = eval_str(r#"{<<1, 1>>, <<2, 2>>}"#).unwrap();
    assert_eq!(result, expected);
}
