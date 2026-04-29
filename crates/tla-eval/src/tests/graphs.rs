// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `builtin_graphs` module — TransitiveClosure and Graphs operators.

use super::eval_str;
use crate::error::EvalError;
use crate::Value;

// --- TransitiveClosure / Warshall ---

#[test]
fn test_transitive_closure_simple_chain() {
    // R = {<<1,2>>, <<2,3>>}
    // TC(R) = {<<1,2>>, <<1,3>>, <<2,3>>}
    let v = eval_str("TransitiveClosure({<<1, 2>>, <<2, 3>>}) = {<<1, 2>>, <<1, 3>>, <<2, 3>>}")
        .unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_transitive_closure_already_closed() {
    // R is already transitively closed
    let v = eval_str(
        "TransitiveClosure({<<1, 2>>, <<2, 3>>, <<1, 3>>}) = {<<1, 2>>, <<2, 3>>, <<1, 3>>}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_transitive_closure_self_loop() {
    // Self-loop: TC({<<1,1>>}) = {<<1,1>>} — no new edges generated
    let v = eval_str("TransitiveClosure({<<1, 1>>}) = {<<1, 1>>}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_transitive_closure_empty() {
    let v = eval_str("TransitiveClosure({}) = {}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_transitive_closure_cycle() {
    // R = {<<1,2>>, <<2,1>>} creates a cycle
    // TC should include <<1,1>>, <<1,2>>, <<2,1>>, <<2,2>>
    let v = eval_str(
        "TransitiveClosure({<<1, 2>>, <<2, 1>>}) = {<<1, 1>>, <<1, 2>>, <<2, 1>>, <<2, 2>>}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true));
}

// --- ReflexiveTransitiveClosure ---

#[test]
fn test_reflexive_transitive_closure() {
    // RTC adds reflexive pairs for all elements in the domain set
    // R = {<<1,2>>}, S = {1,2,3}
    // RTC = TC(R) union {<<1,1>>, <<2,2>>, <<3,3>>} = {<<1,1>>, <<1,2>>, <<2,2>>, <<3,3>>}
    let v = eval_str(
        "ReflexiveTransitiveClosure({<<1, 2>>}, {1, 2, 3}) = {<<1, 1>>, <<1, 2>>, <<2, 2>>, <<3, 3>>}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_reflexive_transitive_closure_includes_tc() {
    // R = {<<1,2>>}, S = {1,2}: RTC = {<<1,1>>, <<1,2>>, <<2,2>>}
    let v =
        eval_str("ReflexiveTransitiveClosure({<<1, 2>>}, {1, 2}) = {<<1, 1>>, <<1, 2>>, <<2, 2>>}")
            .unwrap();
    assert_eq!(v, Value::Bool(true));
}

// --- ConnectedNodes ---

#[test]
fn test_connected_nodes() {
    // ConnectedNodes returns all nodes in the relation
    let v = eval_str("ConnectedNodes({<<1, 2>>, <<3, 4>>}) = {1, 2, 3, 4}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_connected_nodes_empty() {
    let v = eval_str("ConnectedNodes({}) = {}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

// --- IsDirectedGraph ---

#[test]
fn test_is_directed_graph_valid() {
    let v =
        eval_str("IsDirectedGraph([node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}])").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_is_directed_graph_edge_outside_nodes() {
    // Edge references node 4 which is not in the node set
    let v = eval_str("IsDirectedGraph([node |-> {1, 2}, edge |-> {<<1, 4>>}])").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_is_directed_graph_empty() {
    let v = eval_str("IsDirectedGraph([node |-> {}, edge |-> {}])").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_is_directed_graph_non_record() {
    let v = eval_str("IsDirectedGraph(42)").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// --- IsUndirectedGraph ---

#[test]
fn test_is_undirected_graph_valid() {
    // Undirected graphs use set-based edges {a,b}
    let v = eval_str("IsUndirectedGraph([node |-> {1, 2, 3}, edge |-> {{1, 2}, {2, 3}}])").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_is_undirected_graph_invalid_edge_size() {
    // Edge with 3 elements is invalid
    let v = eval_str("IsUndirectedGraph([node |-> {1, 2, 3}, edge |-> {{1, 2, 3}}])").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// --- IsStronglyConnected ---

#[test]
fn test_is_strongly_connected_complete() {
    // Triangle graph is strongly connected
    let v =
        eval_str("IsStronglyConnected([node |-> {1, 2, 3}, edge |-> {{1, 2}, {2, 3}, {1, 3}}])")
            .unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_is_strongly_connected_disconnected() {
    // Two isolated components
    let v = eval_str("IsStronglyConnected([node |-> {1, 2, 3, 4}, edge |-> {{1, 2}}])").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_is_strongly_connected_empty() {
    // Empty graph is trivially connected
    let v = eval_str("IsStronglyConnected([node |-> {}, edge |-> {}])").unwrap();
    assert_eq!(v, Value::Bool(true));
}

// --- #3368 regression: IsStronglyConnected must respect directed edges ---

#[test]
fn test_is_strongly_connected_directed_one_way() {
    // Directed graph: edge <<1,2>> only. No path from 2 to 1.
    // TLC: IsStronglyConnected = FALSE
    let v = eval_str("IsStronglyConnected([node |-> {1, 2}, edge |-> {<<1, 2>>}])").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_is_strongly_connected_directed_cycle() {
    // Directed graph with full cycle: 1->2, 2->3, 3->1. Strongly connected.
    let v = eval_str(
        "IsStronglyConnected([node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}])",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_is_strongly_connected_directed_missing_return() {
    // Directed graph: 1->2, 2->3. Node 3 cannot reach 1. Not strongly connected.
    let v = eval_str("IsStronglyConnected([node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}])")
        .unwrap();
    assert_eq!(v, Value::Bool(false));
}

// --- #2130 regression: scalar node/edge must produce TypeError, not FALSE ---

#[test]
fn test_is_directed_graph_scalar_fields_errors() {
    // #2130: IsDirectedGraph([node |-> 1, edge |-> 2]) must produce a TypeError
    // (TLC parity). TLC evaluates IsDirectedGraph as pure TLA+ (Graphs.tla),
    // where non-enumerable sets raise EvalException, not silently return FALSE.
    let result = eval_str("IsDirectedGraph([node |-> 1, edge |-> 2])");
    assert!(
        matches!(
            result,
            Err(EvalError::TypeError {
                expected: "Set",
                ..
            })
        ),
        "#2130: IsDirectedGraph with scalar node/edge must error, got: {:?}",
        result
    );
}

#[test]
fn test_is_undirected_graph_scalar_node_errors() {
    // Self-audit: IsUndirectedGraph must also propagate TypeError for non-set nodes.
    let result = eval_str("IsUndirectedGraph([node |-> 1, edge |-> {}])");
    assert!(
        matches!(
            result,
            Err(EvalError::TypeError {
                expected: "Set",
                ..
            })
        ),
        "IsUndirectedGraph with scalar node must error, got: {:?}",
        result
    );
}

#[test]
fn test_is_strongly_connected_scalar_node_errors() {
    // Self-audit: IsStronglyConnected must also propagate TypeError for non-set nodes.
    let result = eval_str("IsStronglyConnected([node |-> 1, edge |-> {}])");
    assert!(
        matches!(
            result,
            Err(EvalError::TypeError {
                expected: "Set",
                ..
            })
        ),
        "IsStronglyConnected with scalar node must error, got: {:?}",
        result
    );
}

// === DirectedSubgraph ===

#[test]
fn test_directed_subgraph_empty() {
    let v = eval_str("DirectedSubgraph([node |-> {}, edge |-> {}])").unwrap();
    // Only subgraph of empty graph is the empty graph itself
    assert_eq!(v, eval_str("{[node |-> {}, edge |-> {}]}").unwrap(),);
}

#[test]
fn test_directed_subgraph_single_node() {
    let v = eval_str("DirectedSubgraph([node |-> {1}, edge |-> {}])").unwrap();
    // Subgraphs: empty graph, graph with just node 1
    let expected = eval_str("{[node |-> {}, edge |-> {}], [node |-> {1}, edge |-> {}]}").unwrap();
    assert_eq!(v, expected);
}

#[test]
fn test_directed_subgraph_with_edge() {
    let v = eval_str("DirectedSubgraph([node |-> {1, 2}, edge |-> {<<1, 2>>}])").unwrap();
    // Subgraphs: empty, {1} alone, {2} alone, {1,2} no edges, {1,2} with <<1,2>>
    if let Value::Set(s) = &v {
        assert_eq!(s.len(), 5);
    } else {
        panic!("Expected Set, got {:?}", v);
    }
}

// === SuccessorsOf ===

#[test]
fn test_successors_of_single_node() {
    let v = eval_str(
        "SuccessorsOf({1}, [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<1, 3>>, <<2, 3>>}])",
    )
    .unwrap();
    assert_eq!(v, eval_str("{2, 3}").unwrap());
}

#[test]
fn test_successors_of_no_successors() {
    let v =
        eval_str("SuccessorsOf({3}, [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}])").unwrap();
    assert_eq!(v, eval_str("{}").unwrap());
}

#[test]
fn test_successors_of_multiple_sources() {
    let v = eval_str("SuccessorsOf({1, 2}, [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}])")
        .unwrap();
    assert_eq!(v, eval_str("{2, 3}").unwrap());
}

// === PredecessorsOf ===

#[test]
fn test_predecessors_of_single_node() {
    let v = eval_str("PredecessorsOf({3}, [node |-> {1, 2, 3}, edge |-> {<<1, 3>>, <<2, 3>>}])")
        .unwrap();
    assert_eq!(v, eval_str("{1, 2}").unwrap());
}

#[test]
fn test_predecessors_of_no_predecessors() {
    let v = eval_str("PredecessorsOf({1}, [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}])")
        .unwrap();
    assert_eq!(v, eval_str("{}").unwrap());
}

// === Reachable ===

#[test]
fn test_reachable_from_source() {
    let v =
        eval_str("Reachable({1}, [node |-> {1, 2, 3, 4}, edge |-> {<<1, 2>>, <<2, 3>>}])").unwrap();
    // 1 -> 2 -> 3, but 4 is isolated. Start node 1 excluded (Descendants semantics).
    assert_eq!(v, eval_str("{2, 3}").unwrap());
}

#[test]
fn test_reachable_disconnected() {
    let v =
        eval_str("Reachable({4}, [node |-> {1, 2, 3, 4}, edge |-> {<<1, 2>>, <<2, 3>>}])").unwrap();
    assert_eq!(v, eval_str("{}").unwrap());
}

#[test]
fn test_reachable_cycle() {
    let v =
        eval_str("Reachable({1}, [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>, <<3, 1>>}])")
            .unwrap();
    // Full cycle: 1->2->3->1. Node 1 is reachable from itself via the cycle
    // (matches TLC Descendants semantics: TransitiveClosure[1,1]=TRUE when cycle exists)
    assert_eq!(v, eval_str("{1, 2, 3}").unwrap());
}

// === AreConnectedIn ===

#[test]
fn test_are_connected_in_directed() {
    let v = eval_str("AreConnectedIn(1, 3, [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}])")
        .unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_are_connected_in_directed_not_connected() {
    let v = eval_str("AreConnectedIn(3, 1, [node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}])")
        .unwrap();
    // No path from 3 to 1 in directed graph
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_are_connected_in_undirected() {
    let v =
        eval_str("AreConnectedIn(1, 3, [node |-> {1, 2, 3}, edge |-> {{1, 2}, {2, 3}}])").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_are_connected_in_undirected_disconnected() {
    let v = eval_str("AreConnectedIn(1, 4, [node |-> {1, 2, 3, 4}, edge |-> {{1, 2}}])").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_are_connected_in_same_node() {
    let v = eval_str("AreConnectedIn(1, 1, [node |-> {1, 2}, edge |-> {<<1, 2>>}])").unwrap();
    // A node is trivially connected to itself (BFS starts visited)
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_are_connected_in_node_not_in_graph() {
    let v = eval_str("AreConnectedIn(1, 5, [node |-> {1, 2, 3}, edge |-> {<<1, 2>>}])").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// === Path (infinite set error) ===

#[test]
fn test_path_infinite_error() {
    let result = eval_str("Path([node |-> {1, 2}, edge |-> {<<1, 2>>}])");
    assert!(result.is_err(), "Path(G) should error (infinite set)");
}

// === IsLoopFreeUndirectedGraph ===

#[test]
fn test_is_loop_free_undirected_graph_valid() {
    let v = eval_str("IsLoopFreeUndirectedGraph([node |-> {1, 2, 3}, edge |-> {{1, 2}, {2, 3}}])")
        .unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_is_loop_free_undirected_graph_with_self_loop() {
    // {1, 1} = {1} which is a 1-element set, not a valid 2-element edge
    let v = eval_str("IsLoopFreeUndirectedGraph([node |-> {1, 2}, edge |-> {{1}}])").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_is_loop_free_undirected_graph_empty() {
    let v = eval_str("IsLoopFreeUndirectedGraph([node |-> {}, edge |-> {}])").unwrap();
    assert_eq!(v, Value::Bool(true));
}

// === UndirectedSubgraph ===

#[test]
fn test_undirected_subgraph_empty() {
    let v = eval_str("UndirectedSubgraph([node |-> {}, edge |-> {}])").unwrap();
    if let Value::Set(s) = &v {
        assert_eq!(s.len(), 1); // Just the empty graph
    } else {
        panic!("Expected Set");
    }
}

#[test]
fn test_undirected_subgraph_triangle() {
    let v = eval_str("UndirectedSubgraph([node |-> {1, 2}, edge |-> {{1, 2}}])").unwrap();
    // Subsets: {}, {1}, {2}, {1,2} with no edges, {1,2} with {1,2} edge
    if let Value::Set(s) = &v {
        assert_eq!(s.len(), 5);
    } else {
        panic!("Expected Set");
    }
}

// === SimplePath ===

#[test]
fn test_simple_path_directed_chain() {
    let v = eval_str("SimplePath([node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}])").unwrap();
    // Simple paths: <<1>>, <<2>>, <<3>>, <<1,2>>, <<2,3>>, <<1,2,3>>
    if let Value::Set(s) = &v {
        assert_eq!(s.len(), 6);
    } else {
        panic!("Expected Set, got {:?}", v);
    }
}

#[test]
fn test_simple_path_undirected() {
    let v = eval_str("SimplePath([node |-> {1, 2, 3}, edge |-> {{1, 2}, {2, 3}}])").unwrap();
    // Undirected: paths can go both ways
    // Single nodes: <<1>>, <<2>>, <<3>>
    // Length 2: <<1,2>>, <<2,1>>, <<2,3>>, <<3,2>>
    // Length 3: <<1,2,3>>, <<3,2,1>>
    if let Value::Set(s) = &v {
        assert_eq!(s.len(), 9);
    } else {
        panic!("Expected Set, got {:?}", v);
    }
}

#[test]
fn test_simple_path_empty_graph() {
    let v = eval_str("SimplePath([node |-> {}, edge |-> {}])").unwrap();
    assert_eq!(v, eval_str("{}").unwrap());
}

// === ConnectedComponents ===

#[test]
fn test_connected_components_undirected() {
    let v = eval_str("ConnectedComponents([node |-> {1, 2, 3, 4}, edge |-> {{1, 2}, {3, 4}}])")
        .unwrap();
    // Two components: {1, 2} and {3, 4}
    let expected = eval_str("{{1, 2}, {3, 4}}").unwrap();
    assert_eq!(v, expected);
}

#[test]
fn test_connected_components_single_component() {
    let v =
        eval_str("ConnectedComponents([node |-> {1, 2, 3}, edge |-> {{1, 2}, {2, 3}}])").unwrap();
    let expected = eval_str("{{1, 2, 3}}").unwrap();
    assert_eq!(v, expected);
}

#[test]
fn test_connected_components_all_isolated() {
    let v = eval_str("ConnectedComponents([node |-> {1, 2, 3}, edge |-> {}])").unwrap();
    let expected = eval_str("{{1}, {2}, {3}}").unwrap();
    assert_eq!(v, expected);
}

#[test]
fn test_connected_components_empty() {
    let v = eval_str("ConnectedComponents([node |-> {}, edge |-> {}])").unwrap();
    assert_eq!(v, eval_str("{}").unwrap());
}

#[test]
fn test_connected_components_directed_edges() {
    // ConnectedComponents treats directed edges as undirected for component finding
    let v = eval_str("ConnectedComponents([node |-> {1, 2, 3}, edge |-> {<<1, 2>>, <<2, 3>>}])")
        .unwrap();
    let expected = eval_str("{{1, 2, 3}}").unwrap();
    assert_eq!(v, expected);
}
