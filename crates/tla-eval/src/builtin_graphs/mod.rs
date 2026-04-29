// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod graph_operations;
mod graph_predicates_analysis;
mod graph_predicates_validation;
mod graph_traversal;
mod transitive_closure;

use std::collections::VecDeque;

use rustc_hash::FxHashMap;

use super::{eval_iter_set, EvalCtx, EvalResult, Expr, Span, Spanned, Value};
use crate::value::intern_string;

/// Extract (nodes_vec, edges_vec) from a graph record [node |-> S, edge |-> E].
/// Returns Ok(None) if the value is not a valid graph record shape.
pub(super) fn extract_graph(
    ctx: &EvalCtx,
    gv: &Value,
    span: Option<Span>,
) -> EvalResult<Option<(Vec<Value>, Vec<Value>)>> {
    let func = match gv.to_func_coerced() {
        Some(f) => f,
        None => return Ok(None),
    };
    let node_key = Value::String(intern_string("node"));
    let edge_key = Value::String(intern_string("edge"));
    let nodes = match func.apply(&node_key) {
        Some(n) => n.clone(),
        None => return Ok(None),
    };
    let edges = match func.apply(&edge_key) {
        Some(e) => e.clone(),
        None => return Ok(None),
    };
    if func.domain_len() != 2 {
        return Ok(None);
    }
    let nodes_vec: Vec<Value> = eval_iter_set(ctx, &nodes, span)?.collect();
    let edges_vec: Vec<Value> = eval_iter_set(ctx, &edges, span)?.collect();
    Ok(Some((nodes_vec, edges_vec)))
}

/// Build a directed adjacency list from tuple-based edges <<a, b>>.
/// Returns the adjacency list and a node-to-index map.
#[allow(clippy::mutable_key_type)]
pub(super) fn build_directed_adj(
    nodes: &[Value],
    edges: &[Value],
) -> (Vec<Vec<usize>>, FxHashMap<Value, usize>) {
    let mut node_to_idx: FxHashMap<Value, usize> =
        FxHashMap::with_capacity_and_hasher(nodes.len(), Default::default());
    for (i, n) in nodes.iter().enumerate() {
        node_to_idx.insert(n.clone(), i);
    }
    let mut adj: Vec<Vec<usize>> = vec![vec![]; nodes.len()];
    for edge in edges {
        if let Value::Tuple(pair) = edge {
            if pair.len() == 2 {
                if let (Some(&i), Some(&j)) = (node_to_idx.get(&pair[0]), node_to_idx.get(&pair[1]))
                {
                    adj[i].push(j);
                }
            }
        }
    }
    (adj, node_to_idx)
}

/// Build an undirected adjacency list from set-based edges {a, b} or tuple-based <<a, b>>.
#[allow(clippy::mutable_key_type)]
pub(super) fn build_undirected_adj(
    nodes: &[Value],
    edges: &[Value],
) -> (Vec<Vec<usize>>, FxHashMap<Value, usize>) {
    let mut node_to_idx: FxHashMap<Value, usize> =
        FxHashMap::with_capacity_and_hasher(nodes.len(), Default::default());
    for (i, n) in nodes.iter().enumerate() {
        node_to_idx.insert(n.clone(), i);
    }
    let mut adj: Vec<Vec<usize>> = vec![vec![]; nodes.len()];
    for edge in edges {
        if let Some(edge_inner) = edge.to_sorted_set() {
            let elems: Vec<_> = edge_inner.iter().collect();
            if elems.len() == 2 {
                if let (Some(&i), Some(&j)) = (node_to_idx.get(elems[0]), node_to_idx.get(elems[1]))
                {
                    adj[i].push(j);
                    adj[j].push(i);
                }
            }
        } else if let Value::Tuple(pair) = edge {
            if pair.len() == 2 {
                if let (Some(&i), Some(&j)) = (node_to_idx.get(&pair[0]), node_to_idx.get(&pair[1]))
                {
                    adj[i].push(j);
                    adj[j].push(i);
                }
            }
        }
    }
    (adj, node_to_idx)
}

/// BFS from a start node, returning a visited bitmap.
pub(super) fn bfs_reachable(adj: &[Vec<usize>], start: usize) -> Vec<bool> {
    let mut visited = vec![false; adj.len()];
    let mut queue = VecDeque::new();
    queue.push_back(start);
    visited[start] = true;
    while let Some(curr) = queue.pop_front() {
        for &neighbor in &adj[curr] {
            if !visited[neighbor] {
                visited[neighbor] = true;
                queue.push_back(neighbor);
            }
        }
    }
    visited
}

/// Enumerate all subsets of a slice.
pub(super) fn subsets<T: Clone>(items: &[T]) -> Vec<Vec<T>> {
    let n = items.len();
    let mut result = Vec::with_capacity(1 << n);
    for mask in 0..(1u64 << n) {
        let mut subset = Vec::new();
        for (i, item) in items.iter().enumerate() {
            if mask & (1u64 << i) != 0 {
                subset.push(item.clone());
            }
        }
        result.push(subset);
    }
    result
}

/// Create a graph record value: [node |-> node_set, edge |-> edge_set]
pub(super) fn make_graph_record(nodes: Vec<Value>, edges: Vec<Value>) -> Value {
    Value::Record(
        vec![
            ("edge".to_string(), Value::set(edges)),
            ("node".to_string(), Value::set(nodes)),
        ]
        .into(),
    )
}

pub(super) fn eval_builtin_graphs(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    if let Some(v) = transitive_closure::eval(ctx, name, args, span)? {
        return Ok(Some(v));
    }
    if let Some(v) = graph_predicates_validation::eval(ctx, name, args, span)? {
        return Ok(Some(v));
    }
    if let Some(v) = graph_predicates_analysis::eval(ctx, name, args, span)? {
        return Ok(Some(v));
    }
    if let Some(v) = graph_operations::eval(ctx, name, args, span)? {
        return Ok(Some(v));
    }
    graph_traversal::eval(ctx, name, args, span)
}
