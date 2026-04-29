// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use rustc_hash::FxHashSet;

use super::super::{
    check_arity, eval as eval_expr, eval_iter_set, EvalCtx, EvalResult, Expr, Span, Spanned, Value,
};
use crate::value::intern_string;

pub(super) fn eval(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // IsDirectedGraph(G) - check if G is a valid directed graph record
        // G must be a record with 'node' and 'edge' fields where edge ⊆ node × node
        "IsDirectedGraph" => {
            check_arity(name, args, 1, span)?;
            let gv = eval_expr(ctx, &args[0])?;

            // Check if it's a record with 'node' and 'edge' fields
            let func = match gv.to_func_coerced() {
                Some(f) => f,
                None => return Ok(Some(Value::Bool(false))),
            };

            // Get node and edge fields
            let node_key = Value::String(intern_string("node"));
            let edge_key = Value::String(intern_string("edge"));

            let nodes = match func.apply(&node_key) {
                Some(n) => n.clone(),
                None => return Ok(Some(Value::Bool(false))),
            };

            let edges = match func.apply(&edge_key) {
                Some(e) => e.clone(),
                None => return Ok(Some(Value::Bool(false))),
            };

            // Verify record has exactly {node, edge} keys
            if func.domain_len() != 2 {
                return Ok(Some(Value::Bool(false)));
            }

            // Fix for #2130: propagate eval_iter_set errors (TLC parity).
            // TLC evaluates IsDirectedGraph as pure TLA+ (Graphs.tla), where
            // non-enumerable node/edge sets raise EvalException, not FALSE.
            // Phase 1A (#3073): FxHashSet for O(1) membership instead of OrdSet O(log n)
            #[allow(clippy::mutable_key_type)]
            let node_set: FxHashSet<Value> = eval_iter_set(ctx, &nodes, span)?.collect();
            // Phase 1A (#3073): edge_set only iterated, no membership needed — Vec
            // avoids OrdSet tree insertion overhead.
            let edge_vec: Vec<Value> = eval_iter_set(ctx, &edges, span)?.collect();

            // Check edge ⊆ node × node (each edge is a pair of nodes)
            for edge in &edge_vec {
                // Each edge must be a tuple <<n1, n2>>
                if let Value::Tuple(pair) = edge {
                    if pair.len() != 2 {
                        return Ok(Some(Value::Bool(false)));
                    }
                    // Both elements must be in nodes
                    if !node_set.contains(&pair[0]) || !node_set.contains(&pair[1]) {
                        return Ok(Some(Value::Bool(false)));
                    }
                } else {
                    return Ok(Some(Value::Bool(false)));
                }
            }

            Ok(Some(Value::Bool(true)))
        }

        // IsUndirectedGraph(G) - check if G is a valid undirected graph
        // UndirectedGraphs module uses set-based edges {a,b}
        // G must be [node |-> Set, edge |-> Set of two-element sets]
        "IsUndirectedGraph" => {
            check_arity(name, args, 1, span)?;
            let gv = eval_expr(ctx, &args[0])?;

            let func = match gv.to_func_coerced() {
                Some(f) => f,
                None => return Ok(Some(Value::Bool(false))),
            };

            let node_key = Value::String(intern_string("node"));
            let edge_key = Value::String(intern_string("edge"));

            let nodes = match func.apply(&node_key) {
                Some(n) => n.clone(),
                None => return Ok(Some(Value::Bool(false))),
            };

            let edges = match func.apply(&edge_key) {
                Some(e) => e.clone(),
                None => return Ok(Some(Value::Bool(false))),
            };

            if func.domain_len() != 2 {
                return Ok(Some(Value::Bool(false)));
            }

            // Materialize nodes and edges via eval_iter_set (SetPred-aware).
            // TLC parity: non-set node/edge fields raise errors, not FALSE.
            // Phase 1A (#3073): FxHashSet for O(1) membership instead of OrdSet O(log n)
            #[allow(clippy::mutable_key_type)]
            let node_set: FxHashSet<Value> = eval_iter_set(ctx, &nodes, span)?.collect();
            let edge_iter = eval_iter_set(ctx, &edges, span)?;

            // Each edge must be a 2-element set {a,b} where a,b are nodes
            for edge in edge_iter {
                // Edge should be a set (in UndirectedGraphs)
                if let Some(edge_inner) = edge.to_sorted_set() {
                    // Must be exactly 2 elements
                    if edge_inner.len() != 2 {
                        return Ok(Some(Value::Bool(false)));
                    }
                    // Both elements must be in nodes
                    for elem in &edge_inner {
                        if !node_set.contains(elem) {
                            return Ok(Some(Value::Bool(false)));
                        }
                    }
                } else {
                    return Ok(Some(Value::Bool(false)));
                }
            }

            Ok(Some(Value::Bool(true)))
        }

        // IsLoopFreeUndirectedGraph(G) — undirected graph with no self-loops
        "IsLoopFreeUndirectedGraph" => {
            check_arity(name, args, 1, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let func = match gv.to_func_coerced() {
                Some(f) => f,
                None => return Ok(Some(Value::Bool(false))),
            };

            let node_key = Value::String(intern_string("node"));
            let edge_key = Value::String(intern_string("edge"));

            let nodes = match func.apply(&node_key) {
                Some(n) => n.clone(),
                None => return Ok(Some(Value::Bool(false))),
            };
            let edges = match func.apply(&edge_key) {
                Some(e) => e.clone(),
                None => return Ok(Some(Value::Bool(false))),
            };
            if func.domain_len() != 2 {
                return Ok(Some(Value::Bool(false)));
            }

            #[allow(clippy::mutable_key_type)]
            let node_set: FxHashSet<Value> = eval_iter_set(ctx, &nodes, span)?.collect();
            let edge_iter = eval_iter_set(ctx, &edges, span)?;

            for edge in edge_iter {
                if let Some(edge_inner) = edge.to_sorted_set() {
                    // {a, a} = {a} has len 1, caught by len != 2 check
                    if edge_inner.len() != 2 {
                        return Ok(Some(Value::Bool(false)));
                    }
                    for elem in &edge_inner {
                        if !node_set.contains(elem) {
                            return Ok(Some(Value::Bool(false)));
                        }
                    }
                } else {
                    return Ok(Some(Value::Bool(false)));
                }
            }
            Ok(Some(Value::Bool(true)))
        }

        _ => Ok(None),
    }
}
