// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::VecDeque;

use rustc_hash::FxHashSet;

use super::super::{
    check_arity, eval as eval_expr, eval_iter_set, EvalCtx, EvalError, EvalResult, Expr, Span,
    Spanned, Value,
};
use super::{bfs_reachable, build_directed_adj, build_undirected_adj, extract_graph};

pub(super) fn eval(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // SuccessorsOf(S, G) — immediate successors of nodes in S within directed graph G
        "SuccessorsOf" => {
            check_arity(name, args, 2, span)?;
            let sv = eval_expr(ctx, &args[0])?;
            let gv = eval_expr(ctx, &args[1])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => {
                    return Err(EvalError::type_error("Graph record", &gv, span));
                }
            };

            // S can be a single node or a set of nodes
            #[allow(clippy::mutable_key_type)]
            let source_nodes: FxHashSet<Value> =
                if let Ok(iter) = eval_iter_set(ctx, &sv.clone(), span) {
                    iter.collect()
                } else {
                    let mut s = FxHashSet::default();
                    s.insert(sv);
                    s
                };

            #[allow(clippy::mutable_key_type)]
            let node_set: FxHashSet<Value> = nodes.iter().cloned().collect();
            let mut result = Vec::new();
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2
                        && source_nodes.contains(&pair[0])
                        && node_set.contains(&pair[1])
                    {
                        result.push(pair[1].clone());
                    }
                }
            }
            Ok(Some(Value::set(result)))
        }

        // PredecessorsOf(S, G) — immediate predecessors of nodes in S within directed graph G
        "PredecessorsOf" => {
            check_arity(name, args, 2, span)?;
            let sv = eval_expr(ctx, &args[0])?;
            let gv = eval_expr(ctx, &args[1])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => {
                    return Err(EvalError::type_error("Graph record", &gv, span));
                }
            };

            #[allow(clippy::mutable_key_type)]
            let target_nodes: FxHashSet<Value> =
                if let Ok(iter) = eval_iter_set(ctx, &sv.clone(), span) {
                    iter.collect()
                } else {
                    let mut s = FxHashSet::default();
                    s.insert(sv);
                    s
                };

            #[allow(clippy::mutable_key_type)]
            let node_set: FxHashSet<Value> = nodes.iter().cloned().collect();
            let mut result = Vec::new();
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2
                        && target_nodes.contains(&pair[1])
                        && node_set.contains(&pair[0])
                    {
                        result.push(pair[0].clone());
                    }
                }
            }
            Ok(Some(Value::set(result)))
        }

        // Reachable(S, G) — all nodes reachable from S via directed edges (BFS)
        "Reachable" => {
            check_arity(name, args, 2, span)?;
            let sv = eval_expr(ctx, &args[0])?;
            let gv = eval_expr(ctx, &args[1])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => {
                    return Err(EvalError::type_error("Graph record", &gv, span));
                }
            };

            let (adj, node_to_idx) = build_directed_adj(&nodes, &edges);

            let start_indices: Vec<usize> = if let Ok(iter) = eval_iter_set(ctx, &sv.clone(), span)
            {
                iter.filter_map(|v| node_to_idx.get(&v).copied()).collect()
            } else {
                node_to_idx.get(&sv).map(|&i| vec![i]).unwrap_or_default()
            };

            // BFS from all start nodes.
            // Use separate `processed` (BFS dedup) and `reachable` (reached via edge)
            // arrays so start nodes are only included when reachable via a cycle.
            // TLC's Descendants(G, n) uses TransitiveClosure which returns TC[n,n]=TRUE
            // when a cycle exists through n.
            let mut reachable = vec![false; nodes.len()];
            let mut processed = vec![false; nodes.len()];
            let mut queue = VecDeque::new();
            for &start in &start_indices {
                processed[start] = true;
                queue.push_back(start);
            }
            while let Some(curr) = queue.pop_front() {
                for &neighbor in &adj[curr] {
                    reachable[neighbor] = true;
                    if !processed[neighbor] {
                        processed[neighbor] = true;
                        queue.push_back(neighbor);
                    }
                }
            }

            // Result: all nodes marked reachable via at least one edge
            let result: Vec<Value> = nodes
                .iter()
                .enumerate()
                .filter(|&(i, _)| reachable[i])
                .map(|(_, v)| v.clone())
                .collect();
            Ok(Some(Value::set(result)))
        }

        // AreConnectedIn(m, n, G) — check if m and n are connected in G
        // Polymorphic: directed (tuple) or undirected (set) edges
        // Uses BFS for efficiency (TLC's SimplePath enumeration is exponential)
        "AreConnectedIn" => {
            check_arity(name, args, 3, span)?;
            let mv = eval_expr(ctx, &args[0])?;
            let nv = eval_expr(ctx, &args[1])?;
            let gv = eval_expr(ctx, &args[2])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => {
                    return Err(EvalError::type_error("Graph record", &gv, span));
                }
            };

            let is_undirected = edges
                .first()
                .map(|e| e.to_sorted_set().is_some())
                .unwrap_or(false);
            let (adj, node_to_idx) = if is_undirected {
                build_undirected_adj(&nodes, &edges)
            } else {
                build_directed_adj(&nodes, &edges)
            };

            let m_idx = match node_to_idx.get(&mv) {
                Some(&i) => i,
                None => return Ok(Some(Value::Bool(false))),
            };
            let n_idx = match node_to_idx.get(&nv) {
                Some(&i) => i,
                None => return Ok(Some(Value::Bool(false))),
            };

            let visited = bfs_reachable(&adj, m_idx);
            Ok(Some(Value::Bool(visited[n_idx])))
        }

        // Path(G) — set of all paths (infinite: Seq(G.node))
        // Neither TLC nor TLA2 can enumerate this; use SimplePath instead
        "Path" => {
            check_arity(name, args, 1, span)?;
            let _gv = eval_expr(ctx, &args[0])?;
            Err(EvalError::Internal {
                message: "Path(G) produces an infinite set (Seq(G.node)) and cannot be \
                          enumerated. Use SimplePath(G) for a finite alternative."
                    .to_string(),
                span,
            })
        }

        // Successors(G, n) — immediate successors of node n
        "Successors" => {
            check_arity(name, args, 2, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let nv = eval_expr(ctx, &args[1])?;
            let (_nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };
            let mut result = Vec::new();
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2 && pair[0] == nv {
                        result.push(pair[1].clone());
                    }
                }
            }
            Ok(Some(Value::set(result)))
        }

        // AllSuccessors(G, S) — successors of all nodes in S
        "AllSuccessors" => {
            check_arity(name, args, 2, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let sv = eval_expr(ctx, &args[1])?;
            let (_nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };
            #[allow(clippy::mutable_key_type)]
            let source_set: FxHashSet<Value> = eval_iter_set(ctx, &sv, span)?.collect();
            let mut result = Vec::new();
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2 && source_set.contains(&pair[0]) {
                        result.push(pair[1].clone());
                    }
                }
            }
            Ok(Some(Value::set(result)))
        }

        // Predecessors(G, n) — immediate predecessors of node n
        "Predecessors" => {
            check_arity(name, args, 2, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let nv = eval_expr(ctx, &args[1])?;
            let (_nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };
            let mut result = Vec::new();
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2 && pair[1] == nv {
                        result.push(pair[0].clone());
                    }
                }
            }
            Ok(Some(Value::set(result)))
        }

        // AllPredecessors(G, S) — predecessors of all nodes in S
        "AllPredecessors" => {
            check_arity(name, args, 2, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let sv = eval_expr(ctx, &args[1])?;
            let (_nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };
            #[allow(clippy::mutable_key_type)]
            let target_set: FxHashSet<Value> = eval_iter_set(ctx, &sv, span)?.collect();
            let mut result = Vec::new();
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2 && target_set.contains(&pair[1]) {
                        result.push(pair[0].clone());
                    }
                }
            }
            Ok(Some(Value::set(result)))
        }

        // Ancestors(G, n) — all nodes with a path to n (transitive predecessors)
        "Ancestors" => {
            check_arity(name, args, 2, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let nv = eval_expr(ctx, &args[1])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };

            let (adj, node_to_idx) = build_directed_adj(&nodes, &edges);
            let n_idx = match node_to_idx.get(&nv) {
                Some(&i) => i,
                None => return Ok(Some(Value::empty_set())),
            };

            // Build reverse adjacency and BFS from n_idx
            let mut rev_adj: Vec<Vec<usize>> = vec![vec![]; nodes.len()];
            for (i, neighbors) in adj.iter().enumerate() {
                for &j in neighbors {
                    rev_adj[j].push(i);
                }
            }
            // BFS on reversed graph from target node.
            // Use separate processed/reachable arrays so n is only included if
            // reachable via a cycle (matches Relation.TransitiveClosure semantics:
            // TC[n,n] = TRUE only when n has a cycle through it).
            let mut reachable = vec![false; nodes.len()];
            let mut processed = vec![false; nodes.len()];
            let mut queue = VecDeque::new();
            processed[n_idx] = true;
            queue.push_back(n_idx);
            while let Some(curr) = queue.pop_front() {
                for &neighbor in &rev_adj[curr] {
                    reachable[neighbor] = true;
                    if !processed[neighbor] {
                        processed[neighbor] = true;
                        queue.push_back(neighbor);
                    }
                }
            }
            let result: Vec<Value> = nodes
                .iter()
                .enumerate()
                .filter(|&(i, _)| reachable[i])
                .map(|(_, v)| v.clone())
                .collect();
            Ok(Some(Value::set(result)))
        }

        // Descendants(G, n) — all nodes reachable from n (transitive successors)
        "Descendants" => {
            check_arity(name, args, 2, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let nv = eval_expr(ctx, &args[1])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };

            let (adj, node_to_idx) = build_directed_adj(&nodes, &edges);
            let n_idx = match node_to_idx.get(&nv) {
                Some(&i) => i,
                None => return Ok(Some(Value::empty_set())),
            };

            // BFS from n_idx on forward adjacency.
            // Same pattern as Ancestors/Reachable: n is only included via a cycle.
            let mut reachable = vec![false; nodes.len()];
            let mut processed = vec![false; nodes.len()];
            let mut queue = VecDeque::new();
            processed[n_idx] = true;
            queue.push_back(n_idx);
            while let Some(curr) = queue.pop_front() {
                for &neighbor in &adj[curr] {
                    reachable[neighbor] = true;
                    if !processed[neighbor] {
                        processed[neighbor] = true;
                        queue.push_back(neighbor);
                    }
                }
            }
            let result: Vec<Value> = nodes
                .iter()
                .enumerate()
                .filter(|&(i, _)| reachable[i])
                .map(|(_, v)| v.clone())
                .collect();
            Ok(Some(Value::set(result)))
        }

        // InDegree(G, n) — number of predecessors of n
        "InDegree" => {
            check_arity(name, args, 2, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let nv = eval_expr(ctx, &args[1])?;
            let (_nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };
            // Count distinct predecessors (edges where pair[1] == n)
            #[allow(clippy::mutable_key_type)]
            let mut preds: FxHashSet<Value> = FxHashSet::default();
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2 && pair[1] == nv {
                        preds.insert(pair[0].clone());
                    }
                }
            }
            Ok(Some(Value::int(preds.len() as i64)))
        }

        // OutDegree(G, n) — number of successors of n
        "OutDegree" => {
            check_arity(name, args, 2, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let nv = eval_expr(ctx, &args[1])?;
            let (_nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };
            #[allow(clippy::mutable_key_type)]
            let mut succs: FxHashSet<Value> = FxHashSet::default();
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2 && pair[0] == nv {
                        succs.insert(pair[1].clone());
                    }
                }
            }
            Ok(Some(Value::int(succs.len() as i64)))
        }

        // Roots(G) — nodes with no predecessors (in-degree 0)
        "Roots" => {
            check_arity(name, args, 1, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };
            // Collect all nodes that appear as edge targets
            #[allow(clippy::mutable_key_type)]
            let mut has_predecessor: FxHashSet<Value> = FxHashSet::default();
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2 {
                        has_predecessor.insert(pair[1].clone());
                    }
                }
            }
            let result: Vec<Value> = nodes
                .into_iter()
                .filter(|n| !has_predecessor.contains(n))
                .collect();
            Ok(Some(Value::set(result)))
        }

        // Leaves(G) — nodes with no successors (out-degree 0)
        "Leaves" => {
            check_arity(name, args, 1, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };
            #[allow(clippy::mutable_key_type)]
            let mut has_successor: FxHashSet<Value> = FxHashSet::default();
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2 {
                        has_successor.insert(pair[0].clone());
                    }
                }
            }
            let result: Vec<Value> = nodes
                .into_iter()
                .filter(|n| !has_successor.contains(n))
                .collect();
            Ok(Some(Value::set(result)))
        }

        _ => Ok(None),
    }
}
