// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};

use super::super::{
    check_arity, eval as eval_expr, eval_iter_set, EvalCtx, EvalError, EvalResult, Expr, Span,
    Spanned, Value,
};
use super::{bfs_reachable, build_directed_adj, extract_graph};
use crate::value::intern_string;

pub(super) fn eval(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        "ConnectedNodes" => {
            // ConnectedNodes(R) - the set of all nodes connected by relation R
            // Returns the union of all first and second elements of pairs in R
            check_arity(name, args, 1, span)?;
            let rv = eval_expr(ctx, &args[0])?;
            let rel: Vec<Value> = eval_iter_set(ctx, &rv, Some(args[0].span))?.collect();

            let mut nodes = Vec::new();
            for pair in &rel {
                let tuple = pair
                    .as_seq_or_tuple_elements()
                    .ok_or_else(|| EvalError::type_error("Tuple", pair, span))?;
                if tuple.len() != 2 {
                    return Err(EvalError::Internal {
                        message: format!(
                            "ConnectedNodes requires pairs, got tuple of length {}",
                            tuple.len()
                        ),
                        span,
                    });
                }
                nodes.push(tuple[0].clone());
                nodes.push(tuple[1].clone());
            }
            Ok(Some(Value::set(nodes)))
        }

        // IsStronglyConnected(G) - \A m, n \in G.node : AreConnectedIn(m, n, G)
        // For directed graphs (tuple edges <<a,b>>): needs reachability in both directions
        // For undirected graphs (set edges {a,b}): single BFS suffices
        "IsStronglyConnected" => {
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

            // Materialize nodes and edges via eval_iter_set (SetPred-aware, TLC parity).
            let nodes_vec: Vec<Value> = eval_iter_set(ctx, &nodes, span)?.collect();
            let edge_iter = eval_iter_set(ctx, &edges, span)?;

            // Empty graph is trivially connected
            if nodes_vec.is_empty() {
                return Ok(Some(Value::Bool(true)));
            }
            #[allow(clippy::mutable_key_type)]
            let mut node_to_idx: FxHashMap<&Value, usize> = FxHashMap::default();
            for (i, n) in nodes_vec.iter().enumerate() {
                node_to_idx.insert(n, i);
            }

            // Build forward and reverse adjacency lists.
            // Set edges {a,b} are undirected: add both directions in both lists.
            // Tuple edges <<a,b>> are directed: forward gets a->b, reverse gets b->a.
            let n = nodes_vec.len();
            let mut fwd_adj: Vec<Vec<usize>> = vec![vec![]; n];
            let mut rev_adj: Vec<Vec<usize>> = vec![vec![]; n];
            for edge in edge_iter {
                if let Some(edge_inner) = edge.to_sorted_set() {
                    // Set-based edge {a,b} — undirected
                    let elems: Vec<_> = edge_inner.iter().collect();
                    if elems.len() == 2 {
                        if let (Some(&i), Some(&j)) =
                            (node_to_idx.get(elems[0]), node_to_idx.get(elems[1]))
                        {
                            fwd_adj[i].push(j);
                            fwd_adj[j].push(i);
                            rev_adj[i].push(j);
                            rev_adj[j].push(i);
                        }
                    }
                } else if let Value::Tuple(pair) = &edge {
                    // Tuple-based edge <<a,b>> — directed: a -> b only
                    if pair.len() == 2 {
                        if let (Some(&i), Some(&j)) =
                            (node_to_idx.get(&pair[0]), node_to_idx.get(&pair[1]))
                        {
                            fwd_adj[i].push(j);
                            rev_adj[j].push(i);
                        }
                    }
                }
            }

            // Strong connectivity: BFS from node 0 must reach all nodes
            // in BOTH the forward and reverse adjacency lists.
            let fwd_visited = bfs_reachable(&fwd_adj, 0);
            let rev_visited = bfs_reachable(&rev_adj, 0);

            Ok(Some(Value::Bool(
                fwd_visited.iter().all(|&v| v) && rev_visited.iter().all(|&v| v),
            )))
        }

        // IsTreeWithRoot(G, r) — G is a directed tree rooted at r
        "IsTreeWithRoot" => {
            check_arity(name, args, 2, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let rv = eval_expr(ctx, &args[1])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };

            // IsDirectedGraph(G) check: all edges must be tuples with endpoints in nodes
            #[allow(clippy::mutable_key_type)]
            let node_to_idx: FxHashMap<Value, usize> = nodes
                .iter()
                .enumerate()
                .map(|(i, v)| (v.clone(), i))
                .collect();
            #[allow(clippy::mutable_key_type)]
            let node_set: FxHashSet<Value> = nodes.iter().cloned().collect();
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() != 2
                        || !node_set.contains(&pair[0])
                        || !node_set.contains(&pair[1])
                    {
                        return Ok(Some(Value::Bool(false)));
                    }
                } else {
                    return Ok(Some(Value::Bool(false)));
                }
            }

            let r_idx = match node_to_idx.get(&rv) {
                Some(&i) => i,
                None => return Ok(Some(Value::Bool(false))),
            };

            // TLA+ definition: \A e \in G.edge : e[1] # r /\ (\A f: e[1] = f[1] => e = f)
            // Meaning: root is never an edge source, each node sources at most one edge
            #[allow(clippy::mutable_key_type)]
            let mut source_to_edge: FxHashMap<usize, usize> = FxHashMap::default();
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2 {
                        if let (Some(&src), Some(&_dst)) =
                            (node_to_idx.get(&pair[0]), node_to_idx.get(&pair[1]))
                        {
                            // Root cannot be source
                            if src == r_idx {
                                return Ok(Some(Value::Bool(false)));
                            }
                            // Each source can have at most one edge
                            if source_to_edge.contains_key(&src) {
                                return Ok(Some(Value::Bool(false)));
                            }
                            source_to_edge.insert(src, 0);
                        }
                    }
                }
            }

            // All nodes must be connected to root
            // Build reverse adjacency (follow edges backward to check reachability to root)
            let (adj, _) = build_directed_adj(&nodes, &edges);
            // Build reverse adjacency for checking reachability TO root
            let mut rev_adj: Vec<Vec<usize>> = vec![vec![]; nodes.len()];
            for (i, neighbors) in adj.iter().enumerate() {
                for &j in neighbors {
                    rev_adj[j].push(i);
                }
            }
            // BFS from root on reverse adjacency = all nodes that can reach root
            let reachable = bfs_reachable(&rev_adj, r_idx);
            Ok(Some(Value::Bool(reachable.iter().all(|&v| v))))
        }

        // IsBipartiteWithPartitions(G, U, V)
        "IsBipartiteWithPartitions" => {
            check_arity(name, args, 3, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let uv = eval_expr(ctx, &args[1])?;
            let vv = eval_expr(ctx, &args[2])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };

            #[allow(clippy::mutable_key_type)]
            let u_set: FxHashSet<Value> = eval_iter_set(ctx, &uv, span)?.collect();
            #[allow(clippy::mutable_key_type)]
            let v_set: FxHashSet<Value> = eval_iter_set(ctx, &vv, span)?.collect();

            // U ∩ V = {}
            if u_set.iter().any(|x| v_set.contains(x)) {
                return Ok(Some(Value::Bool(false)));
            }
            // G.node ⊆ U ∪ V
            #[allow(clippy::mutable_key_type)]
            let uv_union: FxHashSet<Value> = u_set.iter().chain(v_set.iter()).cloned().collect();
            if !nodes.iter().all(|n| uv_union.contains(n)) {
                return Ok(Some(Value::Bool(false)));
            }
            // Every edge has endpoints in different partitions
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2 {
                        let e1_in_u = u_set.contains(&pair[0]);
                        let e1_in_v = v_set.contains(&pair[0]);
                        let e2_in_u = u_set.contains(&pair[1]);
                        let e2_in_v = v_set.contains(&pair[1]);
                        if !((e1_in_u && e2_in_v) || (e1_in_v && e2_in_u)) {
                            return Ok(Some(Value::Bool(false)));
                        }
                    }
                }
            }
            Ok(Some(Value::Bool(true)))
        }

        // HasCycle(G) — does the graph contain a cycle?
        "HasCycle" => {
            check_arity(name, args, 1, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };

            let n = nodes.len();
            let (adj, node_to_idx) = build_directed_adj(&nodes, &edges);

            // Check for self-loops: <<n, n>> in edge
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2 && pair[0] == pair[1] {
                        if node_to_idx.contains_key(&pair[0]) {
                            return Ok(Some(Value::Bool(true)));
                        }
                    }
                }
            }

            // Check for cycles using Warshall's algorithm:
            // If ConnectionsIn(G)[m,n] and ConnectionsIn(G)[n,m] for m # n
            let mut matrix = vec![vec![false; n]; n];
            for i in 0..n {
                matrix[i][i] = true;
            }
            for (i, neighbors) in adj.iter().enumerate() {
                for &j in neighbors {
                    matrix[i][j] = true;
                }
            }
            #[allow(clippy::needless_range_loop)]
            for k in 0..n {
                for i in 0..n {
                    if matrix[i][k] {
                        for j in 0..n {
                            if matrix[k][j] {
                                matrix[i][j] = true;
                            }
                        }
                    }
                }
            }
            // Check for mutual reachability between distinct nodes
            for i in 0..n {
                for j in (i + 1)..n {
                    if matrix[i][j] && matrix[j][i] {
                        return Ok(Some(Value::Bool(true)));
                    }
                }
            }
            Ok(Some(Value::Bool(false)))
        }

        // IsDag(G) — is G a directed acyclic graph?
        "IsDag" => {
            check_arity(name, args, 1, span)?;
            let gv = eval_expr(ctx, &args[0])?;

            // Must be a directed graph
            let func = match gv.to_func_coerced() {
                Some(f) => f,
                None => return Ok(Some(Value::Bool(false))),
            };
            let node_key = Value::String(intern_string("node"));
            let edge_key = Value::String(intern_string("edge"));
            let nodes_val = match func.apply(&node_key) {
                Some(n) => n.clone(),
                None => return Ok(Some(Value::Bool(false))),
            };
            let edges_val = match func.apply(&edge_key) {
                Some(e) => e.clone(),
                None => return Ok(Some(Value::Bool(false))),
            };
            if func.domain_len() != 2 {
                return Ok(Some(Value::Bool(false)));
            }

            #[allow(clippy::mutable_key_type)]
            let node_set: FxHashSet<Value> = eval_iter_set(ctx, &nodes_val, span)?.collect();
            let edges_vec: Vec<Value> = eval_iter_set(ctx, &edges_val, span)?.collect();

            // Check IsDirectedGraph: edges must be tuples with endpoints in nodes
            for edge in &edges_vec {
                if let Value::Tuple(pair) = edge {
                    if pair.len() != 2
                        || !node_set.contains(&pair[0])
                        || !node_set.contains(&pair[1])
                    {
                        return Ok(Some(Value::Bool(false)));
                    }
                } else {
                    return Ok(Some(Value::Bool(false)));
                }
            }

            // Check no cycle (topological sort)
            let nodes_vec: Vec<Value> = node_set.into_iter().collect();
            let n = nodes_vec.len();
            #[allow(clippy::mutable_key_type)]
            let node_to_idx: FxHashMap<Value, usize> = nodes_vec
                .iter()
                .enumerate()
                .map(|(i, v)| (v.clone(), i))
                .collect();
            let mut in_degree = vec![0usize; n];
            let mut adj: Vec<Vec<usize>> = vec![vec![]; n];
            for edge in &edges_vec {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2 {
                        // Self-loop = instant cycle
                        if pair[0] == pair[1] {
                            return Ok(Some(Value::Bool(false)));
                        }
                        if let (Some(&i), Some(&j)) =
                            (node_to_idx.get(&pair[0]), node_to_idx.get(&pair[1]))
                        {
                            adj[i].push(j);
                            in_degree[j] += 1;
                        }
                    }
                }
            }
            // Kahn's algorithm for topological sort
            let mut queue: VecDeque<usize> = VecDeque::new();
            for i in 0..n {
                if in_degree[i] == 0 {
                    queue.push_back(i);
                }
            }
            let mut processed = 0;
            while let Some(curr) = queue.pop_front() {
                processed += 1;
                for &neighbor in &adj[curr] {
                    in_degree[neighbor] -= 1;
                    if in_degree[neighbor] == 0 {
                        queue.push_back(neighbor);
                    }
                }
            }
            Ok(Some(Value::Bool(processed == n)))
        }

        _ => Ok(None),
    }
}
