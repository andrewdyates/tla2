// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use super::super::{
    check_arity, eval as eval_expr, eval_iter_set, EvalCtx, EvalError, EvalResult, Expr, FuncValue,
    SortedSet, Span, Spanned, Value,
};
use super::{build_directed_adj, build_undirected_adj, extract_graph, make_graph_record, subsets};

pub(super) fn eval(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // DirectedSubgraph(G) — set of all directed subgraphs of G
        // {H ∈ [node: SUBSET G.node, edge: SUBSET (G.node × G.node)] :
        //    IsDirectedGraph(H) ∧ H.edge ⊆ G.edge}
        "DirectedSubgraph" => {
            check_arity(name, args, 1, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => {
                    return Err(EvalError::type_error("Graph record", &gv, span));
                }
            };

            #[allow(clippy::mutable_key_type)]
            let node_set: FxHashSet<Value> = nodes.iter().cloned().collect();

            // Filter to valid directed edges (tuples with both endpoints in nodes)
            let valid_edges: Vec<Value> = edges
                .iter()
                .filter(|e| {
                    if let Value::Tuple(pair) = e {
                        pair.len() == 2
                            && node_set.contains(&pair[0])
                            && node_set.contains(&pair[1])
                    } else {
                        false
                    }
                })
                .cloned()
                .collect();

            let mut result = Vec::new();
            for node_subset in subsets(&nodes) {
                #[allow(clippy::mutable_key_type)]
                let sub_node_set: FxHashSet<Value> = node_subset.iter().cloned().collect();
                let sub_edges: Vec<Value> = valid_edges
                    .iter()
                    .filter(|e| {
                        if let Value::Tuple(pair) = e {
                            sub_node_set.contains(&pair[0]) && sub_node_set.contains(&pair[1])
                        } else {
                            false
                        }
                    })
                    .cloned()
                    .collect();
                for edge_subset in subsets(&sub_edges) {
                    result.push(make_graph_record(node_subset.clone(), edge_subset));
                }
            }
            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(result)))))
        }

        // UndirectedSubgraph(G) — set of all undirected subgraphs
        "UndirectedSubgraph" => {
            check_arity(name, args, 1, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => {
                    return Err(EvalError::type_error("Graph record", &gv, span));
                }
            };

            #[allow(clippy::mutable_key_type)]
            let node_set: FxHashSet<Value> = nodes.iter().cloned().collect();
            let valid_edges: Vec<Value> = edges
                .iter()
                .filter(|e| {
                    if let Some(inner) = e.to_sorted_set() {
                        inner.len() == 2 && inner.iter().all(|elem| node_set.contains(elem))
                    } else {
                        false
                    }
                })
                .cloned()
                .collect();

            let mut result = Vec::new();
            for node_subset in subsets(&nodes) {
                #[allow(clippy::mutable_key_type)]
                let sub_node_set: FxHashSet<Value> = node_subset.iter().cloned().collect();
                let sub_edges: Vec<Value> = valid_edges
                    .iter()
                    .filter(|e| {
                        if let Some(inner) = e.to_sorted_set() {
                            inner.iter().all(|elem| sub_node_set.contains(elem))
                        } else {
                            false
                        }
                    })
                    .cloned()
                    .collect();
                for edge_subset in subsets(&sub_edges) {
                    result.push(make_graph_record(node_subset.clone(), edge_subset));
                }
            }
            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(result)))))
        }

        // SimplePath(G) — set of all simple paths (no repeated nodes)
        // Polymorphic: directed (tuple) or undirected (set) edges
        "SimplePath" => {
            check_arity(name, args, 1, span)?;
            let gv = eval_expr(ctx, &args[0])?;
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
            let (adj, _) = if is_undirected {
                build_undirected_adj(&nodes, &edges)
            } else {
                build_directed_adj(&nodes, &edges)
            };

            let n = nodes.len();
            let mut paths: Vec<Value> = Vec::new();

            // DFS from each starting node to enumerate all simple paths
            for start in 0..n {
                let mut stack: Vec<(usize, Vec<usize>)> = vec![(start, vec![start])];
                while let Some((curr, path)) = stack.pop() {
                    // Record this path (length >= 1, as per TLA+ definition p # <<>>)
                    let tla_path: Vec<Value> = path.iter().map(|&i| nodes[i].clone()).collect();
                    paths.push(Value::Tuple(tla_path.into()));

                    for &neighbor in &adj[curr] {
                        if !path.contains(&neighbor) {
                            let mut new_path = path.clone();
                            new_path.push(neighbor);
                            stack.push((neighbor, new_path));
                        }
                    }
                }
            }

            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(paths)))))
        }

        // ConnectedComponents(G) — set of connected components (each a set of nodes)
        // Uses union-find for efficiency
        "ConnectedComponents" => {
            check_arity(name, args, 1, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => {
                    return Err(EvalError::type_error("Graph record", &gv, span));
                }
            };

            if nodes.is_empty() {
                return Ok(Some(Value::empty_set()));
            }

            let n = nodes.len();
            let mut parent: Vec<usize> = (0..n).collect();
            let mut uf_rank: Vec<usize> = vec![0; n];

            fn uf_find(parent: &mut [usize], x: usize) -> usize {
                if parent[x] != x {
                    parent[x] = uf_find(parent, parent[x]);
                }
                parent[x]
            }

            fn uf_union(parent: &mut [usize], rank: &mut [usize], x: usize, y: usize) {
                let rx = uf_find(parent, x);
                let ry = uf_find(parent, y);
                if rx != ry {
                    if rank[rx] < rank[ry] {
                        parent[rx] = ry;
                    } else if rank[rx] > rank[ry] {
                        parent[ry] = rx;
                    } else {
                        parent[ry] = rx;
                        rank[rx] += 1;
                    }
                }
            }

            #[allow(clippy::mutable_key_type)]
            let node_to_idx: FxHashMap<Value, usize> = nodes
                .iter()
                .enumerate()
                .map(|(i, v)| (v.clone(), i))
                .collect();

            // Process edges (both set-based and tuple-based)
            for edge in &edges {
                if let Some(edge_inner) = edge.to_sorted_set() {
                    let elems: Vec<_> = edge_inner.iter().collect();
                    if elems.len() == 2 {
                        if let (Some(&i), Some(&j)) =
                            (node_to_idx.get(elems[0]), node_to_idx.get(elems[1]))
                        {
                            uf_union(&mut parent, &mut uf_rank, i, j);
                        }
                    }
                } else if let Value::Tuple(pair) = edge {
                    if pair.len() == 2 {
                        if let (Some(&i), Some(&j)) =
                            (node_to_idx.get(&pair[0]), node_to_idx.get(&pair[1]))
                        {
                            uf_union(&mut parent, &mut uf_rank, i, j);
                        }
                    }
                }
            }

            let mut components: FxHashMap<usize, Vec<Value>> = FxHashMap::default();
            for i in 0..n {
                let root = uf_find(&mut parent, i);
                components.entry(root).or_default().push(nodes[i].clone());
            }

            let result: Vec<Value> = components
                .into_values()
                .map(|component| Value::Set(Arc::new(SortedSet::from_iter(component))))
                .collect();
            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(result)))))
        }

        // Transpose(G) — reverse all edges: <<a,b>> becomes <<b,a>>
        "Transpose" => {
            check_arity(name, args, 1, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };
            let reversed: Vec<Value> = edges
                .iter()
                .filter_map(|e| {
                    if let Value::Tuple(pair) = e {
                        if pair.len() == 2 {
                            return Some(Value::Tuple(
                                vec![pair[1].clone(), pair[0].clone()].into(),
                            ));
                        }
                    }
                    None
                })
                .collect();
            Ok(Some(make_graph_record(nodes, reversed)))
        }

        // GraphUnion(G, H) — union of nodes and edges
        "GraphUnion" => {
            check_arity(name, args, 2, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let hv = eval_expr(ctx, &args[1])?;
            let (g_nodes, g_edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };
            let (h_nodes, h_edges) = match extract_graph(ctx, &hv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &hv, span)),
            };
            let all_nodes: Vec<Value> = g_nodes.into_iter().chain(h_nodes).collect();
            let all_edges: Vec<Value> = g_edges.into_iter().chain(h_edges).collect();
            Ok(Some(make_graph_record(all_nodes, all_edges)))
        }

        // ConnectionsIn(G) — Warshall Boolean reachability matrix
        // Returns function [m,n \in G.node |-> TRUE/FALSE]
        "ConnectionsIn" => {
            check_arity(name, args, 1, span)?;
            let gv = eval_expr(ctx, &args[0])?;
            let (nodes, edges) = match extract_graph(ctx, &gv, span)? {
                Some(g) => g,
                None => return Err(EvalError::type_error("Graph record", &gv, span)),
            };

            let n = nodes.len();
            #[allow(clippy::mutable_key_type)]
            let node_to_idx: FxHashMap<Value, usize> = nodes
                .iter()
                .enumerate()
                .map(|(i, v)| (v.clone(), i))
                .collect();

            // Initialize: m=n or <<m,n>> in edges
            let mut matrix = vec![vec![false; n]; n];
            for i in 0..n {
                matrix[i][i] = true;
            }
            for edge in &edges {
                if let Value::Tuple(pair) = edge {
                    if pair.len() == 2 {
                        if let (Some(&i), Some(&j)) =
                            (node_to_idx.get(&pair[0]), node_to_idx.get(&pair[1]))
                        {
                            matrix[i][j] = true;
                        }
                    }
                }
            }

            // Warshall's algorithm
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

            // Build result as function [<<m,n>> \in G.node \X G.node |-> BOOLEAN]
            let mut entries: Vec<(Value, Value)> = Vec::new();
            for (i, ni) in nodes.iter().enumerate() {
                for (j, nj) in nodes.iter().enumerate() {
                    let key = Value::Tuple(vec![ni.clone(), nj.clone()].into());
                    let val = Value::Bool(matrix[i][j]);
                    entries.push((key, val));
                }
            }
            entries.sort_by(|(a, _), (b, _)| a.cmp(b));
            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                entries,
            )))))
        }

        // EmptyGraph == [node |-> {}, edge |-> {}]
        "EmptyGraph" => {
            check_arity(name, args, 0, span)?;
            Ok(Some(make_graph_record(vec![], vec![])))
        }

        // Graphs(S) — set of all possible directed graphs over node set S
        // [node: {S}, edge: SUBSET (S × S)]
        "Graphs" => {
            check_arity(name, args, 1, span)?;
            let sv = eval_expr(ctx, &args[0])?;
            let nodes_vec: Vec<Value> = eval_iter_set(ctx, &sv, span)?.collect();

            // Build all possible edges (S × S)
            let mut all_edges = Vec::new();
            for a in &nodes_vec {
                for b in &nodes_vec {
                    all_edges.push(Value::Tuple(vec![a.clone(), b.clone()].into()));
                }
            }

            // For each subset of edges, create a graph
            let mut result = Vec::new();
            for edge_subset in subsets(&all_edges) {
                result.push(make_graph_record(nodes_vec.clone(), edge_subset));
            }
            Ok(Some(Value::Set(Arc::new(SortedSet::from_iter(result)))))
        }

        _ => Ok(None),
    }
}
