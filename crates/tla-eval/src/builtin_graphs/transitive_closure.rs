// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::{
    check_arity, eval as eval_expr, eval_iter_set, EvalCtx, EvalError, EvalResult, Expr, Span,
    Spanned, Value,
};

pub(super) fn eval(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // === TransitiveClosure module ===
        "TransitiveClosure" | "Warshall" => {
            if args.len() != 1 {
                return Ok(None);
            }
            // TransitiveClosure(R) - compute the transitive closure of relation R
            // R is a set of pairs <<a, b>> representing edges a -> b
            // Uses Warshall's algorithm (Floyd-Warshall for reachability)
            check_arity(name, args, 1, span)?;
            let rv = eval_expr(ctx, &args[0])?;
            let rel: Vec<Value> = eval_iter_set(ctx, &rv, Some(args[0].span))?.collect();

            // Collect all vertices and build edge map
            let mut vertices: Vec<Value> = Vec::new();
            // Allow: Value has interior mutability for lazy evaluation but Eq/Hash don't depend on it
            #[allow(clippy::mutable_key_type)]
            let mut vertex_index: rustc_hash::FxHashMap<Value, usize> =
                rustc_hash::FxHashMap::default();

            // First pass: collect all vertices from the relation
            for pair in &rel {
                let tuple = pair
                    .as_seq_or_tuple_elements()
                    .ok_or_else(|| EvalError::type_error("Tuple", pair, span))?;
                if tuple.len() != 2 {
                    return Err(EvalError::Internal {
                        message: format!(
                            "TransitiveClosure requires pairs, got tuple of length {}",
                            tuple.len()
                        ),
                        span,
                    });
                }
                for elem in tuple.iter() {
                    if !vertex_index.contains_key(elem) {
                        vertex_index.insert(elem.clone(), vertices.len());
                        vertices.push(elem.clone());
                    }
                }
            }

            let n = vertices.len();
            if n == 0 {
                return Ok(Some(Value::empty_set()));
            }

            // Build adjacency matrix
            let mut matrix = vec![vec![false; n]; n];
            for pair in &rel {
                let tuple = pair
                    .as_seq_or_tuple_elements()
                    .ok_or_else(|| EvalError::type_error("Tuple", pair, span))?;
                if tuple.len() != 2 {
                    return Err(EvalError::Internal {
                        message: format!(
                            "TransitiveClosure requires pairs, got tuple of length {}",
                            tuple.len()
                        ),
                        span,
                    });
                }
                let i = vertex_index[&tuple[0]];
                let j = vertex_index[&tuple[1]];
                matrix[i][j] = true;
            }

            // Warshall's algorithm for transitive closure
            // Note: Index-based loops are clearest for matrix algorithms with cross-references
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

            // Build result set from matrix
            let mut result = Vec::new();
            for i in 0..n {
                for j in 0..n {
                    if matrix[i][j] {
                        result.push(Value::Tuple(
                            vec![vertices[i].clone(), vertices[j].clone()].into(),
                        ));
                    }
                }
            }
            Ok(Some(Value::set(result)))
        }

        "ReflexiveTransitiveClosure" => {
            if args.len() != 2 {
                return Ok(None);
            }
            // ReflexiveTransitiveClosure(R, S) - compute R+ (reflexive transitive closure)
            // This is TransitiveClosure(R) union {<<x, x>> : x \in S}
            check_arity(name, args, 2, span)?;
            let rv = eval_expr(ctx, &args[0])?;
            if rv.to_func_coerced().is_some() {
                return Ok(None);
            }
            let rel: Vec<Value> = eval_iter_set(ctx, &rv, Some(args[0].span))?.collect();
            let sv = eval_expr(ctx, &args[1])?;
            let domain: Vec<Value> = eval_iter_set(ctx, &sv, Some(args[1].span))?.collect();

            // Collect all vertices from both relation and domain set
            let mut vertices: Vec<Value> = Vec::new();
            // Allow: Value has interior mutability for lazy evaluation but Eq/Hash don't depend on it
            #[allow(clippy::mutable_key_type)]
            let mut vertex_index: rustc_hash::FxHashMap<Value, usize> =
                rustc_hash::FxHashMap::default();

            // Add vertices from domain set first
            for elem in &domain {
                if !vertex_index.contains_key(elem) {
                    vertex_index.insert(elem.clone(), vertices.len());
                    vertices.push(elem.clone());
                }
            }

            // Add vertices from relation
            for pair in &rel {
                let tuple = pair
                    .as_seq_or_tuple_elements()
                    .ok_or_else(|| EvalError::type_error("Tuple", pair, span))?;
                if tuple.len() != 2 {
                    return Err(EvalError::Internal {
                        message: format!(
                            "ReflexiveTransitiveClosure requires pairs, got tuple of length {}",
                            tuple.len()
                        ),
                        span,
                    });
                }
                for elem in tuple.iter() {
                    if !vertex_index.contains_key(elem) {
                        vertex_index.insert(elem.clone(), vertices.len());
                        vertices.push(elem.clone());
                    }
                }
            }

            let n = vertices.len();
            if n == 0 {
                return Ok(Some(Value::empty_set()));
            }

            // Build adjacency matrix with reflexive edges
            let mut matrix = vec![vec![false; n]; n];

            // Add reflexive edges for all vertices in domain
            for elem in &domain {
                if let Some(&i) = vertex_index.get(elem) {
                    matrix[i][i] = true;
                }
            }

            // Add edges from relation
            for pair in &rel {
                let tuple = pair
                    .as_seq_or_tuple_elements()
                    .ok_or_else(|| EvalError::type_error("Tuple", pair, span))?;
                if tuple.len() != 2 {
                    return Err(EvalError::Internal {
                        message: format!(
                            "ReflexiveTransitiveClosure requires pairs, got tuple of length {}",
                            tuple.len()
                        ),
                        span,
                    });
                }
                let i = vertex_index[&tuple[0]];
                let j = vertex_index[&tuple[1]];
                matrix[i][j] = true;
            }

            // Warshall's algorithm for transitive closure
            // Note: Index-based loops are clearest for matrix algorithms with cross-references
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

            // Build result set from matrix
            let mut result = Vec::new();
            for i in 0..n {
                for j in 0..n {
                    if matrix[i][j] {
                        result.push(Value::Tuple(
                            vec![vertices[i].clone(), vertices[j].clone()].into(),
                        ));
                    }
                }
            }
            Ok(Some(Value::set(result)))
        }

        _ => Ok(None),
    }
}
