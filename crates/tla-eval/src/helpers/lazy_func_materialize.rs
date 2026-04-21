// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LazyFunc materialization — TLC `FcnLambdaValue.toFcnRcd()` parity.
//!
//! Materializes lazy function values to concrete `Value::Func` by enumerating
//! the domain and evaluating the body for each element. This enables
//! content-based fingerprinting and eliminates dependence on process-local IDs.
//!
//! Part of #2018: Materialize before fingerprinting.

use super::super::{eval, eval_iter_set, EvalCtx, EvalError, EvalResult};
use super::{build_lazy_func_ctx, into_bind_local_bound_var};
use crate::value::{ComponentDomain, FuncBuilder, LazyDomain, LazyFuncValue, Value};
use std::sync::Arc;
use tla_core::ast::BoundPattern;

/// Materialize a `LazyFuncValue` to a concrete `Value::Func`.
///
/// This is the TLA2 equivalent of TLC's `FcnLambdaValue.toFcnRcd()`:
/// enumerate the domain, evaluate the body for each element, and produce
/// a concrete function value suitable for content-based fingerprinting.
///
/// Returns an error for non-enumerable domains (Nat, Int, Real, String),
/// matching TLC behavior — infinite-domain functions cannot appear in state variables.
///
/// Part of #2018: Materialize before fingerprinting.
pub fn materialize_lazy_func_to_func(ctx: &EvalCtx, f: &Arc<LazyFuncValue>) -> EvalResult<Value> {
    // Enumerate domain elements. Infinite domains produce an error (TLC parity).
    let domain_elements: Vec<Value> = enumerate_lazy_domain(ctx, f.domain())?;

    // Build base eval context (mirrors eval_func_apply's context setup)
    // Part of #2955: Self-reference via BindingChain (no HashMap clone).
    let base_ctx = build_lazy_func_ctx(ctx, f, ctx.recursion_depth.saturating_add(1))?;

    let mut builder = FuncBuilder::with_capacity(domain_elements.len());

    for elem in domain_elements {
        // Check memo first — EXCEPT operations pre-populate entries
        let value = if let Some(cached) = f.memoized_value(&elem) {
            cached
        } else {
            // Bind parameters and evaluate body
            // Part of #3395: Use pre-interned bounds for simple bindings.
            let bounds = f.bounds();
            let pre = f.pre_interned_bounds();
            let bound_ctx = if bounds.len() == 1 {
                let bound = &bounds[0];
                if bound.pattern.is_none() || matches!(&bound.pattern, Some(BoundPattern::Var(_))) {
                    let (ref _name, id) = pre[0];
                    base_ctx.clone().into_bind_by_id(id, elem.clone())
                } else {
                    into_bind_local_bound_var(base_ctx.clone(), bound, &elem, None)?
                }
            } else {
                // Multi-arg function: elem should be a tuple
                let components =
                    elem.to_tuple_like_elements()
                        .ok_or_else(|| EvalError::Internal {
                            message: format!(
                                "LazyFunc materialization: expected tuple argument for \
                                 multi-arg function, got {}",
                                elem.type_name()
                            ),
                            span: None,
                        })?;
                if components.len() != bounds.len() {
                    return Err(EvalError::Internal {
                        message: format!(
                            "LazyFunc materialization: expected {} arguments, got {}",
                            bounds.len(),
                            components.len()
                        ),
                        span: None,
                    });
                }
                let mut bctx = base_ctx.clone();
                for (i, bound) in bounds.iter().enumerate() {
                    if bound.pattern.is_none()
                        || matches!(&bound.pattern, Some(BoundPattern::Var(_)))
                    {
                        let (ref _name, id) = pre[i];
                        bctx = bctx.into_bind_by_id(id, components[i].clone());
                    } else {
                        bctx = into_bind_local_bound_var(bctx, bound, &components[i], None)?;
                    }
                }
                bctx
            };
            eval(&bound_ctx, f.body())?
        };
        builder.insert(elem, value);
    }

    Ok(Value::Func(Arc::new(builder.build())))
}

/// Enumerate all elements of a `LazyDomain`.
///
/// Returns `Err` for infinite domains (Nat, Int, Real, String) — TLC's
/// `toFcnRcd()` also errors for these since they cannot be fully enumerated.
fn enumerate_lazy_domain(ctx: &EvalCtx, domain: &LazyDomain) -> EvalResult<Vec<Value>> {
    match domain {
        LazyDomain::Nat | LazyDomain::Int | LazyDomain::Real | LazyDomain::String => {
            Err(EvalError::Internal {
                message: "TLA2 has found a state in which the value of a variable \
                    contains a function over a non-enumerable domain \
                    (Nat, Int, Real, or STRING). TLC requires all function \
                    values in states to be fully materialized \
                    (FcnLambdaValue.toFcnRcd())."
                    .to_string(),
                span: None,
            })
        }
        LazyDomain::Product(components) => {
            // Build cartesian product of all component domains.
            // All components must be finite.
            let mut component_elements: Vec<Vec<Value>> = Vec::with_capacity(components.len());
            for comp in components {
                component_elements.push(enumerate_component_domain(comp)?);
            }
            // Generate cartesian product as tuples
            Ok(cartesian_product_as_tuples(&component_elements))
        }
        // Part of #1828: use eval_iter_set for SetPred-aware iteration.
        LazyDomain::General(domain_val) => Ok(eval_iter_set(ctx, domain_val, None)?.collect()),
    }
}

/// Enumerate elements of a single component domain.
fn enumerate_component_domain(comp: &ComponentDomain) -> EvalResult<Vec<Value>> {
    match comp {
        ComponentDomain::Finite(set) => Ok(set.iter().cloned().collect()),
        ComponentDomain::Nat
        | ComponentDomain::Int
        | ComponentDomain::Real
        | ComponentDomain::String => Err(EvalError::Internal {
            message: "Cannot enumerate infinite component domain \
                (Nat, Int, Real, or STRING) during function materialization."
                .to_string(),
            span: None,
        }),
    }
}

/// Generate the cartesian product of multiple component element vectors as tuples.
///
/// For example, `[[1, 2], ["a", "b"]]` produces
/// `[<<1, "a">>, <<1, "b">>, <<2, "a">>, <<2, "b">>]`.
fn cartesian_product_as_tuples(components: &[Vec<Value>]) -> Vec<Value> {
    if components.is_empty() {
        return vec![Value::Tuple(Arc::new([]))];
    }
    let mut result: Vec<Vec<Value>> = vec![vec![]];
    for component in components {
        let mut next = Vec::with_capacity(result.len() * component.len());
        for prefix in &result {
            for elem in component {
                let mut combo = prefix.clone();
                combo.push(elem.clone());
                next.push(combo);
            }
        }
        result = next;
    }
    result
        .into_iter()
        .map(|elems| Value::Tuple(elems.into()))
        .collect()
}
