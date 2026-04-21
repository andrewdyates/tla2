// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Function definition and eager materialization.
//!
//! Handles `[x \in S |-> expr]` for both single-variable and multi-variable
//! function definitions, including lazy functions over infinite domains.

use super::super::{
    build_lazy_func_from_ctx, eval_iter_set, interval_len_for_bounds_check,
    push_bound_var_mut_preinterned, PreInternedBound,
};
use crate::core::EvalCtx;
use crate::helpers::eval;
use crate::value::{
    cartesian_product, ComponentDomain, FuncValue, IntIntervalFunc, LazyDomain, SortedSet, Value,
};
use num_traits::ToPrimitive;
use std::sync::Arc;
use tla_core::ast::{BoundPattern, BoundVar, Expr};
use tla_core::{Span, Spanned};
use tla_value::error::{EvalError, EvalResult};

fn eval_eager_single_var_function<'a>(
    ctx: &EvalCtx,
    bound: &BoundVar,
    body: &Spanned<Expr>,
    span: Option<Span>,
    iter: Box<dyn Iterator<Item = Value> + 'a>,
) -> EvalResult<Value> {
    // Finite set - evaluate eagerly
    // Collect domain elements and their mapped values in sorted order
    let mut local_ctx = ctx.clone();
    let mark = local_ctx.mark_stack();
    let mut entries: Vec<(Value, Value)> = Vec::new();
    let mut is_seq_domain = true;
    let mut expected_seq_idx: i64 = 1;
    // Part of #2955: Pre-intern bound variable names once before the loop.
    // For sc's <<x,y>> pattern, this avoids 2 × 36 = 72 Arc allocations per state.
    let pre = PreInternedBound::from_bound(bound);
    let is_simple = !matches!(&bound.pattern, Some(BoundPattern::Tuple(_)));

    if is_simple {
        // Part of #3073: Push once, update in-place for subsequent iterations.
        // Saves (N-1) Arc<BindingNode> alloc/dealloc pairs per function construction.
        let mut first_iter = true;
        for elem in iter {
            if is_seq_domain {
                if elem.as_i64() == Some(expected_seq_idx) {
                    expected_seq_idx += 1;
                } else {
                    is_seq_domain = false;
                }
            }
            if first_iter {
                push_bound_var_mut_preinterned(&mut local_ctx, bound, &elem, span, Some(&pre))?;
                first_iter = false;
            } else {
                local_ctx.update_last_binding_value(elem.clone());
            }
            let val = eval(&local_ctx, body)?;
            entries.push((elem, val));
        }
        local_ctx.pop_to_mark(&mark);
    } else {
        // Tuple pattern: push/pop per iteration (multiple bindings per element)
        for elem in iter {
            if is_seq_domain {
                if elem.as_i64() == Some(expected_seq_idx) {
                    expected_seq_idx += 1;
                } else {
                    is_seq_domain = false;
                }
            }
            push_bound_var_mut_preinterned(&mut local_ctx, bound, &elem, span, Some(&pre))?;
            let val = eval(&local_ctx, body)?;
            entries.push((elem, val));
            local_ctx.pop_to_mark(&mark);
        }
    }
    // IMPORTANT: If domain is exactly {1, 2, ..., n}, create a Seq instead of Func
    // because in TLA+ sequences are functions from 1..n and sequence operations
    // (Head, Tail, Append, etc.) need to work on them.
    if entries.is_empty() {
        // Empty function is the empty sequence
        return Ok(Value::Seq(Arc::new(Vec::new().into())));
    }
    if is_seq_domain {
        // Domain is 1..n; entries were collected in key-sorted order
        let seq_values: Vec<Value> = entries.into_iter().map(|(_, v)| v).collect();
        return Ok(Value::Seq(Arc::new(seq_values.into())));
    }
    Ok(Value::Func(Arc::new(FuncValue::from_sorted_entries(
        entries,
    ))))
}

/// Evaluate [x \in S |-> expr]
pub(crate) fn eval_func_def(
    ctx: &EvalCtx,
    bounds: &[BoundVar],
    body: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    // Single-variable function
    if bounds.len() == 1 {
        let bound = &bounds[0];
        let domain_expr = bound.domain.as_ref().ok_or_else(|| EvalError::Internal {
            message: "Function definition requires bounded variable".into(),
            span,
        })?;

        let dv = eval(ctx, domain_expr)?;

        // Handle special case for Nat/Int/Real lazy functions
        if let Value::ModelValue(name) = &dv {
            return match name.as_ref() {
                "Nat" => Ok(Value::LazyFunc(Arc::new(build_lazy_func_from_ctx(
                    ctx,
                    None,
                    LazyDomain::Nat,
                    std::slice::from_ref(bound),
                    body.clone(),
                )))),
                "Int" => Ok(Value::LazyFunc(Arc::new(build_lazy_func_from_ctx(
                    ctx,
                    None,
                    LazyDomain::Int,
                    std::slice::from_ref(bound),
                    body.clone(),
                )))),
                "Real" => Ok(Value::LazyFunc(Arc::new(build_lazy_func_from_ctx(
                    ctx,
                    None,
                    LazyDomain::Real,
                    std::slice::from_ref(bound),
                    body.clone(),
                )))),
                _ => Err(EvalError::type_error("Set", &dv, Some(domain_expr.span))),
            };
        }

        // Handle TupleSet (Cartesian product) with potentially infinite components
        if let Value::TupleSet(ts) = &dv {
            let mut component_domains = Vec::new();
            let mut has_infinite = false;

            for comp in ts.components_iter() {
                let comp_domain = match comp {
                    Value::ModelValue(name) => match name.as_ref() {
                        "Nat" => {
                            has_infinite = true;
                            ComponentDomain::Nat
                        }
                        "Int" => {
                            has_infinite = true;
                            ComponentDomain::Int
                        }
                        "Real" => {
                            has_infinite = true;
                            ComponentDomain::Real
                        }
                        _ => {
                            return Err(EvalError::type_error("Set", comp, Some(domain_expr.span)));
                        }
                    },
                    Value::StringSet => {
                        has_infinite = true;
                        ComponentDomain::String
                    }
                    other => {
                        let d = other.to_sorted_set().ok_or_else(|| {
                            EvalError::type_error("Set", other, Some(domain_expr.span))
                        })?;
                        let _ = d.as_slice();
                        ComponentDomain::Finite(d)
                    }
                };
                component_domains.push(comp_domain);
            }

            if has_infinite {
                return Ok(Value::LazyFunc(Arc::new(build_lazy_func_from_ctx(
                    ctx,
                    None,
                    LazyDomain::Product(component_domains),
                    std::slice::from_ref(bound),
                    body.clone(),
                ))));
            }
        }

        // Optimization: Use IntIntervalFunc for integer interval domains
        if let Value::Interval(intv) = &dv {
            if let (Some(min), Some(max)) = (intv.low().to_i64(), intv.high().to_i64()) {
                let size = interval_len_for_bounds_check(min, max);
                if size <= 1_000_000 {
                    let mut local_ctx = ctx.clone();
                    let mark = local_ctx.mark_stack();
                    let pre = PreInternedBound::from_bound(bound);
                    let mut values = Vec::with_capacity(size);
                    let mut first_iter = true;
                    for i in min..=max {
                        let elem = Value::SmallInt(i);
                        if first_iter {
                            push_bound_var_mut_preinterned(
                                &mut local_ctx,
                                bound,
                                &elem,
                                span,
                                Some(&pre),
                            )?;
                            first_iter = false;
                        } else {
                            local_ctx.update_last_binding_value(elem);
                        }
                        let val = eval(&local_ctx, body)?;
                        values.push(val);
                    }
                    local_ctx.pop_to_mark(&mark);
                    if min == 1 {
                        return Ok(Value::Seq(Arc::new(values.into())));
                    }
                    return Ok(Value::IntFunc(Arc::new(IntIntervalFunc::new(
                        min, max, values,
                    ))));
                }
            }
        }

        // Handle all set-like types
        if dv.is_set() {
            if matches!(&dv, Value::SetPred(_)) {
                let iter = eval_iter_set(ctx, &dv, Some(domain_expr.span))?;
                return eval_eager_single_var_function(ctx, bound, body, span, iter);
            }

            if let Some(iter) = dv.clone().iter_set() {
                return eval_eager_single_var_function(ctx, bound, body, span, iter);
            }

            return Ok(Value::LazyFunc(Arc::new(build_lazy_func_from_ctx(
                ctx,
                None,
                LazyDomain::General(Box::new(dv)),
                std::slice::from_ref(bound),
                body.clone(),
            ))));
        }

        return Err(EvalError::type_error("Set", &dv, Some(domain_expr.span)));
    }

    // Multi-variable function: [x \in S, y \in T |-> e]
    let mut domain_values: Vec<Value> = Vec::with_capacity(bounds.len());
    let mut finite_domains: Vec<Option<SortedSet>> = Vec::with_capacity(bounds.len());
    let mut all_enumerable = true;

    for bound in bounds {
        let domain_expr = bound.domain.as_ref().ok_or_else(|| EvalError::Internal {
            message: "Function definition requires bounded variable".into(),
            span,
        })?;
        let dv = eval(ctx, domain_expr)?;

        if !dv.is_set() {
            return Err(EvalError::type_error("Set", &dv, Some(domain_expr.span)));
        }

        let sorted = dv.to_sorted_set().map(|domain| {
            let _ = domain.as_slice();
            domain
        });
        if sorted.is_none() {
            all_enumerable = false;
        }

        domain_values.push(dv);
        finite_domains.push(sorted);
    }

    if !all_enumerable {
        let mut component_domains: Vec<ComponentDomain> = Vec::with_capacity(bounds.len());
        let mut can_use_product = true;

        for (dv, ord) in domain_values.iter().zip(finite_domains.iter()) {
            let comp = match dv {
                Value::ModelValue(name) => match name.as_ref() {
                    "Nat" => ComponentDomain::Nat,
                    "Int" => ComponentDomain::Int,
                    "Real" => ComponentDomain::Real,
                    _ => {
                        can_use_product = false;
                        break;
                    }
                },
                Value::StringSet => ComponentDomain::String,
                _ => match ord {
                    Some(s) => ComponentDomain::Finite(s.clone()),
                    None => {
                        can_use_product = false;
                        break;
                    }
                },
            };
            component_domains.push(comp);
        }

        let domain = if can_use_product {
            LazyDomain::Product(component_domains)
        } else {
            LazyDomain::General(Box::new(Value::tuple_set(domain_values.clone())))
        };

        return Ok(Value::LazyFunc(Arc::new(build_lazy_func_from_ctx(
            ctx,
            None,
            domain,
            bounds,
            (*body).clone(),
        ))));
    }

    // All domains are finite + enumerable - eagerly compute the function.
    let finite_domains: Vec<SortedSet> = finite_domains
        .into_iter()
        .map(|d| {
            d.ok_or_else(|| EvalError::Internal {
                message: "Expected enumerable domain while evaluating multi-variable function"
                    .into(),
                span,
            })
        })
        .collect::<EvalResult<_>>()?;

    let domain_refs: Vec<_> = finite_domains.iter().collect();
    let product_val = cartesian_product(&domain_refs);
    let product_set = match &product_val {
        Value::Set(set) => set,
        _ => {
            return Err(EvalError::Internal {
                message: "Cartesian product of finite domains should be enumerable".into(),
                span,
            });
        }
    };

    let mut local_ctx = ctx.clone();
    let mark = local_ctx.mark_stack();
    let pre_bounds: Vec<_> = bounds.iter().map(PreInternedBound::from_bound).collect();
    let mut entries: Vec<(Value, Value)> = Vec::with_capacity(product_set.len());
    for tuple_val in product_set.iter() {
        let tuple = tuple_val.as_tuple().ok_or_else(|| EvalError::Internal {
            message: "Cartesian product element should be a tuple".into(),
            span,
        })?;
        for (i, bound) in bounds.iter().enumerate() {
            push_bound_var_mut_preinterned(
                &mut local_ctx,
                bound,
                &tuple[i],
                span,
                Some(&pre_bounds[i]),
            )?;
        }
        let val = eval(&local_ctx, body)?;
        entries.push((tuple_val.clone(), val));
        local_ctx.pop_to_mark(&mark);
    }

    Ok(Value::Func(Arc::new(FuncValue::from_sorted_entries(
        entries,
    ))))
}
