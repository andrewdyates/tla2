// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EXISTS quantifier enumeration helpers for unified successor enumeration.
//!
//! Handles multi-bound EXISTS expressions by recursively processing bound
//! variables and iterating over their domains. Two variants:
//! - `enumerate_exists_in_conjuncts`: EXISTS within AND conjuncts (uses continuation)
//! - `enumerate_exists`: EXISTS at top level (recurses into `enumerate_unified_inner`)
//!
//! Extracted from unified.rs as part of #2360.

use std::sync::Arc;

use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::error::EvalError;
use crate::eval::{eval_iter_set_tlc_normalized, EvalCtx};
use crate::Value;

use super::enabled_early_exit;
use super::subset_constrained::{generate_constrained_subsets, match_constrained_subset_exists};
use super::subset_profile;
use super::tir_leaf::eval_leaf;
use super::unified::{enumerate_conjuncts, enumerate_unified_inner, Cont, EnumMut, EnumParams};

pub(super) struct ConstrainedSubsetRuntime {
    pub(super) var_name: Arc<str>,
    pub(super) values: Vec<Value>,
    pub(super) remaining_body: Option<Spanned<Expr>>,
}

pub(super) fn try_collect_constrained_subset_values(
    ctx: &mut EvalCtx,
    bound: &tla_core::ast::BoundVar,
    body: &Spanned<Expr>,
    working_values: &[Value],
    p: &EnumParams<'_>,
) -> Result<Option<ConstrainedSubsetRuntime>, EvalError> {
    let Some(domain_expr) = bound.domain.as_ref() else {
        return Ok(None);
    };

    let var_name: Arc<str> = Arc::from(bound.name.node.as_str());
    let Some(pattern) = match_constrained_subset_exists(var_name.as_ref(), domain_expr, body)
    else {
        return Ok(None);
    };

    subset_profile::record_entry();

    let base_set = eval_leaf(ctx, pattern.base_set_expr, p.tir_leaf)?;
    let base_elements: Vec<Value> =
        eval_iter_set_tlc_normalized(ctx, &base_set, Some(pattern.base_set_expr.span))?.collect();

    let superset_bound = {
        let _env = ctx.bind_next_state_array_guard(working_values);
        eval_leaf(ctx, pattern.superset_expr, p.tir_leaf)?
    };
    let subset_bound = {
        let _env = ctx.bind_next_state_array_guard(working_values);
        eval_leaf(ctx, pattern.subset_expr, p.tir_leaf)?
    };

    let Some(values) = generate_constrained_subsets(&base_elements, &superset_bound, &subset_bound)
    else {
        return Ok(None);
    };

    Ok(Some(ConstrainedSubsetRuntime {
        var_name,
        values,
        remaining_body: pattern.remaining_body,
    }))
}

pub(super) fn iterate_exists_values_in_conjuncts(
    ctx: &mut EvalCtx,
    var_name: Arc<str>,
    values: Vec<Value>,
    body: Option<&Spanned<Expr>>,
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    let acc_len = m.accumulated.len();
    let save_point = m.rec.undo.len();
    let saved_mask = m.assigned_mask;
    let saved_complex = m.has_complex;

    // Part of #3893: mark/restore replaces ctx.clone() per iteration.
    // EnumMark captures all mutable EvalCtx fields (bindings, let_def_overlay,
    // stable Rc, call_by_name_subs) so that LET scope mutations during body
    // evaluation are correctly discarded between iterations.
    let enum_mark = ctx.mark_enum();

    for value in values {
        ctx.push_binding(Arc::clone(&var_name), value);

        let result = match body {
            Some(body) => enumerate_conjuncts(ctx, c, Some(body), p, m),
            None => enumerate_conjuncts(ctx, c, None, p, m),
        };
        match result {
            Ok(()) => {}
            Err(err) => {
                ctx.pop_to_enum_mark(&enum_mark);
                m.rec
                    .working
                    .unbind_to_no_invalidate(m.rec.undo, save_point);
                return Err(err);
            }
        }

        ctx.pop_to_enum_mark(&enum_mark);
        m.accumulated.truncate(acc_len);
        m.rec
            .working
            .unbind_to_no_invalidate(m.rec.undo, save_point);
        m.assigned_mask = saved_mask;
        m.has_complex = saved_complex;

        if enabled_early_exit() && m.rec.results.has_results() {
            break;
        }
        if m.rec.results.is_stopped() {
            break;
        }
    }

    Ok(())
}

fn iterate_exists_values_top_level(
    ctx: &mut EvalCtx,
    var_name: Arc<str>,
    values: Vec<Value>,
    body: Option<&Spanned<Expr>>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    let save_point = m.rec.undo.len();

    // Part of #3893: mark/restore replaces ctx.clone() per iteration.
    let enum_mark = ctx.mark_enum();

    for value in values {
        ctx.push_binding(Arc::clone(&var_name), value);

        let result = match body {
            Some(body) => enumerate_unified_inner(ctx, body, p, &mut m.rec),
            None => {
                let empty: [&Spanned<Expr>; 0] = [];
                let cont = Cont {
                    conjuncts: &empty,
                    next_idx: 0,
                    scope_restore: None,
                };
                enumerate_conjuncts(ctx, &cont, None, p, m)
            }
        };
        match result {
            Ok(()) => {}
            Err(err) => {
                ctx.pop_to_enum_mark(&enum_mark);
                m.rec
                    .working
                    .unbind_to_no_invalidate(m.rec.undo, save_point);
                return Err(err);
            }
        }

        ctx.pop_to_enum_mark(&enum_mark);
        m.rec
            .working
            .unbind_to_no_invalidate(m.rec.undo, save_point);

        if enabled_early_exit() && m.rec.results.has_results() {
            break;
        }
        if m.rec.results.is_stopped() {
            break;
        }
    }

    Ok(())
}

/// Pre-compute `Arc<str>` for all bound variable names.
///
/// Part of #3900: avoids repeated `Arc::from` heap allocations on each
/// recursive level of multi-bound EXISTS enumeration.
fn intern_bound_names(bounds: &[tla_core::ast::BoundVar]) -> Vec<Arc<str>> {
    bounds
        .iter()
        .map(|b| Arc::from(b.name.node.as_str()))
        .collect()
}

/// Handle multi-bound EXISTS within conjuncts by recursively processing bounds.
///
/// Part of #3893: Uses EnumMark (mark/restore) instead of clone-at-branch.
/// EnumMark captures all mutable EvalCtx fields including stable Rc (which
/// holds local_ops), let_def_overlay, and call_by_name_subs — making
/// mark/restore safe even when the body contains LET with scope_restore.
///
/// Part of #3900: pre-computes Arc<str> for all bound variable names once at
/// entry, avoiding repeated Arc::from allocations on each recursive level.
pub(super) fn enumerate_exists_in_conjuncts(
    ctx: &mut EvalCtx,
    bounds: &[tla_core::ast::BoundVar],
    bound_idx: usize,
    body: &Spanned<Expr>,
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    let bound_names = intern_bound_names(bounds);
    enumerate_exists_in_conjuncts_inner(ctx, bounds, &bound_names, bound_idx, body, c, p, m)
}

fn enumerate_exists_in_conjuncts_inner(
    ctx: &mut EvalCtx,
    bounds: &[tla_core::ast::BoundVar],
    bound_names: &[Arc<str>],
    bound_idx: usize,
    body: &Spanned<Expr>,
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    crate::eval::stack_safe(|| {
        if bound_idx >= bounds.len() {
            // All bounds processed — continue with body + remaining conjuncts
            return enumerate_conjuncts(ctx, c, Some(body), p, m);
        }

        let bound = &bounds[bound_idx];
        // Part of #3900: reuse pre-computed Arc<str> instead of Arc::from per level.
        let var_name = Arc::clone(&bound_names[bound_idx]);

        let domain = match &bound.domain {
            // Part of #3194: use eval_leaf to try TIR for EXISTS domain expressions.
            Some(domain_expr) => eval_leaf(ctx, domain_expr, p.tir_leaf)?,
            None => {
                return Err(EvalError::Internal {
                    message: "enumerate_exists_in_conjuncts: unbounded EXISTS".to_string(),
                    span: None,
                })
            }
        };

        // TLC parity (#2328): iterate EXISTS domains in TLC-normalized order.
        let domain_elems: Vec<Value> =
            eval_iter_set_tlc_normalized(ctx, &domain, bound.domain.as_ref().map(|d| d.span))?
                .collect();

        let acc_len = m.accumulated.len();
        let save_point = m.rec.undo.len();
        let saved_mask = m.assigned_mask;
        let saved_complex = m.has_complex;

        // Part of #3893: mark/restore replaces ctx.clone() per iteration.
        let enum_mark = ctx.mark_enum();

        for val in domain_elems {
            ctx.push_binding(Arc::clone(&var_name), val);

            match enumerate_exists_in_conjuncts_inner(
                ctx,
                bounds,
                bound_names,
                bound_idx + 1,
                body,
                c,
                p,
                m,
            ) {
                Ok(()) => {}
                Err(e) => {
                    ctx.pop_to_enum_mark(&enum_mark);
                    m.rec
                        .working
                        .unbind_to_no_invalidate(m.rec.undo, save_point);
                    return Err(e);
                }
            }

            ctx.pop_to_enum_mark(&enum_mark);
            m.accumulated.truncate(acc_len);
            m.rec
                .working
                .unbind_to_no_invalidate(m.rec.undo, save_point);
            m.assigned_mask = saved_mask;
            m.has_complex = saved_complex;

            // Part of #1285: ENABLED early-exit — stop iterating domain values.
            if enabled_early_exit() && m.rec.results.has_results() {
                break;
            }
            // Part of #3027: Early termination — stop domain iteration if sink stopped.
            if m.rec.results.is_stopped() {
                break;
            }
        }

        Ok(())
    })
}

/// Handle multi-bound EXISTS at top level (not within AND conjuncts).
///
/// Part of #3900: pre-computes Arc<str> for all bound variable names once at
/// entry, avoiding repeated Arc::from allocations on each recursive level.
pub(super) fn enumerate_exists(
    ctx: &mut EvalCtx,
    bounds: &[tla_core::ast::BoundVar],
    bound_idx: usize,
    body: &Spanned<Expr>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    let bound_names = intern_bound_names(bounds);
    enumerate_exists_inner(ctx, bounds, &bound_names, bound_idx, body, p, m)
}

fn enumerate_exists_inner(
    ctx: &mut EvalCtx,
    bounds: &[tla_core::ast::BoundVar],
    bound_names: &[Arc<str>],
    bound_idx: usize,
    body: &Spanned<Expr>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    crate::eval::stack_safe(|| {
        if bound_idx >= bounds.len() {
            // All bounds processed — recurse into body
            return enumerate_unified_inner(ctx, body, p, &mut m.rec);
        }

        let bound = &bounds[bound_idx];
        if bound_idx == 0 && bounds.len() == 1 {
            if let Some(constrained) = try_collect_constrained_subset_values(
                ctx,
                bound,
                body,
                &m.rec.working.materialize_values(),
                p,
            )? {
                return iterate_exists_values_top_level(
                    ctx,
                    constrained.var_name,
                    constrained.values,
                    constrained.remaining_body.as_ref(),
                    p,
                    m,
                );
            }
        }

        // Part of #3900: reuse pre-computed Arc<str> instead of Arc::from per level.
        let var_name = Arc::clone(&bound_names[bound_idx]);

        let domain = match &bound.domain {
            // Part of #3194: use eval_leaf to try TIR for EXISTS domain expressions.
            Some(domain_expr) => eval_leaf(ctx, domain_expr, p.tir_leaf)?,
            None => {
                return Err(EvalError::Internal {
                    message: "enumerate_exists: unbounded EXISTS".to_string(),
                    span: None,
                })
            }
        };

        // TLC parity (#2328): iterate EXISTS domains in TLC-normalized order.
        let domain_elems: Vec<Value> =
            eval_iter_set_tlc_normalized(ctx, &domain, bound.domain.as_ref().map(|d| d.span))?
                .collect();

        let save_point = m.rec.undo.len();

        // Part of #3893: mark/restore replaces ctx.clone() per iteration.
        let enum_mark = ctx.mark_enum();

        for val in domain_elems {
            ctx.push_binding(Arc::clone(&var_name), val);

            match enumerate_exists_inner(
                ctx,
                bounds,
                bound_names,
                bound_idx + 1,
                body,
                p,
                m,
            ) {
                Ok(()) => {}
                Err(e) => {
                    ctx.pop_to_enum_mark(&enum_mark);
                    m.rec
                        .working
                        .unbind_to_no_invalidate(m.rec.undo, save_point);
                    return Err(e);
                }
            }

            ctx.pop_to_enum_mark(&enum_mark);
            m.rec
                .working
                .unbind_to_no_invalidate(m.rec.undo, save_point);

            // Part of #1285: ENABLED early-exit — stop iterating domain values.
            if enabled_early_exit() && m.rec.results.has_results() {
                break;
            }
            // Part of #3027: Early termination — stop domain iteration if sink stopped.
            if m.rec.results.is_stopped() {
                break;
            }
        }

        Ok(())
    })
}
