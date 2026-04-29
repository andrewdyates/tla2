// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Quantifier constraint extraction (\E / \A) from Init predicates.
//! Extracted from init_constraints.rs to keep that file under 500 lines.

use super::{as_dummy_filter, bool_constraint, extract_constraints_rec};
use super::{Constraint, EvalCtx, Value};
use std::sync::Arc;
use tla_core::ast::{BoundVar, Expr, OperatorDef};
use tla_core::{Span, Spanned};
use tla_eval::tir::TirProgram;

use super::eval_helpers::{
    eval_bool_for_init, eval_for_init, eval_iter_set_for_init, substitute_bound_var,
    substitute_bound_var_with_expr,
};
use crate::enumerate::value_to_expr;

pub(super) fn extract_exists_single_bound(
    ctx: &EvalCtx,
    bound_var: &BoundVar,
    body: &Spanned<Expr>,
    vars: &[Arc<str>],
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    let domain = bound_var.domain.as_ref()?;
    let domain_val = eval_for_init(ctx, domain, "extract_exists_single_bound", tir)?;
    // Part of #1828: use eval_iter_set for SetPred-aware iteration.
    let domain_elems: Vec<Value> = eval_iter_set_for_init(
        ctx,
        &domain_val,
        Some(domain.span),
        "extract_exists_single_bound",
    )?
    .collect();

    let mut all_branches = Vec::new();
    for val in domain_elems {
        // Part of #3361: clear TIR expression cache between substitution iterations.
        // SubstituteExpr preserves source spans, so expressions in different iterations
        // share the same Span key despite having different AST content (the substituted
        // bound variable differs). Without clearing, the TIR cache returns stale lowered
        // TIR from a prior iteration, producing wrong evaluation results.
        if let Some(tir) = tir {
            tir.clear_expr_cache();
        }
        // Fix #3674: clear AST eval caches between iterations. eval_for_init() uses
        // eval() (not eval_entry()), so no cache lifecycle management occurs during
        // constraint extraction. Operator caches (ZERO_ARG_OP_CACHE, NARY_OP_CACHE,
        // CONST_LET_CACHE, etc.) populated while evaluating the substituted expression
        // for one domain value can return stale results for a different domain value,
        // since SubstituteExpr(SpanPolicy::Preserve) preserves source spans. This
        // caused YoYoAllGraphs to produce states where `incoming` and `outgoing` were
        // derived from different Nbrs values — a soundness violation.
        crate::eval::clear_for_eval_scope_boundary();
        let substituted = substitute_bound_var(&body.node, &bound_var.name.node, &val);
        if let Some(branches) = extract_constraints_rec(ctx, &substituted, vars, tir) {
            all_branches.extend(branches);
        } else {
            return None;
        }
    }

    if all_branches.is_empty() {
        Some(Vec::new())
    } else {
        Some(all_branches)
    }
}

pub(super) fn extract_exists_two_bounds(
    ctx: &EvalCtx,
    bound_var_0: &BoundVar,
    bound_var_1: &BoundVar,
    body: &Spanned<Expr>,
    vars: &[Arc<str>],
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    let domain0 = bound_var_0.domain.as_ref()?;
    let domain1 = bound_var_1.domain.as_ref()?;

    let domain_val0 = eval_for_init(ctx, domain0, "extract_exists_two_bounds", tir)?;
    // Part of #1828: use eval_iter_set for SetPred-aware iteration.
    let domain_elems0: Vec<_> = eval_iter_set_for_init(
        ctx,
        &domain_val0,
        Some(domain0.span),
        "extract_exists_two_bounds",
    )?
    .collect();

    let mut all_branches = Vec::new();
    for val0 in &domain_elems0 {
        // Part of #3361: clear TIR expression cache between outer substitution iterations.
        if let Some(tir) = tir {
            tir.clear_expr_cache();
        }
        // Fix #3674: clear AST eval caches between outer iterations (see single_bound).
        crate::eval::clear_for_eval_scope_boundary();
        let substituted0 = substitute_bound_var(&body.node, &bound_var_0.name.node, val0);
        let domain_val1 = eval_for_init(ctx, domain1, "extract_exists_two_bounds", tir)?;
        // Part of #1828: use eval_iter_set for SetPred-aware iteration.
        let domain_elems1: Vec<Value> = eval_iter_set_for_init(
            ctx,
            &domain_val1,
            Some(domain1.span),
            "extract_exists_two_bounds",
        )?
        .collect();

        for val1 in domain_elems1 {
            // Part of #3361: clear TIR expression cache between inner substitution iterations.
            if let Some(tir) = tir {
                tir.clear_expr_cache();
            }
            // Fix #3674: clear AST eval caches between inner iterations (see single_bound).
            crate::eval::clear_for_eval_scope_boundary();
            let substituted = substitute_bound_var(&substituted0, &bound_var_1.name.node, &val1);
            if let Some(branches) = extract_constraints_rec(ctx, &substituted, vars, tir) {
                all_branches.extend(branches);
            } else {
                return None;
            }
        }
    }

    if all_branches.is_empty() {
        Some(Vec::new())
    } else {
        Some(all_branches)
    }
}

pub(super) fn extract_exists_constraints(
    ctx: &EvalCtx,
    bound_vars: &[BoundVar],
    body: &Spanned<Expr>,
    vars: &[Arc<str>],
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    if bound_vars.len() == 1 {
        return extract_exists_single_bound(ctx, &bound_vars[0], body, vars, tir);
    }
    if bound_vars.len() == 2 {
        return extract_exists_two_bounds(ctx, &bound_vars[0], &bound_vars[1], body, vars, tir);
    }
    None
}

/// Expand `\A x \in S : body(x)` into the conjunction `body(v1) /\ body(v2) /\ ...`
/// when the domain S is a small constant set. This enables per-conjunct dependency
/// tracking for early filter pruning during init enumeration.
///
/// Part of #129: ISpec pattern performance. Without expansion, the entire ForAll
/// becomes a single Filter constraint depending on ALL state variables, preventing
/// early pruning. With expansion, individual conjuncts from the body can be evaluated
/// as soon as their specific variable dependencies are bound.
pub(super) fn extract_forall_constraints(
    ctx: &EvalCtx,
    bound_vars: &[BoundVar],
    body: &Spanned<Expr>,
    vars: &[Arc<str>],
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    // Only handle single bound variable for now.
    if bound_vars.len() != 1 {
        return None;
    }
    let bound_var = &bound_vars[0];
    let domain = bound_var.domain.as_ref()?;
    let domain_val = eval_for_init(ctx, domain, "extract_forall_constraints", tir)?;
    let domain_elems: Vec<Value> = eval_iter_set_for_init(
        ctx,
        &domain_val,
        Some(domain.span),
        "extract_forall_constraints",
    )?
    .collect();

    // Limit expansion to small domains to avoid combinatorial blowup.
    const MAX_FORALL_EXPANSION: usize = 20;
    if domain_elems.is_empty() {
        // \A x \in {} : P is vacuously true.
        return Some(vec![vec![]]);
    }
    if domain_elems.len() > MAX_FORALL_EXPANSION {
        return None;
    }

    // Expand: substitute each domain element and extract constraints.
    // ForAll is conjunction, so we cross-product all branches.
    let mut accumulated: Vec<Vec<Constraint>> = vec![vec![]]; // Start with one empty branch.
    for val in &domain_elems {
        // Part of #3361: clear TIR expression cache between substitution iterations.
        if let Some(tir) = tir {
            tir.clear_expr_cache();
        }
        // Fix #3674: clear AST eval caches between iterations (see single_bound).
        crate::eval::clear_for_eval_scope_boundary();
        let substituted = substitute_bound_var(&body.node, &bound_var.name.node, val);
        let branches = extract_constraints_rec(ctx, &substituted, vars, tir)?;

        // Cross-product: for each existing accumulated branch, combine with each new branch.
        let mut new_accumulated = Vec::with_capacity(accumulated.len() * branches.len());
        for acc_branch in &accumulated {
            for new_branch in &branches {
                let mut merged = acc_branch.clone();
                merged.extend(new_branch.iter().cloned());
                new_accumulated.push(merged);
            }
        }
        accumulated = new_accumulated;

        // Safety: bail if branch count grows too large.
        if accumulated.len() > 10_000 {
            return None;
        }
    }

    Some(accumulated)
}

pub(super) fn extract_let_constraints(
    ctx: &EvalCtx,
    expr: &Expr,
    defs: &[OperatorDef],
    body: &Spanned<Expr>,
    vars: &[Arc<str>],
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    let spanned_let = Spanned {
        node: expr.clone(),
        span: Span::dummy(),
    };
    if let Some(b) = eval_bool_for_init(ctx, &spanned_let, "extract_let_constraints", tir) {
        return bool_constraint(b);
    }

    let mut substitutions: Vec<(String, Expr)> = Vec::new();
    let mut inlined_body = body.node.clone();

    for def in defs {
        let mut def_body = def.body.node.clone();
        for (name, replacement) in &substitutions {
            def_body = substitute_bound_var_with_expr(&def_body, name, replacement);
        }

        if def.params.is_empty() {
            let def_spanned = Spanned {
                node: def_body.clone(),
                span: def.body.span,
            };
            if let Some(value) = eval_for_init(ctx, &def_spanned, "extract_let_constraints", tir) {
                substitutions.push((def.name.node.clone(), value_to_expr(&value)));
            } else {
                substitutions.push((def.name.node.clone(), def_body));
            }
        } else {
            substitutions.push((def.name.node.clone(), def_body));
        }
    }

    for (name, replacement) in &substitutions {
        inlined_body = substitute_bound_var_with_expr(&inlined_body, name, replacement);
    }

    if let Some(constraints) = extract_constraints_rec(ctx, &inlined_body, vars, tir) {
        return Some(constraints);
    }

    as_dummy_filter(expr)
}

pub(super) fn extract_default_constraints(
    ctx: &EvalCtx,
    expr: &Expr,
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    let spanned_expr = Spanned {
        node: expr.clone(),
        span: Span::dummy(),
    };
    if let Some(b) = eval_bool_for_init(ctx, &spanned_expr, "extract_default_constraints", tir) {
        return bool_constraint(b);
    }
    as_dummy_filter(expr)
}
