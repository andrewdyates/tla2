// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod condition;
mod eval_helpers;
mod quantifiers;

use super::{apply_substitutions, compose_substitutions, Constraint, EvalCtx, OpEnv, Value};
use std::sync::Arc;
use tla_core::ast::{Expr, ModuleTarget, Substitution};
use tla_core::inlining_is_capture_safe;
use tla_core::Span;
use tla_core::Spanned;
use tla_eval::tir::TirProgram;

pub use condition::extract_conjunction_remainder;
use condition::{extract_constraint_from_condition, negate_condition, prepend_constraint};
pub(crate) use eval_helpers::count_expr_nodes;
use eval_helpers::{
    eval_bool_for_init, eval_for_init, init_domain_from_value, substitute_params, MAX_EXPR_NODES,
};

/// Extract constraints from an Init predicate expression.
///
/// Returns a list of constraints that can be used to generate initial states.
/// If the predicate cannot be analyzed, returns None.
/// Part of #3194: uses TIR leaf eval when `tir` is `Some`.
pub fn extract_init_constraints(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    vars: &[Arc<str>],
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    // Bail out early for complex expressions to prevent stack overflow
    if count_expr_nodes(&expr.node) > MAX_EXPR_NODES {
        return None;
    }
    extract_constraints_rec(ctx, &expr.node, vars, tir)
}

fn extract_constraints_rec(
    ctx: &EvalCtx,
    expr: &Expr,
    vars: &[Arc<str>],
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    // Use stack_safe to grow stack on demand for deeply nested expressions.
    crate::eval::stack_safe(|| extract_constraints_rec_inner(ctx, expr, vars, tir))
}

fn as_filter_constraint(expr: &Expr, span: Span) -> Option<Vec<Vec<Constraint>>> {
    Some(vec![vec![Constraint::Filter(Box::new(Spanned {
        node: expr.clone(),
        span,
    }))]])
}

fn as_dummy_filter(expr: &Expr) -> Option<Vec<Vec<Constraint>>> {
    as_filter_constraint(expr, Span::dummy())
}

fn bool_constraint(b: bool) -> Option<Vec<Vec<Constraint>>> {
    if b {
        Some(vec![Vec::new()])
    } else {
        Some(Vec::new())
    }
}

/// O(1) state variable membership test via VarRegistry.
fn is_state_var(name: &str, ctx: &EvalCtx) -> bool {
    ctx.var_registry().get(name).is_some()
}

fn extract_eq_constraints(
    ctx: &EvalCtx,
    expr: &Expr,
    lhs: &Spanned<Expr>,
    rhs: &Spanned<Expr>,
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &lhs.node {
        if is_state_var(name, ctx) {
            if let Some(value) = eval_for_init(ctx, rhs, "extract_eq_constraints", tir) {
                return Some(vec![vec![Constraint::Eq(name.clone(), value)]]);
            }
            return Some(vec![vec![Constraint::Deferred(
                name.clone(),
                Box::new(rhs.clone()),
            )]]);
        }
    }

    if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &rhs.node {
        if is_state_var(name, ctx) {
            if let Some(value) = eval_for_init(ctx, lhs, "extract_eq_constraints", tir) {
                return Some(vec![vec![Constraint::Eq(name.clone(), value)]]);
            }
            return Some(vec![vec![Constraint::Deferred(
                name.clone(),
                Box::new(lhs.clone()),
            )]]);
        }
    }

    as_filter_constraint(expr, lhs.span)
}

fn extract_neq_constraints(
    ctx: &EvalCtx,
    expr: &Expr,
    lhs: &Spanned<Expr>,
    rhs: &Spanned<Expr>,
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &lhs.node {
        if is_state_var(name, ctx) {
            if let Some(value) = eval_for_init(ctx, rhs, "extract_neq_constraints", tir) {
                return Some(vec![vec![Constraint::NotEq(name.clone(), value)]]);
            }
        }
    }

    if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &rhs.node {
        if is_state_var(name, ctx) {
            if let Some(value) = eval_for_init(ctx, lhs, "extract_neq_constraints", tir) {
                return Some(vec![vec![Constraint::NotEq(name.clone(), value)]]);
            }
        }
    }

    as_filter_constraint(expr, lhs.span)
}

fn extract_in_constraints(
    ctx: &EvalCtx,
    expr: &Expr,
    lhs: &Spanned<Expr>,
    rhs: &Spanned<Expr>,
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &lhs.node {
        if is_state_var(name, ctx) {
            if let Some(set_val) = eval_for_init(ctx, rhs, "extract_in_constraints", tir) {
                if let Some(domain) =
                    init_domain_from_value(ctx, set_val, Some(rhs.span), "extract_in_constraints")
                {
                    return Some(vec![vec![Constraint::In(name.clone(), domain)]]);
                }
            }
            return Some(vec![vec![Constraint::DeferredIn(
                name.clone(),
                Box::new(rhs.clone()),
            )]]);
        }
    }

    as_filter_constraint(expr, lhs.span)
}

fn extract_not_constraints(
    ctx: &EvalCtx,
    expr: &Expr,
    inner: &Spanned<Expr>,
    vars: &[Arc<str>],
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    if let Some(inner_branches) = extract_constraints_rec(ctx, &inner.node, vars, tir) {
        if inner_branches.is_empty() {
            return Some(vec![Vec::new()]);
        }
        if inner_branches.len() == 1 && inner_branches[0].is_empty() {
            return Some(Vec::new());
        }
    }

    if let Some(b) = eval_bool_for_init(ctx, inner, "extract_not_constraints", tir) {
        return bool_constraint(!b);
    }

    as_dummy_filter(expr)
}

fn extract_apply_constraints(
    ctx: &EvalCtx,
    expr: &Expr,
    op_expr: &Spanned<Expr>,
    args: &[Spanned<Expr>],
    vars: &[Arc<str>],
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    if let Expr::Ident(name, _) = &op_expr.node {
        let resolved_name = ctx.resolve_op_name(name);
        if let Some(def) = ctx.get_op(resolved_name) {
            if def.params.len() == args.len() {
                // Part of #2575: Don't inline self-recursive operators — their
                // bodies reference themselves, causing infinite recursion during
                // constraint extraction. Treat as a filter instead; the evaluator
                // handles RECURSIVE operators correctly at runtime.
                if tla_core::free_vars(&def.body.node).contains(resolved_name) {
                    return as_dummy_filter(expr);
                }
                if args.is_empty() {
                    return extract_constraints_rec(ctx, &def.body.node, vars, tir);
                }
                if inlining_is_capture_safe(def, args) {
                    let body = substitute_params(&def.body.node, &def.params, args);
                    return extract_constraints_rec(ctx, &body, vars, tir);
                }
            }
        }
    }

    // Never evaluate builtin calls during extraction: keep TLC side-effects/order.
    as_dummy_filter(expr)
}

fn extract_ident_constraints(
    ctx: &EvalCtx,
    expr: &Expr,
    name: &str,
    vars: &[Arc<str>],
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    if is_state_var(name, ctx) {
        return as_dummy_filter(expr);
    }

    // Resolve through config replacements (e.g., TypeOK -> MCTypeOK) so that
    // constraint extraction uses the replacement body, not the original.
    let resolved_name = ctx.resolve_op_name(name);
    if let Some(def) = ctx.get_op(resolved_name) {
        if def.params.is_empty() {
            // Part of #2575: Don't inline self-recursive operators.
            if tla_core::free_vars(&def.body.node).contains(resolved_name) {
                return as_dummy_filter(expr);
            }
            return extract_constraints_rec(ctx, &def.body.node, vars, tir);
        }
    }

    let spanned_expr = Spanned {
        node: expr.clone(),
        span: Span::dummy(),
    };
    if let Some(b) = eval_bool_for_init(ctx, &spanned_expr, "extract_ident_constraints", tir) {
        return bool_constraint(b);
    }

    None
}

fn extract_module_ref_constraints(
    ctx: &EvalCtx,
    expr: &Expr,
    instance_name: &ModuleTarget,
    op_name: &str,
    args: &[Spanned<Expr>],
    vars: &[Arc<str>],
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    if !args.is_empty() {
        return as_dummy_filter(expr);
    }

    // Conjunct selection syntax: Def!n where Def has conjunction body.
    if let (ModuleTarget::Named(base_name), Ok(conjunct_idx)) =
        (instance_name, op_name.parse::<usize>())
    {
        if conjunct_idx > 0 {
            if let Some(def) = ctx.get_op(base_name) {
                if let Expr::And(_, _) = &def.body.node {
                    let conjuncts = crate::expr_visitor::collect_conjuncts_v(&def.body);
                    let idx = conjunct_idx - 1;
                    if idx < conjuncts.len() {
                        return extract_constraints_rec(ctx, &conjuncts[idx].node, vars, tir)
                            .or_else(|| as_dummy_filter(expr));
                    }
                }
            }
        }
    }

    // Resolve instance metadata; nested instances can be local operator refs.
    let (module_name, instance_subs): (String, Vec<Substitution>) =
        if let Some(info) = ctx.get_instance(instance_name.name()) {
            (info.module_name.clone(), info.substitutions.clone())
        } else if let Some(def) = ctx.get_op(instance_name.name()) {
            match &def.body.node {
                Expr::InstanceExpr(module_name, subs) => (module_name.clone(), subs.clone()),
                _ => return as_dummy_filter(expr),
            }
        } else {
            return as_dummy_filter(expr);
        };

    let op_def = if let Some(op_def) = ctx.get_instance_op(&module_name, op_name) {
        op_def
    } else {
        return as_dummy_filter(expr);
    };

    let effective_subs = compose_substitutions(&instance_subs, ctx.instance_substitutions());
    let substituted_body = apply_substitutions(&op_def.body, &effective_subs);

    // Part of #1433: empty default is correct — modules without registered
    // instance operators simply have no local ops in scope. Not error-swallowing.
    let instance_local_ops: OpEnv = ctx
        .instance_ops()
        .get(&module_name)
        .cloned()
        .unwrap_or_default();
    let instance_ctx = ctx.with_instance_scope(instance_local_ops, effective_subs);

    extract_constraints_rec(&instance_ctx, &substituted_body.node, vars, tir)
        .or_else(|| as_dummy_filter(expr))
}

fn extract_if_constraints(
    ctx: &EvalCtx,
    cond: &Spanned<Expr>,
    then_branch: &Spanned<Expr>,
    else_branch: &Spanned<Expr>,
    vars: &[Arc<str>],
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    if let Some(cond_val) = eval_bool_for_init(ctx, cond, "extract_if_constraints", tir) {
        return if cond_val {
            extract_constraints_rec(ctx, &then_branch.node, vars, tir)
        } else {
            extract_constraints_rec(ctx, &else_branch.node, vars, tir)
        };
    }

    let then_constraints = extract_constraints_rec(ctx, &then_branch.node, vars, tir)?;
    let else_constraints = extract_constraints_rec(ctx, &else_branch.node, vars, tir)?;
    let cond_constraint = extract_constraint_from_condition(ctx, &cond.node, tir);
    let negated_constraint = negate_condition(ctx, &cond.node, tir);

    match (cond_constraint, negated_constraint) {
        (Some(cond_c), Some(neg_c)) => {
            let mut all = prepend_constraint(&then_constraints, &cond_c);
            all.extend(prepend_constraint(&else_constraints, &neg_c));
            Some(all)
        }
        (Some(cond_c), None) => {
            let mut all = prepend_constraint(&then_constraints, &cond_c);
            all.extend(else_constraints);
            Some(all)
        }
        _ => {
            let mut all = then_constraints;
            all.extend(else_constraints);
            Some(all)
        }
    }
}

use quantifiers::{
    extract_default_constraints, extract_exists_constraints, extract_forall_constraints,
    extract_let_constraints,
};

fn extract_constraints_rec_inner(
    ctx: &EvalCtx,
    expr: &Expr,
    vars: &[Arc<str>],
    tir: Option<&TirProgram<'_>>,
) -> Option<Vec<Vec<Constraint>>> {
    match expr {
        Expr::And(a, b) => {
            let left = extract_constraints_rec(ctx, &a.node, vars, tir)?;
            let right = extract_constraints_rec(ctx, &b.node, vars, tir)?;

            let mut branches: Vec<Vec<Constraint>> = Vec::new();
            for left_branch in &left {
                for right_branch in &right {
                    let mut merged = left_branch.clone();
                    merged.extend(right_branch.iter().cloned());
                    branches.push(merged);
                }
            }
            Some(branches)
        }
        Expr::Or(a, b) => {
            let mut branches = extract_constraints_rec(ctx, &a.node, vars, tir)?;
            branches.extend(extract_constraints_rec(ctx, &b.node, vars, tir)?);
            Some(branches)
        }
        Expr::Eq(lhs, rhs) => extract_eq_constraints(ctx, expr, lhs, rhs, tir),
        Expr::Neq(lhs, rhs) => extract_neq_constraints(ctx, expr, lhs, rhs, tir),
        Expr::In(lhs, rhs) => extract_in_constraints(ctx, expr, lhs, rhs, tir),
        Expr::Bool(true) => bool_constraint(true),
        Expr::Bool(false) => bool_constraint(false),
        Expr::Not(inner) => extract_not_constraints(ctx, expr, inner, vars, tir),
        Expr::Apply(op_expr, args) => {
            extract_apply_constraints(ctx, expr, op_expr, args, vars, tir)
        }
        Expr::Ident(name, _) => extract_ident_constraints(ctx, expr, name, vars, tir),
        Expr::ModuleRef(instance_name, op_name, args) => {
            extract_module_ref_constraints(ctx, expr, instance_name, op_name, args, vars, tir)
        }
        Expr::If(cond, then_branch, else_branch) => {
            extract_if_constraints(ctx, cond, then_branch, else_branch, vars, tir)
        }
        Expr::Exists(bound_vars, body) => {
            extract_exists_constraints(ctx, bound_vars, body, vars, tir)
        }
        Expr::Forall(bound_vars, body) => {
            if let Some(result) = extract_forall_constraints(ctx, bound_vars, body, vars, tir) {
                return Some(result);
            }
            as_dummy_filter(expr)
        }
        Expr::Leq(_, _)
        | Expr::Geq(_, _)
        | Expr::Lt(_, _)
        | Expr::Gt(_, _)
        | Expr::Subseteq(_, _)
        | Expr::Implies(_, _) => as_dummy_filter(expr),
        Expr::Let(defs, body) => extract_let_constraints(ctx, expr, defs, body, vars, tir),
        _ => extract_default_constraints(ctx, expr, tir),
    }
}
