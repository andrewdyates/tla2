// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Forking conjunct dispatch helpers for unified successor enumeration.
//!
//! These handlers process AND conjuncts that branch or iterate: nested AND,
//! OR disjunction, EXISTS quantification, IF conditionals, IN membership
//! enumeration, and CASE expressions. Each handler follows the continuation
//! pattern, calling back into `enumerate_conjuncts` to process remaining
//! conjuncts.
//!
//! Extracted from unified.rs as part of #2360.

use std::sync::Arc;

use smallvec::SmallVec;
use tla_core::ast::{CaseArm, Expr};
use tla_core::Spanned;

use crate::error::EvalError;
use crate::eval::{eval_iter_set_tlc_normalized, EvalCtx};
use crate::Value;

use super::expr_analysis::flatten_and_spanned;
use super::tir_leaf::eval_leaf;
use super::unified::{enumerate_conjuncts, trace_expr_tag};
use super::unified_emit::process_conjunct_guard_or_assignment;
use super::unified_exists::{
    enumerate_exists_in_conjuncts, iterate_exists_values_in_conjuncts,
    try_collect_constrained_subset_values,
};
use super::unified_types::{Cont, EnumMut, EnumParams};
use super::{case_guard_error, debug_enum_trace, SymbolicAssignment};

// ─── Conjunct dispatch helpers ───────────────────────────────────────────────

/// Nested AND within conjuncts: flatten and continue.
/// Phase H (#3073): uses references instead of cloned AST nodes.
pub(super) fn conjunct_and<'a>(
    ctx: &mut EvalCtx,
    conjunct: &'a Spanned<Expr>,
    c: &Cont<'a>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    let mut flat: SmallVec<[&Spanned<Expr>; 8]> = SmallVec::new();
    flatten_and_spanned(conjunct, &mut flat);

    if flat.is_empty() {
        return enumerate_conjuncts(ctx, c, None, p, m);
    }

    let mut new_conjuncts: SmallVec<[&Spanned<Expr>; 8]> = flat;
    new_conjuncts.extend_from_slice(&c.conjuncts[c.next_idx..]);
    enumerate_conjuncts(
        ctx,
        &Cont {
            conjuncts: &new_conjuncts,
            next_idx: 0,
            scope_restore: c.scope_restore.clone(),
        },
        None,
        p,
        m,
    )
}

/// OR within conjuncts: fork into branches, each continuing with remaining.
///
/// Clone-at-branch pattern (#2834): each branch gets a cloned EvalCtx,
/// guaranteeing the parent ctx is never mutated. This is the Rust-idiomatic
/// equivalent of TLC's immutable Context + cons() — structural isolation
/// via ownership. Eliminates the scope_restore corruption class where
/// `conjunct_let` pops LET bindings from local_stack during one branch,
/// causing "Undefined variable" errors in subsequent branches.
pub(super) fn conjunct_or(
    ctx: &mut EvalCtx,
    a: &Spanned<Expr>,
    b: &Spanned<Expr>,
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    let acc_len = m.accumulated.len();
    let save_point = m.rec.undo.len();
    let saved_mask = m.assigned_mask;
    let saved_complex = m.has_complex;

    // Part of #3893: mark/restore replaces ctx.clone() per branch.
    // EnumMark captures all mutable EvalCtx fields so LET scope
    // mutations during branch evaluation are correctly discarded.
    let enum_mark = ctx.mark_enum();

    // Left branch — mark/restore isolates all ctx state
    enumerate_conjuncts(ctx, c, Some(a), p, m)?;
    ctx.pop_to_enum_mark(&enum_mark);
    m.accumulated.truncate(acc_len);
    m.rec
        .working
        .unbind_to_no_invalidate(m.rec.undo, save_point);
    m.assigned_mask = saved_mask;
    m.has_complex = saved_complex;

    // Part of #3027: Early termination — skip right branch if sink stopped.
    if m.rec.results.is_stopped() {
        return Ok(());
    }

    // Right branch — mark already captured, ctx restored to pristine
    enumerate_conjuncts(ctx, c, Some(b), p, m)?;
    ctx.pop_to_enum_mark(&enum_mark);
    m.accumulated.truncate(acc_len);
    m.rec
        .working
        .unbind_to_no_invalidate(m.rec.undo, save_point);
    m.assigned_mask = saved_mask;
    m.has_complex = saved_complex;

    Ok(())
}

/// EXISTS within conjuncts: iterate domain, each binding continues with body + remaining.
///
/// Clone-at-branch pattern (#2834): each iteration gets a cloned EvalCtx
/// with the binding pushed. Same structural isolation as conjunct_or —
/// scope_restore cannot corrupt subsequent iterations because each
/// operates on its own clone.
pub(super) fn conjunct_exists(
    ctx: &mut EvalCtx,
    bounds: &[tla_core::ast::BoundVar],
    body: &Spanned<Expr>,
    conjunct: &Spanned<Expr>,
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    if bounds.len() != 1 {
        return enumerate_exists_in_conjuncts(ctx, bounds, 0, body, c, p, m);
    }

    let bound = &bounds[0];
    let working_values = m.rec.working.materialize_values();
    if let Some(constrained) =
        try_collect_constrained_subset_values(ctx, bound, body, &working_values, p)?
    {
        return iterate_exists_values_in_conjuncts(
            ctx,
            constrained.var_name,
            constrained.values,
            constrained.remaining_body.as_ref(),
            c,
            p,
            m,
        );
    }

    let var_name = Arc::from(bound.name.node.as_str());

    let domain = match &bound.domain {
        // Part of #3194: use eval_leaf to try TIR for EXISTS domain expressions.
        Some(domain_expr) => eval_leaf(ctx, domain_expr, p.tir_leaf)?,
        None => {
            return Err(EvalError::Internal {
                message: format!(
                    "enumerate_conjuncts: unbounded EXISTS at {:?}",
                    conjunct.span
                ),
                span: Some(conjunct.span),
            })
        }
    };

    // TLC parity (#2328): iterate EXISTS domains in TLC-normalized order.
    // The model checker's successor enumeration must match TLC's element
    // ordering so BFS exploration visits states in the same order, producing
    // identical state counts at invariant violation.
    let domain_elems: Vec<Value> =
        eval_iter_set_tlc_normalized(ctx, &domain, bound.domain.as_ref().map(|d| d.span))?
            .collect();
    iterate_exists_values_in_conjuncts(ctx, var_name, domain_elems, Some(body), c, p, m)
}

/// IF within conjuncts: evaluate condition, process chosen branch as pending.
///
/// Accepts the full IF expression and destructures internally to avoid
/// passing cond/then/else as separate parameters.
pub(super) fn conjunct_if(
    ctx: &mut EvalCtx,
    conjunct: &Spanned<Expr>,
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    let (cond, then_branch, else_branch) = match &conjunct.node {
        Expr::If(cond, then_branch, else_branch) => {
            (cond.as_ref(), then_branch.as_ref(), else_branch.as_ref())
        }
        _ => {
            return Err(EvalError::Internal {
                message: "conjunct_if called with non-If expression".to_string(),
                span: Some(conjunct.span),
            });
        }
    };

    // Part of #3194: use eval_leaf to try TIR for IF condition evaluation.
    let guard_result = {
        let _env = ctx.bind_next_state_env_guard(m.rec.working.env_ref());
        eval_leaf(ctx, cond, p.tir_leaf)
    };

    let guard = guard_result?;

    let branch = match guard.as_bool() {
        Some(true) => then_branch,
        Some(false) => else_branch,
        None => {
            return process_conjunct_guard_or_assignment(ctx, conjunct, c, p, m);
        }
    };

    enumerate_conjuncts(ctx, c, Some(branch), p, m)
}

/// IN within conjuncts: handle `x' \in S` primed membership enumeration.
pub(super) fn conjunct_in<'a>(
    ctx: &mut EvalCtx,
    lhs: &Spanned<Expr>,
    rhs: &'a Spanned<Expr>,
    conjunct: &'a Spanned<Expr>,
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    let trace = debug_enum_trace();
    if let Expr::Prime(inner_lhs) = &lhs.node {
        if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &inner_lhs.node {
            if let Some(idx) = p.registry.get(name.as_str()) {
                let var = &p.vars[idx.as_usize()];
                // O(1) bitmask check instead of O(n) linear scan over accumulated
                let already_bound = if idx.as_usize() < 64 {
                    m.assigned_mask & (1u64 << idx.as_usize()) != 0
                } else {
                    m.accumulated.iter().any(|a| match a {
                        SymbolicAssignment::Value(v, _)
                        | SymbolicAssignment::Expr(v, _, _)
                        | SymbolicAssignment::InSet(v, _, _)
                        | SymbolicAssignment::Unchanged(v) => v == var,
                    })
                };

                if already_bound {
                    if trace {
                        eprintln!(
                            "[enum-trace] level={} kind=binder tag=In var={} already-bound=true action=guard-fallback",
                            ctx.get_tlc_level(),
                            var
                        );
                    }
                    return process_conjunct_guard_or_assignment(ctx, conjunct, c, p, m);
                }

                if trace {
                    eprintln!(
                        "[enum-trace] level={} kind=binder tag=In var={} already-bound=false action=enumerate-domain",
                        ctx.get_tlc_level(),
                        var
                    );
                }
                return enumerate_in_domain(ctx, var, rhs, c, p, m);
            }
        }
    }
    // Not a primed membership — fall through to guard/assignment
    process_conjunct_guard_or_assignment(ctx, conjunct, c, p, m)
}

/// Enumerate all values in a domain set for a primed variable membership.
fn enumerate_in_domain(
    ctx: &mut EvalCtx,
    var: &Arc<str>,
    rhs: &Spanned<Expr>,
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    let trace = debug_enum_trace();
    // FIX #1482: Bind partially-constructed next state so that primed variables
    // already assigned by earlier conjuncts (e.g. opQ') are visible when
    // evaluating the domain expression (e.g. SUBSET(opId' \X opId')).
    // Without this, `eval(ctx, rhs)` fails with "Primed variable cannot be
    // evaluated" when the domain references another primed variable.
    // Part of #3194: use eval_leaf to try TIR for IN domain expression.
    let domain = {
        let _env = ctx.bind_next_state_env_guard(m.rec.working.env_ref());
        eval_leaf(ctx, rhs, p.tir_leaf)
    };
    let domain = domain?;

    if trace {
        eprintln!(
            "[enum-trace] level={} binder var={} domain-tag={} domain-type={}",
            ctx.get_tlc_level(),
            var,
            trace_expr_tag(&rhs.node),
            domain.type_name()
        );
    }

    let var_idx = p.registry.get(var);
    let saved_mask = m.assigned_mask;
    if let Some(idx) = var_idx {
        if idx.as_usize() < 64 {
            m.assigned_mask |= 1u64 << idx.as_usize();
        }
    }

    // #1482 follow-up: SetPred materialization may evaluate predicates that
    // reference primed vars (e.g., {v \in S : v = y'}), so preserve the
    // partially-built next-state binding while iterating the domain.
    // TLC parity (#2328): iterate x' \in S domains in TLC-normalized order.
    // Same rationale as conjunct_exists — BFS exploration order must match TLC.
    let domain_iter = {
        let _env = ctx.bind_next_state_env_guard(m.rec.working.env_ref());
        eval_iter_set_tlc_normalized(ctx, &domain, Some(rhs.span))
    };

    let mut domain_iter = match domain_iter {
        Ok(iter) => iter.peekable(),
        // Non-enumerable domain (value is not a Set type): produce no
        // successors. Matches TLC behavior where membership in a non-set
        // is structurally rejected (no states generated, no error).
        Err(EvalError::TypeError {
            expected: "Set", ..
        }) => {
            m.assigned_mask = saved_mask;
            return Ok(());
        }
        // All other errors propagate as model checking failures.
        Err(e) => {
            m.assigned_mask = saved_mask;
            return Err(e);
        }
    };

    if domain_iter.peek().is_none() {
        if trace {
            eprintln!(
                "[enum-trace] level={} binder var={} domain-empty=true",
                ctx.get_tlc_level(),
                var
            );
        }
        m.assigned_mask = saved_mask;
        return Ok(());
    }

    let acc_len = m.accumulated.len();
    let save_point = m.rec.undo.len();
    let results_before = m.rec.results.count();
    let mut iterated_total = 0usize;

    // Part of #3893: mark/restore replaces ctx.clone() per iteration.
    let enum_mark = ctx.mark_enum();

    for val in domain_iter {
        iterated_total += 1;
        m.accumulated
            .push(SymbolicAssignment::Value(Arc::clone(var), val.clone()));

        if let Some(idx) = var_idx {
            m.rec.working.bind_no_invalidate(idx, val, m.rec.undo);
        }

        match enumerate_conjuncts(ctx, c, None, p, m) {
            Ok(()) => {}
            Err(e) => {
                ctx.pop_to_enum_mark(&enum_mark);
                m.rec
                    .working
                    .unbind_to_no_invalidate(m.rec.undo, save_point);
                m.assigned_mask = saved_mask;
                return Err(e);
            }
        }
        ctx.pop_to_enum_mark(&enum_mark);

        m.accumulated.truncate(acc_len);
        m.rec
            .working
            .unbind_to_no_invalidate(m.rec.undo, save_point);
        // Reset assigned_mask for next iteration (same fix as above, #1316)
        m.assigned_mask = saved_mask;
        if let Some(idx) = var_idx {
            if idx.as_usize() < 64 {
                m.assigned_mask |= 1u64 << idx.as_usize();
            }
        }

        // Part of #3027: Early termination — stop domain iteration if sink stopped.
        if m.rec.results.is_stopped() {
            break;
        }
    }

    if trace {
        eprintln!(
            "[enum-trace] level={} binder var={} iterated={} successors-added={}",
            ctx.get_tlc_level(),
            var,
            iterated_total,
            m.rec.results.count().saturating_sub(results_before)
        );
    }
    m.assigned_mask = saved_mask;
    Ok(())
}

/// CASE within conjuncts: evaluate arm guards and continue with matching body.
///
/// Mirrors the top-level CASE handler in `enumerate_unified_inner` but uses
/// `enumerate_conjuncts` continuation so the matching arm body is processed as
/// part of the AND chain. Without this, CASE arms containing primed assignments
/// would be evaluated as boolean guards (via the catch-all), potentially losing
/// state assignments.
///
/// FIX #1427: self-audit — same dispatch gap class as ModuleRef.
pub(super) fn conjunct_case(
    ctx: &mut EvalCtx,
    arms: &[CaseArm],
    other: Option<&Spanned<Expr>>,
    conjunct: &Spanned<Expr>,
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    for arm in arms {
        // Part of #3194: use eval_leaf to try TIR for CASE guard evaluation.
        match eval_leaf(ctx, &arm.guard, p.tir_leaf) {
            Ok(Value::Bool(true)) => {
                return enumerate_conjuncts(ctx, c, Some(&arm.body), p, m);
            }
            Ok(Value::Bool(false)) => {}
            Ok(other_val) => {
                return Err(case_guard_error(
                    EvalError::TypeError {
                        expected: "BOOLEAN",
                        got: other_val.type_name(),
                        span: Some(arm.guard.span),
                    },
                    arm.guard.span,
                ));
            }
            Err(e) => return Err(case_guard_error(e, arm.guard.span)),
        }
    }
    // No arm matched — use OTHER if present
    if let Some(other_expr) = other {
        enumerate_conjuncts(ctx, c, Some(other_expr), p, m)
    } else {
        Err(EvalError::CaseNoMatch {
            span: Some(conjunct.span),
        })
    }
}
