// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guard evaluation, successor emission, and assignment extraction helpers
//! for unified successor enumeration.
//!
//! These are the "leaf" operations of the recursive dispatch — they emit
//! results or process individual conjuncts without recursing into the
//! expression tree. Called from the conjunct handlers in `unified.rs`.
//!
//! Extracted from unified.rs as part of #2360.

use std::sync::Arc;

use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::error::EvalError;
use crate::eval::EvalCtx;
use crate::state::{ArrayState, DiffChanges, DiffSuccessor, UndoEntry};

use super::build_diff::build_successor_diffs_from_array_into;
use super::symbolic_assignments::{
    evaluate_symbolic_assignments, extract_symbolic_assignments_with_registry,
};
use super::tir_leaf::eval_leaf;
use super::unified::{enumerate_conjuncts, trace_expr_tag, Cont, EnumMut, EnumParams};
use super::unified_classify::is_primed_assignment;
use super::unified_types::DiffSink;
use super::{
    debug_enum_trace, is_action_level_error, is_operator_reference_guard_unsafe,
    is_speculative_eval_fallback, SymbolicAssignment,
};

/// Internal sentinel for the allAssigned fast path loop.
pub(super) enum GuardResult {
    Failed,
    FailedEval(EvalError),
}

// Allow using these as loop break values
pub(super) use GuardResult::Failed as GuardFailed;
pub(super) use GuardResult::FailedEval as GuardFailedEval;

/// Emit a successor from the accumulated symbolic assignments.
///
/// Fast path: if all assignments are Value/Unchanged and already bound to working,
/// compute the DiffSuccessor directly from the undo stack (O(changes) not O(vars)).
///
/// Slow path: for InSet/Expr assignments that need evaluation, delegate to
/// `build_successor_diffs_from_array_into`.
pub(super) fn emit_successor(
    ctx: &mut EvalCtx,
    accumulated: &[SymbolicAssignment],
    p: &EnumParams<'_>,
    working: &ArrayState,
    undo: &[UndoEntry],
    results: &mut dyn DiffSink,
    has_complex: bool,
) -> Result<(), EvalError> {
    if !has_complex && !undo.is_empty() && p.full_mask != 0 {
        // Fast path: all assignments are Value or Unchanged, already bound to working.
        // Guard: full_mask == 0 means >64 state variables, where the u64 seen_mask
        // below would alias indices that differ by 64 (e.g., var 3 and var 67 share
        // the same bit). Fall through to the slow path which has no bitmask limit.
        let mut changes: DiffChanges = smallvec::smallvec![];
        let mut seen_mask: u64 = 0;
        for entry in undo {
            let idx_bit = 1u64 << (entry.idx.as_usize() & 63);
            if seen_mask & idx_bit != 0 {
                continue;
            }
            seen_mask |= idx_bit;

            let base_val = p.base_with_fp.get(entry.idx);
            let working_val = working.get(entry.idx);
            if base_val != working_val {
                changes.push((entry.idx, working_val.clone()));
            }
        }

        if changes.is_empty() {
            let fp = p
                .base_with_fp
                .cached_fingerprint()
                .ok_or_else(|| EvalError::Internal {
                    message: "base state missing fingerprint cache in emit_successor".into(),
                    span: None,
                })?;
            // Part of #3027: ControlFlow propagation — Break signals early
            // termination to the enumeration recursion via is_stopped() checks
            // at enumerate_conjuncts and branch/quantifier loop entries.
            let _ = results.push_with_ctx(ctx, DiffSuccessor::from_smallvec(fp, changes));
        } else {
            let _ = results.push_with_ctx(ctx, DiffSuccessor::from_changes(changes));
        }
        return Ok(());
    }

    // Slow path: has InSet or Expr assignments that need evaluation/enumeration
    let assignments = evaluate_symbolic_assignments(ctx, accumulated, p.tir_leaf)?;

    // Check for DeferredExpr — these are handled by the build pipeline
    build_successor_diffs_from_array_into(
        ctx,
        p.base_with_fp,
        p.vars,
        &assignments,
        p.registry,
        results,
    );
    Ok(())
}

/// Process a conjunct as either a guard (boolean) or assignment (primed var).
pub(super) fn process_conjunct_guard_or_assignment(
    ctx: &mut EvalCtx,
    conjunct: &Spanned<Expr>,
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    let trace = debug_enum_trace();
    // Check if this is a primed assignment
    if is_primed_assignment(ctx, &conjunct.node) {
        if trace {
            eprintln!(
                "[enum-trace] level={} kind=binder tag={} action=extract reason=primed-assignment",
                ctx.get_tlc_level(),
                trace_expr_tag(&conjunct.node)
            );
        }
        return extract_and_continue_conjunct(ctx, conjunct, c, p, m);
    }

    // Skip unsafe operator reference guards
    if is_operator_reference_guard_unsafe(ctx, &conjunct.node) {
        if trace {
            eprintln!(
                "[enum-trace] level={} kind=binder tag={} action=extract reason=unsafe-operator-guard",
                ctx.get_tlc_level(),
                trace_expr_tag(&conjunct.node)
            );
        }
        return extract_and_continue_conjunct(ctx, conjunct, c, p, m);
    }

    // Part of #3194: use eval_leaf to try TIR for guard evaluation.
    let eval_result = {
        let _env = ctx.bind_next_state_env_guard(m.rec.working.env_ref());
        eval_leaf(ctx, conjunct, p.tir_leaf)
    };

    match eval_result {
        Ok(v) => match v.as_bool() {
            Some(true) => {
                if trace {
                    eprintln!(
                        "[enum-trace] level={} kind=guard tag={} result=true",
                        ctx.get_tlc_level(),
                        trace_expr_tag(&conjunct.node)
                    );
                }
                // Guard passed — continue
                enumerate_conjuncts(ctx, c, None, p, m)
            }
            Some(false) => {
                if trace {
                    eprintln!(
                        "[enum-trace] level={} kind=guard tag={} result=false",
                        ctx.get_tlc_level(),
                        trace_expr_tag(&conjunct.node)
                    );
                }
                // Guard failed — no successors
                Ok(())
            }
            None => Err(EvalError::TypeError {
                expected: "BOOLEAN",
                got: v.type_name(),
                span: Some(conjunct.span),
            }),
        },
        Err(e) if is_speculative_eval_fallback(&e) => {
            if trace {
                eprintln!(
                    "[enum-trace] level={} kind=binder tag={} action=extract reason=speculative-fallback err={:?}",
                    ctx.get_tlc_level(),
                    trace_expr_tag(&conjunct.node),
                    e
                );
            }
            // Eval failed due to unresolved reference (e.g., primed variable not
            // detected by is_primed_assignment). Fall back to assignment extraction.
            // TLC handles these structurally; TLA2's speculative eval hits them at runtime.
            extract_and_continue_conjunct(ctx, conjunct, c, p, m)
        }
        Err(e) => {
            if trace {
                eprintln!(
                    "[enum-trace] level={} kind=guard tag={} result=error err={:?}",
                    ctx.get_tlc_level(),
                    trace_expr_tag(&conjunct.node),
                    e
                );
            }
            // TLC propagates all other eval errors as model checking failures.
            Err(e)
        }
    }
}

/// Extract symbolic assignments from a conjunct and continue with remaining.
pub(super) fn extract_and_continue_conjunct(
    ctx: &mut EvalCtx,
    conjunct: &Spanned<Expr>,
    c: &Cont<'_>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    let accumulated_before = m.accumulated.len();

    extract_symbolic_assignments_with_registry(
        ctx,
        conjunct,
        p.vars,
        m.accumulated,
        p.registry,
        p.tir_leaf,
    )?;

    // Bind newly extracted assignments to working state
    for assignment in &mut m.accumulated[accumulated_before..] {
        match assignment {
            SymbolicAssignment::Value(var_name, value) => {
                if let Some(idx) = p.registry.get(var_name.as_ref()) {
                    m.rec
                        .working
                        .bind_no_invalidate(idx, value.clone(), m.rec.undo);
                }
            }
            SymbolicAssignment::Unchanged(var_name) => {
                if let Some(idx) = p.registry.get(var_name.as_ref()) {
                    let current = m.rec.working.get(idx).clone();
                    m.rec.working.bind_no_invalidate(idx, current, m.rec.undo);
                }
            }
            SymbolicAssignment::Expr(var_name, expr, bindings) => {
                let mark = ctx.mark_stack();
                for (name, val) in bindings {
                    ctx.push_binding(Arc::clone(name), val.clone());
                }
                // Bind working state as next-state env so primed variable
                // references (e.g. x' in `y' = x' * 2`) resolve correctly
                // when x' was already bound by enumerate_in_domain. (#1316)
                // Part of #3194: use eval_leaf to try TIR for assignment eval.
                let eval_result = {
                    let _env = ctx.bind_next_state_env_guard(m.rec.working.env_ref());
                    eval_leaf(ctx, expr, p.tir_leaf)
                };
                ctx.pop_to_mark(&mark);

                match eval_result {
                    Ok(value) => {
                        if let Some(idx) = p.registry.get(var_name.as_ref()) {
                            m.rec
                                .working
                                .bind_no_invalidate(idx, value.clone(), m.rec.undo);
                            *assignment = SymbolicAssignment::Value(var_name.clone(), value);
                        }
                    }
                    // Speculative eval of symbolic Expr: unresolved references
                    // and action-level errors are expected when not all primed
                    // vars are bound yet. Keep as Expr for strict-path eval.
                    Err(e) if is_speculative_eval_fallback(&e) || is_action_level_error(&e) => {
                        m.has_complex = true;
                    }
                    // Fatal eval error — propagate. Silently deferring a
                    // genuine failure (AssertionFailed, ArityMismatch, etc.)
                    // could mask a real spec error.
                    Err(e) => return Err(e),
                }
            }
            SymbolicAssignment::InSet(_, _, _) => {
                m.has_complex = true;
            }
        }
    }

    // Update assigned_mask with newly assigned variables
    for assignment in &m.accumulated[accumulated_before..] {
        let var_name = match assignment {
            SymbolicAssignment::Value(v, _)
            | SymbolicAssignment::Unchanged(v)
            | SymbolicAssignment::Expr(v, _, _)
            | SymbolicAssignment::InSet(v, _, _) => v,
        };
        if let Some(idx) = p.registry.get(var_name.as_ref()) {
            if idx.as_usize() < 64 {
                m.assigned_mask |= 1u64 << idx.as_usize();
            }
        }
    }

    enumerate_conjuncts(ctx, c, None, p, m)
}
