// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Recursive-descent enumeration inherently needs many parameters: mutable
// evaluation context, mutable working state, accumulated assignments, undo
// stack, results, plus per-call AST arguments. EnumParams bundles the 4
// immutable ones; RecState bundles the 3 recursive-descent mutable ones
// (working, undo, results); EnumMut extends RecState with 3 additional
// conjunct-processing fields (accumulated, assigned_mask, has_complex).
// EvalCtx stays separate because it's used for eval() calls while
// working/undo are simultaneously mutated.

//! Unified successor enumeration.
//!
//! This module provides a single recursive descent function that handles ALL TLA+
//! expression types for successor enumeration, replacing the triplicated dispatch
//! across `next_rec.rs` (Tier 3), `array_rec.rs` (Tier 2), and
//! `and_enumeration.rs` (Tier 1).
//!
//! Architecture follows TLC's single-scratchpad pattern:
//! - One mutable working `ArrayState` with bind/unbind (matching TLC's `TLCStateMut`)
//! - Continuation-based conjunct processing (matching TLC's `ActionItemList`)
//! - `SuccessorEmitter` trait for output type abstraction (matching TLC's `INextStateFunctor`)
//! - allAssigned bitmap optimization (matching TLC's `getNextStatesAllAssigned`)
//!
//! Part of #1262: Eliminate enumeration triplication.
//!
//! Submodule structure (Part of #2360):
//! - `unified_types`: Shared parameter bundles and mutable state types
//! - `unified_dispatch`: Main recursive dispatch (`enumerate_unified_inner`)
//! - `unified_module_ref`: INSTANCE operator inlining
//! - `unified_conjuncts`: Forking conjunct handlers (AND, OR, EXISTS, IF, IN, CASE)
//! - `unified_scope`: Scope-managing conjunct handlers (LET, Apply, Ident, ModuleRef)
//! - `unified_emit`: Guard evaluation, successor emission, assignment extraction
//! - `unified_exists`: EXISTS quantifier enumeration
//! - `unified_fast_path`: allAssigned optimization
//! - `unified_classify`: Primed variable classification

use tla_core::ast::Expr;
use tla_core::Spanned;

use crate::error::EvalError;
use crate::eval::EvalCtx;

// Re-export types for backward compatibility with existing submodules
// (unified_emit, unified_exists, unified_fast_path) that import from super::unified.
pub(super) use super::unified_types::{Cont, EnumMut, EnumParams, RecState};

// Re-export dispatch function for unified_exists which imports it from super::unified.
pub(super) use super::unified_dispatch::enumerate_unified_inner;

// Conjunct handlers from extracted submodules
use super::unified_conjuncts::{
    conjunct_and, conjunct_case, conjunct_exists, conjunct_if, conjunct_in, conjunct_or,
};
use super::unified_emit::{emit_successor, process_conjunct_guard_or_assignment};
use super::unified_fast_path::all_assigned_fast_path;
use super::unified_scope::{conjunct_apply, conjunct_ident, conjunct_let, conjunct_module_ref};
use super::{debug_enum, debug_enum_trace};

// ─── Top-level entry ─────────────────────────────────────────────────────────

/// Unified top-level entry point for successor enumeration.
///
/// Replaces `enumerate_next_rec_array_as_diffs` from `array_rec.rs`.
/// Handles ALL expression types without fallback — Or, And, Exists, Apply, Ident,
/// If, Let, Case, ModuleRef, In, and arbitrary guards.
///
/// Returns `Ok(())` on success (results are accumulated into `results`).
/// Returns `Err(EvalError)` only for real evaluation errors.
///
/// Part of #1262 Phase 2.
pub(super) fn enumerate_unified(
    ctx: &mut EvalCtx,
    expr: &Spanned<Expr>,
    p: &EnumParams<'_>,
    s: &mut RecState<'_>,
) -> Result<(), EvalError> {
    enumerate_unified_inner(ctx, expr, p, s)
}

// ─── Continuation-based conjunct processing ──────────────────────────────────
//
// This is the core engine from `and_enumeration.rs`, generalized for use by
// the unified path. It processes AND conjuncts one at a time using the
// bind/unbind pattern with the allAssigned bitmap optimization.

#[inline]
pub(super) fn trace_expr_tag(expr: &Expr) -> &'static str {
    match expr {
        Expr::And(_, _) => "And",
        Expr::Or(_, _) => "Or",
        Expr::Exists(_, _) => "Exists",
        Expr::If(_, _, _) => "If",
        Expr::In(_, _) => "In",
        Expr::Let(_, _) => "Let",
        Expr::Apply(_, _) => "Apply",
        Expr::Ident(_, _) => "Ident",
        Expr::ModuleRef(_, _, _) => "ModuleRef",
        Expr::Case(_, _) => "Case",
        _ => "Other",
    }
}

#[inline]
fn trace_kind_hint(expr: &Expr) -> &'static str {
    match expr {
        Expr::And(_, _)
        | Expr::Or(_, _)
        | Expr::Exists(_, _)
        | Expr::If(_, _, _)
        | Expr::Case(_, _) => "branch",
        Expr::In(lhs, _) => {
            if let Expr::Prime(inner_lhs) = &lhs.node {
                if matches!(&inner_lhs.node, Expr::Ident(_, _) | Expr::StateVar(_, _, _)) {
                    return "binder";
                }
            }
            "guard"
        }
        _ => "guard",
    }
}

/// Process AND conjuncts one at a time using continuation-based enumeration.
///
/// This is the TLC-style ActionItemList pattern: conjuncts are processed
/// sequentially, with OR/EXISTS/IF causing forking/iteration. The allAssigned
/// bitmap optimization short-circuits guard evaluation when all variables
/// have been assigned.
pub(super) fn enumerate_conjuncts<'a>(
    ctx: &mut EvalCtx,
    c: &Cont<'a>,
    pending: Option<&'a Spanned<Expr>>,
    p: &EnumParams<'_>,
    m: &mut EnumMut<'_>,
) -> Result<(), EvalError> {
    crate::eval::stack_safe(|| {
        // Part of #3027: Early termination — if the sink has signaled Break,
        // skip all remaining conjuncts, branches, and quantifier iterations.
        if m.rec.results.is_stopped() {
            return Ok(());
        }

        let debug = debug_enum();
        let trace = debug_enum_trace();

        // Base case: all conjuncts processed AND no pending expression
        if c.next_idx >= c.conjuncts.len() && pending.is_none() {
            // Fix #804: If there's a scope_restore, pop LET/apply bindings
            // and continue with the parent continuation instead of emitting.
            if let Some(ref sr) = c.scope_restore {
                ctx.pop_to_mark(&sr.binding_mark);
                ctx.local_ops_mut().clone_from(&sr.saved_local_ops);
                ctx.set_skip_prime_validation(sr.saved_skip_prime);
                let parent = sr.restored_parent_cont();
                return enumerate_conjuncts(ctx, &parent, None, p, m);
            }
            return emit_successor(
                ctx,
                m.accumulated,
                p,
                m.rec.working,
                m.rec.undo,
                m.rec.results,
                m.has_complex,
            );
        }

        // allAssigned fast path: when all state variables have assignments,
        // evaluate remaining conjuncts as boolean guards (no recursion).
        if m.assigned_mask == p.full_mask && p.full_mask != 0 {
            return all_assigned_fast_path(ctx, c, pending, p, m, debug, trace);
        }

        // Determine which expression to process next
        let (conjunct, tail) = if let Some(p_expr) = pending {
            (
                p_expr,
                Cont {
                    conjuncts: c.conjuncts,
                    next_idx: c.next_idx,
                    scope_restore: c.scope_restore.clone(),
                },
            )
        } else {
            (
                c.conjuncts[c.next_idx],
                Cont {
                    conjuncts: c.conjuncts,
                    next_idx: c.next_idx + 1,
                    scope_restore: c.scope_restore.clone(),
                },
            )
        };

        if trace {
            eprintln!(
                "[enum-trace] level={} idx={}/{} pending={} kind={} tag={} assigned_mask={:#x}",
                ctx.get_tlc_level(),
                c.next_idx,
                c.conjuncts.len(),
                pending.is_some(),
                trace_kind_hint(&conjunct.node),
                trace_expr_tag(&conjunct.node),
                m.assigned_mask
            );
        }

        match &conjunct.node {
            Expr::And(_a, _b) => conjunct_and(ctx, conjunct, &tail, p, m),
            Expr::Or(a, b) => conjunct_or(ctx, a, b, &tail, p, m),
            Expr::Exists(bounds, body) => conjunct_exists(ctx, bounds, body, conjunct, &tail, p, m),
            Expr::If(..) => conjunct_if(ctx, conjunct, &tail, p, m),
            Expr::In(lhs, rhs) => conjunct_in(ctx, lhs, rhs, conjunct, &tail, p, m),
            Expr::Let(defs, body) => conjunct_let(ctx, defs, body, &tail, p, m),
            Expr::Apply(op_expr, args) => conjunct_apply(ctx, op_expr, args, conjunct, &tail, p, m),
            Expr::Ident(name, _) => conjunct_ident(ctx, name, conjunct, &tail, p, m),
            Expr::ModuleRef(instance_name, op_name, args) => {
                conjunct_module_ref(ctx, conjunct, instance_name, op_name, args, &tail, p, m)
            }
            Expr::Case(arms, other) => {
                conjunct_case(ctx, arms, other.as_deref(), conjunct, &tail, p, m)
            }
            // Label: transparent wrapper — unwrap and dispatch on the body.
            Expr::Label(label) => {
                process_conjunct_guard_or_assignment(ctx, &label.body, &tail, p, m)
            }
            // Other expressions: treat as guard or assignment
            _ => process_conjunct_guard_or_assignment(ctx, conjunct, &tail, p, m),
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::enumerate::unified_types::{ClosureSink, DiffSink};
    use crate::state::{ArrayState, DiffChanges, DiffSuccessor};
    use crate::var_index::VarRegistry;
    use crate::Value;
    use std::ops::ControlFlow;
    use std::sync::Arc;

    /// Verify that EnumParams disables bitmask optimizations for >64 state variables.
    ///
    /// When full_mask == 0, the emit_successor fast path is skipped to avoid
    /// seen_mask aliasing where variable indices differing by 64 share the same
    /// bitmask bit (e.g., var 3 and var 67 would collide via `1u64 << (idx & 63)`).
    #[test]
    fn test_enum_params_full_mask_disables_for_large_var_counts() {
        let registry = VarRegistry::new();

        // 1 variable: full_mask should be 1
        let vars_1: Vec<Arc<str>> = (0..1).map(|i| Arc::from(format!("v{i}"))).collect();
        let base = ArrayState::from_values(vec![Value::int(0)]);
        let p = EnumParams::new(&vars_1, &registry, &base);
        assert_eq!(p.full_mask, 1, "1 var should have full_mask = 1");

        // 64 variables: full_mask should be u64::MAX
        let vars_64: Vec<Arc<str>> = (0..64).map(|i| Arc::from(format!("v{i}"))).collect();
        let base_64 = ArrayState::from_values(vec![Value::int(0); 64]);
        let p64 = EnumParams::new(&vars_64, &registry, &base_64);
        assert_eq!(
            p64.full_mask,
            u64::MAX,
            "64 vars should have full_mask = u64::MAX"
        );

        // 65 variables: full_mask must be 0 (disables bitmask optimizations)
        let vars_65: Vec<Arc<str>> = (0..65).map(|i| Arc::from(format!("v{i}"))).collect();
        let base_65 = ArrayState::from_values(vec![Value::int(0); 65]);
        let p65 = EnumParams::new(&vars_65, &registry, &base_65);
        assert_eq!(
            p65.full_mask, 0,
            "65 vars should have full_mask = 0 to disable bitmask optimizations"
        );

        // 128 variables: same guard
        let vars_128: Vec<Arc<str>> = (0..128).map(|i| Arc::from(format!("v{i}"))).collect();
        let base_128 = ArrayState::from_values(vec![Value::int(0); 128]);
        let p128 = EnumParams::new(&vars_128, &registry, &base_128);
        assert_eq!(
            p128.full_mask, 0,
            "128 vars should have full_mask = 0 to disable bitmask optimizations"
        );
    }

    /// Verify ClosureSink counts and early termination behavior.
    ///
    /// Part of #3027: Tests that ClosureSink correctly:
    /// 1. Invokes the callback for each pushed successor
    /// 2. Tracks count
    /// 3. Sets is_stopped() when callback returns Break
    /// 4. Short-circuits push() after stop
    #[test]
    fn test_closure_sink_early_termination() {
        // Sink that accepts 2 successors then signals Break
        let mut received: Vec<DiffSuccessor> = Vec::new();
        let limit = 2;
        let mut sink = ClosureSink::new(|diff: DiffSuccessor| {
            received.push(diff);
            if received.len() >= limit {
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(())
            }
        });

        assert_eq!(DiffSink::count(&sink), 0);
        assert!(!DiffSink::is_stopped(&sink));

        // Push 1: Continue
        let diff1 = DiffSuccessor::from_changes(DiffChanges::new());
        let flow = DiffSink::push(&mut sink, diff1);
        assert!(matches!(flow, ControlFlow::Continue(())));
        assert_eq!(DiffSink::count(&sink), 1);
        assert!(!DiffSink::is_stopped(&sink));

        // Push 2: Break (limit reached)
        let diff2 = DiffSuccessor::from_changes(DiffChanges::new());
        let flow = DiffSink::push(&mut sink, diff2);
        assert!(matches!(flow, ControlFlow::Break(())));
        assert_eq!(DiffSink::count(&sink), 2);
        assert!(DiffSink::is_stopped(&sink));

        // Push 3: Short-circuits immediately (doesn't invoke callback)
        let diff3 = DiffSuccessor::from_changes(DiffChanges::new());
        let flow = DiffSink::push(&mut sink, diff3);
        assert!(matches!(flow, ControlFlow::Break(())));
        assert_eq!(
            DiffSink::count(&sink),
            2,
            "count should not increase after stop"
        );
        assert_eq!(
            received.len(),
            2,
            "callback should not be invoked after stop"
        );
    }

    /// Verify that Vec DiffSink never reports is_stopped().
    #[test]
    fn test_vec_sink_never_stops() {
        let mut vec_sink: Vec<DiffSuccessor> = Vec::new();
        assert!(!DiffSink::is_stopped(&vec_sink));

        for _ in 0..100 {
            let flow = DiffSink::push(
                &mut vec_sink,
                DiffSuccessor::from_changes(DiffChanges::new()),
            );
            assert!(matches!(flow, ControlFlow::Continue(())));
        }
        assert!(!DiffSink::is_stopped(&vec_sink));
        assert_eq!(DiffSink::count(&vec_sink), 100);
    }
}
