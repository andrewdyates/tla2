// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Panic-safe RAII guards and evaluation entrypoints for dependency tracking.
//!
//! Contains `OpDepGuard`, `StateLookupModeGuard`, `eval_with_dep_tracking`,
//! and `try_eval_const_level`.

use super::deps::OpEvalDeps;
use super::runtime::{propagate_cached_deps, OpDepFrame, StateLookupMode};
use crate::error::{EvalError, EvalResult};
use crate::value::Value;
use crate::EvalCtx;
use tla_core::ast::Expr;
use tla_core::Spanned;

/// RAII guard that pushes an `OpDepFrame` on creation and pops it on drop.
///
/// Fix #1548: Replaces manual push/pop with `.expect()` that was vulnerable to
/// panic-induced stack leaks. If `eval()` panics and the panic is caught (e.g.,
/// by `catch_unwind` in a parallel worker), the guard ensures the frame is still
/// popped, preventing all subsequent operator evaluations from operating on a
/// corrupted dep stack.
///
/// Part of #3666: Also maintains the `dep_tracking_depth` shadow counter
/// so that `is_dep_tracking_active()` and `record_*` functions can skip
/// RefCell borrows when no dep tracking is active.
pub(crate) struct OpDepGuard<'a> {
    stack: &'a std::cell::RefCell<Vec<OpDepFrame>>,
    depth: &'a std::cell::Cell<u16>,
    armed: bool,
}

impl<'a> OpDepGuard<'a> {
    /// Push a new dep tracking frame and return a guard that pops it on drop.
    ///
    /// Part of #3666: Takes `&EvalCtx` to maintain the `dep_tracking_depth`
    /// shadow counter, enabling `is_dep_tracking_active()` and `record_*`
    /// functions to skip RefCell borrows when the stack is empty.
    pub(crate) fn from_ctx(ctx: &'a EvalCtx, base_stack_len: usize) -> Self {
        ctx.runtime_state
            .op_dep_stack
            .borrow_mut()
            .push(OpDepFrame {
                deps: OpEvalDeps::default(),
                base_stack_len,
            });
        ctx.runtime_state
            .dep_tracking_depth
            .set(ctx.runtime_state.dep_tracking_depth.get() + 1);
        OpDepGuard {
            stack: &ctx.runtime_state.op_dep_stack,
            depth: &ctx.runtime_state.dep_tracking_depth,
            armed: true,
        }
    }

    /// Pop and return deps from the frame owned by this guard.
    pub(crate) fn try_take_deps(mut self) -> Option<OpEvalDeps> {
        self.armed = false;
        self.depth.set(self.depth.get().saturating_sub(1));
        self.stack.borrow_mut().pop().map(|frame| frame.deps)
    }
}

impl Drop for OpDepGuard<'_> {
    fn drop(&mut self) {
        if !self.armed {
            return;
        }
        // Panic-safety path: pop the frame we pushed, discarding its deps.
        // This fires only when the guard is dropped without `try_take_deps()` being called
        // (i.e., during unwinding or early return).
        self.depth.set(self.depth.get().saturating_sub(1));
        let _ = self.stack.borrow_mut().pop();
    }
}

/// RAII guard that saves and restores `state_lookup_mode` on drop, including during panic unwind.
///
/// Fix #2283: `with_state_lookup_mode` used a manual save/restore pattern that was not panic-safe.
/// If the closure panicked (and the panic was caught by `catch_unwind` in a parallel worker),
/// `state_lookup_mode` would remain permanently set to `StateLookupMode::Next`, causing all
/// subsequent unprimed variable lookups on that thread to return next-state values — a soundness
/// violation.
///
/// Pattern mirrors `SubstCacheGuard` (fix #2260) and `OpDepGuard` (fix #1548).
pub(crate) struct StateLookupModeGuard<'a> {
    mode: &'a std::cell::Cell<StateLookupMode>,
    prev: StateLookupMode,
}

impl<'a> StateLookupModeGuard<'a> {
    pub(crate) fn new(ctx: &'a EvalCtx, mode: StateLookupMode) -> Self {
        let prev = ctx.runtime_state.state_lookup_mode.get();
        ctx.runtime_state.state_lookup_mode.set(mode);
        Self {
            mode: &ctx.runtime_state.state_lookup_mode,
            prev,
        }
    }
}

impl Drop for StateLookupModeGuard<'_> {
    fn drop(&mut self) {
        self.mode.set(self.prev);
    }
}

fn eval_with_dep_tracking_impl(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    propagate_to_parent: bool,
) -> EvalResult<(Value, OpEvalDeps)> {
    // Capture the current stack depth - variables at indices >= this are internal
    // to this operator evaluation and should not be recorded as dependencies.
    let base_stack_len = ctx.binding_depth;

    let guard = OpDepGuard::from_ctx(ctx, base_stack_len);

    let result = crate::eval(ctx, expr);

    // On success: take deps and propagate. On error: guard drops and cleans up.
    match (result, guard.try_take_deps()) {
        (Ok(v), Some(deps)) => {
            if propagate_to_parent {
                propagate_cached_deps(ctx, &deps);
            }
            Ok((v, deps))
        }
        (Err(e), Some(_)) => Err(e),
        (Ok(_), None) => Err(EvalError::Internal {
            message: "dependency tracking stack unexpectedly empty after operator eval".into(),
            span: Some(expr.span),
        }),
        (Err(e), None) => Err(e),
    }
}

pub(crate) fn eval_with_dep_tracking(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
) -> EvalResult<(Value, OpEvalDeps)> {
    eval_with_dep_tracking_impl(ctx, expr, true)
}

/// Evaluate under dep tracking without merging the resulting deps into the
/// parent frame. Callers use this when they need to normalize or filter the
/// deps before replaying them upward.
pub(crate) fn eval_with_dep_tracking_unpropagated(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
) -> EvalResult<(Value, OpEvalDeps)> {
    eval_with_dep_tracking_impl(ctx, expr, false)
}

/// Try to evaluate an expression at "constant-level" (TLC `argLevel == 0`) relative to the
/// current binding context.
///
/// Returns `Some(v)` iff:
/// - the expression can be evaluated without a concrete state/next-state (TLCState.Empty), and
/// - dependency tracking reports no current-state (`deps.state`) and no next-state (`deps.next`)
///   reads.
///
/// Local dependencies are allowed (e.g., witnesses bound by bounded `\\E` during action splitting).
pub fn try_eval_const_level(ctx: &EvalCtx, expr: &Spanned<Expr>) -> Option<Value> {
    // Mirror TLCState.Empty: clear state/next sources (but keep the current binding context).
    let const_ctx = ctx.without_state_and_next();

    let (v, deps) = eval_with_dep_tracking(&const_ctx, expr).ok()?;
    if deps.inconsistent {
        return None;
    }
    if deps.state.is_empty() && deps.next.is_empty() && deps.tlc_level.is_none() {
        Some(v)
    } else {
        None
    }
}
