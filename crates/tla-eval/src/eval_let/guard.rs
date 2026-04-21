// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Guard-first short-circuit for LET ... IN /\ guard /\ rest.
//!
//! Extracted from `eval_let.rs` for file size compliance (#3474).

use crate::eval;
use crate::EvalCtx;
use tla_core::ast::{Expr, OperatorDef};
use tla_core::{expr_mentions_name_v, Spanned};

/// Guard-first short-circuit for LET ... IN /\ guard /\ rest.
///
/// Returns `Some(false)` if the guard can be evaluated without LET defs and
/// returns false, meaning the entire LET expression evaluates to false.
/// Returns `None` if the optimization doesn't apply (guard references a def,
/// guard doesn't evaluate to bool, or guard is true).
///
/// Part of #2963: TLC-aligned optimization. TLC's LazyValue defers LET def
/// evaluation until first reference, so `LET x == expensive IN /\ cheap_guard /\ f(x)`
/// only evaluates `expensive` when `cheap_guard` is true. This function provides
/// the same short-circuit without changing the thunk/closure mechanism.
pub(super) fn try_guard_first_shortcircuit(
    ctx: &EvalCtx,
    defs: &[OperatorDef],
    first_conjunct: &Spanned<Expr>,
) -> Option<bool> {
    // Check if the first conjunct mentions any LET def name.
    // If it does, we can't evaluate it without first binding the defs.
    for def in defs {
        if expr_mentions_name_v(&first_conjunct.node, def.name.node.as_str()) {
            return None;
        }
    }

    // The guard doesn't reference any LET def — evaluate it in the original ctx.
    // If it errors, return None to let the normal path handle the error
    // (it may succeed with lazy thunk semantics).
    let guard_val = eval(ctx, first_conjunct).ok()?;
    match guard_val.as_bool() {
        Some(false) => Some(false),
        _ => None, // true or non-boolean: fall through to normal eval_let
    }
}
