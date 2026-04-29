// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Part of #3100: TLC's LNAction-style subscript short-circuit.
//!
//! TLC's `LNAction.eval()` evaluates `<<A>>_v` as a single fused operation:
//! check subscript v first (cheap), then evaluate body A only if v changed
//! (expensive). TLA2 decomposes `<<A>>_v` into separate `ActionPred(A)` and
//! `StateChanged(v)` leaves evaluated independently. This module enables the
//! same short-circuit: when `StateChanged(v)` is false for a transition, the
//! paired `ActionPred(A)` is pre-populated as false without evaluation.

use crate::check::CheckError;
use crate::liveness::LiveExpr;
use crate::state::{ArrayState, Fingerprint};
use crate::storage::ActionBitmaskMap;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;

/// Maps a `StateChanged` leaf tag to its paired `ActionPred` tag from the same
/// `<<A>>_v` pattern. When `StateChanged` is false (v' == v) for a transition,
/// the paired `ActionPred` can be skipped: `<<A>>_v = A /\ v' ≠ v = false`.
pub(in crate::check::model_checker) struct SubscriptActionPair {
    pub(in crate::check::model_checker) state_changed_tag: u32,
    /// The subscript expression `v`. None means use fingerprint comparison.
    pub(in crate::check::model_checker) subscript: Option<Arc<Spanned<Expr>>>,
    /// Liveness quantifier bindings for the subscript expression.
    pub(in crate::check::model_checker) bindings: Option<crate::eval::BindingChain>,
}

/// Extract a `SubscriptActionPair` from an `And([ActionPred, StateChanged])`
/// or `And([StateChanged, ActionPred])` pattern.
fn extract_subscript_action_pair(expr: &LiveExpr) -> Option<SubscriptActionPair> {
    if let LiveExpr::And(parts) = expr {
        if parts.len() == 2 {
            match (&parts[0], &parts[1]) {
                (
                    LiveExpr::ActionPred { .. },
                    LiveExpr::StateChanged {
                        tag: sc_tag,
                        subscript,
                        bindings,
                    },
                ) => {
                    return Some(SubscriptActionPair {
                        state_changed_tag: *sc_tag,
                        subscript: subscript.clone(),
                        bindings: bindings.clone(),
                    });
                }
                (
                    LiveExpr::StateChanged {
                        tag: sc_tag,
                        subscript,
                        bindings,
                    },
                    LiveExpr::ActionPred { .. },
                ) => {
                    return Some(SubscriptActionPair {
                        state_changed_tag: *sc_tag,
                        subscript: subscript.clone(),
                        bindings: bindings.clone(),
                    });
                }
                _ => {}
            }
        }
    }
    None
}

/// Extract subscript-action pairs from fairness expressions, handling
/// quantified fairness that produces `And([wf1, wf2, ...])` conjunctions.
pub(super) fn extract_subscript_action_pairs(
    expr: &LiveExpr,
    pairs: &mut Vec<SubscriptActionPair>,
) {
    if let Some(pair) = extract_subscript_action_pair(expr) {
        pairs.push(pair);
    }
    match expr {
        LiveExpr::And(parts) | LiveExpr::Or(parts) => {
            for part in parts {
                extract_subscript_action_pairs(part, pairs);
            }
        }
        LiveExpr::Not(inner)
        | LiveExpr::Always(inner)
        | LiveExpr::Eventually(inner)
        | LiveExpr::Next(inner) => {
            extract_subscript_action_pairs(inner, pairs);
        }
        _ => {}
    }
}

/// Apply the subscript short-circuit for a single transition (bitmask-only).
///
/// For each `SubscriptActionPair`, evaluates `StateChanged(v)` and when false
/// (v unchanged), the paired `ActionPred` is false (no bit set needed).
/// When true, sets the StateChanged bit in the bitmask.
pub(super) fn apply_subscript_short_circuit_bitmask(
    ctx: &crate::eval::EvalCtx,
    action_bitmasks: &mut ActionBitmaskMap,
    pairs: &[SubscriptActionPair],
    current_fp: Fingerprint,
    current_array: &ArrayState,
    next_fp: Fingerprint,
    next_array: &ArrayState,
) -> Result<(), CheckError> {
    for pair in pairs {
        // Evaluate subscript change using the thread-local subscript cache.
        let changed = match &pair.subscript {
            None => current_fp != next_fp,
            Some(sub_expr) => crate::liveness::eval_subscript_changed_array_cached(
                ctx,
                current_fp,
                current_array,
                next_fp,
                next_array,
                sub_expr,
                pair.bindings.as_ref(),
                pair.state_changed_tag,
            )?,
        };

        // Part of #3208 fix (Bug D): Only OR bits into EXISTING entries.
        // Do not create keys — record_missing_action_results creates keys.
        // Part of #4159: Removed `tag < 64` guard — LiveBitmask handles arbitrary tags.
        if changed {
            if let Some(bm) = action_bitmasks.get_mut_bitmask(&(current_fp, next_fp)) {
                bm.set_tag(pair.state_changed_tag);
            }
        }
        // When !changed: ActionPred is false (no bit to set). The bitmask
        // entry for this transition may or may not exist yet — it will be
        // created by record_missing_action_results which runs after this.
    }
    Ok(())
}
