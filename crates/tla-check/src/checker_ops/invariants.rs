// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Invariant and implied action checking for successor states.
//!
//! Part of #2356: canonical per-successor invariant checking shared by
//! both the sequential and parallel checker paths.

use super::InvariantOutcome;
use crate::check::CheckError;
use crate::eval::EvalCtx;
use crate::state::{ArrayState, Fingerprint};
use crate::EvalCheckError;
use crate::Value;
use tla_core::ast::Expr;
use tla_core::Spanned;

// Part of #4114: Cache debug env var with OnceLock instead of calling
// std::env::var on every invariant check.
debug_flag!(debug_3147_inv, "TLA2_DEBUG_3147");

/// Prepare evaluation context and check invariants for a successor state,
/// returning an [`InvariantOutcome`].
///
/// This is the **canonical** per-successor invariant check entry point used by both
/// the sequential and parallel checker paths. It encapsulates the exact sequence:
/// 1. Early-return if no invariants configured
/// 2. Set TLC level for successor (#1102)
/// 3. Evaluate name-based invariants via [`check_invariants_array_state`]
/// 4. Evaluate eval-based state invariants via [`check_eval_state_invariants`]
/// 5. Map the result to [`InvariantOutcome`]
///
/// State-boundary cache invalidation is handled lazily by the evaluator.
///
/// The caller is responsible for:
/// - Setting trace context BEFORE calling (mode-specific: sequential reconstructs
///   full trace from parent; parallel uses DashMap lookup)
/// - Clearing trace context AFTER calling
/// - Handling `continue_on_error` semantics on `Violation` outcomes (sequential
///   records via `handle_invariant_violation`, parallel uses `OnceLock`)
///
/// Part of #2356 (Phase 2): unifies the duplicated per-successor invariant
/// evaluation -> outcome-mapping path from `check_successor_invariant` (sequential)
/// and `check_successor_invariants` (parallel).
pub(crate) fn check_invariants_for_successor(
    ctx: &mut EvalCtx,
    invariants: &[String],
    eval_state_invariants: &[(String, Spanned<Expr>)],
    succ: &ArrayState,
    succ_fp: Fingerprint,
    succ_level: u32,
) -> InvariantOutcome {
    // Early-return optimization: skip level setting and invariant evaluation when
    // no invariants are configured. Previously only the parallel path had this.
    if invariants.is_empty() && eval_state_invariants.is_empty() {
        return InvariantOutcome::Ok;
    }

    // Part of #3063/#3447: The explicit state-boundary cache clear was removed in
    // #3063 when compiled invariants bypassed SUBST_CACHE. After #3354 Slice 2
    // removed compiled invariants, eval_op-based invariants use runtime INSTANCE
    // resolution which populates SUBST_CACHE. The LAST_STATE_PTR lazy detection
    // can miss state changes on allocator address reuse, so the clear was restored
    // below (Part of #3447). This is a targeted clear_for_eval_scope_boundary(),
    // not the old O(cache_size) retain() that was the MultiPaxos bottleneck.

    // Part of #1102: Invariants must see succState level per TLC Worker.java:434.
    ctx.set_tlc_level(succ_level);

    // Part of #3447/#3391/#3465: Establish the array-bound eval boundary before
    // invariant evaluation. Clears eval-scope caches and aligns state-identity
    // tracking to the currently bound arrays, preventing stale INSTANCE-scoped
    // cache entries from leaking across state boundaries.
    crate::eval::clear_for_bound_state_eval_scope(ctx);

    match check_invariants_array_state(ctx, invariants, succ) {
        std::result::Result::Ok(None) => {}
        std::result::Result::Ok(Some(invariant)) => {
            return InvariantOutcome::Violation {
                invariant,
                state_fp: succ_fp,
            };
        }
        Err(error) => return InvariantOutcome::Error(error),
    }

    // #3113: Check eval-based state invariants (ENABLED-containing state-level
    // terms from PROPERTY entries). These use eval_entry() instead of compiled
    // guards because the compiled guard path cannot handle ENABLED.
    match check_eval_state_invariants(ctx, eval_state_invariants, succ) {
        std::result::Result::Ok(None) => InvariantOutcome::Ok,
        std::result::Result::Ok(Some(invariant)) => InvariantOutcome::Violation {
            invariant,
            state_fp: succ_fp,
        },
        Err(error) => InvariantOutcome::Error(error),
    }
}

/// Check invariants for an `ArrayState`, returning the first violated invariant (if any).
///
/// This is the **canonical** invariant evaluation function used by both the sequential
/// and parallel checker paths. Both paths MUST call this function (or a thin wrapper
/// around it) for all invariant evaluation to prevent parity drift.
///
/// TLC semantics: evaluation errors in invariants are reported as errors, not as violations.
///
/// Prefer [`check_invariants_for_successor`] for the full per-successor contract
/// (level setting + eval-state invariant dispatch + outcome mapping). Call this
/// function directly only when the caller manages those responsibilities itself.
///
/// Part of #2356 (Phase 2): consolidated from the duplicated implementations in
/// `check/model_checker/invariants/eval.rs` and `parallel/mod.rs`.
pub(crate) fn check_invariants_array_state(
    ctx: &mut EvalCtx,
    invariants: &[String],
    array_state: &ArrayState,
) -> Result<Option<String>, CheckError> {
    // State invariants must evaluate against the current state only.
    // Successor generation and action checking can legitimately leave
    // `next_state` / `next_state_env` bound on the shared EvalCtx; if that
    // stale action context leaks into a state invariant, `TLCGet("action")`
    // and next-state cache validation can observe the wrong transition.
    let _next_state_guard = ctx.take_next_state_guard();
    let _next_env_guard = ctx.take_next_state_env_guard();
    let _state_guard = ctx.bind_state_env_guard(array_state.env_ref());

    for inv_name in invariants {
        // Part of #3465: Use replay helper for same-state invariant loop.
        // Resets state_lookup_mode + clears eval-scope caches, preventing
        // runtime state drift across shared Rc<EvalRuntimeState>.
        crate::eval::clear_for_state_eval_replay(ctx);
        match ctx.eval_op(inv_name) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => return Ok(Some(inv_name.clone())),
            Ok(_) => return Err(EvalCheckError::InvariantNotBoolean(inv_name.clone()).into()),
            Err(e) => return Err(EvalCheckError::Eval(e).into()),
        }
    }
    Ok(None)
}

/// Check property init predicates against an initial state (#2834).
///
/// Init predicates are non-Always state/constant-level terms from PROPERTY entries
/// (e.g., `M!Init` in `M!Init /\ [][M!Next]_M!vars`). They must hold on every
/// initial state. Returns the property name of the first violated predicate, or
/// None if all pass.
///
/// This enables full promotion of safety-style PROPERTY entries to BFS-time checking,
/// avoiding the expensive post-BFS safety_temporal pass.
pub(crate) fn check_property_init_predicates(
    ctx: &mut EvalCtx,
    init_predicates: &[(String, tla_core::Spanned<tla_core::ast::Expr>)],
    array_state: &ArrayState,
) -> Result<Option<String>, CheckError> {
    if init_predicates.is_empty() {
        return Ok(None);
    }
    let _next_state_guard = ctx.take_next_state_guard();
    let _next_env_guard = ctx.take_next_state_env_guard();
    let _state_guard = ctx.bind_state_env_guard(array_state.env_ref());
    for (prop_name, expr) in init_predicates {
        // Part of #3465: Use replay helper for same-state predicate loop.
        crate::eval::clear_for_state_eval_replay(ctx);
        match crate::eval::eval_entry(ctx, expr) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                if debug_3147_inv() {
                    eprintln!(
                        "[DEBUG_3147] INIT predicate VIOLATED: prop={prop_name}, expr={:?}",
                        std::mem::discriminant(&expr.node)
                    );
                }
                return Ok(Some(prop_name.clone()));
            }
            Ok(_) => return Err(EvalCheckError::PropertyNotBoolean(prop_name.clone()).into()),
            Err(e) => {
                if debug_3147_inv() {
                    eprintln!("[DEBUG_3147] INIT predicate ERROR: prop={prop_name}, err={e:?}");
                }
                return Err(EvalCheckError::Eval(e).into());
            }
        }
    }
    Ok(None)
}

/// Check eval-based PROPERTY state invariants for a successor state.
///
/// These are state-level `PROPERTY` terms promoted into the BFS invariant lane.
/// They now include both the old ENABLED-containing eval-only terms (#3113) and
/// the formerly compiled PROPERTY state terms moved to the canonical eval path
/// by Slice 2 of #3354.
///
/// Checked for unseen states only (like config invariants), not for all
/// transitions (unlike implied actions). Returns the property name of the
/// first violated invariant, or None if all pass.
///
/// Both sequential and parallel checker paths MUST call this function for all
/// eval-based state invariant evaluation to prevent parity drift.
pub(crate) fn check_eval_state_invariants(
    ctx: &mut EvalCtx,
    eval_state_invariants: &[(String, Spanned<Expr>)],
    array_state: &ArrayState,
) -> Result<Option<String>, CheckError> {
    if eval_state_invariants.is_empty() {
        return Ok(None);
    }
    let _next_state_guard = ctx.take_next_state_guard();
    let _next_env_guard = ctx.take_next_state_env_guard();
    let _state_guard = ctx.bind_state_env_guard(array_state.env_ref());
    for (prop_name, expr) in eval_state_invariants {
        // Part of #3465: Use replay helper for same-state eval loop.
        crate::eval::clear_for_state_eval_replay(ctx);
        match crate::eval::eval_entry(ctx, expr) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                return Ok(Some(prop_name.clone()));
            }
            Ok(_) => return Err(EvalCheckError::PropertyNotBoolean(prop_name.clone()).into()),
            Err(e) => return Err(EvalCheckError::Eval(e).into()),
        }
    }
    Ok(None)
}

// ---------------------------------------------------------------------------
// Implied action checking — canonical function shared by sequential and parallel.
//
// Part of #2670: checks action-level always-terms ([][A]_v from PROPERTY) during
// BFS for EVERY transition (including to already-seen states), matching TLC's
// Worker.java:465-469 `doNextCheckImplied` semantics.
// ---------------------------------------------------------------------------

/// Check eval-based implied actions for a transition (parent -> successor).
///
/// This is the canonical eval path for action-level promoted `PROPERTY` terms.
/// It now handles both the old ModuleRef/INSTANCE eval-only cases (#2983) and
/// the formerly compiled action-level PROPERTY terms moved here by Slice 2 of
/// #3354. Uses `eval_entry()` with array-backed state bindings BFS-inline,
/// matching TLC's `doNextCheckImplied` semantics.
///
/// Performance: slower than compiled guards per-transition (O(k) eval vs O(1) guard),
/// but vastly faster than the post-BFS safety_temporal path which iterates ALL stored
/// transitions with per-transition cache resets.
pub(crate) fn check_eval_implied_actions_for_transition(
    ctx: &mut EvalCtx,
    eval_implied_actions: &[(String, Spanned<Expr>)],
    parent: &ArrayState,
    succ: &ArrayState,
    succ_fp: Fingerprint,
) -> InvariantOutcome {
    if eval_implied_actions.is_empty() {
        return InvariantOutcome::Ok;
    }

    // Part of #3095: do not explicitly clear evaluator caches on every successor.
    //
    // `eval_entry()` already tracks the bound `(state_env, next_state_env)` pair via
    // its last-seen pointer identities and clears only the cache families invalidated
    // by the observed state/next-state change. Keeping this site on a blanket clear
    // destroys current-state reuse across sibling successors from the same parent,
    // which is exactly the hot-path tax in MCPaxosSmall's promoted PROPERTY evaluation.
    //
    // The earlier correctness bugs at this site came from scope-blind cache keys
    // (zero-arg/LET scope discrimination and lazy INSTANCE dep replay). Those are now
    // fixed at the cache key / dep-propagation layer, so this path can rely on
    // `eval_entry()`'s boundary tracking rather than forcing a per-transition reset.

    // Bind parent state (unprimed variables) and successor state (primed variables).
    let _state_guard = ctx.bind_state_env_guard(parent.env_ref());
    let _next_guard = ctx.bind_next_state_env_guard(succ.env_ref());

    // Part of #3147/#3465: Establish the array-bound eval boundary before
    // implied-action evaluation. The parent and successor are now bound via RAII
    // guards above; this clears eval-scope caches and aligns state-identity
    // tracking so eval_entry() sees the correct arrays. MCPaxosSmall false
    // positive at 185K states was caused by missing identity alignment here.
    crate::eval::clear_for_bound_state_eval_scope(ctx);

    for (name, expr) in eval_implied_actions {
        match crate::eval::eval_entry(ctx, expr) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                if debug_3147_inv() {
                    eprintln!("[DEBUG_3147] ACTION property VIOLATED: prop={name}");
                    // Decompose the Or to see which branch fails
                    if let Expr::Or(left, right) = &expr.node {
                        // Part of #3469: Route diagnostic re-evaluation through the
                        // same boundary helper as production paths. This resets
                        // state_lookup_mode and checks for leaked dep frames.
                        crate::eval::clear_for_state_eval_replay(ctx);
                        let left_result = crate::eval::eval_entry(ctx, left);
                        eprintln!("[DEBUG_3147]   Left branch (action): {:?}", left_result);
                        crate::eval::clear_for_state_eval_replay(ctx);
                        let right_result = crate::eval::eval_entry(ctx, right);
                        eprintln!(
                            "[DEBUG_3147]   Right branch (unchanged): {:?}",
                            right_result
                        );
                        // Also print parent and succ state values
                        eprintln!(
                            "[DEBUG_3147]   Parent state ({} vars): {:?}",
                            parent.values().len(),
                            &parent.values()[..parent.values().len().min(10)]
                        );
                        eprintln!(
                            "[DEBUG_3147]   Succ   state ({} vars): {:?}",
                            succ.values().len(),
                            &succ.values()[..succ.values().len().min(10)]
                        );
                    }
                }
                return InvariantOutcome::Violation {
                    invariant: name.clone(),
                    state_fp: succ_fp,
                };
            }
            Ok(_) => {
                return InvariantOutcome::Error(
                    EvalCheckError::PropertyNotBoolean(name.clone()).into(),
                );
            }
            Err(e) => {
                if debug_3147_inv() {
                    eprintln!("[DEBUG_3147] ACTION property ERROR: prop={name}, err={e:?}");
                }
                return InvariantOutcome::Error(EvalCheckError::Eval(e).into());
            }
        }
    }
    InvariantOutcome::Ok
}
