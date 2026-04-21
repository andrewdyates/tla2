// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Main identifier resolution: fast path + slow path + state/env lookup.

use super::binding_chain::resolve_binding_chain;
use super::instance_subst::eval_ident_explicit_instance_substitution;
use crate::{
    current_state_lookup_mode, eval, eval_builtin, eval_ident_shared_zero_arg_op,
    eval_zero_arg_cached, eval_zero_arg_local_op, is_dep_tracking_active,
    lazy_binding_cache_hit_deps, propagate_cached_deps, record_local_read, record_next_read,
    record_state_read, EvalCtx, EvalError, EvalResult, Expr, IdentHint, Span, StateLookupMode,
    Value,
};
use std::sync::Arc;
use tla_core::ast::OperatorDef;
use tla_core::name_intern::{intern_name, lookup_name_id, NameId};
use tla_core::VarIndex;

/// O(1) NameId-to-VarIndex lookup via the pre-built table on SharedCtx.
///
/// Returns `Some(VarIndex)` if the NameId corresponds to a state variable,
/// `None` otherwise. Replaces `VarRegistry::get_by_name_id()` linear scan.
///
/// Falls back to the linear scan when the table is empty (pre-hint-construction)
/// or the NameId is out of range (late-interned name).
///
/// Part of #3961: state var lookup is the hottest path in BFS. The linear scan
/// in `get_by_name_id` costs O(n_vars) per call; this table costs O(1).
#[inline(always)]
pub(crate) fn fast_var_idx_lookup(ctx: &EvalCtx, name_id: NameId) -> Option<VarIndex> {
    let table = &ctx.shared.var_idx_by_name_id;
    let nid = name_id.0 as usize;
    if nid < table.len() {
        // SAFETY: bounds checked above.
        let raw = unsafe { *table.get_unchecked(nid) };
        if raw != u16::MAX {
            return Some(VarIndex(raw));
        }
        None
    } else {
        // Table not yet built or name interned after table construction — fallback.
        ctx.shared.var_registry.get_by_name_id(name_id)
    }
}

/// O(1) NameId-to-OperatorDef lookup via the pre-built table on SharedCtx.
///
/// Returns `Some(&Arc<OperatorDef>)` if the NameId corresponds to a shared operator,
/// `None` otherwise. Replaces `ops.get(name)` string-hashed HashMap lookups on the
/// eval_ident hot path.
///
/// Falls back to `None` when the table is empty (pre-hint-construction) or the
/// NameId is out of range (late-interned name). Callers should fall back to
/// `ctx.shared.ops.get(name)` when this returns `None` and the hint suggests
/// an operator should exist.
///
/// Part of #3961: string-hashed HashMap lookups (SipHash + bucket probe) are
/// the remaining bottleneck after hint classification. This table converts
/// them to a bounds check + array index.
#[inline(always)]
fn fast_op_lookup(ctx: &EvalCtx, name_id: NameId) -> Option<&Arc<OperatorDef>> {
    let table = &ctx.shared.ops_by_name_id;
    let nid = name_id.0 as usize;
    if nid < table.len() {
        // SAFETY: bounds checked above.
        unsafe { table.get_unchecked(nid) }.as_ref()
    } else {
        None
    }
}

/// Evaluate an identifier expression (`Expr::Ident`).
///
/// Identifiers are the most common expression in TLA+ evaluation. This function
/// implements a two-tier lookup strategy:
///
/// **Fast path** (no INSTANCE substitutions, no local_ops): Checks BindingChain,
/// state_env, op_replacements, env, shared ops, and builtins in order.
/// This covers the common case of variable access during action evaluation (e.g.,
/// MCBakery with no INSTANCE and no LET in actions).
///
/// **Slow path** (INSTANCE/local_ops active or op_replacement exists): Handles
/// operator replacement resolution, INSTANCE substitutions, call-by-name substitutions,
/// and zero-arg operator caching with dependency tracking.
///
/// Performance critical: Defers `intern_string()` calls until absolutely needed.
/// Direct string comparison is faster for short identifiers found immediately.
///
/// Part of #3961: Restructured to minimize branching on the hot path.
/// - Resolves NameId once at the top, eliminating 5+ repeated `if let Some(id)` guards.
/// - Merges hint lookup with population check into a single array get.
/// - Defers dynamic overlay (let_def_overlay/local_ops) checks until after hint
///   lookup proves they're relevant (i.e., hint is SharedZeroArgOp or Unknown).
/// - Pre-computes `has_overlays` once, skipping `check_dynamic_overlays` call when
///   both let_def_overlay and local_ops are empty/None (the common BFS case).
/// - Short-circuits eager_subst_bindings check behind has_instance_subs guard.
/// - Accesses call_by_name_subs directly (hot field) instead of through method call.
/// - Splits Unknown hint into populated-hints vs empty-hints paths to avoid
///   running the full waterfall when hints are populated (rare late-interned names).
#[inline]
pub(crate) fn eval_ident(
    ctx: &EvalCtx,
    name: &str,
    name_id: NameId,
    span: Option<Span>,
) -> EvalResult<Value> {
    // Part of #3961: Resolve NameId once at the top. The vast majority of identifiers
    // have pre-resolved NameIds (from Expr::Ident parse-time interning). We branch
    // once here and use the concrete NameId for all subsequent lookups, eliminating
    // 5+ `if let Some(lookup_id) = maybe_name_id` guards on the fast path.
    //
    // Part of #2993: Use pre-resolved NameId from Expr::Ident when available,
    // eliminating runtime lookup_name_id() calls (global RwLock + HashMap).
    // Falls back to lookup_name_id() only for INVALID (unresolved) identifiers.
    // Fix #4044: When lookup_name_id returns None, intern the name instead of
    // short-circuiting to eval_ident_unresolved(). The extracted function was missing
    // checks for precomputed_constants, op_replacements, let_def_overlay, local_ops,
    // and the slow path (INSTANCE/call-by-name), causing incorrect "Undefined variable"
    // errors for names resolved through those fallback paths. Interning is safe here —
    // it's the rare case of a name not pre-interned during parsing, and intern_name's
    // fast path is a read lock that finds existing entries.
    let resolved_name_id = if name_id != NameId::INVALID {
        name_id
    } else if let Some(id) = lookup_name_id(name) {
        id
    } else {
        intern_name(name)
    };

    // Part of #3961: Access call_by_name_subs directly as a hot field on EvalCtx
    // (no method call overhead, no Rc deref). This is the single most common check
    // on the fast-path guard — it's None for all non-call-by-name evaluation.
    let has_instance_subs = ctx.instance_substitutions().is_some();
    // Fix #2364: Remove local_ops.is_none() from fast-path guard. Previously, ALL
    // identifiers in INSTANCE scope were forced through the slow path because INSTANCE
    // always sets local_ops. Now the fast path handles eager_subst_bindings and local_ops
    // directly, eliminating the 61x slowdown on EWD998ChanID.
    let can_take_fast_path = ctx.call_by_name_subs.is_none()
        && (!has_instance_subs || ctx.eager_subst_bindings.is_some());

    if can_take_fast_path {
        // Part of #2364 Phase 2-3: Unified BindingChain lookup — checked FIRST.
        // Part of #3260: delegated to resolve_binding_chain helper.
        if let Some(value) = resolve_binding_chain(ctx, resolved_name_id)? {
            return Ok(value);
        }

        // 0) Eager substitution bindings (INSTANCE targets) — checked first.
        //    When inside an INSTANCE scope with pre-evaluated bindings, substitution
        //    targets must be resolved before any other lookup (matching TLC's Context.cons
        //    which prepends substitution bindings to the lookup chain).
        //
        //    Part of #3961: Guard with has_instance_subs to skip the entire block
        //    when not in INSTANCE scope (the common BFS case).
        if has_instance_subs {
            if let Some(ref eager_subs) = ctx.eager_subst_bindings {
                for (id, value, deps) in eager_subs.iter() {
                    if *id == resolved_name_id {
                        if is_dep_tracking_active(ctx) {
                            propagate_cached_deps(ctx, deps);
                        }
                        return Ok(value.clone());
                    }
                }
            }
        }

        // Part of #2955: local_stack scan eliminated — BindingChain (checked above)
        // is the sole source of truth for local bindings. All bindings that were in
        // local_stack are now in the chain.

        // Part of #3961: Unified state variable lookup using O(1) var_idx_by_name_id
        // table. Resolves VarIndex ONCE and reuses it for both sparse overlay and
        // state_env access, eliminating two separate linear scans in get_by_name_id().
        if let Some(idx) = fast_var_idx_lookup(ctx, resolved_name_id) {
            // 1.8) Part of #3365: Sparse next-state overlay from ENABLED WitnessState.
            // In Next mode, bound sparse slots override current-state values.
            if current_state_lookup_mode(ctx) == StateLookupMode::Next {
                if let Some(sparse_env) = ctx.sparse_next_state_env {
                    // SAFETY: idx bounded by VarRegistry, sparse_env has same layout.
                    let slot = unsafe { sparse_env.get_unchecked(idx.as_usize()) };
                    if let Some(v) = slot {
                        record_next_read(ctx, idx, v);
                        return Ok(v.clone());
                    }
                    // None = unbound in witness, fall through to current state
                }
            }

            // 2) Check state_env (state variables like "num", "pc") - hot path
            //    State variables never have op_replacements, return immediately if found.
            if let Some(state_env) = ctx.state_env {
                debug_assert!(idx.as_usize() < state_env.env_len());
                // SAFETY: `idx` is sourced from the active VarRegistry and bounded above.
                let v = unsafe { state_env.get_value(idx.as_usize()) };
                record_state_read(ctx, idx, &v);
                return Ok(v);
            }
        }

        // Part of #3961: Hint-based dispatch for non-binding, non-state-var identifiers.
        //
        // After BindingChain (quantifier/LET vars) and state_env (state variables)
        // failed to match, use the pre-classified ident_hints table to jump directly
        // to the correct resolution tier. This eliminates the waterfall of 4-7
        // HashMap/Option checks per call.
        //
        // The hint table classifies ALL op_replacements, precomputed constants, shared
        // ops, and builtins at setup time. When hints are populated, we can trust them
        // completely — no redundant HashMap checks needed. The only fallback is for
        // `Unknown` hints (rare: names interned after hint table construction) and
        // `StateVar` hints when state_env is not set (property checking context).
        //
        // Part of #3961: Merged hint lookup with population check into a single
        // array access. When hints are empty (not yet built), all accesses return
        // Unknown, which correctly falls through to the full waterfall.
        let hints = &ctx.shared.ident_hints;
        let hint = if (resolved_name_id.0 as usize) < hints.len() {
            // SAFETY: bounds checked above.
            unsafe { *hints.get_unchecked(resolved_name_id.0 as usize) }
        } else {
            IdentHint::Unknown
        };

        // OpReplacement hint -> must go through slow path for replacement resolution.
        if hint == IdentHint::OpReplacement {
            // Fall through to slow path (below the fast-path block)
        } else if hint == IdentHint::Unknown
            && !ctx.shared.op_replacements.is_empty()
            && ctx.shared.op_replacements.get(name).is_some()
        {
            // Unknown hint with an op_replacement match — fall through to slow path.
            // This covers both the pre-hint-table startup path and the rare case of
            // names interned after hint construction that happen to have replacements.
        } else {
            // No replacement — use hint-based dispatch.
            //
            // Dynamic overlays (let_def_overlay, local_ops) can shadow static hints
            // for PrecomputedConstant, SharedZeroArgOp, and Unknown hints.
            // INSTANCE local_ops can shadow any hint (fix #4068). LET defs go
            // through BindingChain (already checked above). Builtin hints are
            // not shadowed because builtins are language-level, not user-defined.
            //
            // Part of #3961: has_overlays is deferred into specific arms that need
            // it (PrecomputedConstant, SharedZeroArgOp, Unknown) to avoid the check
            // for Builtin/StateVar which never need it.
            match hint {
                IdentHint::PrecomputedConstant => {
                    // Fix #4068: INSTANCE local_ops can shadow precomputed constants.
                    // When inside an INSTANCE scope, the instance module may define
                    // an operator with the same name as an outer precomputed constant
                    // (e.g., EWD998Chan defines `Node == 0..N-1` while the outer
                    // EWD998ChanID has `CONSTANT Node = {n1,...,n5}`). The local_ops
                    // definition must take priority.
                    let has_overlays = !ctx.let_def_overlay.is_empty() || ctx.local_ops.is_some();
                    if has_overlays {
                        if let Some(v) =
                            check_dynamic_overlays(ctx, name, resolved_name_id, has_instance_subs, span)?
                        {
                            return Ok(v);
                        }
                    }
                    if let Some(value) = ctx.shared.precomputed_constants.get(&resolved_name_id) {
                        return Ok(value.clone());
                    }
                    // Hint was stale — fall through to cold waterfall.
                }
                IdentHint::SharedZeroArgOp => {
                    // Part of #3961: Only check dynamic overlays when they exist.
                    // Computed here (not at function top) to avoid the check for
                    // PrecomputedConstant/Builtin/StateVar which never need it.
                    let has_overlays = !ctx.let_def_overlay.is_empty() || ctx.local_ops.is_some();
                    if has_overlays {
                        if let Some(v) =
                            check_dynamic_overlays(ctx, name, resolved_name_id, has_instance_subs, span)?
                        {
                            return Ok(v);
                        }
                    }
                    // Part of #3961: When hint is SharedZeroArgOp, the entry is
                    // guaranteed to be in ops_by_name_id (built at the same time as
                    // hints in build_ident_hints). No string-hash fallback needed.
                    if let Some(def) = fast_op_lookup(ctx, resolved_name_id) {
                        if def.params.is_empty() {
                            if has_overlays || has_instance_subs {
                                return eval_ident_shared_zero_arg_op(ctx, name, def, span);
                            }
                            return eval_zero_arg_cached(ctx, ctx, name, def, span, false);
                        }
                    }
                    // Hint was stale — fall through to cold waterfall.
                }
                IdentHint::Builtin => {
                    if let Some(result) = eval_builtin(ctx, name, &[], span)? {
                        return Ok(result);
                    }
                    // Hint was stale — fall through to cold waterfall.
                }
                IdentHint::StateVar => {
                    // State var not found via state_env (step 2) — may be during
                    // property checking when state_env is not set. Fall through.
                }
                IdentHint::SharedParamOp => {
                    // SharedParamOp: not evaluable as zero-arg, will be an error.
                }
                IdentHint::OpReplacement => {
                    // Already handled above (unreachable).
                }
                IdentHint::Unknown => {
                    // No hint — fall through to cold waterfall below.
                }
            }

            // Part of #3961: Moved waterfall fallback to a cold out-of-line function.
            // This path handles stale hints and Unknown names. During BFS, >99% of
            // identifiers resolve in the hint dispatch above. Keeping the waterfall
            // out-of-line reduces I-cache pressure on the hot path.
            return eval_ident_waterfall_fallback(
                ctx, name, resolved_name_id, has_instance_subs, hint, span,
            );
        }
        // Has op_replacement - fall through to slow path
    }

    // Slow path - only reached when INSTANCE/local_ops active, or op_replacement exists.
    // Part of #3260: delegated to resolve_binding_chain helper.
    eval_ident_slow(ctx, name, resolved_name_id, has_instance_subs, span)
}

/// Check dynamic overlays (let_def_overlay, local_ops) for a name.
///
/// Returns `Ok(Some(value))` if found in an overlay, `Ok(None)` if not.
/// Only checks overlays that are non-empty — the common BFS case has both empty.
///
/// Part of #3961: Extracted to avoid duplicating the overlay check in both
/// SharedZeroArgOp and Unknown hint arms.
///
/// Part of #3961: Uses NameId-based lookup (`get_by_id`) for LetDefOverlay,
/// replacing string comparison with integer comparison. The NameId is stored
/// at overlay construction time (cons) to avoid re-interning.
#[inline]
fn check_dynamic_overlays(
    ctx: &EvalCtx,
    name: &str,
    resolved_name_id: NameId,
    _has_instance_subs: bool,
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    if !ctx.let_def_overlay.is_empty() {
        // Part of #3961: Use NameId integer comparison instead of string comparison.
        if let Some(def) = ctx.let_def_overlay.get_by_id(resolved_name_id) {
            if def.params.is_empty()
                && !matches!(&def.body.node, Expr::InstanceExpr(_, _))
            {
                return eval_zero_arg_local_op(ctx, name, def, span).map(Some);
            }
        }
    }
    if let Some(ref local) = ctx.local_ops {
        if let Some(def) = local.get(name) {
            if def.params.is_empty() && !matches!(&def.body.node, Expr::InstanceExpr(_, _)) {
                return eval_zero_arg_local_op(ctx, name, def, span).map(Some);
            }
        }
    }
    Ok(None)
}

/// Cold waterfall fallback for stale hints and Unknown names.
///
/// This function runs when the hint-based dispatch in eval_ident doesn't find the
/// name (stale hint or Unknown). It checks all remaining resolution tiers, skipping
/// tiers already tried by the hint dispatch.
///
/// Part of #3961: Extracted from the inline fast path to reduce I-cache pressure.
/// During BFS, >99% of identifiers resolve in the hint dispatch above, so this
/// function is rarely called. Marking it #[cold] #[inline(never)] tells the compiler
/// to optimize the fast path at the expense of this path.
///
/// Fix #4044: Full waterfall is required for correctness. Cannot be removed.
#[cold]
#[inline(never)]
fn eval_ident_waterfall_fallback(
    ctx: &EvalCtx,
    name: &str,
    resolved_name_id: NameId,
    has_instance_subs: bool,
    hint: IdentHint,
    span: Option<Span>,
) -> EvalResult<Value> {
    let has_overlays = !ctx.let_def_overlay.is_empty() || ctx.local_ops.is_some();

    // Tier 1: dynamic overlays — skip if SharedZeroArgOp already checked them.
    if has_overlays && hint != IdentHint::SharedZeroArgOp {
        if let Some(v) = check_dynamic_overlays(ctx, name, resolved_name_id, has_instance_subs, span)? {
            return Ok(v);
        }
    }
    // Tier 2: precomputed constants — skip if PrecomputedConstant already checked.
    if hint != IdentHint::PrecomputedConstant {
        if let Some(value) = ctx.shared.precomputed_constants.get(&resolved_name_id) {
            return Ok(value.clone());
        }
    }
    // Tier 3: shared zero-arg ops — skip if SharedZeroArgOp already checked.
    // Part of #3961: Use O(1) NameId-indexed ops table, fall back to string lookup.
    if hint != IdentHint::SharedZeroArgOp {
        let def = fast_op_lookup(ctx, resolved_name_id)
            .or_else(|| ctx.shared.ops.get(name));
        if let Some(def) = def {
            if def.params.is_empty() {
                if has_overlays || has_instance_subs {
                    return eval_ident_shared_zero_arg_op(ctx, name, def, span);
                }
                return eval_zero_arg_cached(ctx, ctx, name, def, span, false);
            }
        }
    }
    // Tier 4: builtins — skip if Builtin already checked.
    if hint != IdentHint::Builtin {
        if let Some(result) = eval_builtin(ctx, name, &[], span)? {
            return Ok(result);
        }
    }

    // env.get() fallback — the one tier not covered by the hint table.
    // Relevant when state_env is not set (property checking, init eval).
    if ctx.state_env.is_none() {
        if let Some(v) = ctx.env.get(name) {
            // Part of #3961: Use O(1) var_idx_by_name_id table.
            if let Some(idx) = fast_var_idx_lookup(ctx, resolved_name_id) {
                record_state_read(ctx, idx, v);
            }
            return Ok(v.clone());
        }
    }

    // Not found
    Err(EvalError::UndefinedVar {
        name: name.to_string(),
        span,
    })
}

/// Slow path for eval_ident — handles INSTANCE/local_ops/op_replacement resolution.
///
/// Separated from the inlined fast path to reduce code size at call sites.
///
/// Part of #3961: Takes a concrete `NameId` instead of `Option<NameId>`, eliminating
/// repeated Option unwrapping throughout.
#[inline(never)]
fn eval_ident_slow(
    ctx: &EvalCtx,
    name: &str,
    orig_name_id: NameId,
    _has_instance_subs: bool,
    span: Option<Span>,
) -> EvalResult<Value> {
    if let Some(value) = resolve_binding_chain(ctx, orig_name_id)? {
        return Ok(value);
    }

    // Apply operator replacement if configured (e.g., NumActors <- n).
    let resolved_name = ctx.resolve_op_name(name);

    // Replacement target may be bound via BindingChain.
    let resolved_op_name_id = if resolved_name == name {
        orig_name_id
    } else if let Some(id) = lookup_name_id(resolved_name) {
        id
    } else {
        intern_name(resolved_name)
    };
    if resolved_name != name {
        if let Some((bv, source)) = ctx.bindings.lookup(resolved_op_name_id) {
            let mode = current_state_lookup_mode(ctx);
            if let Some(v) = bv.get_if_ready(mode, source) {
                if let Some(lazy) = bv.as_lazy() {
                    lazy_binding_cache_hit_deps(ctx, lazy, source, &v, resolved_op_name_id, mode);
                    return Ok(v);
                }
                match source {
                    crate::binding_chain::BindingSourceRef::Instance(deps) => {
                        if is_dep_tracking_active(ctx) {
                            propagate_cached_deps(ctx, deps);
                        }
                    }
                    crate::binding_chain::BindingSourceRef::Local(stack_idx)
                    | crate::binding_chain::BindingSourceRef::Liveness(stack_idx) => {
                        record_local_read(ctx, stack_idx, resolved_op_name_id, &v);
                    }
                    crate::binding_chain::BindingSourceRef::None => {}
                }
                return crate::force_lazy_thunk_if_needed(ctx, v);
            }
            if let crate::binding_chain::BindingSourceRef::Instance(_) = source {
                if let Some(lazy) = bv.as_lazy() {
                    let lazy_ptr = lazy as *const crate::binding_chain::LazyBinding as usize;
                    if let Some(cached) = crate::cache::small_caches::instance_lazy_cache_get(
                        lazy_ptr, mode as u8,
                    ) {
                        lazy_binding_cache_hit_deps(
                            ctx,
                            lazy,
                            source,
                            &cached,
                            resolved_op_name_id,
                            mode,
                        );
                        return Ok(cached);
                    }
                }
            }
            if let Some(lazy) = bv.as_lazy() {
                return crate::force_lazy_binding(ctx, lazy, source, resolved_op_name_id, mode);
            }
        }
    }

    // 2) Apply active INSTANCE substitutions (TLC composes these through nested instances).
    //
    // This must happen BEFORE checking state/env bindings so that an instanced module's
    // variables/constants can be mapped to expressions (e.g., active <- Node2Nat(active)).
    //
    // Fix #2364: Eager value bypass — use pre-evaluated substitution bindings.
    // If the name matches, return the pre-computed value directly (bypassing SUBST_CACHE).
    // If the name is NOT in the set, skip SUBST_CACHE entirely.
    if let Some(ref eager_subs) = ctx.eager_subst_bindings {
        let check_id = if resolved_name == name {
            orig_name_id
        } else {
            resolved_op_name_id
        };
        for (id, value, deps) in eager_subs.iter() {
            if *id == check_id {
                if is_dep_tracking_active(ctx) {
                    propagate_cached_deps(ctx, deps);
                }
                return Ok(value.clone());
            }
        }
        // Name not in substitution targets → skip SUBST_CACHE entirely.
    } else if let Some(value) = eval_ident_explicit_instance_substitution(ctx, resolved_name)? {
        return Ok(value);
    }

    // Part of #188: Apply call-by-name substitutions (for operators with primed parameters).
    //
    // Unlike INSTANCE substitutions which evaluate in outer context, call-by-name subs
    // evaluate in the CURRENT context because the argument expression was written in the
    // calling context. We just need to avoid infinite recursion by clearing call_by_name_subs.
    if let Some(subs) = ctx.call_by_name_subs() {
        if let Some(sub) = subs.iter().find(|s| s.from.node == resolved_name) {
            // Evaluate the substituted expression in the current context,
            // but without call_by_name_subs to avoid infinite recursion.
            let inner_ctx = ctx.without_call_by_name_subs();
            return eval(&inner_ctx, &sub.to);
        }
    }

    // 3) Check local (in-scope) zero-argument operators next.
    //
    // IMPORTANT: When evaluating an operator from the *outer* module while we're inside an
    // INSTANCE scope, instance substitutions must NOT apply to that outer operator body.
    // Only operators from the instanced module (local_ops) should see substitutions.
    if let Some(def) = ctx
        .local_ops
        .as_ref()
        .and_then(|local| local.get(resolved_name))
    {
        // Fix #2984: Skip InstanceExpr bodies (see fast path step 4b for details).
        if def.params.is_empty() && !matches!(&def.body.node, Expr::InstanceExpr(_, _)) {
            return eval_zero_arg_local_op(ctx, resolved_name, def, span);
        }
    }

    // 4) Check precomputed constants (Part of #2364, #2895).
    //    Checked BEFORE state/env to match fast-path reorder. After constant
    //    promotion, model-config constants are here (NameId-keyed, O(1)).
    let precomputed_id = if resolved_name == name {
        orig_name_id
    } else {
        resolved_op_name_id
    };
    if let Some(value) = ctx.shared.precomputed_constants.get(&precomputed_id) {
        return Ok(value.clone());
    }

    // 4b) Fall back to state/environment bindings.
    if let Some(value) = lookup_state_or_env(ctx, name, Some(orig_name_id)) {
        return Ok(value);
    }
    if resolved_name != name {
        if let Some(value) = lookup_state_or_env(ctx, resolved_name, Some(resolved_op_name_id)) {
            return Ok(value);
        }
    }

    // 5b) Check shared (outer-module) zero-argument operators.
    // Part of #3961: Use O(1) NameId-indexed ops table, fall back to string lookup.
    let resolved_op_id = if resolved_name == name {
        orig_name_id
    } else {
        resolved_op_name_id
    };
    let def = fast_op_lookup(ctx, resolved_op_id)
        .or_else(|| ctx.shared.ops.get(resolved_name));
    if let Some(def) = def {
        if def.params.is_empty() {
            return eval_ident_shared_zero_arg_op(ctx, resolved_name, def, span);
        }
    }
    // Check for zero-argument builtins (BOOLEAN, etc.)
    if let Some(result) = eval_builtin(ctx, resolved_name, &[], span)? {
        return Ok(result);
    }
    // Not found
    Err(EvalError::UndefinedVar {
        name: resolved_name.to_string(),
        span,
    })
}

#[inline]
fn lookup_state_or_env(ctx: &EvalCtx, name: &str, maybe_name_id: Option<NameId>) -> Option<Value> {
    if let Some(state_env) = ctx.state_env {
        if let Some(name_id) = maybe_name_id {
            // Part of #3961: Use O(1) var_idx_by_name_id table instead of linear scan.
            if let Some(idx) = fast_var_idx_lookup(ctx, name_id) {
                debug_assert!(idx.as_usize() < state_env.env_len());
                // SAFETY: `state_env` borrows a live `[Value]` slice and `idx` is bounded above.
                let value = unsafe { state_env.get_value(idx.as_usize()) };
                record_state_read(ctx, idx, &value);
                return Some(value);
            }
        }
    }

    // Part of #2895: After promotion, env contains only state variables.
    // When state_env is set and name is interned, state_env (above) handles all
    // state vars, and non-state-var names won't be in env either. Skip the
    // string-hashing HashMap lookup on the BFS hot path.
    if maybe_name_id.is_none() || ctx.state_env.is_none() {
        let value = ctx.env.get(name)?;
        if let Some(name_id) = maybe_name_id {
            // Part of #3961: Use O(1) var_idx_by_name_id table instead of linear scan.
            if let Some(idx) = fast_var_idx_lookup(ctx, name_id) {
                if current_state_lookup_mode(ctx) == StateLookupMode::Next {
                    record_next_read(ctx, idx, value);
                } else {
                    record_state_read(ctx, idx, value);
                }
            }
        }
        return Some(value.clone());
    }
    None
}
