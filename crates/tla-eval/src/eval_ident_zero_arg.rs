// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unified zero-arg operator caching for identifier evaluation.
//!
//! Consolidates the 10-step caching pattern that was duplicated across three
//! call sites in `eval_ident.rs`: fast-path inline, `eval_zero_arg_local_op`,
//! and `eval_ident_shared_zero_arg_op`.
//!
//! Part of #2669.
//! Fix #2462: ZERO_ARG_OP_CONST_CACHE removed. All entries go through
//! ZERO_ARG_OP_CACHE with dep validation via op_cache_entry_valid().

#[cfg(debug_assertions)]
use super::debug_zero_cache;
use super::{
    build_lazy_func_from_ctx, current_state_lookup_mode, eval, eval_builtin,
    materialize_setpred_to_vec, no_local_ops_cache, op_cache_entry_valid, propagate_cached_deps,
    should_prefer_builtin_override, zero_arg_insert, zero_arg_lookup, CachedOpResult, EvalCtx,
    EvalError, EvalResult, Expr, LazyDomain, OpDepGuard, OpEvalDeps, Span, StateLookupMode, Value,
};
use crate::cache::zero_arg_cache::{
    record_zero_arg_canonical_hit, record_zero_arg_constant_fallback_hit, record_zero_arg_miss,
    record_zero_arg_primary_hit, zero_arg_cache_key,
};
use std::sync::Arc;
use tla_core::ast::{BoundVar, OperatorDef};
use tla_core::expr_mentions_name_spanned_v;
use tla_core::name_intern::intern_name;
use tla_core::Spanned;

/// Unified zero-arg operator caching. Consolidates the 10-step caching pattern
/// from three call sites in `eval_ident.rs`.
///
/// Fix #2462: All entries (both constant and state-dependent) are stored in
/// ZERO_ARG_OP_CACHE with dep validation. The separate unvalidated
/// ZERO_ARG_OP_CONST_CACHE has been removed.
///
/// # Parameters
///
/// * `eval_ctx` — Context for evaluation (may be `outer_ctx` for shared ops).
/// * `propagate_ctx` — Context for dep propagation on cache hit (always the
///   original calling `ctx`). Also used for `current_state_lookup_mode` and
///   `should_prefer_builtin_override` checks.
/// * `name` — Operator name.
/// * `def` — Operator definition.
/// * `span` — Source location for error reporting.
/// * `env_pre_check` — `true` for local ops per Fix #100 (check env for
///   existing LazyFunc before constructing a new one).
pub(super) fn eval_zero_arg_cached(
    eval_ctx: &EvalCtx,
    propagate_ctx: &EvalCtx,
    name: &str,
    def: &Arc<OperatorDef>,
    span: Option<Span>,
    env_pre_check: bool,
) -> EvalResult<Value> {
    let action_eval_ctx;
    let eval_ctx = if eval_ctx.in_tlc_action_scope() && eval_ctx.tlc_action_context().is_none() {
        action_eval_ctx = {
            let mut ctx = eval_ctx.clone();
            ctx.install_outermost_tlc_action_context(def);
            ctx
        };
        &action_eval_ctx
    } else {
        eval_ctx
    };

    // Step 1: Builtin override preference check.
    if should_prefer_builtin_override(name, def, 0, propagate_ctx) {
        if let Some(result) = eval_builtin(eval_ctx, name, &[], span)? {
            return Ok(result);
        }
    }

    // Steps 2-5: Self-referential FuncDef detection + cache + construction.
    if let Expr::FuncDef(bounds, func_body) = &def.body.node {
        if expr_mentions_name_spanned_v(func_body, name) {
            return eval_self_referential_func(
                eval_ctx,
                propagate_ctx,
                name,
                def,
                bounds,
                func_body.as_ref(),
                span,
                env_pre_check,
            );
        }
    }

    // Steps 6-10: General zero-arg caching.
    eval_general_zero_arg(eval_ctx, propagate_ctx, name, def, span)
}

/// Handle self-referential FuncDef operators (e.g., `nat2node[i \in S] == ... nat2node[i-1] ...`).
///
/// These need special treatment: a `LazyFunc` is constructed with the domain and body,
/// and the cached LazyFunc preserves its memo across calls.
#[allow(clippy::too_many_arguments)]
fn eval_self_referential_func(
    eval_ctx: &EvalCtx,
    propagate_ctx: &EvalCtx,
    name: &str,
    def: &Arc<OperatorDef>,
    bounds: &[BoundVar],
    func_body: &Spanned<Expr>,
    span: Option<Span>,
    env_pre_check: bool,
) -> EvalResult<Value> {
    // Fix #100: For local ops, check env for existing LazyFunc first (shared memoization).
    if env_pre_check {
        if let Some(existing) = propagate_ctx.env.get(name) {
            if matches!(existing, Value::LazyFunc(_)) {
                return Ok(existing.clone());
            }
        }
    }

    // Check cache for existing LazyFunc with populated memo.
    // Fix #2462: All lookups go through ZERO_ARG_OP_CACHE with dep validation.
    // Part of #3100: Use zero_arg_lookup to probe both state and persistent partitions.
    if !no_local_ops_cache() {
        let is_next_state = current_state_lookup_mode(propagate_ctx) == StateLookupMode::Next;
        let def_loc = def.body.span.start;
        let name_id = intern_name(name);
        let cache_key = zero_arg_cache_key(eval_ctx, name_id, def_loc, is_next_state);

        if let Some(entry) = zero_arg_lookup(&cache_key, |entry| {
            matches!(entry.value, Value::LazyFunc(_)) && op_cache_entry_valid(eval_ctx, entry)
        }) {
            propagate_cached_deps(propagate_ctx, &entry.deps);
            return Ok(entry.value);
        }

        // Canonical key fallback for self-referential LazyFunc (same rationale as
        // Step 6b in eval_general_zero_arg — unstable local_ops_id from recursive ops).
        {
            let canonical_key = crate::cache::zero_arg_cache::zero_arg_canonical_key(
                eval_ctx.shared.id,
                name_id,
                def_loc,
                is_next_state,
            );
            if let Some(entry) =
                crate::cache::zero_arg_cache::zero_arg_canonical_lookup(&canonical_key)
            {
                if matches!(entry.value, Value::LazyFunc(_)) {
                    propagate_cached_deps(propagate_ctx, &entry.deps);
                    return Ok(entry.value);
                }
            }
        }

        // Part of #3109: During ENABLED scope, retry with flipped is_next_state
        // for constant LazyFunc entries (empty deps).
        // Part of #4027: Use shadow via in_enabled_scope_ctx for consistency.
        if crate::cache::lifecycle::in_enabled_scope_ctx(eval_ctx) {
            if let Some(entry) =
                crate::cache::zero_arg_cache::zero_arg_constant_fallback(&cache_key)
            {
                if matches!(entry.value, Value::LazyFunc(_)) {
                    propagate_cached_deps(propagate_ctx, &entry.deps);
                    return Ok(entry.value.clone());
                }
            }
        }
    }

    // Cache miss: construct LazyFunc.
    let domain_val = eval_ident_func_domain(eval_ctx, bounds, span)?;
    if !domain_val.is_set() {
        return Err(EvalError::type_error(
            "Set",
            &domain_val,
            Some(def.body.span),
        ));
    }
    let op_name = Arc::from(name);
    let lazy = build_lazy_func_from_ctx(
        eval_ctx,
        Some(Arc::clone(&op_name)),
        LazyDomain::General(Box::new(domain_val)),
        bounds,
        func_body.clone(),
    );
    let result = Value::LazyFunc(Arc::new(lazy));

    // Fix #4145: Self-referential LazyFuncs MUST NOT be placed in the persistent
    // partition. The LazyFunc captures state arrays via `snapshot_state_envs()` and
    // accumulates state-dependent results in its memo table. If persisted across
    // state boundaries, the stale captured state and populated memo cause incorrect
    // results (VoteProof: 4180 states instead of 6962).
    //
    // Set `instance_lazy_read = true` to route to the state partition, which is
    // cleared on every state boundary. This ensures each state gets a fresh
    // LazyFunc with empty memo and correct captured state. Unlike `inconsistent`,
    // `instance_lazy_read` still allows cache hits within the same state via
    // `op_cache_entry_valid()` (which does not check `instance_lazy_read`).
    //
    // Do NOT store under canonical key (canonical is for persistent/constant
    // entries only).
    //
    // Prior code used `OpEvalDeps::default()` (empty deps → persistent partition),
    // which was incorrect: "LazyFunc creation is pure" ignored that the LazyFunc's
    // memo and captured state are state-dependent at application time.
    if !no_local_ops_cache() {
        let is_next_state = current_state_lookup_mode(propagate_ctx) == StateLookupMode::Next;
        let def_loc = def.body.span.start;
        let name_id = intern_name(name);
        let cache_key = zero_arg_cache_key(eval_ctx, name_id, def_loc, is_next_state);

        let deps = OpEvalDeps {
            instance_lazy_read: true,
            ..OpEvalDeps::default()
        };
        zero_arg_insert(
            cache_key,
            CachedOpResult {
                value: result.clone(),
                deps,
            },
        );
    }
    Ok(result)
}

/// General zero-arg operator caching (non-self-referential operators).
///
/// Steps 6-10 of the unified caching pattern: dep-validated cache scan,
/// cache-miss evaluation with dep tracking, SetPred materialization,
/// and cache store.
///
/// Fix #2462: ZERO_ARG_OP_CONST_CACHE removed. All entries (including those
/// with empty deps) go through ZERO_ARG_OP_CACHE with dep validation.
fn eval_general_zero_arg(
    eval_ctx: &EvalCtx,
    propagate_ctx: &EvalCtx,
    name: &str,
    def: &Arc<OperatorDef>,
    _span: Option<Span>,
) -> EvalResult<Value> {
    // Issue #284: TLA2_NO_LOCAL_OPS_CACHE disables caching to match TLC semantics.
    if no_local_ops_cache() {
        return eval(eval_ctx, &def.body);
    }

    let is_next_state = current_state_lookup_mode(propagate_ctx) == StateLookupMode::Next;
    let def_loc = def.body.span.start;
    let name_id = intern_name(name);
    // Part of #3097: Use shared helper for scope-discriminated key.
    let cache_key = zero_arg_cache_key(eval_ctx, name_id, def_loc, is_next_state);

    // Step 6-7: Part of #3100 — probe both state and persistent partitions.
    if let Some(entry) = zero_arg_lookup(&cache_key, |entry| op_cache_entry_valid(eval_ctx, entry))
    {
        record_zero_arg_primary_hit();
        propagate_cached_deps(propagate_ctx, &entry.deps);
        return Ok(entry.value);
    }

    // Step 6b: Canonical key fallback for constant operators.
    //
    // When `local_ops` contains recursive operators (e.g., RECURSIVE PublicKeyOf
    // in INSTANCE Nano), `compute_local_ops_scope_id` falls back to Arc pointer
    // identity, producing a different `local_ops_id` each time
    // `with_outer_resolution_scope()` is called. This makes scope-discriminated
    // keys unstable for shared operators accessed through INSTANCE modules.
    //
    // Constant operators (empty deps) produce the same value regardless of scope,
    // so a scope-normalized "canonical" key (local_ops_id=0, instance_subs_id=0)
    // allows persistent entries to be found across scope changes.
    {
        let canonical_key = crate::cache::zero_arg_cache::zero_arg_canonical_key(
            eval_ctx.shared.id,
            name_id,
            def_loc,
            is_next_state,
        );
        if let Some(entry) =
            crate::cache::zero_arg_cache::zero_arg_canonical_lookup(&canonical_key)
        {
            record_zero_arg_canonical_hit();
            propagate_cached_deps(propagate_ctx, &entry.deps);
            return Ok(entry.value);
        }
    }

    // Part of #3109: During ENABLED scope, retry with flipped is_next_state.
    // Part of #4027: Use shadow via in_enabled_scope_ctx for consistency.
    if crate::cache::lifecycle::in_enabled_scope_ctx(eval_ctx) {
        if let Some(entry) = crate::cache::zero_arg_cache::zero_arg_constant_fallback(&cache_key) {
            record_zero_arg_constant_fallback_hit();
            propagate_cached_deps(propagate_ctx, &entry.deps);
            return Ok(entry.value.clone());
        }
    }

    // Step 8: Cache miss — evaluate with dep tracking + SetPred materialization.
    debug_eprintln!(
        debug_zero_cache(),
        "[ZERO_CACHE] MISS: {} (next={})",
        name,
        is_next_state
    );
    let base_stack_len = eval_ctx.binding_depth;
    let guard = OpDepGuard::from_ctx(eval_ctx, base_stack_len);
    let val = eval(eval_ctx, &def.body)?;

    // Step 9: Materialize SetPred within dep scope (Fix #1894).
    // Previously missing for local ops — now applied uniformly.
    let val = match &val {
        Value::SetPred(spv) => {
            let elems = materialize_setpred_to_vec(eval_ctx, spv)?;
            Value::set(elems)
        }
        _ => val,
    };

    // Step 9b: Eagerly materialize small finite lazy set types (SetCup, RecordSet,
    // TupleSet) into flat Value::Set(SortedSet) for efficient membership checking.
    //
    // Constant operators like `Block == GenesisBlock \cup SendBlock \cup ...` produce
    // SetCup(RecordSet, SetCup(RecordSet, ...)) trees. Each membership check traverses
    // this tree, calling RecordSet::contains at every node. For MCNanoMedium, this
    // makes TypeInvariant checking ~2x slower than necessary.
    //
    // Materializing to a flat SortedSet converts tree-traversal membership (O(depth *
    // field_checks)) to binary search (O(log n * comparison_cost)). For a 74-element
    // Block set, this is ~6 comparisons vs ~5 RecordSet field-check chains.
    //
    // Only materialize when: (1) cardinality is known and <= 10000, (2) the value
    // is a lazy set type that benefits from materialization. Skip for Value::Set
    // (already flat), Value::Subset (SUBSET S is exponential), Value::FuncSet
    // ([S -> T] is exponential), Value::BigUnion, Value::SeqSet (may be infinite).
    let val = match &val {
        Value::SetCup(_) | Value::RecordSet(_) | Value::TupleSet(_) | Value::SetCap(_)
        | Value::SetDiff(_) | Value::KSubset(_) => {
            use num_traits::ToPrimitive;
            if let Some(len) = val.set_len() {
                if let Some(n) = len.to_u64() {
                    if n <= 10_000 {
                        if let Some(sorted) = val.to_sorted_set() {
                            Value::Set(Arc::new(sorted))
                        } else {
                            val
                        }
                    } else {
                        val
                    }
                } else {
                    val
                }
            } else {
                val
            }
        }
        _ => val,
    };

    let mut deps = match guard.try_take_deps() {
        Some(mut deps) => {
            // Fix #2991: Strip local deps that are internal to this operator evaluation.
            // Internal locals (quantifier iteration variables, comprehension bindings) leak
            // into deps via Instance binding propagation, bypassing record_local_read's
            // depth filter. This causes false `inconsistent=true`, preventing caching.
            deps.strip_internal_locals(&eval_ctx.bindings, base_stack_len);
            record_zero_arg_miss(name, &deps);
            propagate_cached_deps(eval_ctx, &deps);
            deps
        }
        None => {
            return Err(EvalError::Internal {
                message: "dep tracking stack empty after zero-arg op eval".into(),
                span: Some(def.body.span),
            });
        }
    };

    // Part of #3964: Check if LazyFunc name is already set via read-only Arc
    // access before calling Arc::make_mut. This avoids a deep clone of the
    // LazyFuncValue when the name is already set (common case for cached results).
    let mut val = val;
    if let Value::LazyFunc(ref mut f) = val {
        if f.name().is_none() {
            Arc::make_mut(f).set_name_if_missing(Arc::from(name));
        }
    }
    let result = val;

    // Part of #4158: Non-self-referential LazyFuncs that capture state MUST NOT be
    // placed in the persistent partition. Like the self-referential case (Fix #4145),
    // FuncDef evaluation constructs a LazyFunc via `build_lazy_func_from_ctx()` which
    // captures state arrays via `snapshot_state_envs()`. But dep tracking during
    // FuncDef construction sees no state reads (only pointer copies for domain eval +
    // closure capture). Empty deps → `deps_are_persistent()` returns true → persistent
    // partition. In a subsequent state, the stale LazyFunc returns wrong results from
    // its captured state and accumulated memo entries.
    //
    // Example: `F == [x \in Nat |-> x + state_var]` — FuncDef over infinite domain
    // produces a LazyFunc with captured state. Dep tracking sees no state reads during
    // construction, so deps are empty. Without this guard, F is cached persistently
    // and reused across states with stale captured state.
    //
    // Same pattern as Fix #4145 for self-referential case and the `value_captures_state`
    // guard in eval_let/zero_arg_cache.rs for the LET cache path.
    if let Value::LazyFunc(ref f) = result {
        if f.captured_state().is_some() || f.captured_next_state().is_some() {
            deps.instance_lazy_read = true;
        }
    }

    // Step 10: Cache store.
    // Part of #3100: zero_arg_insert routes to persistent or state partition by deps.
    // Part of #3109: Skip insertion during ENABLED scope — dep tracking unreliable.
    // Exception: persistent-qualified deps (empty state/local/next, not inconsistent,
    // not instance_lazy_read) are truly constant — their results are identical whether
    // evaluated inside or outside ENABLED scope. Caching these during ENABLED prevents
    // catastrophic re-evaluation of constant operators like SpanTreeRandom's `Edges`
    // (which calls RandomElement(SUBSET ...) and takes O(2^n) fingerprinting per call).
    // TLC equivalent: constant LazyValues are shared across EvalControl contexts.
    // Part of #4027: Use shadow via in_enabled_scope_ctx for consistency.
    let in_enabled = crate::cache::lifecycle::in_enabled_scope_ctx(eval_ctx);
    let is_persistent = crate::cache::zero_arg_cache::deps_are_persistent(&deps);
    if !deps.inconsistent && (!in_enabled || is_persistent) {
        // Also store under canonical key for constant operators so future lookups
        // from different scope contexts (different Arc<OpEnv> pointers for recursive
        // local_ops) can find the cached result.
        if is_persistent {
            let canonical_key = crate::cache::zero_arg_cache::zero_arg_canonical_key(
                eval_ctx.shared.id,
                name_id,
                def_loc,
                is_next_state,
            );
            crate::cache::zero_arg_cache::zero_arg_canonical_insert(
                canonical_key,
                CachedOpResult {
                    value: result.clone(),
                    deps: deps.clone(),
                },
            );
        }
        zero_arg_insert(
            cache_key,
            CachedOpResult {
                value: result.clone(),
                deps,
            },
        );
    }

    Ok(result)
}

/// Evaluate a resolved zero-argument operator with the same cache and scope
/// boundaries used by `eval_ident`.
pub(crate) fn eval_resolved_zero_arg_op(
    ctx: &EvalCtx,
    resolved_name: &str,
    def: &Arc<OperatorDef>,
    span: Option<Span>,
    shared_scope: bool,
) -> EvalResult<Value> {
    if shared_scope {
        if ctx.local_ops().is_some() || ctx.instance_substitutions().is_some() {
            let outer_ctx = ctx.with_outer_resolution_scope();
            return eval_zero_arg_cached(&outer_ctx, ctx, resolved_name, def, span, false);
        }
        return eval_zero_arg_cached(ctx, ctx, resolved_name, def, span, false);
    }

    eval_zero_arg_cached(ctx, ctx, resolved_name, def, span, true)
}

/// Evaluate a zero-argument local operator (from `local_ops` / INSTANCE module).
///
/// Delegates to [`eval_zero_arg_cached`] with:
/// - `env_pre_check = true` (Fix #100: check env for existing LazyFunc)
pub(super) fn eval_zero_arg_local_op(
    ctx: &EvalCtx,
    name: &str,
    def: &Arc<OperatorDef>,
    span: Option<Span>,
) -> EvalResult<Value> {
    eval_resolved_zero_arg_op(ctx, name, def, span, false)
}

/// Evaluate a shared (outer-module) zero-argument operator.
///
/// Exits the current INSTANCE scope before evaluation. This is necessary because
/// `eval_module_ref` replaces the binding chain with instance substitution entries
/// (via `build_binding_chain_from_eager`/`build_lazy_subst_bindings`). If the
/// shared operator's body references a name that matches an instance substitution
/// (e.g., `INSTANCE M WITH x <- y` makes `x` resolve to `y`), the instance
/// binding would incorrectly shadow the outer-scope variable. Restoring the
/// pre-scope chain ensures the body evaluates in its definition scope.
///
/// Part of #3056 Phase 5: uses `with_outer_resolution_scope()` to rewind to the
/// pre-INSTANCE binding chain. Cannot use `without_instance_resolution_scope()`
/// because the chain is non-empty at this point (reachable from `with_module_scope`).
///
/// Delegates to [`eval_zero_arg_cached`] with `env_pre_check = false`.
pub(super) fn eval_ident_shared_zero_arg_op(
    ctx: &EvalCtx,
    resolved_name: &str,
    def: &Arc<OperatorDef>,
    span: Option<Span>,
) -> EvalResult<Value> {
    eval_resolved_zero_arg_op(ctx, resolved_name, def, span, true)
}

/// Evaluate the domain for a recursive function definition in identifier context.
/// Handles both single-bound and multi-bound function signatures.
pub(super) fn eval_ident_func_domain(
    ctx: &EvalCtx,
    bounds: &[BoundVar],
    span: Option<Span>,
) -> EvalResult<Value> {
    if bounds.len() == 1 {
        let domain_expr = bounds[0]
            .domain
            .as_ref()
            .ok_or_else(|| EvalError::Internal {
                message: "Function definition requires bounded variable".into(),
                span,
            })?;
        eval(ctx, domain_expr)
    } else {
        let mut components = Vec::with_capacity(bounds.len());
        for b in bounds {
            let domain_expr = b.domain.as_ref().ok_or_else(|| EvalError::Internal {
                message: "Function definition requires bounded variable".into(),
                span,
            })?;
            components.push(eval(ctx, domain_expr)?);
        }
        Ok(Value::tuple_set(components))
    }
}
