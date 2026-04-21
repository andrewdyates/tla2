// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(debug_assertions)]
use super::debug_prime;
use super::{
    eval, record_next_read, EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, StateLookupMode,
    Value,
};
use crate::cache::{bump_hoist_state_generation_ctx, StateLookupModeGuard};
use crate::value::intern_string;
use tla_core::name_intern::{intern_name, lookup_name_id, NameId};

/// Check if a name is an INSTANCE substitution target using the most efficient
/// available method, preferring NameId integer comparison over string scans.
///
/// Resolution tiers:
/// 1. Chained path (`eager_subst_bindings` non-empty): O(1) NameId scan of eager entries.
/// 2. SubstIn path (`eager_subst_bindings` empty marker): BindingChain lookup for
///    Instance-sourced LazyBinding via NameId comparison (#3093).
/// 3. Legacy `with_instance_scope` path (`eager_subst_bindings` is None, chain empty):
///    falls back to `instance_substitutions` string scan.
#[inline]
fn is_instance_sub_target(ctx: &EvalCtx, name: &str, name_id: Option<NameId>) -> bool {
    let check_id = name_id
        .filter(|id| *id != NameId::INVALID)
        .unwrap_or_else(|| lookup_name_id(name).unwrap_or_else(|| intern_name(name)));
    if let Some(ref eager) = ctx.eager_subst_bindings {
        if !eager.is_empty() {
            // Chained path: NameId fast check against pre-evaluated eager entries.
            return eager.iter().any(|(id, _, _)| *id == check_id);
        }
        // SubstIn / module_ref_instance path (empty marker): substitution targets
        // are in the BindingChain as Instance-sourced LazyBindings installed by
        // build_lazy_subst_bindings. NameId comparison replaces string scan (#3093).
        return ctx.bindings.has_instance_binding(check_id);
    }
    // Legacy path: with_instance_scope() sets instance_substitutions but not
    // eager_subst_bindings and empties the chain. String scan required.
    ctx.instance_substitutions()
        .is_some_and(|subs| subs.iter().any(|s| s.from.node.as_str() == name))
}

/// Evaluate a primed expression (`Expr::Prime`).
///
/// Primed variables represent next-state values in TLA+ actions. This function
/// implements a multi-tier resolution strategy:
///
/// 1. **Array fast path** (O(1) via VarIndex): When `next_state_env` is set,
///    directly index by VarIndex for `Expr::Ident` and `Expr::StateVar` inner nodes.
///
/// 1b. **Sparse overlay** (O(1) via VarIndex, Part of #3365): When
///    `sparse_next_state_env` is set (ENABLED evaluation), lookup by VarIndex.
///    `None` slots fall through to current state; `Some(v)` returns the bound value.
///
/// 2. **Call-by-name substitution**: If `x'` has a call-by-name sub `x -> expr`,
///    evaluate `(expr)'` instead (Part of #188).
///
/// 3. **INSTANCE substitution**: If `x'` has an INSTANCE sub `x -> expr`,
///    evaluate `(expr)'` in the outer module context (BUG FIX #295).
///
/// 4. **HashMap fallback**: Direct lookup in `next_state` HashMap for simple
///    variables, with complex expression evaluation for non-variable primed exprs.
///
/// 5. **Complex expression path**: For `(f(x))'` etc., swaps next-state environment
///    into state_env so all state variable lookups resolve to next-state values.
pub(super) fn eval_prime(
    ctx: &EvalCtx,
    inner: &Spanned<Expr>,
    span: Option<Span>,
) -> EvalResult<Value> {
    // Fast path: array-based next-state lookup (O(1) via VarIndex)
    if let Some(next_env) = ctx.next_state_env {
        match &inner.node {
            Expr::Ident(name, name_id) => {
                // Fix #2364: Use is_instance_sub_target for fast NameId-based check.
                // Part of #2993: Pass pre-resolved NameId to avoid lookup_name_id().
                let has_instance_sub = is_instance_sub_target(
                    ctx,
                    name,
                    (*name_id != NameId::INVALID).then_some(*name_id),
                );
                let has_cbn_sub = ctx
                    .call_by_name_subs()
                    .is_some_and(|subs| subs.iter().any(|s| s.from.node == *name));

                if !has_instance_sub && !has_cbn_sub {
                    // Look up by VarIndex for O(1) access
                    if let Some(idx) = ctx.var_registry().get(name) {
                        debug_assert!(idx.as_usize() < next_env.env_len());
                        // SAFETY: `next_env` is a live borrowed array and the registry index is bounded.
                        let value = unsafe { next_env.get_value(idx.as_usize()) };
                        record_next_read(ctx, idx, &value);
                        return Ok(value);
                    }
                }
            }
            Expr::StateVar(name, idx, sv_name_id) => {
                // Part of #3093: Use targeted is_instance_sub_target check instead
                // of blanket instance_substitutions().is_none(). resolve_state_var_slot
                // handles index mismatches for non-substituted vars in INSTANCE context
                // (name-based fallback). Original BUG FIX #1096 predates resolve_state_var_slot.
                let has_instance_sub = is_instance_sub_target(ctx, name, Some(*sv_name_id));
                let has_cbn_sub = ctx
                    .call_by_name_subs()
                    .is_some_and(|subs| subs.iter().any(|s| s.from.node.as_str() == name.as_str()));

                if !has_instance_sub && !has_cbn_sub {
                    let resolved_idx = ctx.resolve_state_var_slot(name.as_str(), *idx, *sv_name_id);
                    debug_assert!(resolved_idx.as_usize() < next_env.env_len());
                    // SAFETY: `resolved_idx` is validated against the current registry.
                    let value = unsafe { next_env.get_value(resolved_idx.as_usize()) };
                    record_next_read(ctx, resolved_idx, &value);
                    return Ok(value);
                }
            }
            Expr::Label(label) => return eval_prime(ctx, &label.body, span),
            // Part of #1831: Exhaustive match — non-variable types fall through.
            Expr::Bool(_)
            | Expr::Int(_)
            | Expr::String(_)
            | Expr::Apply(..)
            | Expr::OpRef(_)
            | Expr::ModuleRef(..)
            | Expr::InstanceExpr(..)
            | Expr::Lambda(..)
            | Expr::And(..)
            | Expr::Or(..)
            | Expr::Not(_)
            | Expr::Implies(..)
            | Expr::Equiv(..)
            | Expr::Forall(..)
            | Expr::Exists(..)
            | Expr::Choose(..)
            | Expr::SetEnum(_)
            | Expr::SetBuilder(..)
            | Expr::SetFilter(..)
            | Expr::In(..)
            | Expr::NotIn(..)
            | Expr::Subseteq(..)
            | Expr::Union(..)
            | Expr::Intersect(..)
            | Expr::SetMinus(..)
            | Expr::Powerset(_)
            | Expr::BigUnion(_)
            | Expr::FuncDef(..)
            | Expr::FuncApply(..)
            | Expr::Domain(_)
            | Expr::Except(..)
            | Expr::FuncSet(..)
            | Expr::Record(_)
            | Expr::RecordAccess(..)
            | Expr::RecordSet(_)
            | Expr::Tuple(_)
            | Expr::Times(_)
            | Expr::Prime(_)
            | Expr::Always(_)
            | Expr::Eventually(_)
            | Expr::LeadsTo(..)
            | Expr::WeakFair(..)
            | Expr::StrongFair(..)
            | Expr::Enabled(_)
            | Expr::Unchanged(_)
            | Expr::If(..)
            | Expr::Case(..)
            | Expr::Let(..)
            | Expr::SubstIn(..)
            | Expr::Eq(..)
            | Expr::Neq(..)
            | Expr::Lt(..)
            | Expr::Leq(..)
            | Expr::Gt(..)
            | Expr::Geq(..)
            | Expr::Add(..)
            | Expr::Sub(..)
            | Expr::Mul(..)
            | Expr::Div(..)
            | Expr::IntDiv(..)
            | Expr::Mod(..)
            | Expr::Pow(..)
            | Expr::Neg(_)
            | Expr::Range(..) => {}
        }
    }

    // Part of #3365: Sparse next-state overlay from ENABLED WitnessState.
    // Consult before HashMap fallback — O(1) array index, no allocation.
    if let Some(sparse_env) = ctx.sparse_next_state_env {
        match &inner.node {
            Expr::Ident(name, name_id) => {
                let has_instance_sub = is_instance_sub_target(
                    ctx,
                    name,
                    (*name_id != NameId::INVALID).then_some(*name_id),
                );
                let has_cbn_sub = ctx
                    .call_by_name_subs()
                    .is_some_and(|subs| subs.iter().any(|s| s.from.node == *name));

                if !has_instance_sub && !has_cbn_sub {
                    if let Some(idx) = ctx.var_registry().get(name) {
                        // SAFETY: idx bounded by VarRegistry, sparse_env has same layout.
                        let slot = unsafe { sparse_env.get_unchecked(idx.as_usize()) };
                        if let Some(value) = slot {
                            record_next_read(ctx, idx, value);
                            return Ok(value.clone());
                        }
                        // None = unbound in witness, fall through to current state
                    }
                }
            }
            Expr::StateVar(name, idx, sv_name_id) => {
                let has_instance_sub = is_instance_sub_target(ctx, name, Some(*sv_name_id));
                let has_cbn_sub = ctx
                    .call_by_name_subs()
                    .is_some_and(|subs| subs.iter().any(|s| s.from.node.as_str() == name.as_str()));

                if !has_instance_sub && !has_cbn_sub {
                    let resolved_idx = ctx.resolve_state_var_slot(name.as_str(), *idx, *sv_name_id);
                    // SAFETY: resolved_idx validated against current registry.
                    let slot = unsafe { sparse_env.get_unchecked(resolved_idx.as_usize()) };
                    if let Some(value) = slot {
                        record_next_read(ctx, resolved_idx, value);
                        return Ok(value.clone());
                    }
                    // None = unbound in witness, fall through to current state
                }
            }
            _ => {}
        }
    }

    // Part of #188: Handle call-by-name substitutions for primed identifiers.
    // Prime(Ident(x)) with call-by-name sub x -> expr evaluates Prime(expr).
    if let Some(subs) = ctx.call_by_name_subs() {
        let name = match &inner.node {
            Expr::Ident(name, _) => Some(name.as_str()),
            Expr::StateVar(name, _, _) => Some(name.as_str()),
            _ => None,
        };

        if let Some(name) = name {
            if let Some(sub) = subs.iter().find(|s| s.from.node.as_str() == name) {
                // Create a Prime expression wrapping the substituted expression
                let primed_expr = Spanned {
                    node: Expr::Prime(Box::new(sub.to.clone())),
                    span: inner.span,
                };
                // Evaluate in current context without call_by_name_subs
                let inner_ctx = ctx.without_call_by_name_subs();
                return eval(&inner_ctx, &primed_expr);
            }
        }
    }

    // Part of #3056 Phase 5: INSTANCE substitution primed access now flows through the
    // standard binding chain path. The complex eval path below swaps state_env and sets
    // StateLookupMode::Next. For Ident(x): eval_ident → LazyBinding → mode-aware
    // cached_primed OnceLock. For StateVar(x): eval_statevar → instance_substitution
    // handler with current_state_lookup_mode(). The previous special case here was needed
    // because LazyBinding's OnceLock was write-once without context validation; the dual
    // OnceLock infrastructure (cached + cached_primed) now handles this correctly.

    // Fall back to HashMap-based next_state
    let Some(next_state) = &ctx.next_state else {
        // No array-based next_state_env and no HashMap next_state
        if ctx.next_state_env.is_none() && ctx.sparse_next_state_env.is_none() {
            return Err(EvalError::PrimedVariableNotBound { span });
        }
        // next_state_env or sparse overlay is set but we couldn't resolve via simple
        // lookup — fall through to complex eval for expressions like (f(x))'.
        if ctx.next_state_env.is_some() {
            // Array-based full next state: swap into state_env
            let mut next_ctx = ctx.clone();
            let s = next_ctx.stable_mut();
            s.next_state_env = None;
            s.state_env = ctx.next_state_env;
            let _ = s;
            let _guard = StateLookupModeGuard::new(ctx, StateLookupMode::Next);
            let _gen_guard = bump_hoist_state_generation_ctx(ctx);
            return eval(&next_ctx, inner);
        }
        // Part of #3365: Sparse overlay — evaluate inner with StateLookupMode::Next.
        // The sparse overlay stays on the context; next-mode lookups will consult it.
        let _guard = StateLookupModeGuard::new(ctx, StateLookupMode::Next);
        let _gen_guard = bump_hoist_state_generation_ctx(ctx);
        return eval(ctx, inner);
    };

    // If this is a state variable, resolve it from the next-state environment.
    match &inner.node {
        Expr::Ident(name, name_id) => {
            // If this identifier has an active INSTANCE substitution, we must evaluate the
            // substituted expression in the next-state context (so don't short-circuit with a
            // direct next_state lookup).
            //
            // Part of #2993: Pass pre-resolved NameId to avoid lookup_name_id().
            let has_instance_sub = is_instance_sub_target(
                ctx,
                name,
                (*name_id != NameId::INVALID).then_some(*name_id),
            );
            let has_cbn_sub = ctx
                .call_by_name_subs()
                .is_some_and(|subs| subs.iter().any(|s| s.from.node == *name));

            if !has_instance_sub && !has_cbn_sub {
                if let Some(value) = next_state.get(name.as_str()) {
                    debug_eprintln!(debug_prime(), "Prime: direct lookup {} -> {}", name, value);
                    if let Some(idx) = ctx.var_registry().get(name) {
                        record_next_read(ctx, idx, value);
                    }
                    return Ok(value.clone());
                }
            }
        }
        Expr::StateVar(name, idx, sv_name_id) => {
            let has_instance_sub = is_instance_sub_target(ctx, name, Some(*sv_name_id));
            let has_cbn_sub = ctx
                .call_by_name_subs()
                .is_some_and(|subs| subs.iter().any(|s| s.from.node.as_str() == name.as_str()));

            if !has_instance_sub && !has_cbn_sub {
                if let Some(value) = next_state.get(name.as_str()) {
                    let resolved_idx = ctx.resolve_state_var_slot(name.as_str(), *idx, *sv_name_id);
                    record_next_read(ctx, resolved_idx, value);
                    return Ok(value.clone());
                }
            }
        }
        Expr::Label(label) => return eval_prime(ctx, &label.body, span),
        // Part of #1831: Exhaustive match — non-variable types fall through.
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Apply(..)
        | Expr::OpRef(_)
        | Expr::ModuleRef(..)
        | Expr::InstanceExpr(..)
        | Expr::Lambda(..)
        | Expr::And(..)
        | Expr::Or(..)
        | Expr::Not(_)
        | Expr::Implies(..)
        | Expr::Equiv(..)
        | Expr::Forall(..)
        | Expr::Exists(..)
        | Expr::Choose(..)
        | Expr::SetEnum(_)
        | Expr::SetBuilder(..)
        | Expr::SetFilter(..)
        | Expr::In(..)
        | Expr::NotIn(..)
        | Expr::Subseteq(..)
        | Expr::Union(..)
        | Expr::Intersect(..)
        | Expr::SetMinus(..)
        | Expr::Powerset(_)
        | Expr::BigUnion(_)
        | Expr::FuncDef(..)
        | Expr::FuncApply(..)
        | Expr::Domain(_)
        | Expr::Except(..)
        | Expr::FuncSet(..)
        | Expr::Record(_)
        | Expr::RecordAccess(..)
        | Expr::RecordSet(_)
        | Expr::Tuple(_)
        | Expr::Times(_)
        | Expr::Prime(_)
        | Expr::Always(_)
        | Expr::Eventually(_)
        | Expr::LeadsTo(..)
        | Expr::WeakFair(..)
        | Expr::StrongFair(..)
        | Expr::Enabled(_)
        | Expr::Unchanged(_)
        | Expr::If(..)
        | Expr::Case(..)
        | Expr::Let(..)
        | Expr::SubstIn(..)
        | Expr::Eq(..)
        | Expr::Neq(..)
        | Expr::Lt(..)
        | Expr::Leq(..)
        | Expr::Gt(..)
        | Expr::Geq(..)
        | Expr::Add(..)
        | Expr::Sub(..)
        | Expr::Mul(..)
        | Expr::Div(..)
        | Expr::IntDiv(..)
        | Expr::Mod(..)
        | Expr::Pow(..)
        | Expr::Neg(_)
        | Expr::Range(..) => {}
    }

    debug_eprintln!(
        debug_prime(),
        "Prime: complex expression, inner={:?}",
        std::mem::discriminant(&inner.node)
    );
    debug_eprintln!(
        debug_prime(),
        "  next_state vars: {:?}",
        next_state.keys().collect::<Vec<_>>()
    );
    // Evaluate `inner` with state variables interpreted in the *next* state.
    //
    // When `next_state_env` is set (array-based fast path from prime_guards_hold_in_next_array),
    // swap it into state_env so that state variable lookups go to next-state values.
    // This avoids HashMap iteration and enables O(1) lookups.
    //
    // When `state_env` is set (ArrayState fast path), state variable lookups prefer
    // `state_env` over `env`, so binding next-state values into `env` is insufficient.
    //
    // We handle this in multiple modes:
    // - `next_state_env` is set: swap it into `state_env` for O(1) lookups
    // - Full `next_state` HashMap: clear `state_env` and bind all vars into `env`
    // - Partial `next_state`: shadow via BindingChain (falls back to current state)
    //
    // In every mode below, keep `StateLookupMode::Next` active around `eval` so
    // dependency tracking/cache validation use the same "next state" contract.
    if ctx.next_state_env.is_some() {
        // Fast path: swap next_state_env -> state_env
        let mut next_ctx = ctx.clone();
        let s = next_ctx.stable_mut();
        s.next_state = None;
        s.next_state_env = None;
        s.state_env = ctx.next_state_env;
        let _ = s;
        let _guard = StateLookupModeGuard::new(ctx, StateLookupMode::Next);
        let _gen_guard = bump_hoist_state_generation_ctx(ctx);
        return eval(&next_ctx, inner);
    }
    let mut next_ctx = ctx.clone();
    let s = next_ctx.stable_mut();
    s.next_state = None;
    s.next_state_env = None;
    let _ = s;
    if next_ctx.state_env.is_some() {
        let is_full_next_state = next_state.len() == ctx.var_registry().len();
        if is_full_next_state {
            next_ctx.stable_mut().state_env = None;
            // Part of #3964: Hoist Arc::make_mut outside loop — one Rc+Arc refcount
            // check instead of N (N = state var count).
            next_ctx.batch_insert_into_env(next_state.iter());
        } else {
            for (name, value) in next_state.iter() {
                // Avoid overriding a locally-bound variable that shadows a state var.
                if !next_ctx.has_local_binding(name.as_ref()) {
                    // Part of #188, #232: Intern for pointer equality and NameId for O(1) lookups
                    let interned = intern_string(name.as_ref());
                    let name_id = intern_name(interned.as_ref());
                    next_ctx.push_binding_preinterned(interned, value.clone(), name_id);
                }
            }
        }
    } else {
        // Part of #3964: Hoist Arc::make_mut outside loop.
        next_ctx.batch_insert_into_env(next_state.iter());
    }
    let _guard = StateLookupModeGuard::new(ctx, StateLookupMode::Next);
    let _gen_guard = bump_hoist_state_generation_ctx(ctx);
    let result = eval(&next_ctx, inner);
    debug_eprintln!(debug_prime(), "Prime: result={:?}", result);
    result
}
