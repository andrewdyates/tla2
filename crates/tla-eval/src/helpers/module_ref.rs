// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Module reference resolution dispatch.
//!
//! Routes `ModuleRef` expressions to the appropriate handler:
//! - Named/Parameterized → `module_ref_instance::eval_module_ref`
//! - Chained (A!B!C!D) → `module_ref_chained::eval_chained_module_ref`
//!
//! Implementation details are in sibling modules:
//! - `module_ref_cache.rs` — cache infrastructure for INSTANCE WITH substitution
//! - `module_ref_chained.rs` — chained reference resolution
//! - `module_ref_instance.rs` — non-chained instance evaluation
//!
//! Part of #1643 (module_ref.rs decomposition).

use super::super::{eval, EvalCtx, EvalResult};
use super::eval_apply;
use super::module_ref_cache::MODULE_REF_CACHES;
use super::module_ref_chained::eval_chained_module_ref;
use super::module_ref_instance::eval_module_ref;
use crate::binding_chain::BindingValue;
use crate::value::Value;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use tla_core::ast::{Expr, ModuleTarget, Substitution};
use tla_core::name_intern::intern_name;
use tla_core::{Span, Spanned};

// Part of #4114: Cache debug env var with OnceLock instead of calling
// std::env::var on every parametrized INSTANCE evaluation.
debug_flag!(debug_param_instance, "TLA2_DEBUG_PARAM_INSTANCE");

// Part of #2980/#3962: PARAM_SUBS_CACHE consolidated into MODULE_REF_CACHES.
// See module_ref_cache.rs for the `param_subs` field in ModuleRefCaches.
// Previously a standalone thread_local here — now a single TLS access
// covers the parametrized substitution cache alongside the other 3 module-ref
// caches, saving ~5ns per TLS access on the INSTANCE resolution hot path.

// Re-export cache lifecycle functions for existing callers via `helpers::module_ref::*`.
pub use super::module_ref_cache::{
    clear_eager_bindings_cache, clear_module_ref_caches, evict_next_state_eager_bindings,
    trim_module_ref_caches,
};

// Re-export instance resolution functions for existing callers and sibling modules.
pub(crate) use super::module_ref_instance::build_lazy_subst_bindings;
pub use super::module_ref_instance::{
    apply_substitutions, compose_substitutions, expr_has_any_prime, expr_has_primed_param,
};
pub(super) use super::module_ref_instance::{build_binding_chain_from_eager, get_instance_info};

/// Evaluate a module reference expression with any ModuleTarget type
///
/// Handles:
/// - Named: M!Op
/// - Parameterized: IS(x, y)!Op
/// - Chained: A!B!C!D
pub(crate) fn eval_module_ref_target(
    ctx: &EvalCtx,
    target: &ModuleTarget,
    op_name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Value> {
    // Config overrides can target instance-qualified operator names like `I!X <- XOverride`
    // (Bug44). These must apply to module references (`Expr::ModuleRef`), not just to
    // unqualified identifier lookups.
    if let Some(key) = module_ref_compound_key(target, op_name) {
        if let Some(rhs) = ctx.shared.op_replacements.get(&key) {
            // Evaluate the RHS in the outer (root) operator namespace.
            //
            // Note: we intentionally clear INSTANCE substitutions and instance-local operator
            // scope. Config overrides are keyed and resolved in the root module context.
            //
            // Part of #3056 Phase 5: rewind to outer resolution scope. Cannot use
            // without_instance_resolution_scope() because the chain contains instance
            // substitution entries. The override RHS (e.g., `XOverride`) must resolve in
            // the root namespace — if an instance binding exists, it would shadow the root op.
            let override_ctx = ctx.with_outer_resolution_scope();
            // Part of #2993: Pre-intern the override name to avoid runtime lookup_name_id().
            let rhs_expr = Spanned::new(
                Expr::Ident(rhs.clone(), intern_name(rhs.as_str())),
                Span::dummy(),
            );
            if args.is_empty() {
                return eval(&override_ctx, &rhs_expr);
            }
            return eval_apply(&override_ctx, &rhs_expr, args, span);
        }
    }

    match target {
        ModuleTarget::Named(name) => eval_module_ref(ctx, name, op_name, args, span),
        ModuleTarget::Parameterized(name, param_exprs) => {
            // Part of #2969: Parametrized instances like P(Succ)!Op.
            //
            // P(Succ) == INSTANCE ReachabilityProofs defines a parametrized instance
            // where formal param Succ maps to the CONSTANT Succ in ReachabilityProofs.
            // When evaluating P(f)!Reachable0, we must make the actual argument value
            // visible inside the INSTANCE scope under the formal param name.
            //
            // Two-part strategy:
            // 1) Inject the evaluated arg Values into env (so they survive INSTANCE
            //    scope changes — the binding chain gets cleared but env does not).
            // 2) Set instance_substitutions with the formal param names mapped to the
            //    arg expressions. This ensures MODULE_REF_SCOPE_CACHE and OP_RESULT_CACHE
            //    keys differ for different arg values (the substitution Arc pointer is
            //    unique per call). build_eager_subst_bindings evaluates the RHS
            //    expressions and finds the values in env (step 1).
            let param_ctx = if let Some(def) = ctx.get_op(name) {
                if debug_param_instance() {
                    eprintln!(
                        "[PARAM_INSTANCE] found op={} params={:?}",
                        name,
                        def.params
                            .iter()
                            .map(|p| p.name.node.as_str())
                            .collect::<Vec<_>>()
                    );
                }
                if !def.params.is_empty() {
                    let mut pctx = ctx.clone();
                    // Part of #2991: Push param bindings onto BindingChain instead of
                    // mutating env HashMap. Eliminates the O(env_size) Arc::make_mut
                    // deep clone per parametrized INSTANCE call (~26K calls on
                    // MCReachabilityTestAllGraphs). The chain bindings are found by
                    // build_eager_subst_bindings during substitution evaluation, and
                    // the final build_binding_chain_from_eager replaces the chain
                    // with substitution bindings (which include the param values
                    // evaluated from these chain entries).
                    let mut args_hasher = rustc_hash::FxHasher::default();
                    for (param, arg_expr) in def.params.iter().zip(param_exprs.iter()) {
                        let value = eval(ctx, arg_expr)?;
                        if debug_param_instance() {
                            eprintln!("[PARAM_INJECT] {}={}", param.name.node, value);
                        }
                        // Hash each arg value for cache key disambiguation (#2980).
                        value.hash(&mut args_hasher);
                        let name_id = intern_name(param.name.node.as_str());
                        pctx.bindings = pctx.bindings.cons_local(
                            name_id,
                            BindingValue::eager(value),
                            pctx.binding_depth,
                        );
                        pctx.binding_depth += 1;
                    }
                    // Part of #2980: Store content hash of parametrized arg values so
                    // EAGER_BINDINGS_CACHE can disambiguate entries by argument values.
                    pctx.stable_mut().param_args_hash = args_hasher.finish();
                    // Step 2 (Part of #2980): Reuse cached Arc<Vec<Substitution>> so
                    // downstream pointer-identity caches (MODULE_REF_SCOPE_CACHE,
                    // EAGER_BINDINGS_CACHE, OP_RESULT_CACHE) see the same Arc pointer
                    // across calls from the same callsite. The substitution content is
                    // AST-constant (formal param names + actual arg expressions), so the
                    // cache key is the callsite identity (param_exprs Vec data pointer).
                    let subs_arc = MODULE_REF_CACHES.with(|c| {
                        let mut caches = c.borrow_mut();
                        caches
                            .param_subs
                            .entry(param_exprs.as_ptr() as usize)
                            .or_insert_with(|| {
                                let subs: Vec<Substitution> = def
                                    .params
                                    .iter()
                                    .zip(param_exprs.iter())
                                    .map(|(param, arg_expr)| Substitution {
                                        from: param.name.clone(),
                                        to: arg_expr.clone(),
                                    })
                                    .collect();
                                Arc::new(subs)
                            })
                            .clone()
                    });
                    {
                        let id = crate::cache::scope_ids::compute_instance_subs_id(&subs_arc);
                        let s = pctx.stable_mut();
                        s.instance_substitutions = Some(subs_arc);
                        s.scope_ids.instance_substitutions = id;
                    }
                    pctx
                } else {
                    ctx.clone()
                }
            } else {
                ctx.clone()
            };
            eval_module_ref(&param_ctx, name, op_name, args, span)
        }
        ModuleTarget::Chained(base_expr) => {
            // Chained module reference like A!B!C!D
            // First, resolve the base (A!B!C) to get the intermediate instance context
            eval_chained_module_ref(ctx, base_expr, op_name, args, span)
        }
    }
}

pub(crate) fn module_ref_compound_key(target: &ModuleTarget, op_name: &str) -> Option<String> {
    match target {
        ModuleTarget::Named(name) => Some(format!("{name}!{op_name}")),
        // The config override key is the spelled instance name; parameters are part of the
        // INSTANCE definition, not the reference key shape.
        ModuleTarget::Parameterized(name, _params) => Some(format!("{name}!{op_name}")),
        ModuleTarget::Chained(base_expr) => {
            let Expr::ModuleRef(base_target, intermediate_op, _intermediate_args) = &base_expr.node
            else {
                return None;
            };
            let prefix = module_ref_compound_key(base_target, intermediate_op)?;
            Some(format!("{prefix}!{op_name}"))
        }
    }
}
