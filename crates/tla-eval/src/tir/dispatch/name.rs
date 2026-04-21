// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TIR name resolution — `eval_tir_name()`.
//!
//! Resolves `TirNameRef` identifiers and state variables against the
//! binding chain, state environment, precomputed constants, and
//! operator definitions.

use std::sync::Arc;

use tla_tir::nodes::TirNameKind;
use tla_value::error::{EvalError, EvalResult};
use tla_value::Value;

use crate::cache::{
    current_state_lookup_mode, record_next_read, record_state_read, StateLookupMode,
};
use crate::core::EvalCtx;
use crate::eval_ident::{fast_var_idx_lookup, resolve_binding_chain};

/// Resolve a TIR name reference (state variable or identifier).
pub(super) fn eval_tir_name(
    ctx: &EvalCtx,
    name_ref: &tla_tir::nodes::TirNameRef,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    match &name_ref.kind {
        TirNameKind::StateVar { index } => {
            // Part of #3365: Sparse next-state overlay in Next mode.
            if current_state_lookup_mode(ctx) == StateLookupMode::Next {
                if let Some(sparse_env) = ctx.sparse_next_state_env {
                    let idx = *index as usize;
                    // SAFETY: index from TIR lowering bounded by VarRegistry.
                    let slot = unsafe { sparse_env.get_unchecked(idx) };
                    if let Some(value) = slot {
                        return Ok(value.clone());
                    }
                    // None = unbound, fall through to current state
                }
            }
            // O(1) state variable lookup via array index
            if let Some(state_env) = ctx.state_env {
                let idx = *index as usize;
                debug_assert!(idx < state_env.env_len());
                // SAFETY: index comes from TIR lowering which uses VarRegistry indices.
                let value = unsafe { state_env.get_value(idx) };
                return Ok(value);
            }
            // Fallback: lookup by name in env
            ctx.lookup_state_var(&name_ref.name)
                .ok_or_else(|| EvalError::UndefinedVar {
                    name: name_ref.name.clone(),
                    span,
                })
        }
        TirNameKind::Ident => {
            let lookup_id = if name_ref.name_id != tla_core::NameId::INVALID {
                Some(name_ref.name_id)
            } else {
                tla_core::name_intern::lookup_name_id(&name_ref.name)
            };

            if let Some(lookup_id) = lookup_id {
                if let Some(value) = resolve_binding_chain(ctx, lookup_id)? {
                    return Ok(value);
                }
            }

            // Part of #3961: Unified state variable lookup using O(1) var_idx_by_name_id
            // table. Resolves VarIndex once, reuses for sparse overlay + state_env.
            if let Some(lookup_id) = lookup_id {
                if let Some(idx) = fast_var_idx_lookup(ctx, lookup_id) {
                    if current_state_lookup_mode(ctx) == StateLookupMode::Next {
                        if let Some(sparse_env) = ctx.sparse_next_state_env {
                            // SAFETY: idx bounded by VarRegistry, sparse_env has same layout.
                            let slot = unsafe { sparse_env.get_unchecked(idx.as_usize()) };
                            if let Some(value) = slot {
                                record_next_read(ctx, idx, value);
                                return Ok(value.clone());
                            }
                        }
                    }

                    if let Some(state_env) = ctx.state_env {
                        debug_assert!(idx.as_usize() < state_env.env_len());
                        // SAFETY: idx comes from VarRegistry and is bounded above.
                        let value = unsafe { state_env.get_value(idx.as_usize()) };
                        record_state_read(ctx, idx, &value);
                        return Ok(value);
                    }
                }
            }

            // Part of #3194: check precomputed_constants for config-defined constants
            // (e.g., CONSTANT N = 3 from .cfg). The AST path resolves these in
            // eval_ident step 5; ctx.lookup() misses them during BFS because
            // state_env is set and the env fallback is skipped for interned names.
            if let Some(id) = lookup_id {
                if let Some(value) = ctx.shared.precomputed_constants.get(&id) {
                    return Ok(value.clone());
                }
            }

            if lookup_id.is_none() || ctx.state_env.is_none() {
                if let Some(value) = ctx.env.get(name_ref.name.as_str()) {
                    if let Some(id) = lookup_id {
                        // Part of #3961: Use O(1) var_idx_by_name_id table.
                        if let Some(idx) = fast_var_idx_lookup(ctx, id) {
                            if current_state_lookup_mode(ctx) == StateLookupMode::Next {
                                record_next_read(ctx, idx, value);
                            } else {
                                record_state_read(ctx, idx, value);
                            }
                        }
                    }
                    return Ok(value.clone());
                }
            }

            let resolved_name = ctx.resolve_op_name(&name_ref.name);
            if let Some(def) = ctx.get_op(resolved_name) {
                if def.params.is_empty() {
                    // Route zero-arg operators through the cached evaluation path.
                    // Previously (#3392), this tried the TIR path directly via
                    // eval_tir(ctx, &tir_body), which bypassed the zero-arg operator
                    // cache entirely. For constant operators like HostOf (which
                    // contain CHOOSE expressions), this caused re-evaluation on
                    // every access — O(n) CHOOSE per access x millions of accesses.
                    // The cached path (eval_resolved_zero_arg_op) evaluates once
                    // via dep-tracked eval(), caches the result, and returns the
                    // cached value on subsequent accesses. The inner eval() already
                    // dispatches through TIR when available, so TIR evaluation is
                    // preserved within the cache framework.
                    let shared_scope = ctx
                        .local_ops()
                        .as_ref()
                        .and_then(|local| local.get(resolved_name))
                        .is_none()
                        && ctx
                            .shared
                            .ops
                            .get(resolved_name)
                            .is_some_and(|shared_def| Arc::ptr_eq(shared_def, def));
                    return crate::eval_ident_zero_arg::eval_resolved_zero_arg_op(
                        ctx,
                        resolved_name,
                        def,
                        span,
                        shared_scope,
                    );
                }

                if crate::should_prefer_builtin_override(
                    resolved_name,
                    def.as_ref(),
                    def.params.len(),
                    ctx,
                ) {
                    return Err(EvalError::Internal {
                        message: format!(
                            "TIR eval: builtin override operator '{resolved_name}' is not yet supported as a first-class value"
                        ),
                        span,
                    });
                }

                let params: Vec<String> = def
                    .params
                    .iter()
                    .map(|param| param.name.node.clone())
                    .collect();
                let mut closure =
                    ctx.create_closure(params, def.body.clone(), ctx.local_ops().clone());
                // Part of #3392: attach TIR body so closure application stays
                // in TIR via eval_closure_body's tir_body check.
                if let Some(tir_body) = super::super::try_resolve_operator_tir(resolved_name) {
                    closure =
                        closure.with_tir_body(Box::new(super::super::StoredTirBody::from_arc(tir_body)));
                }
                if def.is_recursive {
                    closure = closure.with_name_if_missing(Arc::from(resolved_name));
                }
                return Ok(Value::Closure(std::sync::Arc::new(closure)));
            }

            Err(EvalError::UndefinedVar {
                name: name_ref.name.clone(),
                span,
            })
        }
    }
}
