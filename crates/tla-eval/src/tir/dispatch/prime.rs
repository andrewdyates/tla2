// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TIR prime evaluation — `eval_tir_prime()` and next-state fallback.
//!
//! Handles primed expressions (`x'`) including direct next-state-env lookup,
//! sparse overlay reads for ENABLED witness state, and the complex fallback
//! path that re-evaluates in next-state context.

use std::sync::Arc;

use tla_core::Spanned;
use tla_tir::nodes::{TirExpr, TirNameKind};
use tla_value::error::{EvalError, EvalResult};
use tla_value::Value;

use crate::cache::{StateLookupMode, StateLookupModeGuard};
use crate::core::EvalCtx;

use super::eval_tir;

/// Evaluate a primed TIR expression.
pub(super) fn eval_tir_prime(
    ctx: &EvalCtx,
    inner: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    match &inner.node {
        TirExpr::Name(name_ref) => match &name_ref.kind {
            TirNameKind::StateVar { index } => {
                // O(1) next-state lookup
                if let Some(next_env) = ctx.next_state_env {
                    let idx = *index as usize;
                    debug_assert!(idx < next_env.env_len());
                    // SAFETY: index from TIR lowering bounded by VarRegistry.
                    let value = unsafe { next_env.get_value(idx) };
                    return Ok(value);
                }
                // Part of #3365: Sparse overlay from ENABLED WitnessState.
                if let Some(sparse_env) = ctx.sparse_next_state_env {
                    let idx = *index as usize;
                    // SAFETY: index from TIR lowering bounded by VarRegistry.
                    let slot = unsafe { sparse_env.get_unchecked(idx) };
                    if let Some(value) = slot {
                        return Ok(value.clone());
                    }
                    // None = unbound, fall through to complex eval
                    return eval_tir_prime_complex(ctx, inner, span);
                }
                // Fallback: HashMap-based next_state lookup
                if let Some(ref next_state) = ctx.next_state {
                    if let Some(v) = next_state.get(name_ref.name.as_str()) {
                        return Ok(v.clone());
                    }
                }
                Err(EvalError::PrimedVariableNotBound { span })
            }
            TirNameKind::Ident => {
                if let Some(next_env) = ctx.next_state_env {
                    if let Some(idx) = ctx.var_registry().get(&name_ref.name) {
                        debug_assert!(idx.as_usize() < next_env.env_len());
                        // SAFETY: `idx` comes from the current runtime var registry.
                        let value = unsafe { next_env.get_value(idx.as_usize()) };
                        return Ok(value);
                    }
                }

                // Part of #3365: Sparse overlay from ENABLED WitnessState.
                if let Some(sparse_env) = ctx.sparse_next_state_env {
                    if let Some(idx) = ctx.var_registry().get(&name_ref.name) {
                        // SAFETY: idx from VarRegistry.
                        let slot = unsafe { sparse_env.get_unchecked(idx.as_usize()) };
                        if let Some(value) = slot {
                            return Ok(value.clone());
                        }
                        // None = unbound, fall through to complex eval
                    }
                }

                if let Some(ref next_state) = ctx.next_state {
                    if let Some(v) = next_state.get(name_ref.name.as_str()) {
                        return Ok(v.clone());
                    }
                }

                // Mirror AST prime evaluation: once the direct simple-variable
                // fast path misses, re-evaluate the inner name in next-state
                // context so unresolved/late-bound names surface as the same
                // contract-level errors (`PrimedVariableNotBound`, `UndefinedVar`, etc.).
                eval_tir_prime_complex(ctx, inner, span)
            }
        },
        _ => eval_tir_prime_complex(ctx, inner, span),
    }
}

fn eval_tir_prime_complex(
    ctx: &EvalCtx,
    inner: &Spanned<TirExpr>,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    if ctx.next_state_env.is_some() {
        let mut next_ctx = ctx.clone();
        let stable = next_ctx.stable_mut();
        stable.next_state = None;
        stable.next_state_env = None;
        stable.state_env = ctx.next_state_env;
        let _ = stable;
        let _guard = StateLookupModeGuard::new(ctx, StateLookupMode::Next);
        return eval_tir(&next_ctx, inner);
    }

    // Part of #3365: Sparse overlay — evaluate in Next mode with overlay visible.
    if ctx.sparse_next_state_env.is_some() {
        let _guard = StateLookupModeGuard::new(ctx, StateLookupMode::Next);
        return eval_tir(ctx, inner);
    }

    let Some(next_state) = &ctx.next_state else {
        return Err(EvalError::PrimedVariableNotBound { span });
    };

    let mut next_ctx = ctx.clone();
    let stable = next_ctx.stable_mut();
    stable.next_state = None;
    stable.next_state_env = None;
    let _ = stable;

    // Part of #3964: Hoist Arc::make_mut outside both loops — one Rc+Arc
    // refcount check instead of N+M (N = registry vars, M = next_state vars).
    // Uses field-level borrow splitting: stable (mut) is disjoint from
    // binding_depth + bindings (read-only).
    {
        let has_locals = next_ctx.binding_depth > 0;
        let state_env_opt = next_ctx.state_env;
        let stable = std::rc::Rc::make_mut(&mut next_ctx.stable);
        stable.state_env = None;
        // Part of #3964: Use Arc::get_mut (non-atomic) when refcount == 1.
        let env = if let Some(e) = Arc::get_mut(&mut stable.env) {
            e
        } else {
            Arc::make_mut(&mut stable.env)
        };

        if let Some(state_env) = state_env_opt {
            for (idx, name) in ctx.var_registry().iter() {
                // Part of #2144: skip current-state vars that shadow local bindings.
                if has_locals {
                    if let Some(id) = tla_core::name_intern::lookup_name_id(name.as_ref()) {
                        if next_ctx.bindings.lookup(id).is_some() {
                            continue;
                        }
                    }
                }
                debug_assert!(idx.as_usize() < state_env.env_len());
                // SAFETY: `idx` originates from this context's `VarRegistry`, which
                // defines the layout for the bound `state_env` array.
                let value = unsafe { state_env.get_value(idx.as_usize()) };
                env.insert(Arc::clone(name), value);
            }
        }

        for (name, value) in next_state.iter() {
            if has_locals {
                if let Some(id) = tla_core::name_intern::lookup_name_id(name.as_ref()) {
                    if next_ctx.bindings.lookup(id).is_some() {
                        continue;
                    }
                }
            }
            env.insert(Arc::clone(name), value.clone());
        }
    }

    let _guard = StateLookupModeGuard::new(ctx, StateLookupMode::Next);
    eval_tir(&next_ctx, inner)
}
