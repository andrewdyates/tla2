// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Thread-local caches for interned parameter names on operator and closure
//! application hot paths.
//!
//! Extracted from `apply.rs` as part of #3021 (file size limit).

use crate::value::intern_string;
use crate::value::ClosureValue;
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::sync::{Arc, OnceLock};
use tla_core::ast::{Expr, OperatorDef};
use tla_core::name_intern::{intern_name, NameId};

#[derive(Clone)]
struct ParamCacheEntry {
    signature: u64,
    params: Arc<[(Arc<str>, NameId)]>,
}

type OperatorParamCache = FxHashMap<usize, ParamCacheEntry>;
type ClosureParamCache = FxHashMap<u64, ParamCacheEntry>;

// Part of #3962: Consolidated OPERATOR_PARAM_CACHE + CLOSURE_PARAM_CACHE into a
// single TLS struct. Previously 2 separate `thread_local!` declarations — each
// access was a separate `_tlv_get_addr` call on macOS (~5ns each). Both caches
// are cleared together in `clear_param_name_caches()` and are on the hot path
// (accessed per operator/closure application). Now 1 TLS access covers both.
struct ParamCaches {
    operator: OperatorParamCache,
    closure: ClosureParamCache,
}

thread_local! {
    static PARAM_CACHES: RefCell<ParamCaches> = RefCell::new(ParamCaches {
        operator: FxHashMap::default(),
        closure: FxHashMap::default(),
    });
}

const FNV_OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0001_0000_01b3;

#[inline]
fn param_names_signature<'a>(params: impl IntoIterator<Item = &'a str>) -> u64 {
    let mut signature = FNV_OFFSET_BASIS;
    for param in params {
        for byte in param.as_bytes() {
            signature ^= u64::from(*byte);
            signature = signature.wrapping_mul(FNV_PRIME);
        }
        // Delimit adjacent names so ["ab", "c"] and ["a", "bc"] stay distinct.
        signature ^= u64::from(u8::MAX);
        signature = signature.wrapping_mul(FNV_PRIME);
    }
    signature
}

#[inline]
fn build_preinterned_params<'a>(
    params: impl IntoIterator<Item = &'a str>,
) -> Arc<[(Arc<str>, NameId)]> {
    params
        .into_iter()
        .map(|param| {
            let s = intern_string(param);
            let id = intern_name(s.as_ref());
            (s, id)
        })
        .collect()
}

pub(crate) fn clear_param_name_caches() {
    PARAM_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        c.operator.clear();
        c.closure.clear();
    });
}

/// Get or compute pre-interned (Arc<str>, NameId) for an operator's parameters.
///
/// Part of #3000: Extended from RECURSIVE-only to ALL user-defined operators.
/// Caches the interned parameter names so each call avoids 2 DashMap/RwLock
/// lookups per parameter and 1 wasted Arc allocation. The cache is keyed by
/// Arc<OperatorDef> pointer and validated by parameter-name signature so reused
/// allocations cannot replay a stale name vector for a different operator.
pub(super) fn get_param_cache(def: &Arc<OperatorDef>) -> Arc<[(Arc<str>, NameId)]> {
    let key = Arc::as_ptr(def) as usize;
    let signature = param_names_signature(def.params.iter().map(|param| param.name.node.as_str()));
    PARAM_CACHES.with(|caches| {
        let borrow = caches.borrow();
        if let Some(cached) = borrow.operator.get(&key) {
            if cached.signature == signature {
                return Arc::clone(&cached.params);
            }
        }
        drop(borrow);

        let params =
            build_preinterned_params(def.params.iter().map(|param| param.name.node.as_str()));
        caches.borrow_mut().operator.insert(
            key,
            ParamCacheEntry {
                signature,
                params: Arc::clone(&params),
            },
        );
        params
    })
}

/// Get or compute pre-interned (Arc<str>, NameId) for a closure's parameters.
///
/// Part of #3021: Same pattern as `get_param_cache` but keyed by closure id
/// (deterministic span-based u64). Validates by parameter-name signature so
/// deterministic id reuse across module reloads cannot replay stale names.
/// Eliminates per-call Arc::from() allocation and 2 DashMap/RwLock lookups per
/// parameter on every closure application.
pub(super) fn get_closure_param_cache(closure: &ClosureValue) -> Arc<[(Arc<str>, NameId)]> {
    let key = closure.id();
    let signature = param_names_signature(closure.params().iter().map(|param| param.as_str()));
    PARAM_CACHES.with(|caches| {
        let borrow = caches.borrow();
        if let Some(cached) = borrow.closure.get(&key) {
            if cached.signature == signature {
                return Arc::clone(&cached.params);
            }
        }
        drop(borrow);

        let params = build_preinterned_params(closure.params().iter().map(|param| param.as_str()));
        caches.borrow_mut().closure.insert(
            key,
            ParamCacheEntry {
                signature,
                params: Arc::clone(&params),
            },
        );
        params
    })
}

/// Check if an expression is trivially evaluable (O(1), no allocation needed).
///
/// Part of #3024: Used by selective lazy evaluation to skip OnceLock + LazyBinding
/// wrapping for arguments that are cheap to evaluate eagerly. Matches AST node
/// types where evaluation is guaranteed O(1) with no heap allocation:
/// - Ident: scope lookup (O(1) via NameId)
/// - StateVar: direct array index (O(1))
/// - Bool/Int/String: literal → Value conversion (no lookup)
pub(super) fn is_trivially_evaluable(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Ident(_, _)
            | Expr::StateVar(_, _, _)
            | Expr::Bool(_)
            | Expr::Int(_)
            | Expr::String(_)
    )
}

/// Check if the N-ary operator result cache is enabled.
///
/// Caches the `TLA2_DISABLE_NARY_CACHE` env var check in a `OnceLock` so it's
/// only read once per process, not on every operator application.
///
/// Part of #3019: removes syscall from hot path.
pub(super) fn nary_cache_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("TLA2_DISABLE_NARY_CACHE").is_err())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::ClosureValue;
    use tla_core::ast::{Expr, OpParam};
    use tla_core::kani_types::HashMap;
    use tla_core::{Span, Spanned};

    fn names_of(params: &[(Arc<str>, NameId)]) -> Vec<String> {
        params
            .iter()
            .map(|(name, _)| name.as_ref().to_string())
            .collect()
    }

    fn make_param(name: &str) -> OpParam {
        OpParam {
            name: Spanned::new(name.to_string(), Span::dummy()),
            arity: 0,
        }
    }

    fn make_operator_def(params: &[&str]) -> Arc<OperatorDef> {
        Arc::new(OperatorDef {
            name: Spanned::new("Op".to_string(), Span::dummy()),
            params: params.iter().copied().map(make_param).collect(),
            body: Spanned::new(Expr::Bool(true), Span::dummy()),
            local: false,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        })
    }

    fn make_closure(params: &[&str]) -> ClosureValue {
        ClosureValue::new(
            params.iter().map(|param| (*param).to_string()).collect(),
            Spanned::new(Expr::Bool(true), Span::dummy()),
            Arc::new(HashMap::default()),
            None,
        )
    }

    #[test]
    fn test_get_param_cache_recomputes_when_same_pointer_key_has_wrong_signature() {
        clear_param_name_caches();

        let def = make_operator_def(&["S", "P"]);
        let key = Arc::as_ptr(&def) as usize;
        PARAM_CACHES.with(|caches| {
            caches.borrow_mut().operator.insert(
                key,
                ParamCacheEntry {
                    signature: param_names_signature(["x", "y"]),
                    params: build_preinterned_params(["x", "y"]),
                },
            );
        });

        let cached = get_param_cache(&def);
        assert_eq!(names_of(&cached), ["S", "P"]);

        PARAM_CACHES.with(|caches| {
            let borrow = caches.borrow();
            let stored = borrow
                .operator
                .get(&key)
                .expect("operator cache entry should exist");
            assert_eq!(stored.signature, param_names_signature(["S", "P"]));
            assert_eq!(names_of(&stored.params), ["S", "P"]);
        });

        clear_param_name_caches();
    }

    #[test]
    fn test_get_closure_param_cache_recomputes_when_same_id_has_wrong_signature() {
        clear_param_name_caches();

        let closure = make_closure(&["S", "P"]);
        let key = closure.id();
        PARAM_CACHES.with(|caches| {
            caches.borrow_mut().closure.insert(
                key,
                ParamCacheEntry {
                    signature: param_names_signature(["x", "y"]),
                    params: build_preinterned_params(["x", "y"]),
                },
            );
        });

        let cached = get_closure_param_cache(&closure);
        assert_eq!(names_of(&cached), ["S", "P"]);

        PARAM_CACHES.with(|caches| {
            let borrow = caches.borrow();
            let stored = borrow
                .closure
                .get(&key)
                .expect("closure cache entry should exist");
            assert_eq!(stored.signature, param_names_signature(["S", "P"]));
            assert_eq!(names_of(&stored.params), ["S", "P"]);
        });

        clear_param_name_caches();
    }

    #[test]
    fn test_clear_for_test_reset_clears_param_name_caches() {
        clear_param_name_caches();

        let def = make_operator_def(&["x"]);
        let closure = make_closure(&["y"]);
        let _ = get_param_cache(&def);
        let _ = get_closure_param_cache(&closure);

        PARAM_CACHES.with(|caches| {
            let c = caches.borrow();
            assert_eq!(c.operator.len(), 1);
            assert_eq!(c.closure.len(), 1);
        });

        crate::clear_for_test_reset();

        PARAM_CACHES.with(|caches| {
            let c = caches.borrow();
            assert!(c.operator.is_empty());
            assert!(c.closure.is_empty());
        });
    }
}
