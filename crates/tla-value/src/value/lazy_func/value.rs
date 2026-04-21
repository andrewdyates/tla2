// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Runtime lazy-function payload and memo behavior.
//!
//! `LazyFuncValue` supports on-demand evaluation for functions with non-enumerable
//! domains (Nat, Int, etc.). Constructors, accessors, EXCEPT cloning, and memo
//! helpers live here.

use super::super::Value;
use super::captures::{CapturedChain, LazyFuncCaptures};
use super::domain::LazyDomain;
use super::{deterministic_id_from_span, pre_intern_bounds};
use num_bigint::BigInt;
use num_traits::Zero;
use std::collections::HashMap as StdHashMap;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, Mutex};
use tla_core::ast::{BoundVar, Expr};
use tla_core::kani_types::HashMap;
use tla_core::name_intern::NameId;
use tla_core::Spanned;

#[cfg(feature = "memory-stats")]
use super::super::memory_stats;

/// Derive a deterministic ID from a parent ID and an exception key-value pair.
///
/// Used by `LazyFuncValue::with_exception` to produce a stable ID for
/// `[f EXCEPT ![k] = v]` that is deterministic across runs.
fn deterministic_exception_id(parent_id: u64, key: &Value, value: &Value) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    parent_id.hash(&mut hasher);
    key.hash(&mut hasher);
    value.hash(&mut hasher);
    hasher.finish()
}

/// A lazily evaluated function value for non-enumerable domains (e.g. Nat, Int).
///
/// This supports `f[x]` by evaluating the function body on-demand.
/// For multi-argument functions, stores multiple bounds and uses tuple keys.
#[derive(Clone)]
pub struct LazyFuncValue {
    pub(crate) id: u64,
    /// Optional name for self-recursive bindings (e.g., `LET f[n \\in Nat] == ... f[n-1] ...`)
    pub(crate) name: Option<Arc<str>>,
    /// Part of #2955: Arc-wrapped for O(1) clone in recursive self-reference push.
    /// LazyDomain::General(Box<Value>) is expensive to deep-clone.
    pub(crate) domain: Arc<LazyDomain>,
    /// Part of #2955: Arc-wrapped for O(1) clone in recursive self-reference push.
    pub(crate) bounds: Arc<[BoundVar]>,
    /// Part of #3395: Pre-interned (Arc<str>, NameId) pairs for each bound variable.
    /// Eliminates per-application String→Arc<str> + intern_name overhead.
    pub(crate) pre_interned_bounds: Arc<[(Arc<str>, NameId)]>,
    pub(crate) body: Arc<Spanned<Expr>>,
    /// Part of #2955: Arc-wrapped for O(1) clone during LazyFunc application.
    /// Previously each `f[x]` application cloned the entire HashMap (~50 entries for
    /// GameOfLife). With Arc, application-time cost is one refcount bump instead of
    /// O(n) key-value clones. The HashMap is built once at definition time via
    /// `captured_env()` and shared across all applications of the same function.
    pub(crate) env: Arc<HashMap<Arc<str>, Value>>,
    /// Part of #2955/#2989: Opaque captured BindingChain from definition time.
    /// At application time, the evaluator restores this chain directly in O(1).
    /// The chain is the sole source of truth for local bindings — captured_bindings
    /// was removed in #2989 as the chain made it vestigial.
    pub(crate) captured_chain: Option<Box<dyn CapturedChain>>,
    /// Part of #2955: The binding_depth at definition time (for correct dep tracking).
    pub(crate) captured_chain_depth: usize,
    /// Issue #174: LazyFuncs must capture local_ops to access operators from
    /// the enclosing LET scope when the body is evaluated
    pub(crate) local_ops: Option<Arc<tla_core::OpEnv>>,
    /// Captured current-state array (for O(1) VarIndex lookups) at function definition time.
    pub(crate) captured_state: Option<Arc<[Value]>>,
    /// Captured next-state array (for O(1) primed VarIndex lookups) at function definition time.
    pub(crate) captured_next_state: Option<Arc<[Value]>>,
    pub(crate) memo: Arc<Mutex<StdHashMap<Value, Value>>>,
}

impl LazyFuncValue {
    /// Create a new lazy function with a single bound variable.
    ///
    /// FIX #1989: ID is derived deterministically from the body expression span,
    /// not from a global counter, so fingerprints are stable across runs.
    pub fn new(
        name: Option<Arc<str>>,
        domain: LazyDomain,
        bound: BoundVar,
        body: Spanned<Expr>,
        captures: LazyFuncCaptures,
    ) -> Self {
        #[cfg(feature = "memory-stats")]
        memory_stats::inc_lazy_func();

        let id = deterministic_id_from_span(&body.span);
        let bounds: Arc<[BoundVar]> = Arc::from(vec![bound]);
        let pre_interned_bounds = pre_intern_bounds(&bounds);
        LazyFuncValue {
            id,
            name,
            domain: Arc::new(domain),
            bounds,
            pre_interned_bounds,
            body: Arc::new(body),
            env: captures.env,
            captured_chain: captures.captured_chain,
            captured_chain_depth: captures.captured_chain_depth,
            local_ops: captures.local_ops,
            captured_state: captures.captured_state,
            captured_next_state: captures.captured_next_state,
            memo: Arc::new(Mutex::new(StdHashMap::new())),
        }
    }

    /// Create a new lazy function with multiple bound variables (for multi-arg functions).
    ///
    /// FIX #1989: ID is derived deterministically from the body expression span.
    pub fn new_multi(
        name: Option<Arc<str>>,
        domain: LazyDomain,
        bounds: Vec<BoundVar>,
        body: Spanned<Expr>,
        captures: LazyFuncCaptures,
    ) -> Self {
        #[cfg(feature = "memory-stats")]
        memory_stats::inc_lazy_func();

        let id = deterministic_id_from_span(&body.span);
        let bounds: Arc<[BoundVar]> = Arc::from(bounds);
        let pre_interned_bounds = pre_intern_bounds(&bounds);
        LazyFuncValue {
            id,
            name,
            domain: Arc::new(domain),
            bounds,
            pre_interned_bounds,
            body: Arc::new(body),
            env: captures.env,
            captured_chain: captures.captured_chain,
            captured_chain_depth: captures.captured_chain_depth,
            local_ops: captures.local_ops,
            captured_state: captures.captured_state,
            captured_next_state: captures.captured_next_state,
            memo: Arc::new(Mutex::new(StdHashMap::new())),
        }
    }

    /// Create a new LazyFunc with an exception value pre-loaded into the memo.
    /// Used for EXCEPT on lazy functions: [f EXCEPT ![k] = v]
    ///
    /// FIX #1989: ID is derived deterministically from the parent ID and the
    /// exception key-value pair, so `[f EXCEPT ![k] = v]` produces a stable
    /// fingerprint across runs.
    ///
    /// Note: clippy warns about mutable_key_type because Value contains LazyFuncValue
    /// which has interior mutability (memo cache). This is safe because:
    /// 1. Value's Hash/Eq use the stable `id` field, not the mutable memo
    /// 2. The memo is purely a cache that doesn't affect semantic equality
    #[allow(clippy::mutable_key_type)]
    pub fn with_exception(&self, key: Value, value: Value) -> Self {
        let id = deterministic_exception_id(self.id, &key, &value);
        // Clone the existing memo and add the exception
        let new_memo = {
            // Memo is a performance cache; recover poisoned contents instead
            // of cascading one panic into all subsequent lazy-function updates.
            let memo = self
                .memo
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let mut new_map = memo.clone();
            new_map.insert(key, value);
            Arc::new(Mutex::new(new_map))
        };
        LazyFuncValue {
            id,
            name: self.name.clone(),
            domain: self.domain.clone(),
            bounds: self.bounds.clone(),
            pre_interned_bounds: self.pre_interned_bounds.clone(),
            body: self.body.clone(),
            env: self.env.clone(),
            captured_chain: self.captured_chain.clone(),
            captured_chain_depth: self.captured_chain_depth,
            local_ops: self.local_ops.clone(),
            captured_state: self.captured_state.clone(),
            captured_next_state: self.captured_next_state.clone(),
            memo: new_memo,
        }
    }

    /// Stable unique identifier used in hashing/fingerprinting contracts.
    pub fn id(&self) -> u64 {
        self.id
    }

    /// Borrow the optional recursive self-binding name.
    pub fn name(&self) -> Option<&Arc<str>> {
        self.name.as_ref()
    }

    /// Set the recursive self-binding name only when it is currently unset.
    pub fn set_name_if_missing(&mut self, name: Arc<str>) {
        if self.name.is_none() {
            self.name = Some(name);
        }
    }

    /// Borrow the function domain descriptor.
    pub fn domain(&self) -> &LazyDomain {
        &self.domain
    }

    /// Borrow the function bound variables.
    pub fn bounds(&self) -> &[BoundVar] {
        &self.bounds
    }

    /// Borrow the pre-interned bound variable names.
    ///
    /// Part of #3395: Pre-computed at creation time. Use with
    /// `push_binding_preinterned` to skip per-application `intern_name`.
    pub fn pre_interned_bounds(&self) -> &[(Arc<str>, NameId)] {
        &self.pre_interned_bounds
    }

    /// Borrow the function body expression.
    pub fn body(&self) -> &Spanned<Expr> {
        self.body.as_ref()
    }

    /// Borrow the captured lexical environment.
    pub fn env(&self) -> &HashMap<Arc<str>, Value> {
        &self.env
    }

    /// Borrow the Arc-wrapped captured environment for O(1) sharing.
    ///
    /// Part of #2955: Used by `build_lazy_func_ctx` to avoid cloning the
    /// entire HashMap on every function application (8.4M times for GameOfLife).
    pub fn env_arc(&self) -> &Arc<HashMap<Arc<str>, Value>> {
        &self.env
    }

    /// Borrow captured local operators, if present.
    pub fn local_ops(&self) -> Option<&Arc<tla_core::OpEnv>> {
        self.local_ops.as_ref()
    }

    /// Borrow captured current-state bindings, if present.
    pub fn captured_state(&self) -> Option<&[Value]> {
        self.captured_state.as_deref()
    }

    /// Borrow captured next-state bindings, if present.
    pub fn captured_next_state(&self) -> Option<&[Value]> {
        self.captured_next_state.as_deref()
    }

    /// Borrow the captured chain, if present.
    /// Part of #2955: Used by `build_lazy_func_ctx` to restore chain in O(1).
    pub fn captured_chain(&self) -> Option<&dyn CapturedChain> {
        self.captured_chain.as_deref()
    }

    /// The binding_depth at definition time.
    /// Part of #2955: Used to restore correct binding_depth in build_lazy_func_ctx.
    pub fn captured_chain_depth(&self) -> usize {
        self.captured_chain_depth
    }

    /// Read a memoized result for a function argument.
    ///
    /// Recovers poisoned lock contents to preserve lazy-function behavior after
    /// earlier panics in unrelated callers.
    pub fn memoized_value(&self, arg: &Value) -> Option<Value> {
        let memo = self
            .memo
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        memo.get(arg).cloned()
    }

    /// Store a memoized result for a function argument.
    ///
    /// Recovers poisoned lock contents to preserve lazy-function behavior after
    /// earlier panics in unrelated callers.
    pub fn memoize_value(&self, arg: Value, value: Value) {
        let mut memo = self
            .memo
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        memo.insert(arg, value);
    }

    /// Expose lock poison state for regression tests.
    pub fn memo_is_poisoned(&self) -> bool {
        self.memo.lock().is_err()
    }

    /// Run a callback while holding the memo lock.
    ///
    /// Used by external regression tests that need to validate lock-poison
    /// recovery behavior.
    pub fn with_memo_lock<R>(&self, f: impl FnOnce(&StdHashMap<Value, Value>) -> R) -> R {
        let memo = self
            .memo
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        f(&memo)
    }

    /// Check if an argument is in the domain
    pub fn in_domain(&self, arg: &Value) -> bool {
        match &*self.domain {
            LazyDomain::Nat => match arg {
                Value::SmallInt(n) => *n >= 0,
                Value::Int(n) => **n >= BigInt::zero(),
                _ => false,
            },
            LazyDomain::Int => matches!(arg, Value::SmallInt(_) | Value::Int(_)),
            LazyDomain::Real => matches!(arg, Value::SmallInt(_) | Value::Int(_)),
            LazyDomain::String => matches!(arg, Value::String(_)),
            LazyDomain::Product(components) => {
                // For product domains, arg should be a tuple with matching components
                match arg {
                    Value::Tuple(elems) if elems.len() == components.len() => elems
                        .iter()
                        .zip(components.iter())
                        .all(|(v, d)| d.contains(v)),
                    _ => false,
                }
            }
            LazyDomain::General(domain_val) => {
                // For general domains, use Value::set_contains for membership check.
                // If the domain contains a SetPred, membership is indeterminate (None);
                // conservatively return false since domain check is a prerequisite.
                domain_val.set_contains(arg).unwrap_or(false)
            }
        }
    }
}
