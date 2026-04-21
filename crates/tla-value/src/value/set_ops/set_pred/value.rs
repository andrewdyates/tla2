// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `SetPredValue` runtime object: struct definition, constructors, and
//! captured-environment accessors.
//!
//! This module owns the lazy-env materialization logic and the runtime-facing
//! API consumed by `tla-eval` and `tla-check`. Identity contract (ordering,
//! hashing, fingerprinting) lives in `identity.rs`.

use super::super::super::*;
use super::super::cached_bound_names::CachedBoundNames;
use super::super::span_normalize::{bound_var_identity_hash, expr_identity_hash};
use super::captures::SetPredCaptures;
use crate::CapturedChain;
use std::sync::OnceLock;
use tla_core::name_intern::NameId;

/// Lazy set filter ({x \in S : P(x)})
///
/// This value represents a filtered set without eagerly evaluating the predicate
/// for all elements. This is essential for filters over non-enumerable sets like STRING.
///
/// Membership checking requires an evaluation context, so `set_contains` returns None.
/// The actual membership check must be done in eval.rs using `check_set_pred_membership`.
///
/// Enumeration is only possible when the source set is enumerable.
#[derive(Clone)]
pub struct SetPredValue {
    /// Debug-only identifier used for diagnostics.
    /// Semantic equality/ordering/hashing/fingerprinting intentionally ignore this.
    pub(crate) id: u64,
    /// The source set S
    pub(crate) source: Box<Value>,
    /// Bound variable for the filter (boxed to reduce Value enum size)
    pub(crate) bound: Box<BoundVar>,
    /// Cached interned bound names for hot membership checks.
    cached_bound_names: CachedBoundNames,
    /// The predicate expression P(x)
    pub(crate) pred: Arc<Spanned<Expr>>,
    /// Captured env as a stable Arc for restore sites and eager sharing.
    env_arc: Arc<HashMap<Arc<str>, Value>>,
    /// Part of #2990: Lazy env — materialized on first identity access via OnceLock.
    pub(crate) env: OnceLock<Arc<HashMap<Arc<str>, Value>>>,
    /// Issue #418: Capture state_env at definition time for TLC parity.
    /// TLC captures state when constructing set filters (Yuan Yu 2010 fix).
    pub(crate) captured_state: Option<Arc<[Value]>>,
    /// Issue #418: Capture next_state_env at definition time for TLC parity.
    pub(crate) captured_next_state: Option<Arc<[Value]>>,
    /// Pre-computed span-normalized identity hash for bound (#2788, #2955).
    /// Part of #2955: Changed from String to u64 hash — eliminates ~12% runtime
    /// spent in Debug-formatting entire AST trees via `format!("{:?}", ...)`.
    pub(super) cached_bound_sig: u64,
    /// Pre-computed span-normalized identity hash for predicate (#2788, #2955).
    pub(super) cached_pred_sig: u64,
    /// Part of #2990: Captured BindingChain for O(1) restore at consumption time.
    /// Same pattern as LazyFuncCaptures. When present, consumption sites restore
    /// the chain directly instead of rebuilding from the flat `env` HashMap.
    captured_chain: Option<Box<dyn CapturedChain>>,
    /// Part of #2990: Binding depth at creation time, for chain restore.
    captured_chain_depth: usize,
}

impl SetPredValue {
    /// Create a new lazy set filter from a normalized capture bundle.
    pub fn new_with_captures(
        source: Value,
        bound: BoundVar,
        pred: Spanned<Expr>,
        captures: SetPredCaptures,
    ) -> Self {
        let id = super::super::super::lazy_func::deterministic_id_from_span(&pred.span);
        let cached_bound_sig = bound_var_identity_hash(&bound);
        let cached_pred_sig = expr_identity_hash(&pred.node);
        let cached_bound_names = CachedBoundNames::from_bound(&bound);
        let env = if captures.captured_chain.is_some() {
            OnceLock::new()
        } else {
            OnceLock::from(Arc::clone(&captures.env))
        };

        SetPredValue {
            id,
            source: Box::new(source),
            bound: Box::new(bound),
            cached_bound_names,
            pred: Arc::new(pred),
            env_arc: captures.env,
            env,
            captured_state: captures.captured_state,
            captured_next_state: captures.captured_next_state,
            cached_bound_sig,
            cached_pred_sig,
            captured_chain: captures.captured_chain,
            captured_chain_depth: captures.captured_chain_depth,
        }
    }

    /// Create a new lazy set filter with eagerly captured environment.
    pub fn new(
        source: Value,
        bound: BoundVar,
        pred: Spanned<Expr>,
        env: HashMap<Arc<str>, Value>,
        captured_state: Option<Arc<[Value]>>,
        captured_next_state: Option<Arc<[Value]>>,
    ) -> Self {
        Self::new_with_captures(
            source,
            bound,
            pred,
            SetPredCaptures::new(Arc::new(env), captured_state, captured_next_state),
        )
    }

    /// Part of #2990 Phase 2: Create with chain capture and deferred env.
    #[allow(clippy::too_many_arguments)]
    pub fn new_with_chain(
        source: Value,
        bound: BoundVar,
        pred: Spanned<Expr>,
        captured_state: Option<Arc<[Value]>>,
        captured_next_state: Option<Arc<[Value]>>,
        chain: Box<dyn CapturedChain>,
        chain_depth: usize,
        env_arc: Arc<HashMap<Arc<str>, Value>>,
    ) -> Self {
        Self::new_with_captures(
            source,
            bound,
            pred,
            SetPredCaptures::new(env_arc, captured_state, captured_next_state)
                .with_captured_chain(chain, chain_depth),
        )
    }

    /// Stable unique identifier used for debug diagnostics.
    pub fn id(&self) -> u64 {
        self.id
    }

    /// Borrow the source set.
    pub fn source(&self) -> &Value {
        self.source.as_ref()
    }

    /// Borrow the bound variable.
    pub fn bound(&self) -> &BoundVar {
        self.bound.as_ref()
    }

    pub fn cached_simple_bound_name(&self) -> Option<(&Arc<str>, NameId)> {
        if let CachedBoundNames::Simple(name, id) = &self.cached_bound_names {
            Some((name, *id))
        } else {
            None
        }
    }

    pub fn cached_tuple_bound_names(&self) -> Option<&[(Arc<str>, NameId)]> {
        if let CachedBoundNames::Tuple(entries) = &self.cached_bound_names {
            Some(entries.as_ref())
        } else {
            None
        }
    }

    /// Borrow the predicate expression.
    pub fn pred(&self) -> &Spanned<Expr> {
        self.pred.as_ref()
    }

    /// Borrow the captured env, materializing lazily from chain if needed.
    pub fn env(&self) -> &HashMap<Arc<str>, Value> {
        self.env
            .get_or_init(|| {
                if let Some(chain) = &self.captured_chain {
                    let mut map = (*self.env_arc).clone();
                    chain.materialize_locals(&mut map);
                    return Arc::new(map);
                }
                Arc::clone(&self.env_arc)
            })
            .as_ref()
    }

    /// Borrow the stable Arc-wrapped captured environment.
    pub fn env_arc(&self) -> &Arc<HashMap<Arc<str>, Value>> {
        &self.env_arc
    }

    /// Borrow captured current-state bindings, if present.
    pub fn captured_state(&self) -> Option<&[Value]> {
        self.captured_state.as_deref()
    }

    /// Borrow captured next-state bindings, if present.
    pub fn captured_next_state(&self) -> Option<&[Value]> {
        self.captured_next_state.as_deref()
    }

    /// Part of #2990: Borrow the captured BindingChain, if present.
    pub fn captured_chain(&self) -> Option<&dyn CapturedChain> {
        self.captured_chain.as_deref()
    }

    /// Part of #2990: Get the binding depth at capture time.
    pub fn captured_chain_depth(&self) -> usize {
        self.captured_chain_depth
    }

    /// Part of #3473: compatibility alias for older chain-aware restore sites.
    pub fn captured_env_arc(&self) -> Option<&Arc<HashMap<Arc<str>, Value>>> {
        self.captured_chain.as_ref().map(|_| self.env_arc())
    }

    /// Check if the source set is enumerable
    #[allow(dead_code)] // called via Value enum dispatch
    pub(crate) fn is_enumerable(&self) -> bool {
        self.source.iter_set().is_some()
    }

    /// Check if the source is a non-enumerable infinite set (STRING, AnySet)
    #[allow(dead_code)] // called via Value enum dispatch
    pub(crate) fn is_infinite(&self) -> bool {
        matches!(self.source.as_ref(), Value::StringSet | Value::AnySet)
    }

    /// Check if the element is in the source set (prerequisite for predicate check)
    /// Returns None if source can't do membership check
    #[allow(dead_code)] // called via Value enum dispatch
    pub(crate) fn source_contains(&self, v: &Value) -> Option<bool> {
        self.source.set_contains(v)
    }
}
