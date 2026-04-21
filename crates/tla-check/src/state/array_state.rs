// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array-based state representation for O(1) variable access.
//!
//! Unlike `State` which uses OrdMap, `ArrayState` stores values in a fixed-size
//! array indexed by VarIndex. This provides O(1) get/set operations and
//! single-allocation state creation, critical for high-performance model checking.
//!
//! Companion modules:
//! - `array_state_bind`: bind/unbind methods for TLC-style mutable enumeration
//! - `array_state_convert`: State-to-ArrayState conversion constructors
//! - `array_state_fingerprint`: fingerprint cache and incremental update methods

use std::fmt;
use std::hash::{Hash, Hasher};

use tla_value::CompactValue;

use tla_eval::StateEnvRef;

use crate::var_index::{VarIndex, VarRegistry};
use crate::Value;

use super::array_state_fingerprint::ArrayStateFpCache;
use super::State;

/// Entry for undo stack during bind/unbind enumeration
///
/// Used by `ArrayState::bind()` and `ArrayState::unbind_to()` to implement
/// TLC-style mutable state exploration with backtracking.
///
/// Part of #3579: Stores `CompactValue` (8B) instead of `Value` (24B),
/// reducing undo stack memory by 3x.
///
/// See designs/2026-01-13-bind-unbind-architecture.md for design rationale.
#[derive(Clone, Debug)]
pub struct UndoEntry {
    /// The variable index that was bound
    pub idx: VarIndex,
    /// The previous compact value before binding (to restore on unbind)
    pub old_value: CompactValue,
}

/// Array-based state for O(1) variable access
///
/// Unlike `State` which uses OrdMap, this stores values in a fixed-size array
/// indexed by VarIndex. This provides O(1) get/set operations and single-allocation
/// state creation, which is critical for high-performance model checking.
///
/// # Usage
///
/// ```rust
/// use tla_check::{ArrayState, VarRegistry, Value};
///
/// let registry = VarRegistry::from_names(["x", "y"]);
/// let idx_x = registry.get("x").unwrap();
/// let idx_y = registry.get("y").unwrap();
///
/// let mut state = ArrayState::new(registry.len());
/// state.set(idx_x, Value::int(1));
/// state.set(idx_y, Value::int(2));
/// let _fp = state.fingerprint(&registry);
/// ```
#[derive(Clone)]
pub struct ArrayState {
    /// Compact values indexed by VarIndex (8B per slot vs 24B for Value)
    ///
    /// Part of #3579: 3x smaller state arrays. Inline scalars (Bool, SmallInt)
    /// are encoded directly in the CompactValue bits. Compound types use a
    /// heap pointer to Box<Value>.
    /// `pub(crate)` for arena promotion path (Part of #3990).
    pub(crate) values: Box<[CompactValue]>,
    /// Cached fingerprint + per-variable fingerprint cache (None until computed)
    /// `pub(crate)` for arena promotion path (Part of #3990).
    pub(crate) fp_cache: Option<ArrayStateFpCache>,
}

impl ArrayState {
    /// Create a new ArrayState with the given number of variables
    /// All values are initialized to Bool(false) as a placeholder
    #[inline]
    pub fn new(num_vars: usize) -> Self {
        #[cfg(feature = "memory-stats")]
        {
            crate::value::memory_stats::inc_array_state();
            crate::value::memory_stats::inc_array_state_bytes(num_vars);
        }

        let false_cv = CompactValue::from(false);
        ArrayState {
            values: vec![false_cv; num_vars].into_boxed_slice(),
            fp_cache: None,
        }
    }

    /// Create an ArrayState directly from a Vec of values
    /// Useful for testing and cases where you already have the values
    #[inline]
    pub fn from_values(values: Vec<Value>) -> Self {
        #[cfg(feature = "memory-stats")]
        {
            crate::value::memory_stats::inc_array_state();
            crate::value::memory_stats::inc_array_state_bytes(values.len());
        }

        let compact: Vec<CompactValue> = values.into_iter().map(CompactValue::from).collect();
        ArrayState {
            values: compact.into_boxed_slice(),
            fp_cache: None,
        }
    }

    // State-conversion constructors (from_state, from_state_with_fp,
    // from_successor_state) are in array_state_convert.rs

    /// Clone this ArrayState without the fp_cache, for use as a working state.
    ///
    /// This is an optimization for bind/unbind enumeration patterns where:
    /// 1. The working state is modified via bind()/unbind()
    /// 2. The fp_cache is never read from the working state
    /// 3. Fingerprints are computed from the base state + changes (DiffSuccessor)
    ///
    /// By not cloning the fp_cache, we avoid:
    /// - Cloning the BoxedSlice of per-variable fingerprints
    /// - Repeated invalidation of fp_cache during bind() calls
    ///
    /// Part of #188: Batch fingerprint optimization
    #[inline]
    pub fn clone_for_working(&self) -> Self {
        ArrayState {
            values: self.values.clone(),
            fp_cache: None, // Don't clone cache - working state won't use it
        }
    }

    /// Clone this ArrayState while preserving a complete per-slot fingerprint cache.
    ///
    /// Unlike `Clone`, this keeps `value_fps` when they are already populated.
    /// The #3285 parallel experiment uses this only on the env-gated queue lane.
    #[inline]
    pub fn clone_with_complete_fp_cache(&self) -> Self {
        let fp_cache = self.fp_cache.as_ref().map(|cache| ArrayStateFpCache {
            combined_xor: cache.combined_xor,
            fingerprint: cache.fingerprint,
            value_fps: cache.value_fps.clone(),
        });

        ArrayState {
            values: self.values.clone(),
            fp_cache,
        }
    }

    /// Overwrite all values from a slice of Values (converting to CompactValue).
    ///
    /// This is useful for reusing a single `ArrayState` allocation as a scratch buffer
    /// (e.g., when reading from bulk state storage).
    #[inline]
    pub fn overwrite_from_slice(&mut self, values: &[Value]) {
        assert_eq!(
            self.values.len(),
            values.len(),
            "overwrite_from_slice: length mismatch"
        );
        for (slot, v) in self.values.iter_mut().zip(values.iter()) {
            *slot = CompactValue::from(v.clone());
        }
        self.fp_cache = None; // Invalidate cached fingerprint + per-var cache
    }

    /// Overwrite all values from a fallible iterator without allocating.
    ///
    /// Part of #3213: enables in-place materialization paths (e.g., HandleState
    /// interner lookups) that produce owned `Value`s one slot at a time.
    ///
    /// Panics if the iterator yields fewer or more items than `self.len()`.
    pub(crate) fn overwrite_from_result_iter<E, I>(&mut self, values: I) -> Result<(), E>
    where
        I: IntoIterator<Item = Result<Value, E>>,
    {
        self.fp_cache = None;

        let mut iter = values.into_iter();
        for slot in self.values.iter_mut() {
            let value = iter
                .next()
                .expect("overwrite_from_result_iter requires exactly one value per slot")?;
            *slot = CompactValue::from(value);
        }

        assert!(
            iter.next().is_none(),
            "overwrite_from_result_iter received more values than slots"
        );
        Ok(())
    }

    /// Get a value by index, converting from CompactValue to owned Value.
    ///
    /// Part of #3579: Returns owned `Value` (not `&Value`) because CompactValue
    /// inline scalars have no Value object to reference. For inline types (Bool,
    /// SmallInt), this is a cheap bitwise reconstruction. For heap types, this
    /// clones the inner Box<Value>.
    #[inline(always)]
    pub fn get(&self, idx: VarIndex) -> Value {
        Value::from(&self.values[idx.as_usize()])
    }

    /// Get a reference to the raw CompactValue at the given index.
    ///
    /// Part of #3579: For callers that can work directly with CompactValue
    /// (e.g., fingerprinting, comparison) without converting to Value.
    #[inline(always)]
    pub fn get_compact(&self, idx: VarIndex) -> &CompactValue {
        &self.values[idx.as_usize()]
    }

    /// Set a value by index (converting Value to CompactValue for storage)
    #[inline(always)]
    pub fn set(&mut self, idx: VarIndex, value: Value) {
        self.values[idx.as_usize()] = CompactValue::from(value);
        self.fp_cache = None; // Invalidate cached fingerprint + per-var cache
    }

    /// Get the compact values array.
    ///
    /// Part of #3579: Returns `&[CompactValue]` (8B per slot). Callers that
    /// need `Value` should use `get()` for single values or `materialize_values()`
    /// for the full array.
    #[inline]
    pub fn values(&self) -> &[CompactValue] {
        &self.values
    }

    /// Materialize all values as a Vec<Value>.
    ///
    /// Part of #3579: Allocating conversion from compact storage to Value.
    /// Used by cold paths that need `&[Value]` (State conversion, serialization,
    /// display). The hot path (BFS evaluation) uses `env_ref()` directly.
    pub fn materialize_values(&self) -> Vec<Value> {
        self.values.iter().map(Value::from).collect()
    }

    /// Get a `StateEnvRef` pointing to this state's compact values array.
    ///
    /// Part of #3579: Returns `Compact` variant for zero-overhead binding
    /// into the evaluation context. The evaluator's `get_value()` reconstructs
    /// inline scalars from CompactValue bits with no heap access.
    #[inline]
    pub fn env_ref(&self) -> StateEnvRef {
        StateEnvRef::from_compact_slice(&self.values)
    }

    /// Convert to State using the given registry
    ///
    /// The State will have its fingerprint computed using ArrayState's algorithm
    /// (registry-based indices) to ensure consistency when converting between
    /// State and ArrayState representations.
    ///
    /// Part of #158: Fixed fingerprint mismatch between State and ArrayState.
    /// Previously this used `compute_fingerprint` which uses alphabetical order,
    /// causing fingerprint mismatches in liveness checking.
    pub fn to_state(&self, registry: &VarRegistry) -> State {
        let values = self.materialize_values();
        State::from_indexed(&values, registry)
    }

    /// Number of variables
    #[inline]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Check if empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    // Bind/unbind methods and snapshot are in array_state_bind.rs.
    // Fingerprint computation methods are in array_state_fingerprint.rs.
}

impl fmt::Debug for ArrayState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ArrayState({} vars", self.values.len())?;
        if let Some(cache) = &self.fp_cache {
            write!(f, ", fp={:016x}", cache.fingerprint.0)?;
        }
        write!(f, ")")
    }
}

impl Hash for ArrayState {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // fp_cache must be populated before hashing. All production paths compute
        // fingerprints via `fingerprint()` or `compute_fingerprint()` before any
        // hash-based lookup. Hitting this without fp_cache means a logic error in
        // the caller — fail loud rather than silently producing collision-heavy hashes.
        let cache = self.fp_cache.as_ref().unwrap_or_else(|| {
            panic!(
                "ArrayState::hash called without fp_cache populated. \
                 Call fingerprint() or compute_fingerprint() before using ArrayState \
                 in hash-based collections."
            )
        });
        cache.fingerprint.0.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::State;

    /// Regression test for #1729: from_state must panic when a registry
    /// variable is missing from the State, not silently default to Bool(false).
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    #[should_panic(expected = "expected registry variables")]
    fn test_1729_from_state_panics_on_missing_var() {
        let registry = VarRegistry::from_names(["x", "y"]);
        // State only has "x", missing "y"
        let state = State::from_pairs([("x", Value::SmallInt(1))]);
        ArrayState::from_state(&state, &registry); // should panic
    }

    /// Regression test for #1729: from_state_with_fp must panic when a registry
    /// variable is missing from the State.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    #[should_panic(expected = "expected registry variables")]
    fn test_1729_from_state_with_fp_panics_on_missing_var() {
        let registry = VarRegistry::from_names(["a", "b"]);
        // State only has "a", missing "b"
        let state = State::from_pairs([("a", Value::Bool(true))]);
        ArrayState::from_state_with_fp(&state, &registry); // should panic
    }

    /// Regression test for #1729: from_successor_state must panic when a
    /// registry variable is missing from the successor State.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    #[should_panic(expected = "expected registry variables")]
    fn test_1729_from_successor_state_panics_on_missing_var() {
        let registry = VarRegistry::from_names(["x", "y"]);
        // Build a valid base state
        let base_state = State::from_pairs([("x", Value::SmallInt(1)), ("y", Value::SmallInt(2))]);
        let base_array = ArrayState::from_state(&base_state, &registry);
        // Successor is missing "y"
        let successor = State::from_pairs([("x", Value::SmallInt(3))]);
        ArrayState::from_successor_state(&successor, &base_array, &registry); // should panic
    }
}
