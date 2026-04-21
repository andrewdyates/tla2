// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Worker-local `ArrayState` with unshared Arc allocations.
//!
//! Part of #3337.

use std::sync::Arc;

use crate::var_index::{VarIndex, VarRegistry};
use crate::Value;

use super::fingerprint::WorkerFpMemo;
use crate::state::value_hash::finalize_fingerprint_xor;
use crate::state::{ArrayState, Fingerprint};
use tla_core::FNV_PRIME;

// ============================================================================
// WorkerArrayState
// ============================================================================

/// A worker-local copy of an `ArrayState` with unshared Arc allocations.
///
/// All top-level compound `Value` variants have their outer Arc reallocated
/// so that the worker's `Arc::clone`/`Arc::drop` operations touch private
/// refcounts rather than cross-thread shared ones. This eliminates the
/// dominant source of atomic contention during `EvalCtx::lookup_state_var`.
///
/// The fingerprint memo replaces embedded `AtomicU64` caches, avoiding
/// cross-thread cache-line bouncing during fingerprint computation.
pub(crate) struct WorkerArrayState {
    values: Box<[Value]>,
    #[allow(dead_code)] // Used by fingerprint() which is tested but not yet in production path
    memo: WorkerFpMemo,
}

impl WorkerArrayState {
    /// Convert a shared `ArrayState` into a worker-local copy.
    ///
    /// This unshares the top-level Arc for each compound value slot,
    /// giving this worker exclusive ownership of the outer refcounts.
    pub(crate) fn from_array_state(state: &ArrayState) -> Self {
        let values: Box<[Value]> = state
            .materialize_values()
            .iter()
            .map(unshare_value)
            .collect::<Vec<_>>()
            .into_boxed_slice();

        let memo = WorkerFpMemo::with_capacity(values.len() * 2);

        WorkerArrayState { values, memo }
    }

    /// Promote back to a shared `ArrayState`.
    ///
    /// This is used when a successor survives dedup/admission and needs
    /// to re-enter the shared work queue.
    #[allow(dead_code)] // Tested but not yet wired into production successor pipeline
    pub(crate) fn into_array_state(self) -> ArrayState {
        ArrayState::from_values(self.values.into_vec())
    }

    /// Get the values slice (for state binding into the evaluator).
    #[inline]
    pub(crate) fn values(&self) -> &[Value] {
        &self.values
    }

    /// Compute the fingerprint using the worker-local memo.
    #[allow(dead_code)] // Tested but not yet wired into production successor pipeline
    pub(crate) fn fingerprint(&mut self, registry: &VarRegistry) -> Fingerprint {
        self.memo.clear();
        let mut combined = 0u64;
        for (i, value) in self.values.iter().enumerate() {
            let value_fp = self.memo.value_fingerprint(value);
            let salt = registry.fp_salt(VarIndex::new(i));
            let contribution = salt.wrapping_mul(value_fp.wrapping_add(1));
            combined ^= contribution;
        }
        Fingerprint(finalize_fingerprint_xor(combined, FNV_PRIME))
    }
}

// ============================================================================
// Value unsharing (top-level Arc reallocation)
// ============================================================================

/// Create a worker-local copy of a value with unshared top-level Arcs.
///
/// For compound types, this allocates a new outer Arc with a private refcount.
/// The inner data (nested values, entries, etc.) still shares Arcs with the
/// original — only the outermost container is unshared. This is sufficient
/// to eliminate contention for `Value::clone()` during state variable lookup.
///
/// For primitive types (Bool, SmallInt), this is a trivial copy.
pub(crate) fn unshare_value(value: &Value) -> Value {
    match value {
        // Inline types: no Arc, trivial copy
        Value::Bool(b) => Value::Bool(*b),
        Value::SmallInt(n) => Value::SmallInt(*n),

        // Arc-wrapped types: create new Arc with cloned inner data.
        // The new Arc has refcount=1 (private to this worker).
        // The inner data's Arcs (entries, elements) remain shared.
        Value::Int(n) => Value::Int(Arc::new((**n).clone())),
        Value::String(s) => Value::String(Arc::from(&**s)),
        Value::ModelValue(s) => Value::ModelValue(Arc::from(&**s)),
        Value::Func(f) => Value::Func(Arc::new((**f).clone())),
        Value::IntFunc(f) => Value::IntFunc(Arc::new((**f).clone())),
        Value::Seq(s) => Value::Seq(Arc::new((**s).clone())),
        Value::Tuple(t) => {
            let cloned: Vec<Value> = t.iter().cloned().collect();
            Value::Tuple(cloned.into())
        }

        // Inline-but-contains-Arc types: clone creates private copies
        // of the outer struct, with the inner Arc refcount bumped.
        // This is acceptable for the first slice since Set and Record
        // inner Arcs are less frequently cloned during evaluation.
        Value::Set(s) => Value::Set(s.clone()),
        Value::Record(r) => Value::Record(r.clone()),

        // All other types: regular clone (rare in MCKVSSafetySmall)
        other => other.clone(),
    }
}
