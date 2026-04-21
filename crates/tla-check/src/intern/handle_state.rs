// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Handle-based state types for lightweight parallel model checking.
//!
//! `HandleState` stores value handles instead of values, making state
//! cloning a pure memcpy with no atomic operations.

use super::{HandleStateInternerBank, InvalidValueHandleError, ValueHandle};
use crate::state::{ArrayState, Fingerprint};
use crate::var_index::{VarIndex, VarRegistry};
use crate::Value;

#[cfg(test)]
use super::ValueInterner;

// ============================================================================
// HandleState - Lightweight state using handles
// ============================================================================

/// Array-based state using value handles instead of values.
///
/// This is a lightweight alternative to `ArrayState` that uses `ValueHandle`
/// instead of `Value`. Cloning this state is a pure memcpy with no atomic
/// operations, eliminating the Arc contention that limits parallel scaling.
///
/// # Usage
///
/// HandleState is used during parallel BFS exploration where state cloning
/// is a hot path. Values are looked up from the interner only when needed
/// (invariant checking, trace reconstruction).
#[derive(Clone)]
pub struct HandleState {
    /// Part of #3212: ID of the worker that produced this state.
    /// Used to select the correct interner shard for materialization.
    owner_worker: u16,
    /// Value handles indexed by VarIndex
    handles: Box<[ValueHandle]>,
    /// Pre-computed state fingerprint from the value fingerprints stored in handles.
    fingerprint: Fingerprint,
}

impl HandleState {
    /// Create a HandleState from an existing set of handles and fingerprint.
    #[cfg(test)]
    #[inline]
    pub fn new(handles: Box<[ValueHandle]>, fingerprint: Fingerprint) -> Self {
        HandleState {
            owner_worker: 0,
            handles,
            fingerprint,
        }
    }

    /// Create a HandleState by interning values into an owner-local shard.
    ///
    /// Part of #3212: Uses the producing worker's shard from the interner bank,
    /// eliminating cross-thread DashMap traffic on the common local-queue path.
    #[cfg(test)]
    pub fn from_values_sharded(
        values: &[Value],
        registry: &VarRegistry,
        bank: &HandleStateInternerBank,
        owner_worker: usize,
    ) -> Self {
        let shard = bank.shard(owner_worker);
        let handles: Vec<ValueHandle> = values.iter().map(|v| shard.intern(v.clone())).collect();

        let fingerprint = compute_handle_fingerprint(&handles, registry);

        HandleState {
            owner_worker: owner_worker as u16,
            handles: handles.into_boxed_slice(),
            fingerprint,
        }
    }

    /// Create a HandleState by interning CompactValues from an ArrayState, avoiding
    /// the intermediate `Vec<Value>` allocation of `materialize_values()`.
    ///
    /// Part of #3579: Each CompactValue is converted to Value inline and interned
    /// directly, eliminating one Vec allocation per successor state.
    pub fn from_array_state_sharded(
        arr: &ArrayState,
        registry: &VarRegistry,
        bank: &HandleStateInternerBank,
        owner_worker: usize,
    ) -> Self {
        let shard = bank.shard(owner_worker);
        let handles: Vec<ValueHandle> = arr
            .values()
            .iter()
            .map(|cv| shard.intern(Value::from(cv)))
            .collect();

        let fingerprint = compute_handle_fingerprint(&handles, registry);

        HandleState {
            owner_worker: owner_worker as u16,
            handles: handles.into_boxed_slice(),
            fingerprint,
        }
    }

    /// Create a HandleState by interning values from a regular ArrayState.
    ///
    /// Legacy path using a single global interner. Test-only since Part of #3212
    /// moved production code to `from_values_sharded`.
    #[cfg(test)]
    pub(crate) fn from_values(
        values: &[Value],
        registry: &VarRegistry,
        interner: &ValueInterner,
    ) -> Self {
        let handles: Vec<ValueHandle> = values.iter().map(|v| interner.intern(v.clone())).collect();

        let fingerprint = compute_handle_fingerprint(&handles, registry);

        HandleState {
            owner_worker: 0,
            handles: handles.into_boxed_slice(),
            fingerprint,
        }
    }

    /// Get all handles.
    #[cfg(test)]
    #[inline]
    pub fn handles(&self) -> &[ValueHandle] {
        &self.handles
    }

    /// Get the pre-computed fingerprint.
    #[inline]
    pub fn fingerprint(&self) -> Fingerprint {
        self.fingerprint
    }

    /// Part of #3212: Get the owner worker ID for this state.
    #[cfg(test)]
    #[inline]
    pub fn owner_worker(&self) -> usize {
        self.owner_worker as usize
    }

    /// Materialize values from handles using the owner's shard in the bank.
    ///
    /// Part of #3212: Reads from the producing worker's shard, so consumption
    /// by a different (stealing) worker still resolves correctly.
    #[cfg(test)]
    pub(crate) fn materialize_from_bank(
        &self,
        bank: &HandleStateInternerBank,
    ) -> Result<Vec<Value>, InvalidValueHandleError> {
        let shard = bank.shard(self.owner_worker as usize);
        self.handles.iter().map(|h| shard.try_get(*h)).collect()
    }

    /// Materialize values directly into an existing ArrayState scratch buffer.
    ///
    /// Part of #3213: avoids the intermediate Vec allocation on the dequeue
    /// path by writing looked-up values straight into the worker-local scratch.
    pub(crate) fn materialize_into_bank(
        &self,
        target: &mut ArrayState,
        bank: &HandleStateInternerBank,
    ) -> Result<(), InvalidValueHandleError> {
        let shard = bank.shard(self.owner_worker as usize);
        target.overwrite_from_result_iter(self.handles.iter().map(|h| shard.try_get(*h)))
    }

    /// Materialize values from handles using a single interner.
    ///
    /// Legacy path for non-sharded callers. Test-only since Part of #3212
    /// moved production code to `materialize_into_bank`.
    #[cfg(test)]
    pub(crate) fn materialize(
        &self,
        interner: &ValueInterner,
    ) -> Result<Vec<Value>, InvalidValueHandleError> {
        self.handles.iter().map(|h| interner.try_get(*h)).collect()
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Compute a state fingerprint from handle fingerprints.
///
/// Uses the same algorithm as ArrayState fingerprinting for consistency.
fn compute_handle_fingerprint(handles: &[ValueHandle], registry: &VarRegistry) -> Fingerprint {
    use tla_core::FNV_PRIME;

    // ValueHandle stores each interned value's fingerprint, so this matches
    // ArrayState's combined XOR when the logical state is the same.
    let mut combined_xor: u64 = 0;
    for (i, handle) in handles.iter().enumerate() {
        let idx = VarIndex::new(i);
        let salt = registry.fp_salt(idx);
        // Add 1 to handle value to avoid zero-contribution for zero fingerprints
        let contribution = salt.wrapping_mul(handle.0.wrapping_add(1));
        combined_xor ^= contribution;
    }

    // Final mixing — must match finalize_fingerprint_xor exactly (Part of #3327)
    let mixed = crate::state::finalize_fingerprint_xor(combined_xor, FNV_PRIME);
    Fingerprint(mixed)
}

#[cfg(test)]
mod tests {
    use super::{HandleState, HandleStateInternerBank, ValueInterner};
    use crate::state::ArrayState;
    use crate::var_index::VarRegistry;
    use crate::Value;

    fn assert_fingerprint_equivalence(values: Vec<Value>) {
        let registry = VarRegistry::from_names((0..values.len()).map(|idx| format!("v{idx}")));

        let mut array_state = ArrayState::from_values(values.clone());
        let array_fp = array_state.fingerprint(&registry);

        let interner = ValueInterner::new();
        let legacy = HandleState::from_values(&values, &registry, &interner);
        assert_eq!(
            legacy.fingerprint(),
            array_fp,
            "legacy HandleState fingerprint must match ArrayState"
        );

        let bank = HandleStateInternerBank::new(1);
        let sharded = HandleState::from_values_sharded(&values, &registry, &bank, 0);
        assert_eq!(
            sharded.fingerprint(),
            array_fp,
            "sharded HandleState fingerprint must match ArrayState"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_handlestate_arraystate_fingerprint_equivalence() {
        let cases = [
            Vec::new(),
            vec![Value::int(0)],
            vec![Value::Bool(false)],
            vec![Value::int(0), Value::int(42), Value::int(-7)],
            vec![Value::int(i64::MAX), Value::int(i64::MIN)],
            vec![
                Value::tuple([Value::int(1), Value::Bool(true)]),
                Value::set([Value::int(2), Value::int(3)]),
            ],
        ];

        for values in cases {
            assert_fingerprint_equivalence(values);
        }
    }
}
