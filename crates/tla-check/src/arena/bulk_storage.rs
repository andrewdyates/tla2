// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BulkStateStorage and BulkStateHandle - contiguous storage for multiple states.
//!
//! Instead of individual `Box<[Value]>` allocations (one per state),
//! this stores all values in a single large buffer. States are accessed
//! by index into the buffer.
//!
//! # Memory Layout
//!
//! ```text
//! [state_0_var_0, state_0_var_1, ..., state_1_var_0, state_1_var_1, ...]
//! |<------- vars_per_state ------->|<------- vars_per_state ------->|
//! ```

use crate::state::Fingerprint;
use crate::Value;

/// Contiguous storage for multiple states, reducing heap fragmentation.
///
/// Instead of 655K individual `Box<[Value]>` allocations (one per state),
/// this stores all values in a single large buffer. States are accessed
/// by index into the buffer.
///
/// # Usage
///
/// ```rust
/// use tla_check::arena::BulkStateStorage; // crate-internal path
/// use tla_check::Value;
///
/// let mut storage = BulkStateStorage::new(2, 3);
///
/// // Add a state
/// let values = [Value::int(1), Value::int(2)];
/// let idx = storage.push_state(&values);
///
/// // Access state values
/// assert_eq!(storage.get_state(idx), &values);
/// ```
pub(crate) struct BulkStateStorage {
    /// Contiguous storage for all state values
    values: Vec<Value>,
    /// Number of variables per state
    vars_per_state: usize,
    /// Number of states currently stored
    pub(crate) num_states: usize,
    /// Cached fingerprints (fingerprint, combined_xor) per state
    fingerprints: Vec<Option<(Fingerprint, u64)>>,
}

impl BulkStateStorage {
    #[inline]
    fn next_state_index_u32(&self) -> u32 {
        assert!(
            self.num_states < (u32::MAX as usize),
            "BulkStateStorage index overflow: num_states ({}) reached u32::MAX ({})",
            self.num_states,
            u32::MAX
        );
        u32::try_from(self.num_states)
            .expect("BulkStateStorage index overflow: num_states does not fit in u32")
    }

    #[inline]
    #[cfg(test)]
    fn state_count_u32(&self) -> u32 {
        u32::try_from(self.num_states)
            .expect("BulkStateStorage count overflow: num_states exceeds u32::MAX")
    }

    /// Create bulk storage with capacity for the given number of states.
    ///
    /// # Arguments
    /// * `vars_per_state` - Number of variables per state (from VarRegistry)
    /// * `capacity` - Initial capacity in number of states
    pub(crate) fn new(vars_per_state: usize, capacity: usize) -> Self {
        let total_values = capacity.saturating_mul(vars_per_state);
        BulkStateStorage {
            values: Vec::with_capacity(total_values),
            vars_per_state,
            num_states: 0,
            fingerprints: Vec::with_capacity(capacity),
        }
    }

    /// Returns true if no states are stored.
    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.num_states == 0
    }

    /// Create empty storage (no pre-allocation)
    pub(crate) fn empty(vars_per_state: usize) -> Self {
        BulkStateStorage {
            values: Vec::new(),
            vars_per_state,
            num_states: 0,
            fingerprints: Vec::new(),
        }
    }

    /// Add a state and return its index.
    ///
    /// # Arguments
    /// * `values` - Values for the state (must have length == vars_per_state)
    ///
    /// # Panics
    /// Panics if `values.len() != vars_per_state`
    #[cfg(test)]
    pub(crate) fn push_state(&mut self, values: &[Value]) -> u32 {
        assert_eq!(
            values.len(),
            self.vars_per_state,
            "State values length mismatch"
        );

        let idx = self.next_state_index_u32();
        self.values.extend(values.iter().cloned());
        self.fingerprints.push(None);
        self.num_states += 1;
        idx
    }

    /// Add a state from an iterator of values.
    #[cfg(any(test, feature = "z4"))]
    pub(crate) fn push_state_iter(&mut self, values: impl IntoIterator<Item = Value>) -> u32 {
        let idx = self.next_state_index_u32();
        let start_len = self.values.len();

        self.values.extend(values);

        // Verify we got the expected number of values
        let added = self.values.len() - start_len;
        assert_eq!(
            added, self.vars_per_state,
            "State values count mismatch: expected {}, got {}",
            self.vars_per_state, added
        );

        self.fingerprints.push(None);
        self.num_states += 1;
        idx
    }

    /// Get values for a state by index.
    #[inline]
    pub(crate) fn get_state(&self, idx: u32) -> &[Value] {
        let start = (idx as usize) * self.vars_per_state;
        &self.values[start..start + self.vars_per_state]
    }

    /// Get a specific value from a state.
    #[inline]
    #[cfg(test)]
    pub(crate) fn get_value(&self, state_idx: u32, var_idx: usize) -> &Value {
        let offset = (state_idx as usize) * self.vars_per_state + var_idx;
        &self.values[offset]
    }

    /// Set a specific value in a state.
    #[inline]
    #[cfg(test)]
    pub(crate) fn set_value(&mut self, state_idx: u32, var_idx: usize, value: Value) {
        let offset = (state_idx as usize) * self.vars_per_state + var_idx;
        self.values[offset] = value;
        // Invalidate fingerprint cache
        self.fingerprints[state_idx as usize] = None;
    }

    /// Get or compute fingerprint for a state.
    #[cfg(test)]
    pub(crate) fn fingerprint(
        &mut self,
        idx: u32,
        registry: &crate::var_index::VarRegistry,
    ) -> Fingerprint {
        if let Some((fp, _)) = self.fingerprints[idx as usize] {
            return fp;
        }

        // Compute fingerprint using same algorithm as ArrayState
        let values = self.get_state(idx);
        let fp = crate::state::compute_fingerprint_from_array(values, registry);

        // Cache the fingerprint (combined_xor would need separate computation, store 0 for now)
        self.fingerprints[idx as usize] = Some((fp, 0));
        fp
    }

    /// Number of states stored.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.num_states
    }

    /// Number of variables per state.
    #[inline]
    #[cfg(test)]
    pub(crate) fn vars_per_state(&self) -> usize {
        self.vars_per_state
    }

    /// Total memory used in bytes (approximate).
    pub(crate) fn memory_usage(&self) -> usize {
        // Vec<Value> capacity
        let values_mem = self.values.capacity() * std::mem::size_of::<Value>();
        // Vec fingerprints
        let fp_mem =
            self.fingerprints.capacity() * std::mem::size_of::<Option<(Fingerprint, u64)>>();
        values_mem + fp_mem
    }
}

#[allow(clippy::missing_fields_in_debug)]
impl std::fmt::Debug for BulkStateStorage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BulkStateStorage")
            .field("num_states", &self.num_states)
            .field("vars_per_state", &self.vars_per_state)
            .field("memory_usage", &self.memory_usage())
            .finish()
    }
}

/// A handle to a state stored in BulkStateStorage.
///
/// This is a lightweight reference (8 bytes) that can be used instead of
/// cloning an entire ArrayState. The handle is valid as long as the
/// BulkStateStorage is not dropped.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct BulkStateHandle {
    /// Index into BulkStateStorage
    pub(crate) index: u32,
    /// Cached fingerprint (if computed)
    pub(crate) fingerprint: Option<Fingerprint>,
}

impl BulkStateHandle {
    /// Create a new handle with the given index.
    #[inline]
    #[cfg(test)]
    pub(crate) fn new(index: u32) -> Self {
        BulkStateHandle {
            index,
            fingerprint: None,
        }
    }

    /// Create a handle with a pre-computed fingerprint.
    #[inline]
    pub(crate) fn with_fingerprint(index: u32, fingerprint: Fingerprint) -> Self {
        BulkStateHandle {
            index,
            fingerprint: Some(fingerprint),
        }
    }
}

impl BulkStateStorage {
    /// Push a state from a value slice directly (no State/OrdMap creation).
    ///
    /// Values must be in VarRegistry index order. This is the most memory-efficient
    /// way to add states, avoiding OrdMap allocation entirely.
    ///
    /// # Arguments
    /// * `values` - Values in VarRegistry index order
    ///
    /// # Returns
    /// The index of the newly added state.
    ///
    /// # Panics
    /// Panics if `values.len() != vars_per_state`.
    #[inline]
    pub(crate) fn push_from_values(&mut self, values: &[Value]) -> u32 {
        assert_eq!(
            values.len(),
            self.vars_per_state,
            "Value slice size mismatch: expected {}, got {}",
            self.vars_per_state,
            values.len()
        );

        let idx = self.next_state_index_u32();

        // Push all values - they're already in registry order
        self.values.extend_from_slice(values);
        self.fingerprints.push(None);
        self.num_states += 1;
        idx
    }

    /// Convert a State to a bulk state entry, returning the index.
    ///
    /// This is useful for batch-converting initial states from State to
    /// bulk storage format.
    pub(crate) fn push_from_state(
        &mut self,
        state: &crate::state::State,
        registry: &crate::var_index::VarRegistry,
    ) -> u32 {
        assert_eq!(
            registry.len(),
            self.vars_per_state,
            "Registry size mismatch"
        );

        let idx = self.next_state_index_u32();

        // Add values in registry index order
        for (var_idx, _name) in registry.iter() {
            let name = registry.name(var_idx);
            let value = state.get(name).cloned().unwrap_or_else(|| {
                panic!(
                    "BulkStateStorage::push_from_state: state missing variable '{}' \
                     expected by registry (state has {} vars, registry has {})",
                    name,
                    state.len(),
                    registry.len()
                )
            });
            self.values.push(value);
        }

        self.fingerprints.push(None);
        self.num_states += 1;
        idx
    }

    /// Create a BulkStateStorage from a slice of States.
    ///
    /// This is the most efficient way to bulk-convert initial states.
    #[cfg(test)]
    pub(crate) fn from_states(
        states: &[crate::state::State],
        registry: &crate::var_index::VarRegistry,
    ) -> Self {
        let num_states = states.len();
        let vars_per_state = registry.len();
        let mut storage = BulkStateStorage::new(vars_per_state, num_states);

        for state in states {
            storage.push_from_state(state, registry);
        }

        storage
    }

    /// Convert a bulk state to an ArrayState.
    ///
    /// This creates an independent ArrayState that owns its values.
    /// Use sparingly - the point of bulk storage is to avoid this.
    #[cfg(test)]
    pub(crate) fn to_array_state(&self, idx: u32) -> crate::state::ArrayState {
        let values = self.get_state(idx);
        crate::state::ArrayState::from_values(values.to_vec())
    }

    /// Get an iterator over all state handles.
    #[cfg(test)]
    pub(crate) fn handles(&self) -> impl Iterator<Item = BulkStateHandle> {
        (0..self.state_count_u32()).map(BulkStateHandle::new)
    }
}
