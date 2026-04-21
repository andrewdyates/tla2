// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State-to-ArrayState conversion constructors.
//!
//! These methods create `ArrayState` from `State` or successor `State` values,
//! computing fingerprints using the registry-based algorithm.

use tla_core::FNV_PRIME;
use tla_value::CompactValue;

use crate::var_index::{VarIndex, VarRegistry};
use crate::Value;

use super::array_state::ArrayState;
use super::array_state_fingerprint::ArrayStateFpCache;
use super::value_hash::{
    combined_xor_from_array, combined_xor_from_compact_array, finalize_fingerprint_xor,
    value_fingerprint,
};
use super::{Fingerprint, State};

impl ArrayState {
    /// Create an ArrayState from a State using the given registry
    ///
    /// NOTE: Does NOT copy the State's fingerprint because ArrayState uses
    /// a different fingerprinting algorithm optimized for array-based states.
    /// The fingerprint will be computed on demand using `fingerprint(&registry)`.
    pub fn from_state(state: &State, registry: &VarRegistry) -> Self {
        #[cfg(feature = "memory-stats")]
        {
            crate::value::memory_stats::inc_array_state();
            crate::value::memory_stats::inc_array_state_bytes(registry.len());
        }

        let false_cv = CompactValue::from(false);
        let mut values: Vec<CompactValue> = vec![false_cv; registry.len()];
        let mut assigned = 0usize;
        for (name, value) in state.vars() {
            if let Some(idx) = registry.get(name) {
                values[idx.as_usize()] = CompactValue::from(value.clone());
                assigned += 1;
            }
        }
        assert_eq!(
            assigned,
            registry.len(),
            "ArrayState::from_state: state has {} of {} expected registry variables",
            assigned,
            registry.len()
        );
        ArrayState {
            values: values.into_boxed_slice(),
            fp_cache: None, // Will be computed on demand
        }
    }

    /// Create an ArrayState from a State with pre-computed fingerprint.
    ///
    /// This computes the fingerprint using ArrayState's algorithm (registry-based
    /// indices) to ensure consistency across all ArrayState fingerprints.
    ///
    /// IMPORTANT (#158): Cannot copy State's fingerprint because State uses
    /// alphabetical order (OrdMap iteration) while ArrayState uses registry
    /// index order. This caused liveness checking false positives.
    ///
    /// Part of #131: Close 5x performance gap vs TLC
    pub fn from_state_with_fp(state: &State, registry: &VarRegistry) -> Self {
        #[cfg(feature = "memory-stats")]
        {
            crate::value::memory_stats::inc_array_state();
            crate::value::memory_stats::inc_array_state_bytes(registry.len());
        }

        // Build Value vec first for fingerprinting, then convert to CompactValue
        let mut value_vec: Vec<Value> = vec![Value::Bool(false); registry.len()];
        let mut assigned = 0usize;
        for (name, value) in state.vars() {
            if let Some(idx) = registry.get(name) {
                value_vec[idx.as_usize()] = value.clone();
                assigned += 1;
            }
        }
        assert_eq!(
            assigned,
            registry.len(),
            "ArrayState::from_state_with_fp: state has {} of {} expected registry variables",
            assigned,
            registry.len()
        );

        // Compute combined_xor and derive fingerprint from Value slice.
        let combined_xor = combined_xor_from_array(&value_vec, registry);
        let fp = Fingerprint(finalize_fingerprint_xor(combined_xor, FNV_PRIME));

        // Convert to compact storage
        let compact: Vec<CompactValue> = value_vec.into_iter().map(CompactValue::from).collect();

        ArrayState {
            values: compact.into_boxed_slice(),
            fp_cache: Some(ArrayStateFpCache {
                combined_xor,
                fingerprint: fp,
                value_fps: None,
            }),
        }
    }

    /// Create an ArrayState from a successor State with incremental fingerprinting.
    ///
    /// This is an optimization for successor generation: instead of computing the
    /// fingerprint from scratch (O(n) where n = number of variables), we compute it
    /// incrementally from the base state's fingerprint by XORing out old contributions
    /// and XORing in new contributions for changed variables only.
    ///
    /// This provides significant speedup when most variables are unchanged between
    /// the base state and successor (the common case in model checking).
    ///
    /// Part of #131: Close 5x performance gap vs TLC (non-enumeration bottlenecks)
    pub fn from_successor_state(
        successor_state: &State,
        base_array: &ArrayState,
        registry: &VarRegistry,
    ) -> Self {
        #[cfg(feature = "memory-stats")]
        {
            crate::value::memory_stats::inc_array_state();
            crate::value::memory_stats::inc_array_state_bytes(registry.len());
        }

        // Build successor values array (as Value for fingerprinting)
        let mut value_vec: Vec<Value> = vec![Value::Bool(false); registry.len()];
        let mut assigned = 0usize;
        for (name, value) in successor_state.vars() {
            if let Some(idx) = registry.get(name) {
                value_vec[idx.as_usize()] = value.clone();
                assigned += 1;
            }
        }
        assert_eq!(
            assigned,
            registry.len(),
            "ArrayState::from_successor_state: state has {} of {} expected registry variables",
            assigned,
            registry.len()
        );

        // Get base state's combined_xor for incremental computation
        let base_combined_xor = match &base_array.fp_cache {
            Some(cache) => cache.combined_xor,
            None => combined_xor_from_compact_array(&base_array.values, registry),
        };

        // Compute fingerprint incrementally by finding changed variables
        let mut combined_xor = base_combined_xor;
        for (i, new_val) in value_vec.iter().enumerate() {
            let old_val = Value::from(&base_array.values[i]);
            if new_val != &old_val {
                let new_fp = value_fingerprint(new_val);
                let old_fp = value_fingerprint(&old_val);

                let idx = VarIndex::new(i);
                let salt = registry.fp_salt(idx);
                let old_contrib = salt.wrapping_mul(old_fp.wrapping_add(1));
                let new_contrib = salt.wrapping_mul(new_fp.wrapping_add(1));
                combined_xor ^= old_contrib ^ new_contrib;
            }
        }

        let fp = Fingerprint(finalize_fingerprint_xor(combined_xor, FNV_PRIME));

        // Convert to compact storage
        let compact: Vec<CompactValue> = value_vec.into_iter().map(CompactValue::from).collect();

        ArrayState {
            values: compact.into_boxed_slice(),
            fp_cache: Some(ArrayStateFpCache {
                combined_xor,
                fingerprint: fp,
                value_fps: None,
            }),
        }
    }
}
