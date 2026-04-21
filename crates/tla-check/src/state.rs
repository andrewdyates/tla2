// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLA+ State representation
//!
//! A state in TLA+ is a mapping from variable names to values. States are:
//! - Immutable: Transitions create new states rather than mutating existing ones
//! - Hashable: For efficient state-space exploration (detecting duplicates)
//! - Comparable: For deterministic ordering
//!
//! # Fingerprinting
//!
//! States are identified by a 64-bit fingerprint computed via FNV-1a hash.
//! This matches TLC's approach (though TLC uses 64-bit fingerprints too).
//! Collision probability is acceptable for model checking purposes.

mod array_state;
mod array_state_bind;
mod array_state_convert;
mod array_state_fingerprint;
pub(crate) mod atomic_fp_set;
mod diff_successor;
// JIT V2 flat state pipeline — wiring into production BFS as Tier 0 interpreter adapter (#4126)
mod flat_bfs_adapter;
mod flat_bfs_bridge;
pub mod flat_fingerprint;
mod flat_state;
#[allow(dead_code)]
mod flat_state_store;
#[allow(dead_code)]
mod flat_successor;
// GPU batch fingerprinting — scaffolding for large-frontier acceleration (#3956)
#[allow(dead_code)]
pub(crate) mod gpu_fingerprint;
mod layout_inference;
#[cfg(feature = "jit")]
pub(crate) mod layout_bridge;
mod state_layout;
mod symmetry;
mod value_hash;
mod value_hash_additive;
mod value_hash_alt;
mod value_hash_fnv;
mod value_hash_state;
pub(crate) mod worker_value_hash;

// Re-export submodule public items
pub use array_state::{ArrayState, UndoEntry};
/// Part of #3990: Re-export for arena promotion path.
pub(crate) use array_state_fingerprint::ArrayStateFpCache;
#[allow(unused_imports)]
pub(crate) use diff_successor::compute_diff_fingerprint_with_change_fps;
pub(crate) use diff_successor::{compute_diff_fingerprint_with_xor, DiffChanges, DiffSuccessor};
// JIT V2 flat state re-exports — Tier 0 interpreter adapter wired (#4126)
pub(crate) use flat_bfs_adapter::FlatBfsAdapter;
pub(crate) use flat_bfs_bridge::FlatBfsBridge;
pub(crate) use flat_state::FlatState;
#[allow(unused_imports)]
pub(crate) use flat_state_store::FlatStateStore;
#[allow(unused_imports)]
pub(crate) use flat_successor::{flat_state_bytes, FlatSuccessor, FlatSuccessorWriter};
pub(crate) use layout_inference::{infer_layout, infer_layout_from_wavefront};
#[cfg(feature = "jit")]
pub(crate) use layout_bridge::{check_layout_to_jit_layout, jit_layout_to_check_layout, layouts_compatible};
pub(crate) use state_layout::StateLayout;
#[allow(unused_imports)]
pub(crate) use state_layout::VarLayoutKind;
pub(crate) use symmetry::print_symmetry_stats;
pub use value_hash::value_fingerprint;
pub(crate) use value_hash::{
    compute_canonical_fingerprint_from_compact_array, compute_fingerprint_from_array,
    compute_fingerprint_from_compact_array, finalize_fingerprint_xor, states_to_trace_value,
};
pub(crate) use value_hash_additive::{additive_entry_hash, splitmix64, ADDITIVE_FUNC_SEED};
pub use value_hash_alt::{value_fingerprint_ahash, value_fingerprint_xxh3};
pub(crate) use value_hash_state::compact_value_fingerprint;
#[cfg(test)]
pub(crate) use value_hash_state::compute_canonical_fingerprint_from_array;

use crate::value::RecordBuilder;
use crate::var_index::VarRegistry;
use crate::Value;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, OnceLock};
use tla_core::kani_types::OrdMap;

use value_hash::compute_fingerprint;

/// A 64-bit state fingerprint for fast state comparison
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Fingerprint(pub u64);

/// Identity hasher for `Fingerprint` values.
///
/// Fingerprints are already high-quality 64-bit hashes (FP64 polynomial or
/// additive splitmix64). Running them through FxHash's Fibonacci multiplication
/// is pure overhead and degrades hash table distribution at scale (MCBoulanger
/// regression: 244s -> 369s with FxHash, 51% slower at 7.87M entries).
///
/// Part of #4128: Fix MCBoulanger 51% performance regression from FxHash.
#[derive(Default, Clone)]
pub struct FingerprintHasher(u64);

impl std::hash::Hasher for FingerprintHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }

    #[inline]
    fn write(&mut self, _bytes: &[u8]) {
        unreachable!("FingerprintHasher expects write_u64 only");
    }

    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.0 = i;
    }
}

/// BuildHasher for `FingerprintHasher`.
#[derive(Default, Clone)]
pub struct BuildFingerprintHasher;

impl std::hash::BuildHasher for BuildFingerprintHasher {
    type Hasher = FingerprintHasher;

    #[inline]
    fn build_hasher(&self) -> FingerprintHasher {
        FingerprintHasher(0)
    }
}

/// HashMap optimized for `Fingerprint` keys (identity hashing).
pub type FpHashMap<V> = std::collections::HashMap<Fingerprint, V, BuildFingerprintHasher>;

/// HashSet optimized for `Fingerprint` values (identity hashing).
pub type FpHashSet = std::collections::HashSet<Fingerprint, BuildFingerprintHasher>;

/// Create an empty `FpHashMap` with default capacity.
#[inline]
pub fn fp_hashmap<V>() -> FpHashMap<V> {
    std::collections::HashMap::with_hasher(BuildFingerprintHasher)
}

/// Create an `FpHashMap` with pre-allocated capacity.
#[inline]
pub fn fp_hashmap_with_capacity<V>(capacity: usize) -> FpHashMap<V> {
    std::collections::HashMap::with_capacity_and_hasher(capacity, BuildFingerprintHasher)
}

/// Create an empty `FpHashSet`.
#[inline]
pub fn fp_hashset() -> FpHashSet {
    std::collections::HashSet::with_hasher(BuildFingerprintHasher)
}

/// Create an `FpHashSet` with pre-allocated capacity.
#[inline]
pub fn fp_hashset_with_capacity(capacity: usize) -> FpHashSet {
    std::collections::HashSet::with_capacity_and_hasher(capacity, BuildFingerprintHasher)
}

impl fmt::Debug for Fingerprint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FP({:016x})", self.0)
    }
}

impl fmt::Display for Fingerprint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:016x}", self.0)
    }
}

/// A TLA+ state: a mapping from variable names to values
///
/// States are the nodes in the state graph explored by the model checker.
/// Each state represents a possible configuration of the system.
pub struct State {
    /// Variable bindings
    pub(super) vars: OrdMap<Arc<str>, Value>,
    /// Cached fingerprint (computed at construction time)
    fingerprint: Fingerprint,
    /// Cached canonical (symmetry-reduced) fingerprint, populated lazily
    /// Using OnceLock for thread-safe lazy initialization
    pub(super) canonical_fingerprint: OnceLock<Fingerprint>,
}

impl Clone for State {
    fn clone(&self) -> Self {
        State {
            vars: self.vars.clone(),
            fingerprint: self.fingerprint,
            // Clone the cached canonical fingerprint if available
            canonical_fingerprint: self
                .canonical_fingerprint
                .get()
                .map(|fp| {
                    let lock = OnceLock::new();
                    let _ = lock.set(*fp);
                    lock
                })
                .unwrap_or_default(),
        }
    }
}

impl State {
    /// Create an empty state
    pub fn new() -> Self {
        let vars = OrdMap::new();
        let fingerprint = compute_fingerprint(&vars);
        State {
            vars,
            fingerprint,
            canonical_fingerprint: OnceLock::new(),
        }
    }

    /// Create a state from a map of variables
    pub fn from_vars(vars: OrdMap<Arc<str>, Value>) -> Self {
        let fingerprint = compute_fingerprint(&vars);
        State {
            vars,
            fingerprint,
            canonical_fingerprint: OnceLock::new(),
        }
    }

    /// Create a state from an iterator of (name, value) pairs
    pub fn from_pairs(iter: impl IntoIterator<Item = (impl Into<Arc<str>>, Value)>) -> Self {
        let vars: OrdMap<Arc<str>, Value> = iter.into_iter().map(|(k, v)| (k.into(), v)).collect();
        State::from_vars(vars)
    }

    /// Create a state from an array of values indexed by variable index
    ///
    /// This is faster than `from_pairs` when you have pre-sorted values
    /// matching the VarRegistry order. Uses ArrayState internally for
    /// efficient fingerprint computation.
    ///
    /// # Arguments
    /// * `values` - Values in VarRegistry index order
    /// * `registry` - The variable registry mapping indices to names
    pub fn from_indexed(values: &[Value], registry: &VarRegistry) -> Self {
        // Build OrdMap from values in index order
        let vars: OrdMap<Arc<str>, Value> = registry
            .iter()
            .map(|(idx, name)| (Arc::clone(name), values[idx.as_usize()].clone()))
            .collect();

        // Compute fingerprint using the fast array-based method
        let fingerprint = compute_fingerprint_from_array(values, registry);

        State {
            vars,
            fingerprint,
            canonical_fingerprint: OnceLock::new(),
        }
    }

    /// Create a state from an ArrayState
    pub fn from_array_state(array_state: &mut ArrayState, registry: &VarRegistry) -> Self {
        let vars: OrdMap<Arc<str>, Value> = registry
            .iter()
            .map(|(idx, name)| {
                (
                    Arc::clone(name),
                    Value::from(&array_state.values()[idx.as_usize()]),
                )
            })
            .collect();

        // Get or compute fingerprint
        let fingerprint = array_state.fingerprint(registry);

        State {
            vars,
            fingerprint,
            canonical_fingerprint: OnceLock::new(),
        }
    }

    /// Get a variable's value
    pub fn get(&self, name: &str) -> Option<&Value> {
        self.vars.get(name)
    }

    /// Set a variable's value, returning a new state
    pub fn with_var(&self, name: impl Into<Arc<str>>, value: Value) -> State {
        let mut new_vars = self.vars.clone();
        new_vars.insert(name.into(), value);
        State::from_vars(new_vars)
    }

    /// Update multiple variables at once
    pub fn with_vars(
        &self,
        updates: impl IntoIterator<Item = (impl Into<Arc<str>>, Value)>,
    ) -> State {
        let mut new_vars = self.vars.clone();
        for (name, value) in updates {
            new_vars.insert(name.into(), value);
        }
        State::from_vars(new_vars)
    }

    /// Get all variable names
    pub fn var_names(&self) -> impl Iterator<Item = &Arc<str>> {
        self.vars.keys()
    }

    /// Get all variables as (name, value) pairs
    pub fn vars(&self) -> impl Iterator<Item = (&Arc<str>, &Value)> {
        self.vars.iter()
    }

    /// Number of variables
    pub fn len(&self) -> usize {
        self.vars.len()
    }

    /// Check if state has no variables
    pub fn is_empty(&self) -> bool {
        self.vars.is_empty()
    }

    /// Convert state variables to an array indexed by VarRegistry indices.
    ///
    /// This enables efficient array-based state variable binding via `EvalCtx::bind_state_array`,
    /// avoiding HashMap lookups during evaluation. Used by liveness checking.
    ///
    /// # Panics
    ///
    /// Panics if a variable in the registry is not present in the state. This matches
    /// the assertion in `ArrayState::from_state` — a missing variable indicates a
    /// programming invariant violation (state/registry mismatch), not a user spec error.
    /// Fix for #1773: previously defaulted missing vars to Bool(false), silently
    /// corrupting liveness evaluation.
    pub fn to_values(&self, registry: &VarRegistry) -> Box<[Value]> {
        let mut values = Vec::with_capacity(registry.len());
        for (_idx, name) in registry.iter() {
            values.push(self.vars.get(name).cloned().unwrap_or_else(|| {
                panic!(
                    "State::to_values: variable '{}' not found in state \
                             (state has {} vars, registry has {})",
                    name,
                    self.vars.len(),
                    registry.len()
                )
            }));
        }
        values.into_boxed_slice()
    }

    /// Convert state to a TLA+ record value.
    ///
    /// Part of #1117: Used by TLCExt!Trace to convert states to records.
    /// Each state becomes a record with field names matching variable names.
    pub fn to_record(&self) -> Value {
        let mut builder = RecordBuilder::new();
        for (name, value) in &self.vars {
            builder.insert(tla_core::intern_name(name), value.clone());
        }
        Value::Record(builder.build())
    }

    /// Compute the fingerprint of this state
    ///
    /// Uses FNV-1a hash for fast fingerprinting. The fingerprint is
    /// deterministic across runs (depends only on var names and values).
    pub fn fingerprint(&self) -> Fingerprint {
        self.fingerprint
    }
}

impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "State{{")?;
        let mut first = true;
        for (name, value) in &self.vars {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "{}: {:?}", name, value)?;
        }
        write!(f, "}}")
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "/\\ state")?;
        for (name, value) in &self.vars {
            writeln!(f, "   /\\ {} = {}", name, value)?;
        }
        Ok(())
    }
}

impl PartialEq for State {
    fn eq(&self, other: &Self) -> bool {
        self.vars == other.vars
    }
}

impl Eq for State {}

impl Hash for State {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.fingerprint().0.hash(state);
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        // Compare by fingerprint for speed; fall back to full comparison
        let fp_cmp = self.fingerprint().cmp(&other.fingerprint());
        if fp_cmp != Ordering::Equal {
            return fp_cmp;
        }
        // Same fingerprint - compare content (rare, only on collision)
        self.vars.cmp(&other.vars)
    }
}

#[cfg(test)]
mod tests;
