// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani-compatible type aliases for HashMap and HashSet.
//!
//! Under `#[cfg(kani)]`, CBMC cannot handle `hashbrown::RawTable` operations
//! (SIMD, pointer arithmetic, `getrandom`). This module provides alternatives:
//!
//! - **Kani builds**: `BTreeMap`/`BTreeSet` — no unsafe, fully CBMC-compatible.
//!   Keys must implement `Ord` (all z4 key types do).
//! - **Normal builds**: `hashbrown::HashMap`/`HashSet` — full performance.
//!
//! This unblocks 39+ Kani harnesses that were previously intractable due to
//! hashbrown internals. See z4 #5979.
//!
//! # Usage
//!
//! ```rust
//! use z4_core::kani_compat::{DetHashMap, DetHashSet, det_hash_map_new, det_hash_set_new};
//!
//! let mut map: DetHashMap<u32, u32> = det_hash_map_new();
//! map.insert(1, 2);
//!
//! let mut set: DetHashSet<u32> = det_hash_set_new();
//! set.insert(1);
//!
//! assert_eq!(map.get(&1), Some(&2));
//! assert!(set.contains(&1));
//! ```

// ── cfg(kani): BTreeMap/BTreeSet ──────────────────────────────────────────────

#[cfg(kani)]
/// Kani-compatible map type (BTreeMap under CBMC, hashbrown::HashMap otherwise).
pub type DetHashMap<K, V> = std::collections::BTreeMap<K, V>;

#[cfg(kani)]
/// Kani-compatible set type (BTreeSet under CBMC, hashbrown::HashSet otherwise).
pub type DetHashSet<T> = std::collections::BTreeSet<T>;

// ── cfg(not(kani)): hashbrown ─────────────────────────────────────────────────

#[cfg(not(kani))]
/// Kani-compatible map type (BTreeMap under CBMC, hashbrown::HashMap otherwise).
pub type DetHashMap<K, V> = hashbrown::HashMap<K, V>;

#[cfg(not(kani))]
/// Kani-compatible set type (BTreeSet under CBMC, hashbrown::HashSet otherwise).
pub type DetHashSet<T> = hashbrown::HashSet<T>;

// ── Legacy aliases (origin/main naming) ───────────────────────────────────────

/// Alias for `DetHashMap` — matches the `KaniHashMap` naming from z4-core's
/// initial kani_compat module.
pub type KaniHashMap<K, V> = DetHashMap<K, V>;

/// Alias for `DetHashSet` — matches the `KaniHashSet` naming from z4-core's
/// initial kani_compat module.
pub type KaniHashSet<T> = DetHashSet<T>;

// ── Constructor helpers (API compatibility) ───────────────────────────────────

/// Create an empty `DetHashMap`.
#[inline]
pub fn det_hash_map_new<K, V>() -> DetHashMap<K, V>
where
    K: Ord,
{
    Default::default()
}

/// Create a `DetHashMap` with pre-allocated capacity.
///
/// Under Kani (BTreeMap), capacity is ignored since BTreeMap does not
/// pre-allocate. Under normal builds, uses hashbrown's `with_capacity`.
#[inline]
pub fn det_hash_map_with_capacity<K, V>(capacity: usize) -> DetHashMap<K, V>
where
    K: Ord + std::hash::Hash + Eq,
{
    #[cfg(kani)]
    {
        let _ = capacity;
        std::collections::BTreeMap::new()
    }
    #[cfg(not(kani))]
    {
        hashbrown::HashMap::with_capacity(capacity)
    }
}

/// Create an empty `DetHashSet`.
#[inline]
pub fn det_hash_set_new<T>() -> DetHashSet<T>
where
    T: Ord,
{
    Default::default()
}

/// Create a `DetHashSet` with pre-allocated capacity.
///
/// Under Kani (BTreeSet), capacity is ignored. Under normal builds,
/// uses hashbrown's `with_capacity`.
#[inline]
pub fn det_hash_set_with_capacity<T>(capacity: usize) -> DetHashSet<T>
where
    T: Ord + std::hash::Hash + Eq,
{
    #[cfg(kani)]
    {
        let _ = capacity;
        std::collections::BTreeSet::new()
    }
    #[cfg(not(kani))]
    {
        hashbrown::HashSet::with_capacity(capacity)
    }
}
