// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani-compatible type aliases for HashMap and HashSet (z4-sat local).
//!
//! Under `#[cfg(kani)]`, uses `BTreeMap`/`BTreeSet` to avoid CBMC-intractable
//! `hashbrown::RawTable` operations. Under normal builds, uses standard
//! `HashMap`/`HashSet` (with `std::collections` which delegates to hashbrown).
//!
//! See also: `z4_core::kani_compat` for the shared cross-crate version.
//! This module maintains backward compatibility for z4-sat internal code
//! that imports from `crate::kani_compat`.

// ── cfg(kani): BTreeMap/BTreeSet ──────────────────────────────────────────────

#[cfg(kani)]
pub(crate) type DetHashMap<K, V> = std::collections::BTreeMap<K, V>;
#[cfg(kani)]
pub(crate) type DetHashSet<T> = std::collections::BTreeSet<T>;

// ── cfg(not(kani)): std collections ───────────────────────────────────────────

#[cfg(not(kani))]
pub(crate) type DetHashMap<K, V> = std::collections::HashMap<K, V>;
#[cfg(not(kani))]
pub(crate) type DetHashSet<T> = std::collections::HashSet<T>;

// ── Constructor helpers ───────────────────────────────────────────────────────

/// Create an empty `DetHashSet`.
///
/// Under Kani, `HashSet::new()` may be unavailable for custom hashers.
/// `Default::default()` works for all backends.
#[inline]
pub(crate) fn det_hash_set_new<T>() -> DetHashSet<T>
where
    T: Ord,
{
    Default::default()
}

/// Create a `DetHashSet` with pre-allocated capacity.
#[inline]
pub(crate) fn det_hash_set_with_capacity<T>(capacity: usize) -> DetHashSet<T>
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
        std::collections::HashSet::with_capacity(capacity)
    }
}
