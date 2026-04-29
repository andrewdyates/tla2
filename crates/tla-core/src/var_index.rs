// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Variable indexing for O(1) state access
//!
//! TLA+ specifications have a fixed set of variables. By assigning each
//! variable a numeric index at load time, we can use array-based lookups
//! instead of hash map lookups for O(1) state access.
//!
//! This is modeled after TLC's approach where each UniqueString gets an
//! index and state is represented as `Value[]` rather than `Map<String, Value>`.

use crate::name_intern::{intern_name, NameId};
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::sync::Arc;

/// A variable index for O(1) state access
///
/// Variables are numbered 0..n-1 where n is the number of variables in the spec.
/// This is a newtype wrapper around u16, supporting up to 65,536 variables.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VarIndex(pub u16);

impl VarIndex {
    /// Create a VarIndex from a usize with runtime bounds checking.
    ///
    /// Panics if `idx > u16::MAX` (65535). Use this constructor at all sites
    /// outside VarRegistry to ensure the u16 invariant is enforced in release builds.
    #[inline]
    pub fn new(idx: usize) -> Self {
        assert!(
            u16::try_from(idx).is_ok(),
            "VarIndex overflow: {idx} exceeds u16::MAX (65535)"
        );
        VarIndex(idx as u16)
    }

    /// Get the index as usize for array indexing
    #[inline(always)]
    pub fn as_usize(self) -> usize {
        self.0 as usize
    }
}

/// Internal storage for VarRegistry (wrapped in Arc for cheap cloning)
#[derive(Clone, Debug)]
struct VarRegistryInner {
    /// Variable names in index order (index -> name)
    names: Vec<Arc<str>>,
    /// Index lookup by name (name -> index)
    indices: HashMap<Arc<str>, VarIndex, FnvBuildHasher>,
    /// Index lookup by interned NameId (NameId -> index).
    /// Small vec (typically <20 state vars) searched linearly with u32 compare.
    /// Populated at registration time so the eval fast path can skip string hashing.
    name_id_indices: Vec<(NameId, VarIndex)>,
    /// NameId in index order (index -> NameId) for O(1) VarIndex → NameId validation.
    /// Part of #3063: enables integer comparison instead of string comparison in
    /// resolve_state_var_slot hot path.
    name_ids: Vec<NameId>,
    /// Pre-computed fingerprint salts for each variable (index -> salt)
    /// Used to avoid hashing variable names during state fingerprinting
    fp_salts: Vec<u64>,
}

/// Registry mapping variable names to indices
///
/// This is built once at module load time and shared across all evaluation
/// contexts. It provides O(1) lookup of variable indices by name.
///
/// Also pre-computes fingerprint "salts" for each variable to optimize
/// state fingerprinting (removes name hashing from hot path).
///
/// Cloning is O(1) - only increments an Arc reference count.
#[derive(Clone, Debug)]
pub struct VarRegistry {
    inner: Arc<VarRegistryInner>,
}

use crate::fnv::{FNV_OFFSET, FNV_PRIME};

/// Fast deterministic hasher for VarRegistry indices.
///
/// `std::collections::HashMap` defaults to SipHash, which is intentionally slow.
/// VarRegistry lookups are in a hot path (millions of lookups of a tiny set of keys),
/// so we use FNV-1a for much lower overhead on short variable names.
#[derive(Clone, Default)]
struct FnvHasher(u64);

impl Hasher for FnvHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut hash = if self.0 == 0 { FNV_OFFSET } else { self.0 };
        for &byte in bytes {
            hash ^= byte as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        self.0 = hash;
    }

    #[inline]
    fn finish(&self) -> u64 {
        if self.0 == 0 {
            FNV_OFFSET
        } else {
            self.0
        }
    }
}

type FnvBuildHasher = BuildHasherDefault<FnvHasher>;

/// Compute a fingerprint salt for a variable at a given index
/// This creates a unique "mixing value" for each variable position
fn compute_var_salt(idx: usize, name: &str) -> u64 {
    let mut hash = FNV_OFFSET;
    // Mix in the index (position matters)
    for byte in (idx as u64).to_le_bytes() {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    // Mix in the name (different names get different salts)
    for byte in name.bytes() {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    // Final mixing step
    hash ^= 0xFF;
    hash = hash.wrapping_mul(FNV_PRIME);
    hash
}

impl VarRegistry {
    /// Create a new empty registry
    pub fn new() -> Self {
        VarRegistry {
            inner: Arc::new(VarRegistryInner {
                names: Vec::new(),
                indices: HashMap::default(),
                name_id_indices: Vec::new(),
                name_ids: Vec::new(),
                fp_salts: Vec::new(),
            }),
        }
    }

    /// Create a registry from a list of variable names
    pub fn from_names<S: Into<Arc<str>>>(names: impl IntoIterator<Item = S>) -> Self {
        let mut inner = VarRegistryInner {
            names: Vec::new(),
            indices: HashMap::default(),
            name_id_indices: Vec::new(),
            name_ids: Vec::new(),
            fp_salts: Vec::new(),
        };
        for name in names {
            let name: Arc<str> = name.into();
            if inner.indices.contains_key(&name) {
                continue;
            }
            let idx_val = inner.names.len();
            assert!(
                u16::try_from(idx_val).is_ok(),
                "TLA+ spec exceeds VarIndex u16 limit ({} variables, max {})",
                idx_val + 1,
                u16::MAX as usize + 1
            );
            let idx = VarIndex(idx_val as u16);
            let salt = compute_var_salt(idx_val, &name);
            let nid = intern_name(&name);
            inner.fp_salts.push(salt);
            inner.name_id_indices.push((nid, idx));
            inner.name_ids.push(nid);
            inner.names.push(name.clone());
            inner.indices.insert(name, idx);
        }
        VarRegistry {
            inner: Arc::new(inner),
        }
    }

    /// Register a variable and get its index
    /// Returns existing index if already registered
    pub fn register<S: Into<Arc<str>>>(&mut self, name: S) -> VarIndex {
        let name: Arc<str> = name.into();
        if let Some(&idx) = self.inner.indices.get(&name) {
            return idx;
        }
        // Need to mutate - get mutable access to inner
        let inner = Arc::make_mut(&mut self.inner);
        let idx_val = inner.names.len();
        assert!(
            u16::try_from(idx_val).is_ok(),
            "TLA+ spec exceeds VarIndex u16 limit ({} variables, max {})",
            idx_val + 1,
            u16::MAX as usize + 1
        );
        let idx = VarIndex(idx_val as u16);
        // Pre-compute fingerprint salt for this variable
        let salt = compute_var_salt(idx_val, &name);
        let nid = intern_name(&name);
        inner.fp_salts.push(salt);
        inner.name_id_indices.push((nid, idx));
        inner.name_ids.push(nid);
        inner.names.push(name.clone());
        inner.indices.insert(name, idx);
        idx
    }

    /// Get the interned NameId for a variable by index (O(1)).
    /// Part of #3063: used in resolve_state_var_slot fast path for
    /// u32 comparison instead of string comparison.
    #[inline(always)]
    pub fn name_id_at(&self, idx: VarIndex) -> NameId {
        self.inner.name_ids[idx.as_usize()]
    }

    /// Get the pre-computed fingerprint salt for a variable index
    #[inline(always)]
    pub fn fp_salt(&self, idx: VarIndex) -> u64 {
        self.inner.fp_salts[idx.as_usize()]
    }

    /// Look up a variable index by name (O(1) hash lookup)
    #[inline]
    pub fn get(&self, name: &str) -> Option<VarIndex> {
        self.inner.indices.get(name).copied()
    }

    /// Look up a variable index by interned NameId.
    /// Linear scan over a small vec (typically <20 state vars) with u32 comparison.
    /// Avoids string hashing on the eval hot path when NameId is already available.
    #[inline]
    pub fn get_by_name_id(&self, id: NameId) -> Option<VarIndex> {
        for &(nid, idx) in &self.inner.name_id_indices {
            if nid == id {
                return Some(idx);
            }
        }
        None
    }

    /// Get a variable name by index (O(1))
    #[inline]
    pub fn name(&self, idx: VarIndex) -> &str {
        &self.inner.names[idx.as_usize()]
    }

    /// Get all variable names in index order
    pub fn names(&self) -> &[Arc<str>] {
        &self.inner.names
    }

    /// Number of registered variables
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.names.len()
    }

    /// Check if registry is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.names.is_empty()
    }

    /// Iterator over (index, name) pairs
    pub fn iter(&self) -> impl Iterator<Item = (VarIndex, &Arc<str>)> {
        self.inner
            .names
            .iter()
            .enumerate()
            .map(|(i, name)| (VarIndex::new(i), name))
    }
}

impl Default for VarRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_var_registry_basic() {
        let mut reg = VarRegistry::new();

        let idx_x = reg.register("x");
        let idx_y = reg.register("y");
        let idx_z = reg.register("z");

        assert_eq!(idx_x, VarIndex(0));
        assert_eq!(idx_y, VarIndex(1));
        assert_eq!(idx_z, VarIndex(2));

        assert_eq!(reg.get("x"), Some(VarIndex(0)));
        assert_eq!(reg.get("y"), Some(VarIndex(1)));
        assert_eq!(reg.get("z"), Some(VarIndex(2)));
        assert_eq!(reg.get("w"), None);

        assert_eq!(reg.name(VarIndex(0)), "x");
        assert_eq!(reg.name(VarIndex(1)), "y");
        assert_eq!(reg.name(VarIndex(2)), "z");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_var_registry_from_names() {
        let reg = VarRegistry::from_names(["x", "y", "z"]);

        assert_eq!(reg.len(), 3);
        assert_eq!(reg.get("x"), Some(VarIndex(0)));
        assert_eq!(reg.get("y"), Some(VarIndex(1)));
        assert_eq!(reg.get("z"), Some(VarIndex(2)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_var_registry_duplicate_registration() {
        let mut reg = VarRegistry::new();

        let idx1 = reg.register("x");
        let idx2 = reg.register("x"); // Same name

        // Should return the same index
        assert_eq!(idx1, idx2);
        assert_eq!(reg.len(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_var_registry_get_by_name_id() {
        let reg = VarRegistry::from_names(["pc", "num", "flag"]);

        let nid_pc = intern_name("pc");
        let nid_num = intern_name("num");
        let nid_flag = intern_name("flag");
        let nid_missing = intern_name("missing");

        assert_eq!(reg.get_by_name_id(nid_pc), Some(VarIndex(0)));
        assert_eq!(reg.get_by_name_id(nid_num), Some(VarIndex(1)));
        assert_eq!(reg.get_by_name_id(nid_flag), Some(VarIndex(2)));
        assert_eq!(reg.get_by_name_id(nid_missing), None);

        // Consistency: get_by_name_id matches get for all registered vars
        for (idx, name) in reg.iter() {
            let nid = intern_name(name);
            assert_eq!(reg.get_by_name_id(nid), Some(idx));
            assert_eq!(reg.get(name), Some(idx));
        }
    }

    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    #[should_panic(expected = "VarIndex u16 limit")]
    fn test_var_registry_register_overflow_panics() {
        let mut reg = VarRegistry::new();
        for i in 0..=(u16::MAX as usize) {
            reg.register(format!("v{i}"));
        }
        // 65536 variables registered (indices 0..65535). Next should panic.
        reg.register("overflow");
    }
}
