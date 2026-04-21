// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fingerprint cache and incremental fingerprint methods for `ArrayState`.

use tla_core::FNV_PRIME;

use crate::var_index::{VarIndex, VarRegistry};
use crate::Value;

use super::array_state::ArrayState;
use super::value_hash::{compact_value_fingerprint, finalize_fingerprint_xor, value_fingerprint};
use super::Fingerprint;

/// Internal fingerprint cache for ArrayState.
///
/// Stores the combined XOR value and final fingerprint, plus optional
/// per-variable cached value fingerprints for incremental updates.
/// Internal fingerprint cache for ArrayState.
///
/// `pub(crate)` visibility allows arena module to construct this when promoting
/// `ArenaArrayState` to heap-owned `ArrayState` (Part of #3990).
pub(crate) struct ArrayStateFpCache {
    /// XOR of salted contributions (pre-final-mix)
    pub(crate) combined_xor: u64,
    /// Final mixed fingerprint
    pub(crate) fingerprint: Fingerprint,
    /// Optional per-variable cached value fingerprints.
    ///
    /// When present, incremental fingerprint updates can avoid recomputing the
    /// old value's fingerprint on each update.
    ///
    /// This cache is intentionally dropped on `Clone` to avoid per-successor
    /// allocations in the BFS hot path. It can be rehydrated on demand via
    /// `ArrayState::ensure_fp_cache_with_value_fps`.
    pub(crate) value_fps: Option<Box<[u64]>>,
}

impl Clone for ArrayStateFpCache {
    fn clone(&self) -> Self {
        Self {
            combined_xor: self.combined_xor,
            fingerprint: self.fingerprint,
            value_fps: None,
        }
    }
}

impl ArrayState {
    /// Set a value by index, updating the cached fingerprint incrementally when available.
    ///
    /// If this ArrayState has a cached fingerprint (via a prior call to `fingerprint()`),
    /// we can update it in O(1) using XOR-delta updates instead of recomputing over all vars.
    ///
    /// If no fingerprint cache is present, this behaves like `set()` and leaves the cache empty.
    #[inline]
    pub fn set_with_registry(&mut self, idx: VarIndex, value: Value, registry: &VarRegistry) {
        let Some(cache) = self.fp_cache.as_mut() else {
            self.values[idx.as_usize()] = value.into();
            return;
        };

        debug_assert_eq!(registry.len(), self.values.len());

        let idx_usize = idx.as_usize();
        let new_fp = value_fingerprint(&value);
        let old_fp = cache.value_fps.as_ref().map_or_else(
            || compact_value_fingerprint(&self.values[idx_usize]),
            |fps| fps[idx_usize],
        );
        if old_fp != new_fp {
            let salt = registry.fp_salt(idx);
            let old_contrib = salt.wrapping_mul(old_fp.wrapping_add(1));
            let new_contrib = salt.wrapping_mul(new_fp.wrapping_add(1));
            cache.combined_xor ^= old_contrib ^ new_contrib;

            let mixed = finalize_fingerprint_xor(cache.combined_xor, FNV_PRIME);
            cache.fingerprint = Fingerprint(mixed);
            if let Some(fps) = cache.value_fps.as_mut() {
                fps[idx_usize] = new_fp;
            }
        }

        self.values[idx_usize] = value.into();
    }

    /// Set a value by index with a precomputed value fingerprint.
    ///
    /// This is a specialization for hot-path enumeration that avoids recomputing
    /// `value_fingerprint()` when the caller already has it.
    #[inline]
    pub fn set_with_fp(
        &mut self,
        idx: VarIndex,
        value: Value,
        value_fp: u64,
        registry: &VarRegistry,
    ) {
        let Some(cache) = self.fp_cache.as_mut() else {
            self.values[idx.as_usize()] = value.into();
            return;
        };

        debug_assert_eq!(registry.len(), self.values.len());

        let idx_usize = idx.as_usize();
        let old_fp = cache.value_fps.as_ref().map_or_else(
            || compact_value_fingerprint(&self.values[idx_usize]),
            |fps| fps[idx_usize],
        );
        if old_fp != value_fp {
            let salt = registry.fp_salt(idx);
            let old_contrib = salt.wrapping_mul(old_fp.wrapping_add(1));
            let new_contrib = salt.wrapping_mul(value_fp.wrapping_add(1));
            cache.combined_xor ^= old_contrib ^ new_contrib;

            let mixed = finalize_fingerprint_xor(cache.combined_xor, FNV_PRIME);
            cache.fingerprint = Fingerprint(mixed);
            if let Some(fps) = cache.value_fps.as_mut() {
                fps[idx_usize] = value_fp;
            }
        }

        self.values[idx_usize] = value.into();
    }

    /// Compute and cache the fingerprint, including per-variable fingerprints.
    ///
    /// Part of #1150: Store per-variable fingerprints during initial computation
    /// so that `enumerate_successors_split_actions` can use the current state
    /// directly as the base for diff fingerprinting, avoiding a full state clone.
    /// The extra cost is one Vec<u64> allocation (~80 bytes for 10 vars) per state,
    /// saving a Box<[CompactValue]> clone per state in the BFS hot path.
    pub fn fingerprint(&mut self, registry: &VarRegistry) -> Fingerprint {
        if let Some(cache) = &self.fp_cache {
            return cache.fingerprint;
        }

        let mut combined_xor = 0u64;
        let mut value_fps: Vec<u64> = Vec::with_capacity(self.values.len());

        for (i, cv) in self.values.iter().enumerate() {
            let vfp = compact_value_fingerprint(cv);
            value_fps.push(vfp);
            let salt = registry.fp_salt(VarIndex::new(i));
            let contribution = salt.wrapping_mul(vfp.wrapping_add(1));
            combined_xor ^= contribution;
        }

        let mixed = finalize_fingerprint_xor(combined_xor, FNV_PRIME);
        let fp = Fingerprint(mixed);

        self.fp_cache = Some(ArrayStateFpCache {
            combined_xor,
            fingerprint: fp,
            value_fps: Some(value_fps.into_boxed_slice()),
        });

        fp
    }

    /// Ensure the fingerprint cache includes per-variable value fingerprints.
    ///
    /// This supports fast incremental updates via `set_with_registry`/`set_with_fp` without
    /// recomputing old-value fingerprints on every update.
    pub fn ensure_fp_cache_with_value_fps(&mut self, registry: &VarRegistry) {
        if self.fp_cache.is_none() {
            // Compute fingerprint + value_fps together in one pass.
            let mut combined_xor = 0u64;
            let mut value_fps: Vec<u64> = Vec::with_capacity(self.values.len());

            for (i, cv) in self.values.iter().enumerate() {
                let vfp = compact_value_fingerprint(cv);
                value_fps.push(vfp);
                let salt = registry.fp_salt(VarIndex::new(i));
                let contribution = salt.wrapping_mul(vfp.wrapping_add(1));
                combined_xor ^= contribution;
            }

            let mixed = finalize_fingerprint_xor(combined_xor, FNV_PRIME);
            let fp = Fingerprint(mixed);

            self.fp_cache = Some(ArrayStateFpCache {
                combined_xor,
                fingerprint: fp,
                value_fps: Some(value_fps.into_boxed_slice()),
            });
            return;
        }

        let Some(cache) = self.fp_cache.as_mut() else {
            return;
        };
        if cache.value_fps.is_some() {
            return;
        }

        // CRITICAL FIX (#132): Must recompute combined_xor alongside value_fps.
        let mut combined_xor = 0u64;
        let mut value_fps: Vec<u64> = Vec::with_capacity(self.values.len());
        for (i, cv) in self.values.iter().enumerate() {
            let vfp = compact_value_fingerprint(cv);
            value_fps.push(vfp);
            let salt = registry.fp_salt(VarIndex::new(i));
            let contribution = salt.wrapping_mul(vfp.wrapping_add(1));
            combined_xor ^= contribution;
        }

        cache.combined_xor = combined_xor;
        cache.value_fps = Some(value_fps.into_boxed_slice());
    }

    /// Get cached fingerprint if available
    #[inline]
    pub fn cached_fingerprint(&self) -> Option<Fingerprint> {
        self.fp_cache.as_ref().map(|c| c.fingerprint)
    }

    /// Get cached per-variable fingerprints if available.
    ///
    /// Returns the per-variable `value_fingerprint` values that were computed
    /// during the last `fingerprint()` or `ensure_fp_cache_with_value_fps()` call.
    /// Returns `None` if the cache is not populated or does not include per-var fps.
    ///
    /// Part of #4032: Used by `fingerprint_jit_flat_successor` to avoid
    /// recomputing `compact_value_fingerprint` for unchanged compound variables.
    #[inline]
    pub fn cached_value_fps(&self) -> Option<&[u64]> {
        self.fp_cache
            .as_ref()
            .and_then(|c| c.value_fps.as_deref())
    }

    /// Override the cached fingerprint value.
    ///
    /// Part of #3011: When symmetry is active, the canonical (minimum across
    /// all permutations) fingerprint must be stored so that subsequent
    /// `fingerprint()` calls return the canonical value. This ensures
    /// parent fingerprints are consistent with successor fingerprints
    /// throughout the BFS.
    #[inline]
    pub fn set_cached_fingerprint(&mut self, fp: Fingerprint) {
        if let Some(cache) = &mut self.fp_cache {
            cache.fingerprint = fp;
        } else {
            self.fp_cache = Some(ArrayStateFpCache {
                combined_xor: 0,
                fingerprint: fp,
                value_fps: None,
            });
        }
    }

    /// Set cached fingerprint along with the pre-finalization `combined_xor`.
    ///
    /// This allows the state to participate in incremental fingerprinting
    /// when it later becomes a parent in the BFS. Without `combined_xor`,
    /// the incremental path falls back to the full O(n) scan.
    ///
    /// Part of #4030: Propagate combined_xor through JIT fused path.
    #[inline]
    pub fn set_cached_fingerprint_with_xor(&mut self, fp: Fingerprint, combined_xor: u64) {
        if let Some(cache) = &mut self.fp_cache {
            cache.fingerprint = fp;
            cache.combined_xor = combined_xor;
        } else {
            self.fp_cache = Some(ArrayStateFpCache {
                combined_xor,
                fingerprint: fp,
                value_fps: None,
            });
        }
    }

    /// Check if fp_cache includes per-variable fingerprints (complete cache).
    ///
    /// Part of #1150: When true, this state can be used directly as the base
    /// for diff fingerprint computation without cloning.
    #[inline]
    pub fn has_complete_fp_cache(&self) -> bool {
        self.fp_cache
            .as_ref()
            .is_some_and(|c| c.value_fps.is_some())
    }
}
