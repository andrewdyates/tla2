// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compact diff-based successor state representation.
//!
//! `DiffSuccessor` avoids cloning the entire `ArrayState` during enumeration.
//! Only the changed values and result fingerprint are stored. The full state
//! can be materialized later (only for unique states, typically ~5% of successors).

use smallvec::SmallVec;
use tla_core::FNV_PRIME;
use tla_value::CompactValue;

use crate::var_index::{VarIndex, VarRegistry};
use crate::Value;

use super::array_state::ArrayState;
use super::array_state_fingerprint::ArrayStateFpCache;
use super::value_hash::{compact_value_fingerprint, finalize_fingerprint_xor, value_fingerprint};
use super::Fingerprint;

/// Inline capacity for DiffSuccessor changes.
/// Most TLA+ actions change 1-4 variables. This avoids heap allocation
/// for the common case, reducing allocator pressure in the hot path.
pub const DIFF_INLINE_CAPACITY: usize = 4;

/// Type alias for the changes storage in DiffSuccessor.
/// Uses SmallVec to store up to 4 changes inline (no heap allocation).
pub type DiffChanges = SmallVec<[(VarIndex, Value); DIFF_INLINE_CAPACITY]>;

/// A compact representation of a successor state as a diff from a base state.
///
/// This avoids cloning the entire ArrayState during enumeration. Only the
/// changed values and the result fingerprint are stored. The full ArrayState
/// can be materialized later (only for unique states, ~5% of successors).
///
/// # Performance
///
/// For specs with high duplicate rates (95%+), this can dramatically reduce
/// the number of Value clones:
/// - Before: Clone N values per successor (for dedup check AND queueing)
/// - After: Clone N values only for unique successors (~5%)
///
/// Uses SmallVec to store changes inline (up to 4 changes) to avoid heap
/// allocation for most successors, reducing allocator pressure.
#[derive(Clone)]
pub struct DiffSuccessor {
    /// Fingerprint of the result state
    pub fingerprint: Fingerprint,
    /// Changes from base state: (VarIndex, new_value)
    /// Uses SmallVec to avoid heap allocation for small change sets.
    pub changes: DiffChanges,
}

impl DiffSuccessor {
    /// Create a new DiffSuccessor with the given fingerprint and changes (SmallVec).
    /// This is the preferred constructor when building changes incrementally.
    #[inline]
    pub fn from_smallvec(fingerprint: Fingerprint, changes: DiffChanges) -> Self {
        Self {
            fingerprint,
            changes,
        }
    }

    /// Create a new DiffSuccessor from changes only, without pre-computing fingerprint.
    ///
    /// Part of #228: Deferred fingerprinting optimization. The fingerprint will be
    /// computed later in the BFS worker, after enumeration is complete. This avoids
    /// fingerprinting during enumeration (which was the main performance bottleneck).
    ///
    /// The fingerprint field is set to Fingerprint(0) as a placeholder - callers
    /// should compute the actual fingerprint before use.
    #[inline]
    pub fn from_changes(changes: DiffChanges) -> Self {
        Self {
            fingerprint: Fingerprint(0),
            changes,
        }
    }

    /// Materialize this diff into a full ArrayState by applying changes to the base.
    ///
    /// This clones the base ArrayState and clones the changed values.
    /// Prefer `into_array_state` when you can consume the DiffSuccessor.
    ///
    /// Part of #228: This now computes the fingerprint internally from combined_xor,
    /// supporting deferred fingerprinting where DiffSuccessor.fingerprint may be a placeholder.
    #[inline]
    pub fn materialize(&self, base: &ArrayState, registry: &VarRegistry) -> ArrayState {
        let mut result = base.clone();

        let (mut combined_xor, base_value_fps) = base.incremental_fp_base(registry);

        for (idx, value) in &self.changes {
            let idx_usize = idx.as_usize();
            let old_fp = base_value_fps.map_or_else(
                || compact_value_fingerprint(&base.values[idx_usize]),
                |fps| fps[idx_usize],
            );
            let new_fp = value_fingerprint(value);
            if old_fp != new_fp {
                let salt = registry.fp_salt(*idx);
                let old_contrib = salt.wrapping_mul(old_fp.wrapping_add(1));
                let new_contrib = salt.wrapping_mul(new_fp.wrapping_add(1));
                combined_xor ^= old_contrib ^ new_contrib;
            }

            result.values[idx_usize] = CompactValue::from(value.clone());
        }

        // Part of #228: Compute fingerprint from combined_xor instead of trusting self.fingerprint.
        let computed_fp = Fingerprint(finalize_fingerprint_xor(combined_xor, FNV_PRIME));

        // Debug check: if fingerprint was pre-computed (not placeholder), verify it matches
        debug_assert!(
            self.fingerprint.0 == 0 || self.fingerprint == computed_fp,
            "DiffSuccessor fingerprint {:016x} does not match computed {:016x}",
            self.fingerprint.0,
            computed_fp.0
        );

        result.fp_cache = Some(ArrayStateFpCache {
            combined_xor,
            fingerprint: computed_fp,
            value_fps: None,
        });

        result
    }

    /// Materialize this diff into a full ArrayState by applying changes to the base.
    ///
    /// Consumes the DiffSuccessor, moving changed Values into the result to avoid extra clones.
    ///
    /// Part of #228: Accepts pre-computed fingerprint to avoid double computation.
    /// When `precomputed_fp` is Some, uses that fingerprint directly and skips
    /// fingerprint computation entirely for maximum performance.
    #[inline]
    pub fn into_array_state(
        self,
        base: &ArrayState,
        registry: &VarRegistry,
        precomputed_fp: Option<Fingerprint>,
    ) -> ArrayState {
        let mut result = base.clone();

        if let Some(fp) = precomputed_fp {
            // Fast path: Use pre-computed fingerprint
            let (mut combined_xor, base_value_fps) = base.incremental_fp_base(registry);

            for (idx, value) in self.changes {
                let idx_usize = idx.as_usize();
                let old_fp = base_value_fps.map_or_else(
                    || compact_value_fingerprint(&base.values[idx_usize]),
                    |fps| fps[idx_usize],
                );
                let new_fp = value_fingerprint(&value);
                if old_fp != new_fp {
                    let salt = registry.fp_salt(idx);
                    let old_contrib = salt.wrapping_mul(old_fp.wrapping_add(1));
                    let new_contrib = salt.wrapping_mul(new_fp.wrapping_add(1));
                    combined_xor ^= old_contrib ^ new_contrib;
                }
                result.values[idx_usize] = CompactValue::from(value);
            }

            result.fp_cache = Some(ArrayStateFpCache {
                combined_xor,
                fingerprint: fp,
                value_fps: None,
            });
        } else {
            // Slow path: compute fingerprint from combined_xor
            let (mut combined_xor, base_value_fps) = base.incremental_fp_base(registry);

            for (idx, value) in self.changes {
                let idx_usize = idx.as_usize();
                let old_fp = base_value_fps.map_or_else(
                    || compact_value_fingerprint(&base.values[idx_usize]),
                    |fps| fps[idx_usize],
                );
                let new_fp = value_fingerprint(&value);
                if old_fp != new_fp {
                    let salt = registry.fp_salt(idx);
                    let old_contrib = salt.wrapping_mul(old_fp.wrapping_add(1));
                    let new_contrib = salt.wrapping_mul(new_fp.wrapping_add(1));
                    combined_xor ^= old_contrib ^ new_contrib;
                }
                result.values[idx_usize] = CompactValue::from(value);
            }

            let computed_fp = Fingerprint(finalize_fingerprint_xor(combined_xor, FNV_PRIME));
            result.fp_cache = Some(ArrayStateFpCache {
                combined_xor,
                fingerprint: computed_fp,
                value_fps: None,
            });
        }

        result
    }

    /// Materialize this diff using pre-computed fingerprint AND combined_xor.
    ///
    /// Part of #228: This is the fast path that avoids recomputing XOR operations.
    /// Use this when you already have both the fingerprint (from dedup check) and
    /// combined_xor (from `compute_diff_fingerprint_with_xor`).
    ///
    /// This method ONLY copies values - no XOR computation is performed.
    #[inline]
    pub fn into_array_state_with_fp(
        self,
        base: &ArrayState,
        fp: Fingerprint,
        combined_xor: u64,
    ) -> ArrayState {
        let mut result = base.clone();

        // Only copy values - NO XOR computation needed
        for (idx, value) in self.changes {
            result.values[idx.as_usize()] = CompactValue::from(value);
        }

        result.fp_cache = Some(ArrayStateFpCache {
            combined_xor,
            fingerprint: fp,
            value_fps: None,
        });

        result
    }

    /// Materialize this diff while preserving a complete per-slot fingerprint cache.
    ///
    /// Part of #3285: clone and patch `value_fps` only for changed slots so the
    /// next dequeue can reuse the cache instead of rebuilding it from scratch.
    ///
    /// Part of #3805: Prefer `into_array_state_with_precomputed_fps` when per-change
    /// fingerprints are already available from `compute_diff_fingerprint_with_change_fps`.
    #[inline]
    pub fn into_array_state_with_complete_fp_cache(
        self,
        base: &ArrayState,
        fp: Fingerprint,
        combined_xor: u64,
        registry: &VarRegistry,
    ) -> ArrayState {
        let mut result = base.clone_with_complete_fp_cache();
        debug_assert_eq!(registry.len(), result.values.len());

        let mut value_fps = result.fp_cache.take().and_then(|cache| cache.value_fps);

        for (idx, value) in self.changes {
            let idx_usize = idx.as_usize();
            if let Some(fps) = value_fps.as_mut() {
                fps[idx_usize] = value_fingerprint(&value);
            }
            result.values[idx_usize] = CompactValue::from(value);
        }

        result.fp_cache = Some(ArrayStateFpCache {
            combined_xor,
            fingerprint: fp,
            value_fps,
        });

        result
    }

    /// Materialize with pre-computed per-change value fingerprints.
    ///
    /// Part of #3805: Avoids recomputing `value_fingerprint` for changed slots when
    /// the caller already has the per-change fps from `compute_diff_fingerprint_with_change_fps`.
    /// This eliminates the double value_fingerprint computation in the streaming admitted path.
    ///
    /// Not yet wired into the streaming pipeline — available for future use.
    #[inline]
    #[allow(dead_code)]
    pub fn into_array_state_with_precomputed_fps(
        self,
        base: &ArrayState,
        fp: Fingerprint,
        combined_xor: u64,
        change_fps: &[u64],
    ) -> ArrayState {
        let mut result = base.clone_with_complete_fp_cache();

        let mut value_fps = result.fp_cache.take().and_then(|cache| cache.value_fps);

        for (i, (idx, value)) in self.changes.into_iter().enumerate() {
            let idx_usize = idx.as_usize();
            if let Some(fps) = value_fps.as_mut() {
                fps[idx_usize] = change_fps[i];
            }
            result.values[idx_usize] = CompactValue::from(value);
        }

        result.fp_cache = Some(ArrayStateFpCache {
            combined_xor,
            fingerprint: fp,
            value_fps,
        });

        result
    }

    /// Materialize this diff into an existing ArrayState, reusing its allocation.
    ///
    /// Part of #3023: scratch-buffer variant of `into_array_state_with_fp`.
    /// Instead of cloning the base state (Box allocation + N CompactValue clones),
    /// this overwrites an existing ArrayState in-place (N CompactValue clones only,
    /// no Box allocation). For specs with high duplicate rates (~95%), this
    /// avoids one Box alloc+free per duplicate successor.
    ///
    /// The caller must ensure `target.values.len() == base.values.len()`.
    /// Like `into_array_state_with_fp`, this method performs no XOR computation.
    #[inline]
    pub fn materialize_into(
        self,
        target: &mut ArrayState,
        base: &ArrayState,
        fp: Fingerprint,
        combined_xor: u64,
    ) {
        debug_assert_eq!(
            target.values.len(),
            base.values.len(),
            "materialize_into: target and base must have same number of variables"
        );
        target.values.clone_from_slice(&base.values);
        for (idx, value) in self.changes {
            target.values[idx.as_usize()] = CompactValue::from(value);
        }
        target.fp_cache = Some(ArrayStateFpCache {
            combined_xor,
            fingerprint: fp,
            value_fps: None,
        });
    }

    /// Get the number of changed variables (debug-only: used for diff successor logging)
    #[cfg(debug_assertions)]
    #[inline]
    pub fn num_changes(&self) -> usize {
        self.changes.len()
    }
}

impl std::fmt::Debug for DiffSuccessor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "DiffSuccessor(fp={:016x}, {} changes)",
            self.fingerprint.0,
            self.changes.len()
        )
    }
}

// Part of #3354 Slice 4: compute_diff_fingerprint removed — superseded by
// compute_diff_fingerprint_with_xor which returns the additional combined_xor
// value needed by the BFS pipeline. No callers remained.

/// Compute fingerprint AND combined_xor for later use in materialization.
///
/// Part of #228: This returns both the fingerprint (for deduplication) and
/// the combined_xor value (for fp_cache), avoiding recomputation during
/// `into_array_state_with_fp()`.
///
/// Returns `(Fingerprint, combined_xor)` tuple.
pub(crate) fn compute_diff_fingerprint_with_xor(
    base: &ArrayState,
    changes: &[(VarIndex, Value)],
    registry: &VarRegistry,
) -> (Fingerprint, u64) {
    // Use cached combined_xor when available, otherwise compute it from the base state.
    let (mut combined_xor, base_value_fps) = base.incremental_fp_base(registry);

    // Apply changes: XOR out old contribution, XOR in new contribution.
    for (idx, new_value) in changes {
        let idx_usize = idx.as_usize();
        let old_fp = base_value_fps.map_or_else(
            || compact_value_fingerprint(&base.values[idx_usize]),
            |fps| fps[idx_usize],
        );
        let new_fp = value_fingerprint(new_value);

        if old_fp != new_fp {
            let salt = registry.fp_salt(*idx);
            let old_contrib = salt.wrapping_mul(old_fp.wrapping_add(1));
            let new_contrib = salt.wrapping_mul(new_fp.wrapping_add(1));
            combined_xor ^= old_contrib ^ new_contrib;
        }
    }

    let final_fp = Fingerprint(finalize_fingerprint_xor(combined_xor, FNV_PRIME));
    (final_fp, combined_xor)
}

/// Like `compute_diff_fingerprint_with_xor`, but also returns per-change value
/// fingerprints so callers that need to update the per-slot `value_fps` cache
/// can reuse them instead of recomputing `value_fingerprint` a second time.
///
/// Part of #3805: Eliminates double `value_fingerprint` computation for the
/// ~5% of successors that survive admission and need complete fp caches.
/// Returns `(Fingerprint, combined_xor, per_change_fps)`.
///
/// Not yet wired into the streaming pipeline — available for future use when
/// `admitted_diffs` storage is updated to carry per-change fps.
#[allow(dead_code)]
pub(crate) fn compute_diff_fingerprint_with_change_fps(
    base: &ArrayState,
    changes: &[(VarIndex, Value)],
    registry: &VarRegistry,
) -> (Fingerprint, u64, SmallVec<[u64; DIFF_INLINE_CAPACITY]>) {
    let (mut combined_xor, base_value_fps) = base.incremental_fp_base(registry);

    let mut change_fps = SmallVec::<[u64; DIFF_INLINE_CAPACITY]>::with_capacity(changes.len());

    for (idx, new_value) in changes {
        let idx_usize = idx.as_usize();
        let old_fp = base_value_fps.map_or_else(
            || compact_value_fingerprint(&base.values[idx_usize]),
            |fps| fps[idx_usize],
        );
        let new_fp = value_fingerprint(new_value);
        change_fps.push(new_fp);

        if old_fp != new_fp {
            let salt = registry.fp_salt(*idx);
            let old_contrib = salt.wrapping_mul(old_fp.wrapping_add(1));
            let new_contrib = salt.wrapping_mul(new_fp.wrapping_add(1));
            combined_xor ^= old_contrib ^ new_contrib;
        }
    }

    (
        Fingerprint(finalize_fingerprint_xor(combined_xor, FNV_PRIME)),
        combined_xor,
        change_fps,
    )
}
