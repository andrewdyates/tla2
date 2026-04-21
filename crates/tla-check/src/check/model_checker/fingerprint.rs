// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(debug_assertions)]
use super::debug::{
    debug_symmetry_invariant, debug_symmetry_invariant_dump_state, debug_symmetry_invariant_panic,
};
use super::{ArrayState, CheckError, Fingerprint, ModelChecker, State};

/// Default soft cap for the symmetry fingerprint cache.
///
/// When the cache exceeds this limit, it is evicted (cleared) to prevent
/// unbounded memory growth on specs with large symmetric state spaces.
/// The cache is a performance optimization only — correctness does not
/// depend on it — so clearing is always safe.
///
/// Override via `TLA2_SYMMETRY_FP_CACHE_CAP` env var (0 = unlimited).
///
/// Part of #4080: OOM safety — cap unbounded symmetry fp_cache.
pub(super) const DEFAULT_SYMMETRY_FP_CACHE_CAP: usize = 1_000_000;

/// Read the symmetry fp_cache cap from env or use default.
///
/// Part of #4080.
pub(super) fn symmetry_fp_cache_cap() -> usize {
    static CACHED: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *CACHED.get_or_init(|| {
        std::env::var("TLA2_SYMMETRY_FP_CACHE_CAP")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or(DEFAULT_SYMMETRY_FP_CACHE_CAP)
    })
}

impl<'a> ModelChecker<'a> {
    /// Compute the fingerprint of a state, applying VIEW and symmetry reduction if configured.
    ///
    /// Fingerprinting order of operations:
    /// 1. If VIEW is configured: delegates to `checker_ops::compute_view_fingerprint`
    /// 2. If symmetry permutations are configured: return the canonical fingerprint
    ///    (fingerprint of the lexicographically minimal symmetric state)
    /// 3. Otherwise: return the regular state fingerprint
    ///
    /// Part of #2756: VIEW fingerprinting now delegates to the canonical implementation
    /// in `checker_ops.rs`, shared with the parallel checker path. The canonical function
    /// manages `tlc_level` self-contained (save/set/restore), so the caller's prior
    /// `set_tlc_level(succ_level)` call is redundant but harmless for the VIEW path.
    pub(super) fn state_fingerprint(&mut self, state: &State) -> Result<Fingerprint, CheckError> {
        // Part of #4319 Phase 0 (Option D): fingerprint mixed-mode guard.
        //
        // The OrdMap-based `state_fingerprint` path must never be taken when
        // compiled xxh3 fingerprinting is active. When `jit_compiled_fp_active`
        // is true, every successor — whether emitted by compiled or interpreter
        // paths — must be hashed via `array_state_fingerprint` →
        // `fingerprint_flat_compiled` (xxh3 + FLAT_COMPILED_DOMAIN_SEED) to keep
        // `seen_fps` in a single hash domain. Reaching this function with the
        // flag set would mix xxh3 and FP64 fingerprints in the same dedup
        // table, causing silent state loss. The only callers that route
        // through here (symmetry canonical fingerprinting, VIEW computation,
        // legacy State-only paths) activate before `try_activate_compiled_fingerprinting`
        // can set the flag, so this assertion documents and enforces the
        // invariant rather than guarding a reachable path.
        debug_assert!(
            !self.jit_compiled_fp_active,
            "#4319: state_fingerprint() called with jit_compiled_fp_active=true. \
             OrdMap fingerprint path would mix FP64 with the xxh3 domain used by \
             array_state_fingerprint. See designs/2026-04-20-llvm2-fingerprint-unification.md."
        );

        // If VIEW is configured, delegate to the canonical implementation.
        if let Some(ref view_name) = self.compiled.cached_view_name.clone() {
            // Pass the current tlc_level as bfs_level. The caller (engine.rs) has already
            // set this to succ_level; the canonical function saves/sets/restores it
            // internally, which is a no-op here but keeps the function self-contained.
            let bfs_level = self.ctx.get_tlc_level();
            return crate::checker_ops::compute_view_fingerprint(
                &mut self.ctx,
                state,
                view_name,
                bfs_level,
            );
        }

        // For symmetry-based fingerprinting, use the cache.
        if !self.symmetry.mvperms.is_empty() {
            let original_fp = state.fingerprint();
            // Check cache first.
            if let Some(&canonical) = self.symmetry.fp_cache.get(&original_fp) {
                self.symmetry.fp_cache_hits += 1;
                return Ok(canonical);
            }
            self.symmetry.fp_cache_misses += 1;
            // Compute and cache (Part of #358: use fast O(1) MVPerm lookup).
            let canonical = state.fingerprint_with_symmetry_fast(&self.symmetry.mvperms);

            // Track states folded: when canonical differs from original, this state
            // will be identified with its canonical representative.
            if canonical != original_fp {
                self.symmetry.states_folded += 1;
            }

            // Optional: validate symmetry canonicalization invariant for debugging (#86).
            // For each permutation P, canonical(S) must equal canonical(P(S)).
            debug_block!(debug_symmetry_invariant(), {
                let perm_limit = self.symmetry.mvperms.len();
                for (idx, mvperm) in self.symmetry.mvperms.iter().take(perm_limit).enumerate() {
                    let permuted = state.permute_fast(mvperm);
                    let permuted_canonical =
                        permuted.fingerprint_with_symmetry_fast(&self.symmetry.mvperms);
                    if permuted_canonical != canonical {
                        eprintln!(
                            "SYMMETRY INVARIANT VIOLATION: state={:016x} canonical={:016x} perm_idx={} permuted_canonical={:016x}",
                            original_fp.0,
                            canonical.0,
                            idx,
                            permuted_canonical.0
                        );
                        debug_block!(debug_symmetry_invariant_dump_state(), {
                            eprintln!("  state: {:?}", state);
                            eprintln!("  permuted: {:?}", permuted);
                        });
                        debug_block!(debug_symmetry_invariant_panic(), {
                            panic!(
                                "Symmetry invariant violation for state {:016x} (canonical {:016x})",
                                original_fp.0, canonical.0
                            );
                        });
                        break;
                    }
                }
            });

            // Part of #4080: enforce soft cap to prevent unbounded growth.
            // The cache is a pure optimization — clearing is always safe.
            let cap = symmetry_fp_cache_cap();
            if cap > 0 && self.symmetry.fp_cache.len() >= cap {
                self.symmetry.fp_cache_evictions += 1;
                if self.symmetry.fp_cache_evictions == 1 {
                    eprintln!(
                        "[symmetry] fp_cache exceeded soft cap ({cap} entries), evicting. \
                         Set TLA2_SYMMETRY_FP_CACHE_CAP to adjust."
                    );
                }
                self.symmetry.fp_cache.clear();
            }
            self.symmetry.fp_cache.insert(original_fp, canonical);
            return Ok(canonical);
        }

        // Regular fingerprint (no symmetry).
        Ok(state.fingerprint())
    }

    /// Compute fingerprint for an ArrayState.
    ///
    /// Fast path when no VIEW or symmetry is configured - uses ArrayState directly.
    /// Falls back to State-based fingerprinting for symmetry handling.
    ///
    /// Part of #3792: VIEW fingerprinting now uses `compute_view_fingerprint_array`
    /// directly, avoiding the O(n) ArrayState → State (OrdMap) conversion that was
    /// performed for every successor. This matches the parallel checker path.
    ///
    /// Part of #3987: When `jit_compiled_fp_active` is true, uses xxh3 SIMD
    /// fingerprinting on the flat i64 representation instead of per-variable FP64.
    pub(super) fn array_state_fingerprint(
        &mut self,
        array_state: &mut ArrayState,
    ) -> Result<Fingerprint, CheckError> {
        // Fast path: if fingerprint is already cached and no VIEW/symmetry, return it.
        // This avoids registry access for states popped from queue.
        if self.compiled.cached_view_name.is_none() && self.symmetry.perms.is_empty() {
            if let Some(fp) = array_state.cached_fingerprint() {
                return Ok(fp);
            }
        }

        // If VIEW is configured, use the array-native path (no OrdMap conversion).
        if let Some(ref view_name) = self.compiled.cached_view_name.clone() {
            let bfs_level = self.ctx.get_tlc_level();
            return crate::checker_ops::compute_view_fingerprint_array(
                &mut self.ctx,
                array_state,
                view_name,
                bfs_level,
            );
        }

        let registry = self.ctx.var_registry().clone();

        // If symmetry is configured, fall back to State-based fingerprinting.
        if !self.symmetry.perms.is_empty() {
            let state = array_state.to_state(&registry);
            return self.state_fingerprint(&state);
        }

        // Part of #3987: Compiled xxh3 fingerprinting for all-scalar JIT specs.
        // When active, flatten the ArrayState to i64 and hash with xxh3 SIMD
        // instead of iterating per-variable with FP64 type dispatch.
        if self.jit_compiled_fp_active {
            let fp = self.array_state_fingerprint_xxh3(array_state);
            array_state.set_cached_fingerprint(fp);
            return Ok(fp);
        }

        // Fast path: compute fingerprint directly from ArrayState.
        let fp = array_state.fingerprint(&registry);
        Ok(fp)
    }

    /// Compute fingerprint for an ArrayState using xxh3 SIMD on the flat i64 buffer.
    ///
    /// This extracts each CompactValue as an i64 (bool → 0/1, int → value) and
    /// hashes the resulting buffer with xxh3-64. Only valid when ALL variables are
    /// scalar (Int/Bool) — compound values cannot be represented as a single i64.
    ///
    /// Part of #3987: Compiled xxh3 fingerprinting.
    /// Part of #3986: Uses reusable `flat_fp_scratch` buffer to avoid per-state
    /// `Vec<i64>` allocation on the BFS hot path.
    pub(in crate::check::model_checker) fn array_state_fingerprint_xxh3(&mut self, array_state: &ArrayState) -> Fingerprint {
        let values = array_state.values();
        let num_vars = values.len();

        // Reuse the scratch buffer — resize only when var count changes (i.e., never
        // in a single model-checking run, since all states have the same number of vars).
        let scratch = &mut self.flat_fp_scratch;
        scratch.resize(num_vars, 0);

        for (i, cv) in values.iter().enumerate() {
            scratch[i] = if cv.is_bool() {
                i64::from(cv.as_bool())
            } else if cv.is_int() {
                cv.as_int()
            } else {
                // Compound variable — should not happen when jit_compiled_fp_active is true.
                debug_assert!(
                    false,
                    "array_state_fingerprint_xxh3 called with compound variable"
                );
                0
            };
        }
        super::invariants::fingerprint_flat_compiled(&scratch[..num_vars])
    }

    /// Populate symmetry reduction statistics into CheckStats.
    ///
    /// Called during finalization to transfer accumulated symmetry counters
    /// into the public stats structure.
    pub(in crate::check) fn populate_symmetry_stats(&mut self) {
        if self.symmetry.perms.is_empty() {
            return;
        }
        let stats = &mut self.stats.symmetry_reduction;
        stats.permutation_count = self.symmetry.perms.len();
        stats.fp_cache_hits = self.symmetry.fp_cache_hits;
        stats.fp_cache_misses = self.symmetry.fp_cache_misses;
        stats.states_folded = self.symmetry.states_folded;
        stats.group_names = self.symmetry.group_names.clone();
        stats.auto_detected = self.symmetry.auto_detected;

        // Count independent symmetry groups from group_names.
        stats.symmetry_groups = if self.symmetry.group_names.is_empty() {
            if self.symmetry.perms.is_empty() {
                0
            } else {
                1
            }
        } else {
            self.symmetry.group_names.len()
        };

        // Compute reduction factor: estimate the unreduced state count as
        // states_found + states_folded (each folded state was a distinct raw
        // state that mapped to an existing canonical representative).
        let states_found = self.stats.states_found as f64;
        let total_raw = states_found + self.symmetry.states_folded as f64;
        stats.reduction_factor = if states_found > 0.0 {
            total_raw / states_found
        } else {
            1.0
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_symmetry_fp_cache_cap_is_reasonable() {
        // The default cap should be large enough to avoid eviction on small/medium
        // specs but small enough to prevent OOM on large symmetric state spaces.
        assert_eq!(DEFAULT_SYMMETRY_FP_CACHE_CAP, 1_000_000);
    }

    #[test]
    fn test_symmetry_fp_cache_cap_returns_default_without_env() {
        // When the env var is not set, should return the default.
        // Note: this test is sensitive to env state — if TLA2_SYMMETRY_FP_CACHE_CAP
        // is set in the environment, it will use that value. But in normal test
        // environments it is not set.
        let cap = symmetry_fp_cache_cap();
        // The OnceLock may have been initialized by a previous test, so we just
        // verify it returns a positive value.
        assert!(cap > 0, "cap should be positive, got {cap}");
    }

    #[test]
    fn test_symmetry_fp_cache_eviction_on_hashmap_directly() {
        // Test the eviction pattern directly on a HashMap to verify the logic
        // without requiring a full ModelChecker construction.
        use rustc_hash::FxHashMap;

        let cap: usize = 100;
        let mut cache: FxHashMap<u64, u64> = FxHashMap::default();
        let mut evictions: u64 = 0;

        for i in 0..250u64 {
            // Check cap before insert (same logic as in state_fingerprint)
            if cap > 0 && cache.len() >= cap {
                evictions += 1;
                cache.clear();
            }
            cache.insert(i, i * 2);
        }

        // With cap=100 and 250 inserts:
        // - First 100 fill the cache
        // - At i=100, cache hits cap, eviction 1, clear, insert 100
        // - At i=200, cache hits cap again, eviction 2, clear, insert 200
        // - Remaining 50 fill to 50
        assert_eq!(evictions, 2, "should evict twice");
        assert_eq!(cache.len(), 50, "should have 50 entries after last eviction");
        // Verify the cache contains the most recent entries
        assert!(cache.contains_key(&249));
        assert!(cache.contains_key(&200));
        // Old entries should be gone
        assert!(!cache.contains_key(&99));
    }
}
