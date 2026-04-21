// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(debug_assertions)]
use super::debug::{
    debug_symmetry_invariant, debug_symmetry_invariant_dump_state, debug_symmetry_invariant_panic,
};
use super::{ArrayState, CheckError, Fingerprint, ModelChecker, State};

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

        // Fast path: compute fingerprint directly from ArrayState.
        Ok(array_state.fingerprint(&registry))
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
