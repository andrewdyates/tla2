// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(debug_assertions)]
use super::debug::{
    debug_symmetry_invariant, debug_symmetry_invariant_dump_state, debug_symmetry_invariant_panic,
};
use super::{ArrayState, CheckError, Fingerprint, ModelChecker, State};
use crate::state::FlatState;

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

/// Canonical fingerprint-domain classification for the sequential BFS loop.
///
/// This answers a more precise question than `jit_compiled_fp_active`: which
/// fingerprint function actually owns dedup for this run.
///
/// Part of #4319: partial LLVM2 action coverage can still be sound when the
/// BFS stays on the ArrayState FP64 domain (for example, constraints or
/// implied-action filtering force the per-action/full-state path even though
/// some actions are compiled).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::check) enum BfsFingerprintDomain {
    /// `fingerprint_flat_compiled` / `FlatState::fingerprint_compiled`.
    CompiledFlat,
    /// VIEW-specific fingerprinting via `compute_view_fingerprint{,_array}`.
    View,
    /// Symmetry-canonical fingerprints from the representative state.
    SymmetryCanonical,
    /// Plain FP64 fingerprints while full states are retained.
    FullStateFp64,
    /// Plain FP64 fingerprints over `ArrayState` in no-trace mode.
    ArrayFp64,
}

impl BfsFingerprintDomain {
    pub(in crate::check) const fn diagnostic_name(self) -> &'static str {
        match self {
            Self::CompiledFlat => "xxh3_flat_compiled",
            Self::View => "view",
            Self::SymmetryCanonical => "symmetry_canonical",
            Self::FullStateFp64 => "fp64_full_states",
            Self::ArrayFp64 => "fp64_array_state",
        }
    }
}

impl<'a> ModelChecker<'a> {
    pub(in crate::check) fn bfs_fingerprint_domain(&self) -> BfsFingerprintDomain {
        let compiled_flat_domain = !crate::tir_mode::tir_mode_requested()
            && !self.state_storage.store_full_states
            && (self.jit_compiled_fp_active
                || (self.flat_state_primary
                    && self.compiled.eval_implied_actions.is_empty()
                    && self.state_constraints_allow_compiled_flat_domain()
                    && self.config.action_constraints.is_empty()
                    && self.por.independence.is_none()
                    && !(self.coverage.collect && !self.coverage.actions.is_empty())
                    && self.symmetry.perms.is_empty()
                    && self.compiled.cached_view_name.is_none()));

        if compiled_flat_domain {
            return BfsFingerprintDomain::CompiledFlat;
        }
        if self.compiled.cached_view_name.is_some() {
            return BfsFingerprintDomain::View;
        }
        if !self.symmetry.perms.is_empty() {
            return BfsFingerprintDomain::SymmetryCanonical;
        }
        if self.state_storage.store_full_states {
            return BfsFingerprintDomain::FullStateFp64;
        }
        BfsFingerprintDomain::ArrayFp64
    }

    fn state_constraints_allow_compiled_flat_domain(&self) -> bool {
        if self.config.constraints.is_empty() {
            return true;
        }

        // State-constrained flat fingerprints are only safe when the constrained
        // compiled BFS level is the active successor-admission path. The LLVM2
        // builder refuses to install that level unless the native fused backend
        // reported every configured state constraint as active.
        self.should_use_compiled_bfs()
            && self
                .compiled_bfs_level
                .as_ref()
                .is_some_and(|level| level.has_fused_level())
    }

    pub(in crate::check) fn uses_compiled_bfs_fingerprint_domain(&self) -> bool {
        matches!(
            self.bfs_fingerprint_domain(),
            BfsFingerprintDomain::CompiledFlat
        )
    }

    fn compiled_fingerprint_layout(&self) -> Option<std::sync::Arc<crate::state::StateLayout>> {
        self.flat_bfs_adapter
            .as_ref()
            .map(|adapter| adapter.layout().clone())
            .or_else(|| self.flat_state_layout.clone())
    }

    fn compiled_bfs_fingerprint_for_array_state(
        &mut self,
        array_state: &ArrayState,
    ) -> Fingerprint {
        if let Some(layout) = self.compiled_fingerprint_layout() {
            return FlatState::from_array_state(array_state, layout).fingerprint_compiled();
        }

        debug_assert!(
            self.jit_compiled_fp_active,
            "compiled BFS fingerprint domain active without a flat state layout"
        );
        self.array_state_fingerprint_xxh3(array_state)
    }

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
        if self.uses_compiled_bfs_fingerprint_domain() {
            debug_assert!(
                self.compiled.cached_view_name.is_none() && self.symmetry.perms.is_empty(),
                "#4319: compiled BFS fingerprint domain unexpectedly combined with VIEW or SYMMETRY \
                 during state replay fingerprinting"
            );
            let registry = self.ctx.var_registry().clone();
            let array_state = ArrayState::from_state(state, &registry);
            return Ok(self.compiled_bfs_fingerprint_for_array_state(&array_state));
        }

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
                            original_fp.0, canonical.0, idx, permuted_canonical.0
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
        let compiled_domain_active = self.uses_compiled_bfs_fingerprint_domain();

        // Fast path: if fingerprint is already cached and no VIEW/symmetry, return it.
        // This avoids registry access for states popped from queue.
        if !compiled_domain_active
            && self.compiled.cached_view_name.is_none()
            && self.symmetry.perms.is_empty()
        {
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
        if compiled_domain_active {
            let fp = self.compiled_bfs_fingerprint_for_array_state(array_state);
            if self.jit_compiled_fp_active {
                array_state.set_cached_fingerprint(fp);
            }
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
    pub(in crate::check::model_checker) fn array_state_fingerprint_xxh3(
        &mut self,
        array_state: &ArrayState,
    ) -> Fingerprint {
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
    use super::super::bfs::compiled_step_trait::{CompiledBfsLevel, CompiledLevelResult};
    use super::*;
    use crate::config::Config;
    use crate::test_support::parse_module;
    use crate::value::{FuncValue, Value};
    use tla_jit_runtime::BfsStepError;

    struct TestCompiledBfsLevel {
        has_fused_level: bool,
    }

    impl CompiledBfsLevel for TestCompiledBfsLevel {
        fn has_fused_level(&self) -> bool {
            self.has_fused_level
        }

        fn run_level_fused_arena(
            &self,
            _arena: &[i64],
            _parent_count: usize,
        ) -> Option<Result<CompiledLevelResult, BfsStepError>> {
            None
        }
    }

    fn infer_scalar_flat_primary(checker: &mut ModelChecker<'_>) {
        let init = ArrayState::from_values(vec![Value::SmallInt(0)]);
        checker.infer_flat_state_layout(&init);
        assert!(
            checker.flat_state_primary,
            "test setup should produce a flat-primary scalar layout"
        );
    }

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
        assert_eq!(
            cache.len(),
            50,
            "should have 50 entries after last eviction"
        );
        // Verify the cache contains the most recent entries
        assert!(cache.contains_key(&249));
        assert!(cache.contains_key(&200));
        // Old entries should be gone
        assert!(!cache.contains_key(&99));
    }

    #[test]
    fn test_compiled_bfs_fingerprint_domain_disabled_for_full_state_runs() {
        let module = parse_module(
            r#"
---- MODULE CompiledDomainFullState ----
VARIABLE x
Init == x = "a"
Next == x' = x
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };

        let mut checker = ModelChecker::new(&module, &config);
        checker.set_store_states(true);
        checker.flat_state_primary = true;

        assert!(
            !checker.uses_compiled_bfs_fingerprint_domain(),
            "full-state runs must stay in the FP64 domain even if flat_state_primary is set"
        );
    }

    #[test]
    fn test_bfs_fingerprint_domain_uses_compiled_flat_for_flat_state_primary() {
        let module = parse_module(
            r#"
---- MODULE CompiledDomainFlatPrimary ----
VARIABLE x
Init == x = 0
Next == x' = x
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };

        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;

        assert_eq!(
            checker.bfs_fingerprint_domain(),
            BfsFingerprintDomain::CompiledFlat,
            "flat_state_primary should select the flat compiled fingerprint domain when no guard blocks it"
        );
    }

    #[test]
    fn test_bfs_fingerprint_domain_uses_array_fp64_when_constraints_block_flat_domain() {
        let module = parse_module(
            r#"
---- MODULE CompiledDomainConstraint ----
VARIABLE x
Init == x = 0
Next == x' = x
Constraint == TRUE
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            constraints: vec!["Constraint".to_string()],
            ..Default::default()
        };

        let mut checker = ModelChecker::new(&module, &config);
        checker.flat_state_primary = true;

        assert_eq!(
            checker.bfs_fingerprint_domain(),
            BfsFingerprintDomain::ArrayFp64,
            "constraints without an active native fused constraint level must stay in the ArrayState FP64 domain"
        );
    }

    #[test]
    fn test_bfs_fingerprint_domain_allows_constraints_with_active_native_fused_level() {
        let module = parse_module(
            r#"
---- MODULE CompiledDomainNativeConstraint ----
VARIABLE x
Init == x = 0
Next == x' = x
Constraint == TRUE
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            constraints: vec!["Constraint".to_string()],
            ..Default::default()
        };

        let mut checker = ModelChecker::new(&module, &config);
        infer_scalar_flat_primary(&mut checker);
        checker.compiled_bfs_level = Some(Box::new(TestCompiledBfsLevel {
            has_fused_level: true,
        }));

        assert_eq!(
            checker.bfs_fingerprint_domain(),
            BfsFingerprintDomain::CompiledFlat,
            "state-constrained native fused levels can use the compiled-flat fingerprint domain"
        );
    }

    #[test]
    fn test_bfs_fingerprint_domain_blocks_constraints_when_compiled_bfs_disabled() {
        let module = parse_module(
            r#"
---- MODULE CompiledDomainConstraintDisabled ----
VARIABLE x
Init == x = 0
Next == x' = x
Constraint == TRUE
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            constraints: vec!["Constraint".to_string()],
            use_compiled_bfs: Some(false),
            ..Default::default()
        };

        let mut checker = ModelChecker::new(&module, &config);
        infer_scalar_flat_primary(&mut checker);
        checker.compiled_bfs_level = Some(Box::new(TestCompiledBfsLevel {
            has_fused_level: true,
        }));

        assert_eq!(
            checker.bfs_fingerprint_domain(),
            BfsFingerprintDomain::ArrayFp64,
            "compiled-flat fingerprints must stay disabled when the constrained compiled BFS path is disabled"
        );
    }

    #[test]
    fn test_bfs_fingerprint_domain_blocks_constraints_without_fused_level() {
        let module = parse_module(
            r#"
---- MODULE CompiledDomainConstraintNoFusedLevel ----
VARIABLE x
Init == x = 0
Next == x' = x
Constraint == TRUE
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            constraints: vec!["Constraint".to_string()],
            ..Default::default()
        };

        let mut checker = ModelChecker::new(&module, &config);
        infer_scalar_flat_primary(&mut checker);
        checker.compiled_bfs_level = Some(Box::new(TestCompiledBfsLevel {
            has_fused_level: false,
        }));

        assert_eq!(
            checker.bfs_fingerprint_domain(),
            BfsFingerprintDomain::ArrayFp64,
            "a non-fused compiled level must not unlock state-constrained compiled-flat fingerprints"
        );
    }

    #[test]
    fn test_bfs_fingerprint_domain_keeps_view_and_symmetry_domains_over_flat_primary() {
        let module = parse_module(
            r#"
---- MODULE CompiledDomainCanonicalGuards ----
VARIABLE x
Init == x = 0
Next == x' = x
====
"#,
        );
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };

        let mut view_checker = ModelChecker::new(&module, &config);
        view_checker.flat_state_primary = true;
        view_checker.compiled.cached_view_name = Some("View".to_string());
        assert_eq!(
            view_checker.bfs_fingerprint_domain(),
            BfsFingerprintDomain::View,
            "VIEW fingerprinting must override flat_state_primary"
        );

        let mut symmetry_checker = ModelChecker::new(&module, &config);
        symmetry_checker.flat_state_primary = true;
        symmetry_checker
            .symmetry
            .perms
            .push(FuncValue::from_sorted_entries(Vec::<(Value, Value)>::new()));
        assert_eq!(
            symmetry_checker.bfs_fingerprint_domain(),
            BfsFingerprintDomain::SymmetryCanonical,
            "SYMMETRY canonicalization must override flat_state_primary"
        );
    }
}
