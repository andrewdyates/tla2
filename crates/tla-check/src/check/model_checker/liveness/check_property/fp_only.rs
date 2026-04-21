// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    check_error_to_result, Arc, CheckResult, Fingerprint, FxHashMap, LiveExpr, ModelChecker, State,
    SuccessorGraph,
};
use crate::state::ArrayState;
use crate::LivenessCheckError;
use rustc_hash::FxHashSet;
use std::collections::VecDeque;

/// Default maximum number of entries in the fp-only liveness replay cache.
///
/// The replay cache materializes `State` (OrdMap-based) for every reachable
/// fingerprint. Each `State` is ~200-500 bytes depending on variable count,
/// so 5M entries can consume 1-2.5 GB. Beyond this limit, the BFS replay
/// stops inserting new entries and falls back to per-state trace reconstruction
/// for the remaining states — slower but bounded in memory.
///
/// Override via the `TLA2_REPLAY_CACHE_MAX` environment variable.
///
/// Part of #4080: OOM safety — fp_only_replay_cache capping.
const DEFAULT_REPLAY_CACHE_MAX: usize = 5_000_000;

/// Read the max replay cache size from `TLA2_REPLAY_CACHE_MAX` env var,
/// falling back to [`DEFAULT_REPLAY_CACHE_MAX`].
/// Cached via `OnceLock` (Part of #4114).
fn replay_cache_max_from_env() -> usize {
    static CACHED: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *CACHED.get_or_init(|| {
        std::env::var("TLA2_REPLAY_CACHE_MAX")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or(DEFAULT_REPLAY_CACHE_MAX)
    })
}

fn all_leaves_within_tag_range(
    expr: &LiveExpr,
    max_fairness_tag: u32,
    max_inline_tag: u32,
) -> bool {
    match expr {
        LiveExpr::Bool(_) => true,
        LiveExpr::StatePred { tag, .. }
        | LiveExpr::Enabled { tag, .. }
        | LiveExpr::ActionPred { tag, .. }
        | LiveExpr::StateChanged { tag, .. } => {
            *tag > 0 && (*tag <= max_fairness_tag || *tag <= max_inline_tag)
        }
        LiveExpr::Not(inner) => {
            all_leaves_within_tag_range(inner, max_fairness_tag, max_inline_tag)
        }
        LiveExpr::And(exprs) | LiveExpr::Or(exprs) => exprs
            .iter()
            .all(|expr| all_leaves_within_tag_range(expr, max_fairness_tag, max_inline_tag)),
        LiveExpr::Always(_) | LiveExpr::Eventually(_) | LiveExpr::Next(_) => false,
    }
}

pub(super) fn all_checks_structurally_cached(
    plan: &crate::liveness::GroupedLivenessPlan,
    max_fairness_tag: u32,
    max_inline_tag: u32,
    has_inline_results: bool,
) -> bool {
    if !has_inline_results {
        return false;
    }

    let mut action_used = vec![false; plan.check_action.len()];
    let mut state_used = vec![false; plan.check_state.len()];
    for pem in &plan.pems {
        for &idx in &pem.ea_action_idx {
            if idx < action_used.len() {
                action_used[idx] = true;
            }
        }
        for &idx in &pem.ae_action_idx {
            if idx < action_used.len() {
                action_used[idx] = true;
            }
        }
        for &idx in &pem.ea_state_idx {
            if idx < state_used.len() {
                state_used[idx] = true;
            }
        }
        for &idx in &pem.ae_state_idx {
            if idx < state_used.len() {
                state_used[idx] = true;
            }
        }
    }

    let state_ok = plan.check_state.iter().enumerate().all(|(idx, check)| {
        !state_used[idx] || all_leaves_within_tag_range(check, max_fairness_tag, max_inline_tag)
    });
    let action_ok = plan.check_action.iter().enumerate().all(|(idx, check)| {
        !action_used[idx] || all_leaves_within_tag_range(check, max_fairness_tag, max_inline_tag)
    });
    state_ok && action_ok
}

impl ModelChecker<'_> {
    pub(super) fn replay_fingerprint_path(
        &mut self,
        path: &[Fingerprint],
    ) -> Result<Vec<State>, CheckResult> {
        if path.is_empty() {
            return Ok(Vec::new());
        }

        let (init_name, next_name) =
            match (&self.trace.cached_init_name, &self.trace.cached_next_name) {
                (Some(init), Some(next)) => (init.clone(), next.clone()),
                _ => {
                    return Err(check_error_to_result(
                        LivenessCheckError::RuntimeFailure(
                            "Init/Next operator names not cached for liveness counterexample replay"
                                .to_string(),
                        )
                        .into(),
                        &self.stats,
                    ));
                }
            };

        let initial_states = match self.generate_initial_states(&init_name) {
            Ok(states) => states,
            Err(error) => return Err(check_error_to_result(error, &self.stats)),
        };

        let Some(mut current_state) = initial_states.into_iter().find(|state| {
            self.state_fingerprint(state)
                .map(|fp| fp == path[0])
                .unwrap_or(false)
        }) else {
            return Err(check_error_to_result(
                LivenessCheckError::RuntimeFailure(format!(
                    "could not reconstruct fingerprint path: no initial state matches {}",
                    path[0]
                ))
                .into(),
                &self.stats,
            ));
        };

        let mut states = vec![current_state.clone()];
        for &target_fp in &path[1..] {
            let successors = match self.solve_next_relation(&next_name, &current_state) {
                Ok(successors) => successors,
                Err(error) => return Err(check_error_to_result(error, &self.stats)),
            };

            let mut matched_state = None;
            for successor in successors {
                let successor_fp = match self.state_fingerprint(&successor) {
                    Ok(fp) => fp,
                    Err(error) => return Err(check_error_to_result(error, &self.stats)),
                };
                if successor_fp == target_fp {
                    matched_state = Some(successor);
                    break;
                }
            }

            let Some(next_state) = matched_state else {
                return Err(check_error_to_result(
                    LivenessCheckError::RuntimeFailure(format!(
                        "counterexample replay could not find transition {} -> {}",
                        current_state.fingerprint(),
                        target_fp
                    ))
                    .into(),
                    &self.stats,
                ));
            };

            states.push(next_state.clone());
            current_state = next_state;
        }

        Ok(states)
    }

    /// Build the full state cache for fp-only liveness checking using BFS-order
    /// replay. Cached across properties to avoid redundant replay per property.
    ///
    /// Part of #3210: The old implementation called `reconstruct_trace(fp)` for each
    /// of S states, replaying the full Init→...→state path per state — O(S×D) total
    /// work (D = avg depth), called N times (once per property). The new implementation
    /// does a single BFS from init states through `cached_successors`, reconstructing
    /// each state exactly once via Next-relation evaluation — O(S) total, called once.
    /// Matches the parallel checker's `replay_fp_only_state_cache()` pattern.
    #[allow(clippy::type_complexity)]
    pub(super) fn build_fp_only_liveness_state_cache(
        &mut self,
        init_fps: &[Fingerprint],
        cached_successors: &SuccessorGraph,
    ) -> Result<
        (
            Arc<FxHashMap<Fingerprint, State>>,
            Arc<FxHashMap<Fingerprint, Fingerprint>>,
        ),
        CheckResult,
    > {
        // Return cached result if already computed for a previous property.
        if let Some(ref cached) = self.liveness_cache.fp_only_replay_cache {
            return Ok(cached.clone());
        }

        let registry = self.ctx.var_registry().clone();
        let cache_max = replay_cache_max_from_env();

        // Step 1: Seed from init states in the liveness cache (small, typically 1-10).
        // Cap pre-allocation to avoid over-reserving when successor graph is huge.
        let prealloc = (init_fps.len() + cached_successors.len()).min(cache_max);
        let mut state_cache: FxHashMap<Fingerprint, State> =
            FxHashMap::with_capacity_and_hasher(prealloc, Default::default());
        let mut queue: VecDeque<Fingerprint> = VecDeque::new();
        let mut cache_capped = false;

        for (fp, arr) in &self.liveness_cache.init_states {
            state_cache.insert(*fp, arr.to_state(&registry));
            queue.push_back(*fp);
        }

        // Step 2: BFS from init states through cached_successors, replaying
        // Next-relation via ArrayState-based generation (DiffSuccessor streaming
        // path) instead of the slow State-based `solve_next_relation`. This avoids
        // O(n) OrdMap construction per successor — only matched successors are
        // converted to State via `to_state()`. Part of #3739.
        //
        // Part of #4080: Stop BFS when cache exceeds `cache_max` entries. The
        // remaining unreached states will be handled by the per-state fallback
        // in Step 3, which is slower but bounded in memory (one state at a time).

        while let Some(parent_fp) = queue.pop_front() {
            // Part of #4080: Stop BFS replay when cache is at capacity.
            if state_cache.len() >= cache_max {
                if !cache_capped {
                    cache_capped = true;
                    eprintln!(
                        "Warning: fp-only liveness replay cache capped at {} entries. \
                         Remaining states will use per-state trace reconstruction \
                         (slower but memory-bounded). Set TLA2_REPLAY_CACHE_MAX to \
                         adjust this limit.",
                        cache_max
                    );
                }
                break;
            }

            // Part of #4080: Use get_ref() to avoid cloning the entire Vec<Fingerprint>
            // on every lookup in the in-memory backend. Falls back to get() for disk.
            let owned_fallback;
            let expected_succs: &[Fingerprint] =
                if let Some(s) = cached_successors.get_ref(&parent_fp) {
                    s
                } else {
                    owned_fallback = cached_successors.get(&parent_fp);
                    match owned_fallback.as_deref() {
                        Some(s) => s,
                        None => continue,
                    }
                };
            if expected_succs.is_empty() {
                continue;
            }

            // Collect only successors not yet in cache.
            let needed: Vec<Fingerprint> = expected_succs
                .iter()
                .filter(|fp| !state_cache.contains_key(fp))
                .copied()
                .collect();
            if needed.is_empty() {
                continue;
            }

            let parent_state = match state_cache.get(&parent_fp) {
                Some(s) => s.clone(),
                None => continue,
            };

            // Convert parent to ArrayState for array-based successor generation.
            let parent_array = ArrayState::from_state(&parent_state, &registry);

            // Use ArrayState-based successor generation which avoids State/OrdMap
            // construction overhead. Falls back to State-based path on error.
            let succ_arrays = self
                .generate_successors_as_array(&parent_array)
                .map_err(|e| check_error_to_result(e, &self.stats))?;

            let mut needed_set: FxHashSet<Fingerprint> =
                FxHashSet::with_capacity_and_hasher(needed.len(), Default::default());
            needed_set.extend(needed.iter().copied());

            for mut succ_array in succ_arrays {
                let succ_fp = self
                    .array_state_fingerprint(&mut succ_array)
                    .map_err(|e| check_error_to_result(e, &self.stats))?;
                if needed_set.remove(&succ_fp) {
                    // Only convert to State for matched successors (the ~5% that
                    // are actually needed), avoiding OrdMap construction for the
                    // vast majority of duplicates.
                    state_cache.insert(succ_fp, succ_array.to_state(&registry));
                    queue.push_back(succ_fp);
                }
                if needed_set.is_empty() {
                    break;
                }
                // Part of #4080: Check cache cap within inner loop too.
                if state_cache.len() >= cache_max {
                    break;
                }
            }
        }

        // Step 3: Fallback for any states not reached by BFS replay.
        // This can happen when fingerprinting produces different results during
        // replay vs BFS (e.g., evaluation caching, interner state). Fall back to
        // per-state trace reconstruction for just the missing states.
        let mut all_expected = cached_successors.collect_all_fingerprints();
        all_expected.extend(init_fps.iter().copied());
        let missing: Vec<Fingerprint> = all_expected
            .into_iter()
            .filter(|fp| !state_cache.contains_key(fp))
            .collect();
        if !missing.is_empty() {
            for fp in &missing {
                let trace = self.reconstruct_trace(*fp);
                if let Some(state) = trace.states.last().cloned() {
                    state_cache.insert(*fp, state);
                }
            }
        }

        let mut state_fp_to_canon_fp: FxHashMap<Fingerprint, Fingerprint> =
            FxHashMap::with_capacity_and_hasher(state_cache.len(), Default::default());
        for (canon_fp, state) in &state_cache {
            state_fp_to_canon_fp.insert(state.fingerprint(), *canon_fp);
        }

        let result = (Arc::new(state_cache), Arc::new(state_fp_to_canon_fp));
        self.liveness_cache.fp_only_replay_cache = Some(result.clone());
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::{resolve_spec_from_config, CheckResult};
    use crate::Config;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    const FP_ONLY_FALLBACK_SPEC: &str = r#"
---- MODULE FpOnlyFallbackReplay ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next ==
    \/ /\ x = 0
       /\ x' = 1
    \/ /\ x = 1
       /\ x' = 2
    \/ /\ x = 2
       /\ x' = 2

Spec == Init /\ [][Next]_x /\ WF_x(Next)

EventuallyTwo == <> (x = 2)
====
"#;

    fn run_fp_only_checker(use_disk_successors: bool) {
        let tree = parse_to_syntax_tree(FP_ONLY_FALLBACK_SPEC);
        let module = lower(FileId(0), &tree).module.expect("lowered module");
        let unresolved = Config {
            specification: Some("Spec".to_string()),
            ..Default::default()
        };
        let resolved =
            resolve_spec_from_config(&unresolved, &tree).expect("SPECIFICATION should resolve");
        let config = Config {
            init: Some(resolved.init.clone()),
            next: Some(resolved.next.clone()),
            specification: unresolved.specification.clone(),
            properties: vec!["EventuallyTwo".to_string()],
            ..Default::default()
        };

        let mut checker = ModelChecker::new(&module, &config);
        if use_disk_successors {
            checker.liveness_cache.successors =
                SuccessorGraph::disk().expect("disk successor graph should initialize");
        }
        checker.set_deadlock_check(false);
        checker.set_store_states(false);
        checker.set_fairness(resolved.fairness);
        checker.set_stuttering_allowed(resolved.stuttering_allowed);

        match checker.check() {
            CheckResult::Success(stats) => {
                assert_eq!(stats.states_found, 3, "expected 3 reachable states");
            }
            other => panic!("expected liveness success, got: {other:?}"),
        }

        let init_fps: Vec<Fingerprint> = checker
            .liveness_cache
            .init_states
            .iter()
            .map(|(fp, _)| *fp)
            .collect();
        assert_eq!(init_fps.len(), 1, "expected one initial state");

        checker.liveness_cache.fp_only_replay_cache = None;
        checker.liveness_cache.init_states.clear();

        let cached_successors = std::mem::take(&mut checker.liveness_cache.successors);
        let rebuilt = checker
            .build_fp_only_liveness_state_cache(&init_fps, &cached_successors)
            .expect("fallback replay should rebuild the full state cache");
        checker.liveness_cache.successors = cached_successors;

        assert_eq!(
            rebuilt.0.len(),
            3,
            "fallback replay should rebuild all three states when the init-state seed is absent"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn fp_only_replay_fallback_rebuilds_state_cache_with_in_memory_successors() {
        run_fp_only_checker(false);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn fp_only_replay_fallback_rebuilds_state_cache_with_disk_successors() {
        run_fp_only_checker(true);
    }
}
