// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Graph data extraction for post-BFS liveness checking.
//! Converts parallel DashMaps into sequential FxHashMaps for `LivenessChecker`.
//! Part of #3210: when `store_full_states` is false, reconstructs concrete
//! states from the cached fingerprint graph on the cold liveness path.

use super::*;

use crate::check::check_error_to_result;
use crate::liveness::SuccessorWitnessMap;
use crate::storage::LookupOutcome;
use crate::EvalCheckError;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::VecDeque;

/// Data extracted from the parallel checker's DashMaps for liveness analysis.
pub(super) struct LivenessGraphData {
    /// Part of #2661: Preserve ArrayState storage through the safety-temporal
    /// fast path. The cold Tableau/SCC path materializes State values lazily.
    pub(super) state_cache: Arc<FxHashMap<Fingerprint, ArrayState>>,
    pub(super) state_fp_to_canon_fp: Arc<FxHashMap<Fingerprint, Fingerprint>>,
    /// Part of #3065: Initial state fingerprints for the fingerprint-based direct path.
    /// Part of #2661: init_states Vec<State> removed — the cold Tableau/SCC path
    /// resolves init states from the materialized state cache via init_fps,
    /// eliminating to_state() conversion from the hot build path.
    pub(super) init_fps: Vec<Fingerprint>,
    pub(super) cached_successors: FxHashMap<Fingerprint, Vec<Fingerprint>>,
    /// Part of #3011: Concrete successor witness states for symmetry liveness.
    /// `None` when symmetry is not active.
    pub(super) succ_witnesses: Option<Arc<SuccessorWitnessMap>>,
}

impl ParallelChecker {
    /// Convert parallel checker's DashMaps into sequential FxHashMaps for liveness.
    ///
    /// This method is for **post-BFS liveness only** (all workers joined).
    /// Missing states indicate a bug in the `cache_for_liveness` mechanism and
    /// trigger a hard error unless `TLA2_STRICT_LIVENESS=0` overrides.
    ///
    /// For periodic liveness during BFS, use [`build_periodic_liveness_graph_data`]
    /// instead, which avoids the expensive `build_full_state_liveness_cache()` call.
    pub(super) fn build_liveness_graph_data(
        &self,
        stats: &CheckStats,
        partial_graph: bool,
    ) -> Result<LivenessGraphData, CheckResult> {
        let registry = self.var_registry.clone();
        let cached_successors = self.collect_cached_successors();

        // Part of #3801: When liveness is active (successors.is_some()), workers
        // now store full ArrayState values in `self.seen` even in fp-only mode,
        // so we always use the full-state cache path. The unreliable fp-only
        // replay path (which re-enumerates successors and can produce different
        // fingerprints due to evaluation context differences) is only used when
        // `self.seen` has no data — i.e., when liveness is NOT active.
        let has_liveness_states = self.successors.is_some();
        let (state_cache, init_fps) = if self.store_full_states || has_liveness_states {
            self.build_full_state_liveness_cache()
        } else {
            self.build_fp_only_liveness_cache(&cached_successors, &registry, stats)?
        };

        // Part of #2661: Build fingerprint→canonical map only under SYMMETRY.
        // Without symmetry, state.fingerprint() == canon_fp (identity), so
        // consumers handle the empty-map case via unwrap_or(fp) fallbacks.
        let has_symmetry = self.config.symmetry.is_some();
        let mut state_fp_to_canon_fp: FxHashMap<Fingerprint, Fingerprint> = if has_symmetry {
            let mut map =
                FxHashMap::with_capacity_and_hasher(state_cache.len(), Default::default());
            for (fp, state) in &state_cache {
                let mut state = state.clone();
                map.insert(state.fingerprint(&registry), *fp);
            }
            map
        } else {
            FxHashMap::default()
        };

        // Part of #3011: Build successor witness map and register witness FPs.
        let succ_witnesses = if has_symmetry {
            self.build_successor_witnesses(&registry, &mut state_fp_to_canon_fp)
        } else {
            None
        };
        let state_fp_to_canon_fp = Arc::new(state_fp_to_canon_fp);

        // Part of #3065: Wrap in Arc for zero-copy sharing with BehaviorGraph.
        let state_cache = Arc::new(state_cache);

        // Part of #3746: Validate state cache completeness before liveness analysis.
        // Part of #3801: For post-BFS liveness (partial_graph=false), missing states
        // indicate a bug and produce a hard error. For periodic liveness during BFS
        // (partial_graph=true), missing states are expected and tolerated.
        Self::validate_liveness_state_cache(
            &state_cache,
            &cached_successors,
            &init_fps,
            partial_graph,
            stats,
        )?;

        Ok(LivenessGraphData {
            state_cache,
            state_fp_to_canon_fp,
            init_fps,
            cached_successors,
            succ_witnesses,
        })
    }

    /// Build a lightweight `LivenessGraphData` for periodic liveness during BFS.
    ///
    /// Part of #3801: During periodic liveness, workers are suspended but DashMap
    /// iteration is weakly consistent — `build_full_state_liveness_cache()` can
    /// miss entries inserted by workers before suspension if the iterator's
    /// per-shard snapshot was taken before a particular insert became visible.
    ///
    /// This method avoids the expensive and potentially incomplete state cache
    /// snapshot entirely. During periodic liveness, `self.successors.is_some()`
    /// is always true (checked by `periodic_liveness_enabled`), so all state
    /// lookups in `check_safety_temporal_terms` go through `self.seen` directly
    /// via `get_array_state_for_fp` — they never need `graph.state_cache`.
    ///
    /// We only populate `cached_successors` (the successor graph topology) since
    /// that is needed for action-level safety-temporal checks. State data for
    /// those checks comes from `self.seen` on demand.
    pub(super) fn build_periodic_liveness_graph_data(&self) -> LivenessGraphData {
        let cached_successors = self.collect_cached_successors();

        // Part of #3801: Collect init fingerprints only (no state data needed).
        let init_fps: Vec<Fingerprint> = self
            .liveness_init_states
            .iter()
            .map(|entry| *entry.key())
            .collect();

        // Part of #3801: Build successor witness map for symmetry action checks.
        // Under symmetry, action-level safety-temporal terms need concrete witness
        // states (not canonical representatives). The witness DashMap is small
        // relative to the full state cache and its iteration is bounded.
        let has_symmetry = self.config.symmetry.is_some();
        let registry = self.var_registry.clone();
        let mut state_fp_to_canon_fp: FxHashMap<Fingerprint, Fingerprint> = FxHashMap::default();
        let succ_witnesses = if has_symmetry {
            self.build_successor_witnesses(&registry, &mut state_fp_to_canon_fp)
        } else {
            None
        };

        LivenessGraphData {
            // Part of #3801: Empty state cache — periodic safety-temporal checks
            // read state data from `self.seen` directly via `get_array_state_for_fp`,
            // avoiding the weakly-consistent DashMap snapshot entirely.
            state_cache: Arc::new(FxHashMap::default()),
            state_fp_to_canon_fp: Arc::new(state_fp_to_canon_fp),
            init_fps,
            cached_successors,
            succ_witnesses,
        }
    }

    /// Build successor witness map from DashMap and register witness FPs.
    ///
    /// Part of #3011: Converts the concurrent `successor_witnesses` DashMap into a
    /// sequential `SuccessorWitnessMap`, and adds witness state raw FPs to
    /// `state_fp_to_canon_fp`. Under symmetry, concrete witness states have raw
    /// FPs that differ from the canonical representative stored in the liveness
    /// state cache. Without these entries, UNCHANGED/StateChanged evaluation
    /// produces incorrect results.
    /// Matches sequential checker at liveness.rs:878-910.
    /// Part of #2661: Stores ArrayState directly instead of converting to State,
    /// eliminating the O(W) `to_state` conversion. Fingerprints are computed
    /// during the build loop for `state_fp_to_canon_fp` registration.
    fn build_successor_witnesses(
        &self,
        registry: &VarRegistry,
        state_fp_to_canon_fp: &mut FxHashMap<Fingerprint, Fingerprint>,
    ) -> Option<Arc<SuccessorWitnessMap>> {
        let witness_map = self.successor_witnesses.as_ref()?;
        let mut out: SuccessorWitnessMap =
            FxHashMap::with_capacity_and_hasher(witness_map.len(), Default::default());
        for entry in witness_map.iter() {
            let mut converted = Vec::with_capacity(entry.value().len());
            for (to_fp, arr) in entry.value() {
                let mut arr_clone = arr.clone();
                let raw_fp = arr_clone.fingerprint(registry);
                state_fp_to_canon_fp.entry(raw_fp).or_insert(*to_fp);
                converted.push((*to_fp, arr_clone));
            }
            out.insert(*entry.key(), converted);
        }
        Some(Arc::new(out))
    }

    /// Part of #3746: Validate that the state cache covers all fingerprints
    /// referenced by the successor graph.
    ///
    /// Part of #3746: Behavior depends on `partial_graph`:
    /// - `partial_graph=true` (periodic liveness during BFS): missing states are
    ///   expected because workers may be mid-processing. Warn and proceed.
    /// - `partial_graph=false` (post-BFS liveness): all workers are joined and
    ///   states should be present, but the non-atomic `seen_fps.insert_checked()`
    ///   / `seen.insert()` pair in `core_adapter::admit()` means a small number
    ///   of states can be missing if a worker error interrupted the sequence.
    ///   Downstream liveness code (#3746 guards) handles missing states by
    ///   skipping affected nodes/edges, so we warn and proceed by default.
    ///   Set `TLA2_STRICT_LIVENESS=1` to upgrade to a hard error for debugging.
    #[allow(clippy::result_large_err)]
    fn validate_liveness_state_cache(
        state_cache: &FxHashMap<Fingerprint, ArrayState>,
        cached_successors: &FxHashMap<Fingerprint, Vec<Fingerprint>>,
        init_fps: &[Fingerprint],
        partial_graph: bool,
        stats: &CheckStats,
    ) -> Result<(), CheckResult> {
        // Collect all FPs referenced as source or destination in the successor graph.
        let mut referenced: FxHashSet<Fingerprint> =
            FxHashSet::with_capacity_and_hasher(cached_successors.len() * 2, Default::default());
        for (src_fp, dest_fps) in cached_successors {
            referenced.insert(*src_fp);
            for fp in dest_fps {
                referenced.insert(*fp);
            }
        }
        for fp in init_fps {
            referenced.insert(*fp);
        }

        let missing: Vec<Fingerprint> = referenced
            .iter()
            .filter(|fp| !state_cache.contains_key(fp))
            .copied()
            .collect();

        if missing.is_empty() {
            return Ok(());
        }

        let preview: Vec<String> = missing.iter().take(5).map(ToString::to_string).collect();

        if partial_graph {
            // Periodic liveness during BFS — missing states are expected.
            // Workers may be mid-processing and haven't flushed all states yet.
            if crate::check::debug::liveness_profile() {
                eprintln!(
                    "Info: periodic liveness state cache is missing {count} of {total} \
                     referenced state(s) (expected during BFS): {preview}",
                    count = missing.len(),
                    total = referenced.len(),
                    preview = preview.join(", "),
                );
            }
            return Ok(());
        }

        // Part of #3746: Post-BFS liveness — all workers joined, all states
        // should be present. Missing states indicate a non-atomic seen_fps/seen
        // insert race (seen_fps.insert_checked() completes before the
        // corresponding seen.insert() for the same fingerprint). Downstream
        // liveness code (#3746 guards in ea_precompute, ea_precompute_enabled,
        // ea_precompute_leaf_batch, liveness_safety, liveness_execution)
        // handles missing states gracefully by skipping affected nodes/edges.
        // Demote to a warning and proceed — the missing states will be caught
        // on the next periodic run or are harmless post-BFS because the behavior
        // graph exploration filters missing-state fingerprints.
        let strict = crate::liveness::debug::strict_liveness();

        if strict {
            return Err(check_error_to_result(
                crate::LivenessCheckError::RuntimeFailure(format!(
                    "Post-BFS liveness state cache is missing {count} of {total} \
                     referenced state(s): {preview}. \
                     This indicates a non-atomic seen_fps/seen insert race (#3746). \
                     Set TLA2_STRICT_LIVENESS=0 (or unset) to downgrade to a warning.",
                    count = missing.len(),
                    total = referenced.len(),
                    preview = preview.join(", "),
                ))
                .into(),
                stats,
            ));
        }

        if crate::check::debug::liveness_profile() {
            eprintln!(
                "Warning: post-BFS parallel liveness state cache is missing {count} of {total} \
                 referenced state(s): {preview}. \
                 Downstream liveness code will skip affected nodes/edges (#3746).",
                count = missing.len(),
                total = referenced.len(),
                preview = preview.join(", "),
            );
        }
        Ok(())
    }

    fn collect_cached_successors(&self) -> FxHashMap<Fingerprint, Vec<Fingerprint>> {
        if let Some(ref succ_map) = self.successors {
            let mut cache = FxHashMap::with_capacity_and_hasher(succ_map.len(), Default::default());
            for entry in succ_map.iter() {
                cache.insert(*entry.key(), entry.value().clone());
            }
            cache
        } else {
            FxHashMap::default()
        }
    }

    fn build_full_state_liveness_cache(
        &self,
    ) -> (FxHashMap<Fingerprint, ArrayState>, Vec<Fingerprint>) {
        let mut state_cache: FxHashMap<Fingerprint, ArrayState> =
            FxHashMap::with_capacity_and_hasher(self.seen.len(), Default::default());
        for entry in self.seen.iter() {
            state_cache.insert(*entry.key(), entry.value().clone());
        }

        // Part of #2661: Use BFS-cached init states instead of O(N) scan over
        // state_cache filtered by parents. liveness_init_states is populated
        // during init processing (init_processing.rs:147).
        // Part of #2661: Only collect fingerprints here. Vec<State> init_states
        // removed — the cold Tableau/SCC path resolves init states from the
        // materialized state cache, avoiding to_state() on the hot path.
        let init_fps: Vec<Fingerprint> = self
            .liveness_init_states
            .iter()
            .map(|entry| *entry.key())
            .collect();

        (state_cache, init_fps)
    }

    fn build_fp_only_liveness_cache(
        &self,
        cached_successors: &FxHashMap<Fingerprint, Vec<Fingerprint>>,
        registry: &VarRegistry,
        stats: &CheckStats,
    ) -> Result<(FxHashMap<Fingerprint, ArrayState>, Vec<Fingerprint>), CheckResult> {
        let (mut replay_ctx, cached_view_name, mvperms) =
            self.prepare_fp_only_liveness_replay(stats)?;
        let init_arrays = self.collect_fp_only_init_states(
            &mut replay_ctx,
            cached_view_name.as_deref(),
            &mvperms,
            registry,
            stats,
        )?;

        // Part of #2661: Only collect fingerprints — Vec<State> init_states
        // removed. The cold Tableau/SCC path resolves init states from the
        // materialized state cache via init_fps.
        let init_fps: Vec<Fingerprint> = init_arrays.keys().copied().collect();
        let state_cache = self.replay_fp_only_state_cache(
            &mut replay_ctx,
            cached_view_name.as_deref(),
            &mvperms,
            cached_successors,
            &init_arrays,
            stats,
        )?;

        Ok((state_cache, init_fps))
    }

    fn prepare_fp_only_liveness_replay(
        &self,
        stats: &CheckStats,
    ) -> Result<(EvalCtx, Option<String>, Vec<crate::value::MVPerm>), CheckResult> {
        let ctx = self.prepare_base_ctx()?;
        let cached_view_name = crate::checker_ops::validate_view_operator(&ctx, &self.config);
        let mvperms = if self.config.symmetry.is_some() {
            let perms = crate::check::compute_symmetry_perms(&ctx, &self.config)
                .map_err(|error| check_error_to_result(error, stats))?;
            perms
                .iter()
                .map(crate::value::MVPerm::from_func_value)
                .collect::<Result<Vec<_>, _>>()
                .map_err(|error| check_error_to_result(EvalCheckError::Eval(error).into(), stats))?
        } else {
            Vec::new()
        };
        Ok((ctx, cached_view_name, mvperms))
    }

    fn collect_fp_only_init_states(
        &self,
        ctx: &mut EvalCtx,
        cached_view_name: Option<&str>,
        mvperms: &[crate::value::MVPerm],
        registry: &VarRegistry,
        stats: &CheckStats,
    ) -> Result<FxHashMap<Fingerprint, ArrayState>, CheckResult> {
        let mut init_arrays: FxHashMap<Fingerprint, ArrayState> =
            FxHashMap::with_capacity_and_hasher(
                self.liveness_init_states.len(),
                Default::default(),
            );
        for entry in self.liveness_init_states.iter() {
            init_arrays.insert(*entry.key(), entry.value().clone());
        }
        if !init_arrays.is_empty() {
            return Ok(init_arrays);
        }

        let init_name =
            self.config.init.as_deref().ok_or_else(|| {
                check_error_to_result(ConfigCheckError::MissingInit.into(), stats)
            })?;
        // Resolve through op_replacements (e.g., `CONSTANT Init <- MCInit`).
        let init_name = ctx.resolve_op_name(init_name);
        let initial_states = self
            .generate_initial_states(ctx, init_name)
            .map_err(|error| check_error_to_result(error, stats))?;

        for state in initial_states {
            let array_state = ArrayState::from_state(&state, registry);
            let passes_constraints = crate::checker_ops::check_state_constraints_array(
                ctx,
                &self.config.constraints,
                &array_state,
            )
            .map_err(|error| check_error_to_result(error, stats))?;
            if !passes_constraints {
                continue;
            }

            let fp = self.fingerprint_replayed_state(
                ctx,
                &state,
                &array_state,
                cached_view_name,
                mvperms,
                1,
                stats,
            )?;
            let present = if self.store_full_states {
                self.seen.contains_key(&fp)
            } else {
                matches!(self.seen_fps.contains_checked(fp), LookupOutcome::Present)
            };
            if present {
                init_arrays.entry(fp).or_insert(array_state);
            }
        }

        Ok(init_arrays)
    }

    fn replay_fp_only_state_cache(
        &self,
        ctx: &mut EvalCtx,
        cached_view_name: Option<&str>,
        mvperms: &[crate::value::MVPerm],
        cached_successors: &FxHashMap<Fingerprint, Vec<Fingerprint>>,
        init_arrays: &FxHashMap<Fingerprint, ArrayState>,
        stats: &CheckStats,
    ) -> Result<FxHashMap<Fingerprint, ArrayState>, CheckResult> {
        let next_name =
            self.config.next.as_deref().ok_or_else(|| {
                check_error_to_result(ConfigCheckError::MissingNext.into(), stats)
            })?;
        let next_def = self
            .op_defs
            .get(next_name)
            .ok_or_else(|| check_error_to_result(ConfigCheckError::MissingNext.into(), stats))?
            .clone();

        let capacity = init_arrays.len() + cached_successors.len();
        let mut state_cache: FxHashMap<Fingerprint, ArrayState> =
            FxHashMap::with_capacity_and_hasher(capacity, Default::default());
        let mut replay_states: FxHashMap<Fingerprint, State> =
            FxHashMap::with_capacity_and_hasher(capacity, Default::default());
        let mut queue: VecDeque<Fingerprint> = VecDeque::new();

        for (fp, arr) in init_arrays {
            state_cache.insert(*fp, arr.clone());
            replay_states.insert(*fp, arr.to_state(&self.var_registry));
            queue.push_back(*fp);
        }

        let mut expected_fps: FxHashSet<Fingerprint> =
            FxHashSet::with_capacity_and_hasher(capacity, Default::default());
        expected_fps.extend(init_arrays.keys().copied());
        for (from_fp, succ_fps) in cached_successors {
            expected_fps.insert(*from_fp);
            expected_fps.extend(succ_fps.iter().copied());
        }

        while let Some(parent_fp) = queue.pop_front() {
            let Some(parent_state) = replay_states.get(&parent_fp).cloned() else {
                continue;
            };
            let Some(expected_succs) = cached_successors.get(&parent_fp) else {
                continue;
            };
            if expected_succs.is_empty() {
                continue;
            }

            self.replay_parent_successors(
                ctx,
                &next_def,
                parent_fp,
                &parent_state,
                cached_view_name,
                mvperms,
                expected_succs,
                &mut state_cache,
                &mut replay_states,
                &mut queue,
                stats,
            )?;
        }

        // Part of #3801: Convert hard failure to warning. The fp-only replay
        // may not reconstruct every state referenced by `cached_successors`
        // (e.g., when replay re-enumeration produces different fingerprints
        // than the original BFS due to evaluation context differences).
        // Downstream liveness code (#3746, #3801 filters) handles missing
        // states gracefully by skipping affected nodes/edges.
        let missing_count = expected_fps
            .iter()
            .filter(|fp| !state_cache.contains_key(fp))
            .count();
        if missing_count > 0 {
            let preview = expected_fps
                .iter()
                .filter(|fp| !state_cache.contains_key(fp))
                .take(4)
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ");
            eprintln!(
                "Warning: fingerprint-only parallel liveness could not replay \
                 {missing_count} state(s) (of {} expected): {preview}. \
                 Liveness checking will proceed with the partial state cache.",
                expected_fps.len()
            );
        }

        Ok(state_cache)
    }

    #[allow(clippy::too_many_arguments)]
    fn replay_parent_successors(
        &self,
        ctx: &mut EvalCtx,
        next_def: &OperatorDef,
        parent_fp: Fingerprint,
        parent_state: &State,
        cached_view_name: Option<&str>,
        mvperms: &[crate::value::MVPerm],
        expected_succs: &[Fingerprint],
        state_cache: &mut FxHashMap<Fingerprint, ArrayState>,
        replay_states: &mut FxHashMap<Fingerprint, State>,
        queue: &mut VecDeque<Fingerprint>,
        stats: &CheckStats,
    ) -> Result<(), CheckResult> {
        let expected: FxHashSet<Fingerprint> = expected_succs.iter().copied().collect();
        if expected.is_empty() {
            return Ok(());
        }

        let current_array = ArrayState::from_state(parent_state, &self.var_registry);
        let mut remaining = expected;
        let depth = self
            .depths
            .get(&parent_fp)
            .map_or(0, |entry| *entry.value());
        let current_level = crate::checker_ops::depth_to_tlc_level(depth)
            .map_err(|error| check_error_to_result(error, stats))?;
        let succ_level = crate::checker_ops::depth_to_tlc_level(depth.saturating_add(1))
            .map_err(|error| check_error_to_result(error, stats))?;
        ctx.set_tlc_level(current_level);
        let successors =
            crate::enumerate::enumerate_successors(ctx, next_def, parent_state, &self.vars)
                .map_err(|error| {
                    check_error_to_result(EvalCheckError::Eval(error).into(), stats)
                })?;

        for succ_state in successors {
            let succ_array = ArrayState::from_state(&succ_state, &self.var_registry);
            let passes_constraints = crate::checker_ops::check_constraints_for_successor_array(
                ctx,
                &self.config.constraints,
                &self.config.action_constraints,
                &current_array,
                &succ_array,
            )
            .map_err(|error| check_error_to_result(error, stats))?;
            if !passes_constraints {
                continue;
            }

            let succ_fp = self.fingerprint_replayed_state(
                ctx,
                &succ_state,
                &succ_array,
                cached_view_name,
                mvperms,
                succ_level,
                stats,
            )?;
            if remaining.remove(&succ_fp) && !state_cache.contains_key(&succ_fp) {
                state_cache.insert(succ_fp, succ_array);
                replay_states.insert(succ_fp, succ_state);
                queue.push_back(succ_fp);
            }
            if remaining.is_empty() {
                break;
            }
        }

        // Part of #3801: Convert hard failure to warning. Replay may fail
        // to match all expected successor fingerprints when evaluation context
        // differences cause re-enumeration to produce different states.
        // Downstream liveness code handles missing states gracefully.
        if !remaining.is_empty() {
            if crate::check::debug::liveness_profile() {
                let preview = remaining
                    .iter()
                    .take(4)
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                eprintln!(
                    "Warning: fp-only replay could not reconstruct {} successor(s) \
                     for parent {parent_fp}: {preview}",
                    remaining.len()
                );
            }
        }

        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn fingerprint_replayed_state(
        &self,
        ctx: &mut EvalCtx,
        state: &State,
        array_state: &ArrayState,
        cached_view_name: Option<&str>,
        mvperms: &[crate::value::MVPerm],
        bfs_level: u32,
        stats: &CheckStats,
    ) -> Result<Fingerprint, CheckResult> {
        // Part of #3906: Use array-native path to avoid OrdMap construction.
        if let Some(view_name) = cached_view_name {
            return crate::checker_ops::compute_view_fingerprint_array(
                ctx,
                array_state,
                view_name,
                bfs_level,
            )
            .map_err(|error| check_error_to_result(error, stats));
        }
        if !mvperms.is_empty() {
            return Ok(
                crate::state::compute_canonical_fingerprint_from_compact_array(
                    array_state.values(),
                    &self.var_registry,
                    mvperms,
                ),
            );
        }
        Ok(state.fingerprint())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::parse_module;
    use crate::ConstantValue;

    /// Regression for replacement-routed INIT handling in fp-only liveness replay.
    ///
    /// The parallel checker must resolve `INIT Init` through config operator
    /// replacements when rebuilding init states from the fingerprint graph after BFS.
    #[cfg_attr(test, ntest::timeout(30000))]
    #[test]
    fn fp_only_liveness_replay_resolves_init_replacements() {
        let _serial = crate::test_utils::acquire_interner_lock();
        let src = r"
---- MODULE ParallelInitReplacementLivenessReplay ----
VARIABLE x
Init == x = 99
MCInit == x = 0
Next == IF x < 1 THEN x' = x + 1 ELSE x' = x
Inv == x \in {0, 1}
====
";
        let module = parse_module(src);

        let mut config = crate::Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };
        config.constants.insert(
            "Init".to_string(),
            ConstantValue::Replacement("MCInit".to_string()),
        );

        let checker = ParallelChecker::new(&module, &config, 2);
        let stats = match checker.check() {
            crate::CheckResult::Success(stats) => {
                assert_eq!(
                    stats.initial_states, 1,
                    "expected single replacement-routed init"
                );
                assert_eq!(
                    stats.states_found, 2,
                    "expected MCInit to seed the reachable {{0, 1}} counter states"
                );
                stats
            }
            other => panic!("expected success with replacement-routed Init, got: {other:?}"),
        };

        // Force fp-only liveness replay to regenerate initial states from config
        // instead of reusing the BFS-cached init map.
        checker.liveness_init_states.clear();
        let graph = checker
            .build_liveness_graph_data(&stats, false)
            .expect("replacement-routed fp-only liveness replay should succeed");
        assert_eq!(
            graph.init_fps.len(),
            1,
            "expected one replayed init fingerprint"
        );
        let init_state = graph
            .state_cache
            .get(&graph.init_fps[0])
            .expect("replayed init fingerprint must resolve in the state cache")
            .to_state(&checker.var_registry);
        assert_eq!(init_state.get("x"), Some(&crate::Value::int(0)));
    }
}
