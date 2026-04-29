// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Checkpoint/resume support for model checking.

use super::super::{
    ArrayState, CheckError, InsertOutcome, ModelChecker, State, TraceLocationStorage,
};
use crate::ConfigCheckError;
use std::collections::VecDeque;

impl<'a> ModelChecker<'a> {
    /// Create a checkpoint of the current model checking state.
    ///
    /// This captures all data needed to resume model checking later:
    /// - Seen fingerprints
    /// - Frontier states (from the provided queue)
    /// - Parent pointers
    /// - Depth tracking
    /// - Statistics
    ///
    /// # Arguments
    /// * `frontier` - The current BFS frontier (states to explore)
    /// * `spec_path` - Optional spec file path for verification on resume
    /// * `config_path` - Optional config file path for verification on resume
    pub(crate) fn create_checkpoint(
        &mut self,
        frontier: &VecDeque<State>,
        spec_path: Option<&str>,
        config_path: Option<&str>,
    ) -> Result<crate::checkpoint::Checkpoint, CheckError> {
        use crate::checkpoint::{Checkpoint, CheckpointStats};

        let mut checkpoint = Checkpoint::new().with_paths(spec_path, config_path);

        // Populate content hashes from the pre-computed values in CheckpointState.
        // These were computed eagerly at set_checkpoint_paths() time so that the
        // hash reflects the file contents as they were when checking started.
        checkpoint
            .metadata
            .spec_hash
            .clone_from(&self.checkpoint.spec_hash);
        checkpoint
            .metadata
            .config_hash
            .clone_from(&self.checkpoint.config_hash);

        // Part of #2656: Notify storage backend that a checkpoint is starting.
        // For mmap backends, this flushes pending writes to disk so the
        // fingerprint data is consistent before we extract from the depth map.
        if let Err(fault) = self.state_storage.seen_fps.begin_checkpoint() {
            return Err(crate::checker_ops::storage_fault_to_check_error(
                &*self.state_storage.seen_fps,
                &fault,
            ));
        }

        // Part of #2353: Verify coherence between trace.depths (which we use as
        // the fingerprint source) and the authoritative fingerprint storage.
        // A mismatch means depth bookkeeping has diverged from membership tracking,
        // so the checkpoint would under- or over-snapshot the visited set.
        let depths_count = self.trace.depths.len();
        let fps_count = self.state_storage.seen_fps.len();
        if depths_count != fps_count {
            return Err(ConfigCheckError::Setup(format!(
                "Checkpoint coherence failure: trace.depths has {depths_count} entries \
                 but fingerprint storage has {fps_count} entries. The checkpoint would \
                 snapshot an incomplete visited set. This indicates a bug in depth \
                 bookkeeping or fingerprint storage."
            ))
            .into());
        }

        // Collect fingerprints from depths keys.
        //
        // We intentionally avoid relying on iterating the fingerprint set because:
        // - `MmapFingerprintSet` doesn't support iteration
        // - After resume, we may have fingerprints restored without full states
        checkpoint.fingerprints = self.trace.depths.keys().copied().collect();

        // Copy frontier states
        checkpoint.frontier = frontier.iter().cloned().collect();

        // Part of #3178: extract parent pointers from trace file (cold path).
        if let Some(ref mut trace_file) = self.trace.trace_file {
            match trace_file.build_parents_map() {
                Ok(parents) => checkpoint.parents = parents,
                Err(_) => {
                    self.trace.trace_degraded = true;
                }
            }
        }

        // Copy depths
        checkpoint.depths = self.trace.depths.iter().map(|(k, v)| (*k, *v)).collect();

        // Set stats
        checkpoint.metadata.stats = CheckpointStats::from(&self.stats);
        checkpoint.metadata.stats.frontier_size = frontier.len();

        // Persist first_violation from continue_on_error mode
        checkpoint
            .first_violation
            .clone_from(&self.exploration.first_violation);
        checkpoint
            .first_action_property_violation
            .clone_from(&self.exploration.first_action_property_violation);

        // Part of #2656: Notify storage backend that checkpoint data is complete.
        if let Err(fault) = self.state_storage.seen_fps.commit_checkpoint() {
            return Err(crate::checker_ops::storage_fault_to_check_error(
                &*self.state_storage.seen_fps,
                &fault,
            ));
        }

        Ok(checkpoint)
    }

    /// Restore model checking state from a checkpoint.
    ///
    /// This restores:
    /// - Seen fingerprints to the fingerprint set
    /// - Parent pointers
    /// - Depth tracking
    /// - Statistics
    ///
    /// The frontier is returned separately so the caller can resume BFS.
    ///
    /// # Returns
    /// The frontier states to continue BFS from, or an error if VIEW
    /// fingerprinting fails (indicates violated BFS precondition).
    pub(crate) fn restore_from_checkpoint(
        &mut self,
        checkpoint: crate::checkpoint::Checkpoint,
    ) -> Result<VecDeque<State>, CheckError> {
        // Clear in-memory state maps (checkpoint restores these).
        self.state_storage.seen.clear();
        self.trace.depths.clear();
        self.liveness_cache.successors.clear();
        self.liveness_cache.successor_witnesses.clear();
        // Bitmask maps cleared (inline_state_results/inline_action_results removed).
        self.liveness_cache.inline_state_bitmasks.clear();
        self.liveness_cache.inline_action_bitmasks.clear();
        self.liveness_cache.inline_property_plans.clear();

        // Restore fingerprints to the seen set
        for fp in &checkpoint.fingerprints {
            // Mark as seen in the fingerprint set
            match self.state_storage.seen_fps.insert_checked(*fp) {
                InsertOutcome::Inserted | InsertOutcome::AlreadyPresent => {}
                InsertOutcome::StorageFault(fault) => {
                    // Part of #2056: Use shared conversion helper.
                    return Err(crate::checker_ops::storage_fault_to_check_error(
                        &*self.state_storage.seen_fps,
                        &fault,
                    ));
                }
                _ => unreachable!(),
            }

            // If we have full states mode, we don't have the actual states
            // So we can't populate self.state_storage.seen - trace reconstruction will need
            // to use fingerprint replay
        }

        // Part of #2656: Notify storage backend that fingerprint replay is complete.
        // Backends may rebuild indexes or finalize internal recovery state.
        if let Err(fault) = self.state_storage.seen_fps.recover_checkpoint() {
            return Err(crate::checker_ops::storage_fault_to_check_error(
                &*self.state_storage.seen_fps,
                &fault,
            ));
        }

        // Part of #3178: restore parent pointers into a fresh trace file.
        // Create trace file first, then write checkpoint parents into it.
        self.maybe_auto_create_trace_file();
        if !checkpoint.parents.is_empty() {
            if let Some(ref mut trace_file) = self.trace.trace_file {
                match trace_file.restore_parents(&checkpoint.parents) {
                    Ok(offset_map) => {
                        for (fp, loc) in offset_map {
                            self.trace.trace_locs.insert(fp, loc);
                        }
                    }
                    Err(_) => {
                        self.trace.trace_degraded = true;
                    }
                }
            }
        }

        // Restore depths
        let checkpoint_depth_keys: crate::state::FpHashSet =
            checkpoint.depths.iter().map(|(fp, _)| *fp).collect();
        self.trace.depths = checkpoint.depths.into_iter().collect();

        // Validate frontier/depth coherence: every frontier state must have a depth entry.
        // Part of #2233: checkpoint corruption or partial metadata could leave frontier states
        // without depth entries, causing silent coercion to depth 0 in the BFS dequeue loop.
        //
        // Fingerprint computation must match BFS: convert State → ArrayState and use
        // array_state_fingerprint(). Deserialized States use compute_fingerprint() (OrdMap
        // iteration order) which can differ from compute_fingerprint_from_array() (registry
        // order) when variable registration order ≠ alphabetical order.
        let registry = self.ctx.var_registry().clone();

        // Reconstruct the flat-state fingerprint domain from the saved frontier
        // before validating or requeueing states. Fresh runs infer this after
        // init-state solving; resume has to recover the same layout from the
        // checkpointed states or flat-primary checkpoints will be keyed under
        // a different fingerprint domain on restore.
        let frontier_arrays: Vec<ArrayState> = checkpoint
            .frontier
            .iter()
            .take(1024)
            .map(|state| ArrayState::from_state(state, &registry))
            .collect();
        if let Some(first) = frontier_arrays.first() {
            if frontier_arrays.len() >= 2 {
                self.infer_flat_state_layout_from_wavefront(&frontier_arrays);
            } else {
                self.infer_flat_state_layout(first);
            }

            if self.uses_compiled_bfs_fingerprint_domain() {
                let frontier_matches_compiled_domain = frontier_arrays.iter().try_fold(
                    true,
                    |all_match, state| -> Result<bool, CheckError> {
                        if !all_match {
                            return Ok(false);
                        }
                        let mut array_state = state.clone();
                        let fp = self.array_state_fingerprint(&mut array_state)?;
                        Ok(checkpoint_depth_keys.contains(&fp))
                    },
                )?;
                if !frontier_matches_compiled_domain {
                    self.flat_state_primary = false;
                }
            }
        }

        for state in &checkpoint.frontier {
            let mut array_state = ArrayState::from_state(state, &registry);
            let fp = self.array_state_fingerprint(&mut array_state)?;
            if !self.trace.depths.contains_key(&fp) {
                return Err(ConfigCheckError::Setup(format!(
                    "Checkpoint depth metadata is incomplete: frontier state with \
                     fingerprint {fp} has no depth entry. The checkpoint may be \
                     corrupted or was saved with inconsistent depth tracking."
                ))
                .into());
            }
        }

        // Restore statistics
        self.stats.states_found = checkpoint.metadata.stats.states_found;
        self.stats.initial_states = checkpoint.metadata.stats.initial_states;
        self.stats.transitions = checkpoint.metadata.stats.transitions;
        self.stats.max_depth = checkpoint.metadata.stats.max_depth;

        // If configured to store full states, keep the frontier states in memory.
        // This improves trace quality immediately after resume without requiring replay.
        if self.state_storage.store_full_states {
            for state in &checkpoint.frontier {
                // Compute fingerprint via ArrayState to match BFS keying.
                let mut array_state = ArrayState::from_state(state, &registry);
                let fp = self.array_state_fingerprint(&mut array_state)?;
                self.state_storage.seen.insert(fp, array_state);
            }
        }

        // Restore first_violation from continue_on_error mode
        self.exploration.first_violation = checkpoint.first_violation;
        self.exploration.first_action_property_violation =
            checkpoint.first_action_property_violation;

        // Return frontier for caller to resume BFS
        Ok(checkpoint.frontier.into_iter().collect())
    }
}
