// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parallel checkpoint create/save/resume support.
//!
//! Part of #2749: Creates a `Checkpoint` by snapshotting DashMap state
//! while all workers are suspended at the barrier. Also provides the
//! resume path: loading a checkpoint and restoring DashMap state.

use super::ParallelChecker;
use crate::check::{CheckError, CheckResult, CheckStats, Trace};
use crate::checkpoint::{Checkpoint, CheckpointStats};
use crate::state::Fingerprint;
use crate::storage::InsertOutcome;
use crate::ConfigCheckError;
use std::path::Path;
use std::sync::atomic::Ordering;

fn resume_property_classification_error(result: CheckResult) -> std::io::Error {
    match result {
        CheckResult::Error { error, .. } => std::io::Error::other(format!(
            "parallel resume property classification failed: {error}"
        )),
        other => std::io::Error::other(format!(
            "parallel resume property classification produced unexpected result: {other:?}"
        )),
    }
}

fn resume_action_detection_error(result: CheckResult) -> std::io::Error {
    match result {
        CheckResult::Error { error, .. } => {
            std::io::Error::other(format!("parallel resume action detection failed: {error}"))
        }
        other => std::io::Error::other(format!(
            "parallel resume action detection produced unexpected result: {other:?}"
        )),
    }
}

impl ParallelChecker {
    /// Create a checkpoint from the current parallel checker state.
    ///
    /// **Precondition:** All workers MUST be suspended at the barrier before
    /// calling this method. No concurrent mutations to `seen`, `parents`,
    /// `depths`, or `seen_fps` may occur.
    ///
    /// This mirrors the sequential `ModelChecker::create_checkpoint()` but
    /// reads from DashMaps instead of HashMaps.
    /// Part of #2893: Validate that the FP backend supports collect_fingerprints.
    /// Future checkpoint serialization (#2749) may need to enumerate all seen
    /// fingerprints. Catch misconfigured backends at checkpoint time.
    fn assert_collect_fingerprints_supported(&self) {
        debug_assert!(
            self.seen_fps.collect_fingerprints().is_ok(),
            "checkpoint requires FingerprintSet backend with working collect_fingerprints"
        );
    }

    pub(crate) fn create_checkpoint(&self) -> Result<Checkpoint, CheckError> {
        self.assert_collect_fingerprints_supported();

        let mut checkpoint = Checkpoint::new().with_paths(
            self.checkpoint_spec_path.as_deref(),
            self.checkpoint_config_path.as_deref(),
        );

        // Notify storage backend that a checkpoint is starting.
        // For mmap backends, this flushes pending writes.
        if let Err(fault) = self.seen_fps.begin_checkpoint() {
            return Err(crate::checker_ops::storage_fault_to_check_error(
                &*self.seen_fps,
                &fault,
            ));
        }

        // Coherence check: depths must match the active state count.
        // In full-state mode, states are in `seen` (DashMap); in fingerprint-only
        // mode, states are in `seen_fps`. Use `states_count()` which already
        // dispatches on `store_full_states`.
        let depths_count = self.depths.len();
        let states_count = self.states_count();
        if depths_count != states_count {
            return Err(ConfigCheckError::Setup(format!(
                "Parallel checkpoint coherence failure: depths has {depths_count} entries \
                 but state storage has {states_count} entries. The checkpoint would \
                 snapshot an incomplete visited set."
            ))
            .into());
        }

        // Extract fingerprints and depths from the DashMap.
        // This is O(N) with N = states visited.
        let mut fingerprints = Vec::with_capacity(depths_count);
        let mut depths = std::collections::HashMap::with_capacity(depths_count);
        for entry in self.depths.iter() {
            fingerprints.push(*entry.key());
            depths.insert(*entry.key(), *entry.value());
        }
        checkpoint.fingerprints = fingerprints;
        checkpoint.depths = depths;

        // Part of #3178: Build parent map from append-only log.
        checkpoint.parents = self.parent_log.build_map().into_iter().collect();

        // Frontier is empty in parallel mode — on resume, all states are
        // re-explored from initial states with the fingerprint set as filter.
        // See design doc: designs/2026-03-01-2749-parallel-checkpoint-architecture.md
        checkpoint.frontier = Vec::new();

        // Stats from atomics.
        checkpoint.metadata.stats = CheckpointStats {
            states_found: self.states_count(),
            initial_states: 0, // Will be recomputed on resume.
            transitions: self
                .total_transitions
                .load(std::sync::atomic::Ordering::SeqCst),
            max_depth: self.max_depth.load(std::sync::atomic::Ordering::SeqCst),
            frontier_size: 0, // No frontier in parallel checkpoint.
        };

        // Persist first_violation and trace from continue_on_error mode.
        self.collect_violation_data(&mut checkpoint);

        // Notify storage backend that checkpoint data is complete.
        if let Err(fault) = self.seen_fps.commit_checkpoint() {
            return Err(crate::checker_ops::storage_fault_to_check_error(
                &*self.seen_fps,
                &fault,
            ));
        }

        Ok(checkpoint)
    }

    /// Part of #3112: Collect first_violation and its trace into a checkpoint.
    ///
    /// If `store_full_states` is enabled, captures the violation trace at
    /// checkpoint creation time. On resume, the stored trace is used directly
    /// instead of trying to reconstruct from the (empty) `seen` DashMap.
    fn collect_violation_data(&self, checkpoint: &mut Checkpoint) {
        checkpoint.first_violation = self.first_violation.get().cloned();
        checkpoint.first_action_property_violation =
            self.first_action_property_violation.get().cloned();
        let trace_fp = checkpoint
            .first_violation
            .as_ref()
            .map(|(_, fp)| *fp)
            .or_else(|| {
                checkpoint
                    .first_action_property_violation
                    .as_ref()
                    .map(|(_, fp)| *fp)
            });
        if let Some(fp) = trace_fp {
            if let Some(trace) = self.first_violation_trace.get() {
                if !trace.is_empty() {
                    checkpoint.first_violation_trace = trace.clone();
                    return;
                }
            }
            if self.store_full_states {
                let trace = self.reconstruct_trace(fp);
                checkpoint.first_violation_trace = trace.states;
            }
        }
    }

    /// Check if checkpointing is configured.
    pub(crate) fn checkpoint_enabled(&self) -> bool {
        self.checkpoint_dir.is_some()
    }

    /// Part of #3233: depth tracking is needed for checkpoints and fp-only liveness replay.
    pub(crate) fn track_depths_enabled(&self) -> bool {
        self.checkpoint_enabled() || self.successors.is_some()
    }

    /// Validate that the checkpoint's spec/config paths match the current checker's.
    ///
    /// Part of #2749: Mirrors sequential `validate_checkpoint_metadata_identity`.
    fn validate_checkpoint_identity(&self, checkpoint: &Checkpoint) -> Result<(), std::io::Error> {
        Self::validate_path_field(
            "spec",
            self.checkpoint_spec_path.as_deref(),
            checkpoint.metadata.spec_path.as_deref(),
        )?;
        Self::validate_path_field(
            "config",
            self.checkpoint_config_path.as_deref(),
            checkpoint.metadata.config_path.as_deref(),
        )?;
        Ok(())
    }

    /// Check a single path field for identity.
    ///
    /// Matches the sequential checker's `validate_checkpoint_path_identity`:
    /// if the current checker has a path set, the checkpoint must have a matching one.
    fn validate_path_field(
        label: &str,
        current: Option<&str>,
        checkpoint: Option<&str>,
    ) -> Result<(), std::io::Error> {
        match (current, checkpoint) {
            (None, _) => Ok(()),
            (Some(cur), Some(cp)) => {
                if cur == cp {
                    return Ok(());
                }
                // Try canonical path comparison for symlinks/relative paths.
                match (std::fs::canonicalize(cur), std::fs::canonicalize(cp)) {
                    (Ok(a), Ok(b)) if a == b => Ok(()),
                    _ => Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        format!(
                            "checkpoint {label} path mismatch: \
                             current={cur:?}, checkpoint={cp:?}"
                        ),
                    )),
                }
            }
            (Some(cur), None) => Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!(
                    "checkpoint missing {label} path metadata; \
                     current run expects {cur:?}"
                ),
            )),
        }
    }

    /// Restore parallel checker state from a checkpoint.
    ///
    /// Populates `seen_fps`, `parents`, `depths` from checkpoint data.
    /// Called before any BFS work; workers have not been spawned yet.
    ///
    /// Part of #2749 Step 5: Parallel checkpoint resume.
    fn restore_from_checkpoint(&self, checkpoint: &Checkpoint) -> Result<(), std::io::Error> {
        // Populate seen_fps from checkpoint fingerprints.
        for fp in &checkpoint.fingerprints {
            match self.seen_fps.insert_checked(*fp) {
                InsertOutcome::Inserted | InsertOutcome::AlreadyPresent => {}
                InsertOutcome::StorageFault(fault) => {
                    return Err(std::io::Error::other(format!(
                        "fingerprint restore failed: {fault:?}"
                    )));
                }
                _ => unreachable!(),
            }
        }

        // Notify storage backend that fingerprint replay is complete.
        if let Err(fault) = self.seen_fps.recover_checkpoint() {
            return Err(std::io::Error::other(format!(
                "fingerprint set recovery failed: {fault:?}"
            )));
        }

        // Part of #3178: Load parent pointers into append-only log.
        self.parent_log
            .extend(checkpoint.parents.iter().map(|(&fp, &parent)| (fp, parent)));

        // Populate depths DashMap.
        for (fp, depth) in &checkpoint.depths {
            self.depths.insert(*fp, *depth);
        }

        // If store_full_states is enabled, populate seen DashMap from
        // frontier states (frontier is empty for parallel checkpoints,
        // but this handles cross-format compatibility with sequential
        // checkpoints that include frontier states).
        if self.store_full_states {
            for state in &checkpoint.frontier {
                let mut array_state =
                    crate::state::ArrayState::from_state(state, &self.var_registry);
                let fp = array_state.fingerprint(&self.var_registry);
                self.seen.insert(fp, array_state);
            }
        }

        // Restore stats into atomics.
        self.admitted_states
            .store(checkpoint.metadata.stats.states_found, Ordering::SeqCst);
        self.max_depth
            .store(checkpoint.metadata.stats.max_depth, Ordering::SeqCst);
        self.total_transitions
            .store(checkpoint.metadata.stats.transitions, Ordering::SeqCst);

        // Restore first_violation from continue-on-error mode.
        if let Some(ref violation) = checkpoint.first_violation {
            let _ = self.first_violation.set(violation.clone());
        }
        if let Some(ref violation) = checkpoint.first_action_property_violation {
            let _ = self.first_action_property_violation.set(violation.clone());
        }

        Ok(())
    }

    /// Resume parallel model checking from a previously saved checkpoint.
    ///
    /// Part of #2749: Loads checkpoint data and either returns a saved
    /// violation or re-runs BFS from scratch.
    ///
    /// The parallel checkpoint cannot save the BFS frontier (crossbeam deques
    /// are `!Send`). TLC solves this by using a serializable `DiskStateQueue`,
    /// but our work-stealing deques don't support iteration or serialization.
    ///
    /// **Resume strategy:**
    /// 1. If the checkpoint contains a saved violation (continue-on-error mode),
    ///    restore parent pointers for trace reconstruction and return it.
    /// 2. Otherwise, re-run BFS from scratch via `run_check_inner()`. The
    ///    checkpoint's progress info is displayed for user awareness. Future
    ///    optimization: save frontier fingerprints during worker suspension.
    ///
    /// # Returns
    ///
    /// * `Ok(CheckResult::InvariantViolation/PropertyViolation { .. })` — saved violation from continue-on-error
    /// * `Ok(CheckResult)` — result from fresh BFS re-exploration
    /// * `Err(io::Error)` — checkpoint loading or validation failed
    pub fn check_with_resume<P: AsRef<Path>>(
        &self,
        checkpoint_dir: P,
    ) -> Result<CheckResult, std::io::Error> {
        // One-shot guard (same as check()).
        assert!(
            !self.has_run.swap(true, Ordering::SeqCst),
            "ParallelChecker called more than once. \
             ParallelChecker is one-shot: create a new instance for each run (#1851)."
        );

        let mut checkpoint = Checkpoint::load(checkpoint_dir)?;
        self.validate_checkpoint_identity(&checkpoint)?;

        eprintln!(
            "Resuming from checkpoint: {} states, {} transitions, depth {}",
            checkpoint.metadata.stats.states_found,
            checkpoint.metadata.stats.transitions,
            checkpoint.metadata.stats.max_depth,
        );

        let take_saved_trace = |checkpoint: &mut Checkpoint, fallback_fp: Fingerprint| {
            if !checkpoint.first_violation_trace.is_empty() {
                Trace::from_states(std::mem::take(&mut checkpoint.first_violation_trace))
            } else {
                self.reconstruct_trace(fallback_fp)
            }
        };

        // If checkpoint has a saved violation (continue-on-error mode),
        // restore parent pointers for trace reconstruction and return it
        // immediately without re-exploring.
        if let Some((property, fp)) = checkpoint.first_action_property_violation.clone() {
            let (detected_actions, detected_action_ids) = self
                .detected_actions_for_resume()
                .map_err(resume_action_detection_error)?;
            let stats = CheckStats {
                states_found: checkpoint.metadata.stats.states_found,
                initial_states: checkpoint.metadata.stats.initial_states,
                transitions: checkpoint.metadata.stats.transitions,
                max_depth: checkpoint.metadata.stats.max_depth,
                detected_actions,
                detected_action_ids,
                ..Default::default()
            };

            self.restore_from_checkpoint(&checkpoint)?;
            let trace = take_saved_trace(&mut checkpoint, fp);
            return Ok(CheckResult::PropertyViolation {
                property,
                kind: crate::check::PropertyViolationKind::ActionLevel,
                trace,
                stats,
            });
        }

        if let Some((invariant, fp)) = checkpoint.first_violation.clone() {
            let (detected_actions, detected_action_ids) = self
                .detected_actions_for_resume()
                .map_err(resume_action_detection_error)?;
            let stats = CheckStats {
                states_found: checkpoint.metadata.stats.states_found,
                initial_states: checkpoint.metadata.stats.initial_states,
                transitions: checkpoint.metadata.stats.transitions,
                max_depth: checkpoint.metadata.stats.max_depth,
                detected_actions,
                detected_action_ids,
                ..Default::default()
            };

            // Restore parent pointers and full states for trace reconstruction.
            self.restore_from_checkpoint(&checkpoint)?;

            // Part of #3112: Use the stored violation trace if available.
            // The parallel checkpoint doesn't save full states in `seen`, so
            // `reconstruct_trace` would fail to look up states and emit a
            // misleading warning. The stored trace was collected at checkpoint
            // creation time when the states were still in memory.
            let trace = take_saved_trace(&mut checkpoint, fp);
            let is_property_state_violation =
                if self.config.properties.iter().any(|name| name == &invariant) {
                    self.state_property_violation_names_for_resume()
                        .map_err(resume_property_classification_error)?
                        .contains(&invariant)
                } else {
                    false
                };
            return Ok(if is_property_state_violation {
                CheckResult::PropertyViolation {
                    property: invariant,
                    kind: crate::check::PropertyViolationKind::StateLevel,
                    trace,
                    stats,
                }
            } else {
                CheckResult::InvariantViolation {
                    invariant,
                    trace,
                    stats,
                }
            });
        }

        // No saved violation: re-run BFS from scratch.
        //
        // The parallel checkpoint does not save the BFS frontier because
        // crossbeam Worker deques are !Send and cannot be iterated from
        // the main thread. TLC avoids this by using a DiskStateQueue that
        // supports serialization (see TLC ModelChecker.checkpoint() and
        // DiskStateQueue.beginChkpt()).
        //
        // Re-exploring from initial states with the restored fingerprint set
        // does NOT work: all states (including frontier) are in seen_fps,
        // so successors are rejected as duplicates and BFS terminates
        // immediately after processing initial states.
        //
        // Therefore, resume re-runs the full BFS. The checkpoint preserves:
        // - Progress info (displayed above for user awareness)
        // - Violation data (handled above for continue-on-error recovery)
        // - Future checkpoints will be saved during re-exploration if enabled
        eprintln!(
            "Note: parallel resume re-explores from scratch \
             (frontier serialization not yet supported)"
        );
        Ok(self.run_check_inner())
    }
}
