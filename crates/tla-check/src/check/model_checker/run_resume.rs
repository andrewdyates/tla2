// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Checkpoint-based resume for BFS model checking.
//!
//! Extracted from `run.rs` to reduce file size (Part of #1310).
//!
//! Part of #2356: the BFS loop is now delegated to `run_bfs_loop_core`
//! (the same loop used by non-resume BFS), eliminating ~150 lines of
//! resume-specific loop code.
//!
//! Part of #1812: post-loop finalization is now shared via
//! `finish_check_after_bfs(resume_mode=true)`, which rejects liveness
//! (not yet supported for resume) instead of running it.

use super::bfs::{BfsLoopOutcome, FingerprintOnlyStorage, FullStateStorage, NoTraceQueueEntry};
use super::{
    ArrayState, CheckResult, Fingerprint, ModelChecker, State, TraceLocationStorage, VecDeque,
};

struct ResumeGuardErrorStatsFlush {
    disarmed: bool,
}

impl ResumeGuardErrorStatsFlush {
    fn new() -> Self {
        Self { disarmed: false }
    }

    fn disarm(&mut self) {
        self.disarmed = true;
    }
}

impl Drop for ResumeGuardErrorStatsFlush {
    fn drop(&mut self) {
        if !self.disarmed {
            crate::guard_error_stats::emit_warning_and_reset();
        }
    }
}

impl<'a> ModelChecker<'a> {
    fn checkpoint_paths_match(current_path: &str, checkpoint_path: &str) -> bool {
        if current_path == checkpoint_path {
            return true;
        }

        match (
            std::fs::canonicalize(current_path),
            std::fs::canonicalize(checkpoint_path),
        ) {
            (Ok(current), Ok(checkpoint)) => current == checkpoint,
            _ => false,
        }
    }

    fn validate_checkpoint_path_identity(
        label: &str,
        current_path: Option<&str>,
        checkpoint_path: Option<&str>,
    ) -> std::io::Result<()> {
        match (current_path, checkpoint_path) {
            // If the caller did not provide current invocation metadata, keep legacy
            // behavior and skip identity checks for this field.
            (None, _) => Ok(()),
            (Some(current), Some(checkpoint)) => {
                if Self::checkpoint_paths_match(current, checkpoint) {
                    Ok(())
                } else {
                    Err(std::io::Error::new(
                        std::io::ErrorKind::InvalidData,
                        format!(
                            "checkpoint {label} path mismatch: checkpoint={checkpoint:?}, current={current:?}"
                        ),
                    ))
                }
            }
            (Some(current), None) => Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!(
                    "checkpoint missing {label} path metadata; current run expects {current:?}"
                ),
            )),
        }
    }

    fn validate_checkpoint_metadata_identity(
        &self,
        checkpoint: &crate::checkpoint::Checkpoint,
    ) -> std::io::Result<()> {
        Self::validate_checkpoint_path_identity(
            "spec",
            self.checkpoint.spec_path.as_deref(),
            checkpoint.metadata.spec_path.as_deref(),
        )?;
        Self::validate_checkpoint_path_identity(
            "config",
            self.checkpoint.config_path.as_deref(),
            checkpoint.metadata.config_path.as_deref(),
        )?;

        // Content hash validation: detect spec/config file modifications between
        // checkpoint save and resume, even when the file path is unchanged.
        // Backward-compatible: old checkpoints without hashes are accepted (warn only).
        Self::validate_checkpoint_content_hash(
            "spec",
            self.checkpoint.spec_hash.as_deref(),
            checkpoint.metadata.spec_hash.as_deref(),
        )?;
        Self::validate_checkpoint_content_hash(
            "config",
            self.checkpoint.config_hash.as_deref(),
            checkpoint.metadata.config_hash.as_deref(),
        )?;

        Ok(())
    }

    /// Validate that a file's content hash matches between the current run and the checkpoint.
    ///
    /// - If either side is `None`, skip (backward-compatible with old checkpoints or
    ///   invocations that don't provide paths).
    /// - If both are `Some` and differ, the file was modified between checkpoint save
    ///   and resume, which would produce silently incorrect results.
    fn validate_checkpoint_content_hash(
        label: &str,
        current_hash: Option<&str>,
        checkpoint_hash: Option<&str>,
    ) -> std::io::Result<()> {
        match (current_hash, checkpoint_hash) {
            (Some(current), Some(saved)) if current != saved => Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!(
                    "checkpoint {label} content hash mismatch: the {label} file has been \
                     modified since the checkpoint was saved (checkpoint={saved}, \
                     current={current}). Resuming against a modified {label} would produce \
                     incorrect results."
                ),
            )),
            _ => Ok(()),
        }
    }

    /// Build the BFS queue from a checkpoint frontier for full-state mode.
    ///
    /// Converts the `VecDeque<State>` frontier (which `restore_from_checkpoint`
    /// has already loaded into `state_storage.seen`) into `(Fingerprint, depth)`
    /// queue entries compatible with `FullStateStorage`.
    ///
    /// Part of #2881 Step 3: depth is carried in the queue entry rather than
    /// being looked up from `trace.depths` at dequeue time.
    fn build_resume_queue_full_state(
        &mut self,
        frontier: &VecDeque<State>,
    ) -> Result<VecDeque<(Fingerprint, usize)>, std::io::Error> {
        let mut queue = VecDeque::with_capacity(frontier.len());
        for state in frontier {
            let fp = self.state_fingerprint(state).map_err(|e| {
                std::io::Error::other(format!("resume frontier fingerprint error: {e}"))
            })?;
            // Depth was restored from checkpoint into trace.depths.
            let depth = self.trace.depths.get(&fp).copied().unwrap_or(0);
            queue.push_back((fp, depth));
        }
        Ok(queue)
    }

    /// Build the BFS queue from a checkpoint frontier for fingerprint-only mode.
    ///
    /// Converts the `VecDeque<State>` frontier into `(NoTraceQueueEntry, depth, trace_loc)`
    /// entries compatible with `FingerprintOnlyStorage`. Each state is converted
    /// to `ArrayState` and paired with its depth from `trace.depths`.
    fn build_resume_queue_notrace(
        &mut self,
        frontier: &VecDeque<State>,
    ) -> Result<VecDeque<(NoTraceQueueEntry, usize, u64)>, std::io::Error> {
        // Part of #2881 Step 3: build trace index from file if lazy mode was
        // active (the previous BFS run skipped per-state trace_locs inserts).
        self.trace.ensure_trace_index_built();

        let registry = self.ctx.var_registry().clone();
        let mut queue = VecDeque::with_capacity(frontier.len());
        for state in frontier {
            let fp = self.state_fingerprint(state).map_err(|e| {
                std::io::Error::other(format!("resume frontier fingerprint error: {e}"))
            })?;
            // Part of #1433: warn when frontier state has no depth entry during resume.
            // Missing depth suggests checkpoint/depth-map inconsistency. Defaulting
            // to 0 may cause re-exploration at incorrect depths.
            let depth = match self.trace.depths.get(&fp) {
                Some(&d) => d,
                None => {
                    eprintln!(
                        "WARNING: resume frontier state {fp:?} has no depth entry (defaulting to 0)"
                    );
                    0
                }
            };
            // Part of #2881 Step 3: look up trace_loc from the trace_locs table
            // (cold path — resume only happens once, not on the BFS hot path).
            let trace_loc = self.trace.trace_locs.get(&fp).unwrap_or(0);
            let array_state = ArrayState::from_state(state, &registry);
            queue.push_back((
                NoTraceQueueEntry::Owned {
                    state: array_state,
                    fp,
                },
                depth,
                trace_loc,
            ));
        }
        Ok(queue)
    }

    /// Resume model checking from a previously saved checkpoint.
    ///
    /// This method:
    /// 1. Loads checkpoint from the specified directory
    /// 2. Restores seen states, parents, and depths
    /// 3. Continues BFS exploration from the checkpoint's frontier using
    ///    the shared `run_bfs_loop_core` (same loop as non-resume BFS)
    ///
    /// Part of #2356: eliminates the resume-specific BFS loop by delegating
    /// to `run_bfs_loop_core` with `FullStateStorage` or `FingerprintOnlyStorage`.
    ///
    /// # Arguments
    /// * `checkpoint_dir` - Directory containing the checkpoint files
    ///
    /// # Returns
    /// * `Ok(CheckResult)` - Result of continued model checking
    /// * `Err` - If checkpoint loading fails
    pub fn check_with_resume<P: AsRef<std::path::Path>>(
        &mut self,
        checkpoint_dir: P,
    ) -> Result<CheckResult, std::io::Error> {
        let _model_check_run_guard = crate::intern::ModelCheckRunGuard::begin();
        let _subset_profile_guard = crate::enumerate::subset_profile::RunGuard::begin();
        crate::guard_error_stats::reset();
        let mut guard_error_stats_flush = ResumeGuardErrorStatsFlush::new();

        let result =
            crate::eval::stack_safe(|| self.check_with_resume_inner(checkpoint_dir.as_ref()));
        let suppressed_guard_errors = crate::guard_error_stats::take_and_reset();
        guard_error_stats_flush.disarm();

        let result = match result {
            Ok(result) => Ok(result.with_suppressed_guard_errors(suppressed_guard_errors)),
            Err(err) => {
                if let Some(msg) = crate::guard_error_stats::render_warning(suppressed_guard_errors)
                {
                    eprintln!("{msg}");
                }
                Err(err)
            }
        };
        self.emit_terminal_warnings();
        result
    }

    fn check_with_resume_inner(
        &mut self,
        checkpoint_dir: &std::path::Path,
    ) -> Result<CheckResult, std::io::Error> {
        use crate::checkpoint::Checkpoint;

        if let Some(err) = self.module.setup_error.take() {
            return Ok(CheckResult::from_error(err, self.stats.clone()));
        }

        // Load the checkpoint
        let checkpoint = Checkpoint::load(checkpoint_dir)?;
        self.validate_checkpoint_metadata_identity(&checkpoint)?;

        eprintln!(
            "Resuming from checkpoint: {} states, {} frontier",
            checkpoint.fingerprints.len(),
            checkpoint.frontier.len()
        );

        // Shared BFS setup: constant binding, symmetry, VIEW, next validation,
        // invariant compilation, operator expansion, action compilation.
        // Part of #1230: previously duplicated setup that also missed compiled invariants,
        // trace detection, operator expansion, and action compilation on the resume path.
        let next_name = match self.prepare_bfs_common() {
            Ok(name) => name,
            Err(result) => return Ok(result),
        };

        // Sync TLC config for TLCGet("config") support (must happen before ASSUME
        // checking, since ASSUME expressions may reference TLCGet("config")).
        // Mirrors check_impl at run.rs:408.
        // Part of #1797: previously missing from resume path.
        self.sync_tlc_config("bfs");

        // Check ASSUME statements after constant binding (done in prepare_bfs_common).
        // TLC checks all assumptions and stops if any evaluate to FALSE.
        // Mirrors check_impl at run.rs:457.
        // Fix for #1797: previously missing from resume path, allowing resumed runs
        // to silently succeed when ASSUME evaluates to FALSE.
        if let Some(result) = self.check_assumes() {
            return Ok(result);
        }

        // Cache init name for trace reconstruction (resume may not have init)
        self.trace.cached_init_name = self.config.init.clone();

        // Keep resume-path setup in parity with check_impl for coverage and POR.
        self.setup_actions_and_por(&next_name);

        // Auto-create temp trace file for fingerprint-only mode (#88)
        self.maybe_auto_create_trace_file();

        // Resume does not yet serialize the BFS-time liveness caches needed for
        // temporal checking, so avoid paying successor-cache overhead that can
        // never be consumed in this path. finish_check_after_bfs(resume_mode=true)
        // fails loudly for any unchecked temporal properties before returning Success.
        self.liveness_cache.cache_for_liveness = false;
        self.liveness_cache.successors.clear();
        self.liveness_cache.successor_witnesses.clear();
        self.liveness_cache.inline_state_bitmasks.clear();
        self.liveness_cache.inline_action_bitmasks.clear();
        self.liveness_cache.inline_property_plans.clear();

        // Restore state from checkpoint
        let frontier = self
            .restore_from_checkpoint(checkpoint)
            .map_err(|e| std::io::Error::other(format!("checkpoint restore failed: {e}")))?;

        // Initialize checkpoint timing
        self.initialize_checkpoint_timing();

        // Part of #2356: delegate to run_bfs_loop_core instead of maintaining
        // a separate resume-specific BFS loop. The same loop handles dequeue,
        // progress, checkpoints, limits, depth computation, and successor
        // processing for both normal and resumed runs.
        let fingerprint_only_mode = !self.state_storage.store_full_states;
        let outcome = if fingerprint_only_mode {
            // Fingerprint-only mode: states travel with queue entries.
            let mut queue = self.build_resume_queue_notrace(&frontier)?;
            let registry = self.ctx.var_registry().clone();
            let mut storage = FingerprintOnlyStorage::new(
                crate::arena::BulkStateStorage::empty(registry.len()),
                registry.len(),
            );
            self.run_bfs_loop_core(&mut storage, &mut queue)
        } else {
            // Full-state mode: states are in state_storage.seen,
            // queue holds fingerprints.
            let mut queue = self.build_resume_queue_full_state(&frontier)?;
            let mut storage = FullStateStorage;
            self.run_bfs_loop_core(&mut storage, &mut queue)
        };

        // Part of #1812: delegate to the shared finish_check_after_bfs with
        // resume_mode=true, which rejects liveness instead of running it.
        Ok(match outcome {
            BfsLoopOutcome::Terminated(result) => *result,
            BfsLoopOutcome::Complete {
                depth_limit_reached,
            } => self.finish_check_after_bfs(depth_limit_reached, true),
        })
    }
}
