// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State storage bookkeeping.
//!
//! TLC alignment: `Worker.isSeenState()` + `Worker.writeState()` + FPSet interaction
//! (fingerprint insert + lookup).

use super::super::{
    states_to_trace_value, ArrayState, CapacityStatus, CheckResult, Fingerprint, InsertOutcome,
    LookupOutcome, ModelChecker, StorageFault, TraceLocationStorage,
};

impl<'a> ModelChecker<'a> {
    // ========== State tracking helper methods ==========

    pub(in crate::check::model_checker) fn storage_fault_result(
        &self,
        fault: StorageFault,
    ) -> CheckResult {
        // Part of #2056: Delegate to shared conversion helper.
        let error =
            crate::checker_ops::storage_fault_to_check_error(&*self.state_storage.seen_fps, &fault);
        CheckResult::from_error(error, self.stats.clone())
    }

    /// Checked version of `is_state_seen` that preserves storage-fault semantics.
    #[allow(clippy::result_large_err)]
    pub(in crate::check::model_checker) fn is_state_seen_checked(
        &self,
        fp: Fingerprint,
    ) -> Result<bool, CheckResult> {
        match self.state_storage.seen_fps.contains_checked(fp) {
            LookupOutcome::Present => Ok(true),
            LookupOutcome::Absent => Ok(false),
            LookupOutcome::StorageFault(fault) => Err(self.storage_fault_result(fault)),
            _ => unreachable!(),
        }
    }

    pub(in crate::check::model_checker) fn mark_trace_degraded(&mut self, error: &std::io::Error) {
        if !self.trace.trace_degraded {
            eprintln!(
                "WARNING: trace file I/O error (counterexample traces may be incomplete): {error}"
            );
            self.trace.trace_degraded = true;
        }
    }

    /// Combined test-and-set state admission with storage-fault semantics.
    ///
    /// Part of #2881 Step 2: returns `Ok(true)` if the fingerprint was newly
    /// inserted (bookkeeping performed), `Ok(false)` if already present (no
    /// bookkeeping — the state is already tracked). This eliminates the need
    /// for a separate `is_state_seen_checked` call before admission, reducing
    /// lock acquisitions from 3 to 2 per new state (matching TLC's
    /// `FPSet.put()` atomic test-and-set).
    #[allow(clippy::result_large_err)]
    pub(in crate::check::model_checker) fn mark_state_seen_checked(
        &mut self,
        fp: Fingerprint,
        array_state: &ArrayState,
        parent: Option<Fingerprint>,
        depth: usize,
    ) -> Result<bool, CheckResult> {
        self.debug_record_seen_state_array(fp, array_state, depth);
        match self.state_storage.seen_fps.insert_checked(fp) {
            InsertOutcome::Inserted => {}
            InsertOutcome::AlreadyPresent => return Ok(false),
            InsertOutcome::StorageFault(fault) => return Err(self.storage_fault_result(fault)),
            _ => unreachable!(),
        }

        // Collision detection: record state for fingerprint collision checking.
        if let Some(ref detector) = self.collision_detector {
            detector.record_state(fp, array_state);
        }

        // Part of #3178: store full states in memory when configured.
        if self.state_storage.store_full_states {
            self.state_storage.seen.insert(fp, array_state.clone());
        }

        // Part of #3178: unified trace-file path for parent tracking in both
        // full-state and fp-only modes. Replaces the in-memory parents HashMap
        // with buffered disk writes (16 bytes per state).
        if let Some(ref mut trace_file) = self.trace.trace_file {
            let loc = if let Some(parent_fp) = parent {
                // Part of #2881 Step 3: use pre-cached parent trace_loc from queue
                // entry to avoid HashMap read on the hot path. Falls back to HashMap
                // lookup when not available (e.g., tests, legacy callers).
                let parent_loc = if let Some(cached) = self.trace.current_parent_trace_loc {
                    cached
                } else {
                    // Fallback: HashMap lookup (cold path for tests / resume)
                    match self.trace.trace_locs.get(&parent_fp) {
                        Some(loc) => loc,
                        None => {
                            if !self.trace.trace_degraded {
                                eprintln!(
                                    "WARNING: parent fingerprint {parent_fp:?} not found in trace location index (using root as fallback)"
                                );
                            }
                            0
                        }
                    }
                };
                match trace_file.write_state(parent_loc, fp) {
                    Ok(loc) => Some(loc),
                    Err(e) => {
                        self.mark_trace_degraded(&e);
                        None
                    }
                }
            } else {
                match trace_file.write_initial(fp) {
                    Ok(loc) => Some(loc),
                    Err(e) => {
                        self.mark_trace_degraded(&e);
                        None
                    }
                }
            };

            if let Some(loc) = loc {
                // Part of #2881 Step 3: record trace_loc for queue entry construction
                // (used by admit_successor). When lazy_trace_index is false, also
                // populate the index for cold-path trace reconstruction.
                self.trace.last_inserted_trace_loc = loc;
                if !self.trace.lazy_trace_index && !self.trace.trace_locs.insert(fp, loc) {
                    self.trace.trace_degraded = true;
                }
            }
        }

        // Part of #2881 Step 3: only populate depths HashMap when checkpoints
        // are configured. This is the sole consumer — during BFS, depth is carried
        // on queue entries. Skipping this avoids a HashMap insert per state on the
        // common (no-checkpoint) hot path.
        if self.checkpoint.dir.is_some() {
            self.trace.depths.insert(fp, depth);
        }
        Ok(true)
    }

    /// Combined test-and-set state admission (fp-only) for no-trace mode.
    ///
    /// Part of #2881 Step 2: returns `Ok(true)` if newly inserted, `Ok(false)`
    /// if already present (skips bookkeeping for duplicates).
    #[allow(clippy::result_large_err)]
    pub(in crate::check::model_checker) fn mark_state_seen_fp_only_checked(
        &mut self,
        fp: Fingerprint,
        parent: Option<Fingerprint>,
        depth: usize,
    ) -> Result<bool, CheckResult> {
        debug_assert!(!self.state_storage.store_full_states);
        match self.state_storage.seen_fps.insert_checked(fp) {
            InsertOutcome::Inserted => {}
            InsertOutcome::AlreadyPresent => return Ok(false),
            InsertOutcome::StorageFault(fault) => return Err(self.storage_fault_result(fault)),
            _ => unreachable!(),
        }

        if let Some(ref mut trace_file) = self.trace.trace_file {
            let loc = if let Some(parent_fp) = parent {
                // Part of #2881 Step 3: use pre-cached parent trace_loc from queue
                // entry to avoid HashMap read on the hot path.
                let parent_loc = if let Some(cached) = self.trace.current_parent_trace_loc {
                    cached
                } else {
                    match self.trace.trace_locs.get(&parent_fp) {
                        Some(loc) => loc,
                        None => {
                            if !self.trace.trace_degraded {
                                eprintln!(
                                    "WARNING: parent fingerprint {parent_fp:?} not found in trace location index (using root as fallback)"
                                );
                            }
                            0
                        }
                    }
                };
                match trace_file.write_state(parent_loc, fp) {
                    Ok(loc) => Some(loc),
                    Err(e) => {
                        self.mark_trace_degraded(&e);
                        None
                    }
                }
            } else {
                match trace_file.write_initial(fp) {
                    Ok(loc) => Some(loc),
                    Err(e) => {
                        self.mark_trace_degraded(&e);
                        None
                    }
                }
            };

            if let Some(loc) = loc {
                // Part of #2881 Step 3: record trace_loc for queue entry construction.
                // Skip index population when lazy_trace_index is active (BFS hot path).
                self.trace.last_inserted_trace_loc = loc;
                if !self.trace.lazy_trace_index && !self.trace.trace_locs.insert(fp, loc) {
                    self.trace.trace_degraded = true;
                }
            }
        }

        // Part of #2881 Step 3: skip depths tracking when no checkpoint configured.
        if self.checkpoint.dir.is_some() {
            self.trace.depths.insert(fp, depth);
        }
        Ok(true)
    }

    /// Combined test-and-set state admission (full-state, owned) for full-state mode.
    ///
    /// Part of #2881 Step 2: returns `Ok(true)` if newly inserted (state stored,
    /// bookkeeping performed), `Ok(false)` if already present (state NOT consumed,
    /// no bookkeeping). Callers should check the return value to avoid redundant work.
    #[allow(clippy::result_large_err)]
    pub(in crate::check::model_checker) fn mark_state_seen_owned_checked(
        &mut self,
        fp: Fingerprint,
        array_state: ArrayState,
        parent: Option<Fingerprint>,
        depth: usize,
    ) -> Result<bool, CheckResult> {
        debug_assert!(self.state_storage.store_full_states);
        self.debug_record_seen_state_array(fp, &array_state, depth);
        match self.state_storage.seen_fps.insert_checked(fp) {
            InsertOutcome::Inserted => {}
            InsertOutcome::AlreadyPresent => return Ok(false),
            InsertOutcome::StorageFault(fault) => return Err(self.storage_fault_result(fault)),
            _ => unreachable!(),
        }

        self.state_storage.seen.insert(fp, array_state);

        // Part of #3178: write parent relationship to trace file (same path as
        // mark_state_seen_checked). Replaces the in-memory parents HashMap.
        if let Some(ref mut trace_file) = self.trace.trace_file {
            let loc = if let Some(parent_fp) = parent {
                let parent_loc = if let Some(cached) = self.trace.current_parent_trace_loc {
                    cached
                } else {
                    match self.trace.trace_locs.get(&parent_fp) {
                        Some(loc) => loc,
                        None => {
                            if !self.trace.trace_degraded {
                                eprintln!(
                                    "WARNING: parent fingerprint {parent_fp:?} not found in trace location index (using root as fallback)"
                                );
                            }
                            0
                        }
                    }
                };
                match trace_file.write_state(parent_loc, fp) {
                    Ok(loc) => Some(loc),
                    Err(e) => {
                        self.mark_trace_degraded(&e);
                        None
                    }
                }
            } else {
                match trace_file.write_initial(fp) {
                    Ok(loc) => Some(loc),
                    Err(e) => {
                        self.mark_trace_degraded(&e);
                        None
                    }
                }
            };

            if let Some(loc) = loc {
                self.trace.last_inserted_trace_loc = loc;
                if !self.trace.lazy_trace_index && !self.trace.trace_locs.insert(fp, loc) {
                    self.trace.trace_degraded = true;
                }
            }
        }

        // Part of #2881 Step 3: skip depths tracking when no checkpoint configured.
        if self.checkpoint.dir.is_some() {
            self.trace.depths.insert(fp, depth);
        }
        Ok(true)
    }

    /// Get the number of states found (works in both modes)
    pub(in crate::check::model_checker) fn states_count(&self) -> usize {
        self.state_storage.seen_fps.len()
    }

    /// Check if the fingerprint storage has encountered any errors (e.g., overflow).
    ///
    /// If errors occurred, returns an error result; otherwise returns None.
    pub(in crate::check::model_checker) fn check_fingerprint_storage_errors(
        &self,
    ) -> Option<CheckResult> {
        // Part of #2056: delegate to shared helper for .max(1) floor logic.
        crate::checker_ops::check_fingerprint_errors(self.state_storage.seen_fps.as_ref())
            .map(|error| CheckResult::from_error(error, self.stats.clone()))
    }

    /// Check fingerprint storage capacity and warn if approaching limits.
    ///
    /// Only emits a warning when the status changes from normal to warning/critical,
    /// or from warning to critical. This avoids spamming the user with repeated warnings.
    pub(in crate::check::model_checker) fn check_and_warn_capacity(&mut self) {
        let status = self.state_storage.seen_fps.capacity_status();

        // Only warn if status has changed and is not Normal
        if status == self.hooks.last_capacity_status {
            return;
        }

        match status {
            CapacityStatus::Normal => {
                // Status improved back to normal - no warning needed
            }
            CapacityStatus::Warning {
                count,
                capacity,
                usage,
            } => {
                eprintln!(
                    "Warning: Fingerprint storage at {:.1}% capacity ({} / {} states). \
                     Consider increasing --mmap-fingerprints capacity if state space is larger.",
                    usage * 100.0,
                    count,
                    capacity
                );
            }
            CapacityStatus::Critical {
                count,
                capacity,
                usage,
            } => {
                eprintln!(
                    "CRITICAL: Fingerprint storage at {:.1}% capacity ({} / {} states). \
                     Insert failures imminent! Increase --mmap-fingerprints capacity.",
                    usage * 100.0,
                    count,
                    capacity
                );
            }
            _ => {}
        }

        self.hooks.last_capacity_status = status;
    }

    // =============================================================================
    // TLCExt Trace context helpers (Part of #1117)
    // =============================================================================

    /// Set trace context for initial state invariant checking (ArrayState variant).
    ///
    /// Part of #1117: Like set_trace_context_for_init but for the streaming init path
    /// that uses ArrayState instead of State.
    pub(in crate::check::model_checker) fn set_trace_context_for_init_array(
        &mut self,
        arr: &ArrayState,
    ) {
        if self.compiled.uses_trace {
            let registry = self.ctx.var_registry().clone();
            let state = arr.to_state(&registry);
            self.ctx
                .set_tlc_trace_value(Some(states_to_trace_value(&[state])));
        }
    }

    /// Set trace context for successor state invariant checking.
    ///
    /// Part of #1117: When uses_trace is true and we're checking invariants on a successor
    /// state, reconstruct the trace from initial state to the PARENT, then append the successor.
    ///
    /// This is expensive (trace reconstruction), so only call when uses_trace is true.
    /// The successor state is not yet in the parent map, so we build:
    ///   trace_to_parent + [succ_state]
    pub(in crate::check::model_checker) fn set_trace_context_for_successor(
        &mut self,
        parent_fp: Fingerprint,
        succ: &ArrayState,
    ) {
        if self.compiled.uses_trace {
            self.stats.trace_reconstructions += 1;
            let registry = self.ctx.var_registry().clone();
            // Reconstruct trace to parent
            let mut parent_trace = self.reconstruct_trace(parent_fp);
            // Convert successor ArrayState to State and append
            let succ_state = succ.to_state(&registry);
            parent_trace.states.push(succ_state);
            self.ctx
                .set_tlc_trace_value(Some(states_to_trace_value(&parent_trace.states)));
        }
    }

    /// Clear trace context after invariant checking.
    ///
    /// Part of #1117: Clean up trace context after invariant evaluation.
    pub(in crate::check::model_checker) fn clear_trace_context(&mut self) {
        if self.compiled.uses_trace {
            self.ctx.set_tlc_trace_value(None);
        }
    }
}
