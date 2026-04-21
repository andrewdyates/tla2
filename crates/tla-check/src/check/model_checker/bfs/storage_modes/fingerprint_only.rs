// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fingerprint-only BFS storage backend.
//!
//! Part of #3436: extracted from `storage_modes.rs`.

use super::super::super::frontier::BfsFrontier;
use super::super::super::{
    check_error_to_result, ArrayState, BulkStateHandle, BulkStateStorage, CheckResult, Fingerprint,
    ModelChecker, State, VecDeque,
};
use super::super::checkpoint_view;
use super::BfsStorage;
use crate::state::FlatState;
use crate::EvalCheckError;

/// Queue entry type for no-trace (fingerprint-only) BFS mode.
///
/// Bulk entries reference initial states stored in contiguous `BulkStateStorage`;
/// owned entries hold successor states materialized during BFS exploration.
/// Flat entries hold states as contiguous `[i64]` buffers, auto-detected for
/// specs where all state variables are scalar, or force-enabled via
/// `TLA2_FLAT_BFS=1` (Part of #4126: Tier 0 interpreter sandwich).
pub(in crate::check::model_checker) enum NoTraceQueueEntry {
    Bulk(BulkStateHandle),
    Owned { state: ArrayState, fp: Fingerprint },
    /// Flat i64 buffer representation for the interpreter sandwich.
    ///
    /// Auto-activated when the state layout is fully flat (all vars scalar)
    /// and roundtrip verification passes. Can also be force-enabled via
    /// `TLA2_FLAT_BFS=1` or `Config::use_flat_state = Some(true)`.
    ///
    /// On dequeue, the `FlatState` is converted to `ArrayState` via the
    /// `FlatBfsAdapter` for interpreter evaluation. On successor admission,
    /// `ArrayState` successors are converted to `FlatState` before enqueue.
    ///
    /// Part of #4126: Tier 0 interpreter sandwich.
    Flat { flat: FlatState, fp: Fingerprint },
}

/// Fingerprint-only BFS storage: states are not kept in a HashMap.
///
/// Queue entries carry the actual `ArrayState` (for successors) or a handle
/// to `BulkStateStorage` (for initial states). Traces are reconstructed from
/// a disk-based trace file when needed.
pub(in crate::check::model_checker) struct FingerprintOnlyStorage {
    pub(in crate::check::model_checker) bulk_initial: BulkStateStorage,
    num_vars: usize,
}

impl FingerprintOnlyStorage {
    pub(in crate::check::model_checker) fn new(
        bulk_initial: BulkStateStorage,
        num_vars: usize,
    ) -> Self {
        Self {
            bulk_initial,
            num_vars,
        }
    }
}

impl BfsStorage for FingerprintOnlyStorage {
    /// Queue entries carry `(NoTraceQueueEntry, depth, trace_loc)`.
    ///
    /// Part of #2881 Step 3: the `trace_loc` (u64) is the trace file offset of
    /// this state, carried on the queue entry to eliminate per-successor HashMap
    /// reads when processing this state's successors. Matches TLC's pattern of
    /// embedding per-state metadata on the state/queue object.
    type QueueEntry = (NoTraceQueueEntry, usize, u64);

    fn dequeue(
        &mut self,
        (entry, depth, trace_loc): (NoTraceQueueEntry, usize, u64),
        mc: &mut ModelChecker,
    ) -> Result<Option<(Fingerprint, ArrayState, usize)>, CheckResult> {
        // Part of #2881 Step 3: cache the parent's trace_loc for successor admission.
        mc.trace.current_parent_trace_loc = Some(trace_loc);
        match entry {
            NoTraceQueueEntry::Bulk(handle) => {
                let mut state = ArrayState::new(self.num_vars);
                state.overwrite_from_slice(self.bulk_initial.get_state(handle.index));

                // Re-materialize lazy values after bulk reload.
                if let Err(e) = crate::materialize::materialize_array_state(&mc.ctx, &mut state, mc.compiled.spec_may_produce_lazy) {
                    return Err(check_error_to_result(
                        EvalCheckError::Eval(e).into(),
                        &mc.stats,
                    ));
                }

                let fp = match handle.fingerprint {
                    Some(fp) => fp,
                    None => mc
                        .array_state_fingerprint(&mut state)
                        .map_err(|e| check_error_to_result(e, &mc.stats))?,
                };
                Ok(Some((fp, state, depth)))
            }
            NoTraceQueueEntry::Owned { state, fp } => Ok(Some((fp, state, depth))),
            NoTraceQueueEntry::Flat { flat, fp } => {
                // Part of #4126: Tier 0 interpreter sandwich — convert FlatState
                // to ArrayState for interpreter evaluation.
                let registry = mc.ctx.var_registry().clone();
                let state = match mc.flat_bfs_adapter.as_mut() {
                    Some(adapter) => adapter.flat_to_array(&flat, &registry, None),
                    None => {
                        // Adapter not initialized — should not happen when Flat entries exist.
                        return Err(check_error_to_result(
                            crate::ConfigCheckError::Setup(
                                "FlatBfsAdapter not initialized for Flat queue entry".to_string(),
                            )
                            .into(),
                            &mc.stats,
                        ));
                    }
                };
                Ok(Some((fp, state, depth)))
            }
        }
    }

    fn return_current(&mut self, _fp: Fingerprint, _state: ArrayState, _mc: &mut ModelChecker) {
        // No-op: fingerprint-only mode doesn't store states in a HashMap.
    }

    fn admit_successor(
        &mut self,
        fp: Fingerprint,
        state: ArrayState,
        parent_fp: Option<Fingerprint>,
        depth: usize,
        mc: &mut ModelChecker,
    ) -> Result<Option<(NoTraceQueueEntry, usize, u64)>, CheckResult> {
        if mc.mark_state_seen_checked(fp, &state, parent_fp, depth)? {
            // Part of #2881 Step 3: carry the new state's trace_loc on the queue
            // entry so successors can use it without a HashMap read.
            let trace_loc = mc.trace.last_inserted_trace_loc;

            // Part of #4126: When flat BFS is active (auto-detected for scalar
            // specs or force-enabled via TLA2_FLAT_BFS=1), convert the ArrayState
            // to FlatState for queue storage. The interpreter sandwich converts
            // back on dequeue.
            //
            // `should_use_flat_bfs()` encapsulates the full decision hierarchy:
            // env var overrides, config overrides, and auto-detection for fully-flat
            // layouts with verified roundtrip.
            let entry = if mc.should_use_flat_bfs() {
                if let Some(ref mut adapter) = mc.flat_bfs_adapter {
                    let flat = adapter.array_to_flat(&state);
                    NoTraceQueueEntry::Flat { flat, fp }
                } else {
                    // should_use_flat_bfs() returned true but adapter is None —
                    // should not happen. Fall back to Owned.
                    NoTraceQueueEntry::Owned { state, fp }
                }
            } else {
                NoTraceQueueEntry::Owned { state, fp }
            };

            Ok(Some((entry, depth, trace_loc)))
        } else {
            Ok(None)
        }
    }

    fn use_diffs(&self, mc: &ModelChecker) -> bool {
        mc.compiled.cached_view_name.is_none()
            && mc.symmetry.perms.is_empty()
            && !mc.liveness_cache.cache_for_liveness
    }

    fn checkpoint_frontier(
        &self,
        current: &ArrayState,
        queue: &impl BfsFrontier<Entry = (NoTraceQueueEntry, usize, u64)>,
        registry: &crate::var_index::VarRegistry,
        mc: &ModelChecker,
    ) -> VecDeque<State> {
        checkpoint_view::build_checkpoint_frontier(current, queue, registry, |(entry, _, _)| {
            Some(match entry {
                NoTraceQueueEntry::Bulk(handle) => {
                    State::from_indexed(self.bulk_initial.get_state(handle.index), registry)
                }
                NoTraceQueueEntry::Owned { state, .. } => state.to_state(registry),
                NoTraceQueueEntry::Flat { flat, .. } => {
                    // Part of #4126: Convert FlatState back to State for checkpoint.
                    match mc.flat_bfs_bridge() {
                        Some(bridge) => {
                            let arr = bridge.to_array_state(flat, registry);
                            arr.to_state(registry)
                        }
                        None => {
                            // Shouldn't happen: Flat entries require the bridge.
                            // Return a placeholder state to avoid panicking in checkpoint.
                            State::new()
                        }
                    }
                }
            })
        })
    }

    fn cache_diff_liveness(
        &self,
        _parent_fp: Fingerprint,
        _succ_fps: Option<Vec<Fingerprint>>,
        _mc: &mut ModelChecker,
    ) -> Result<(), crate::check::CheckError> {
        // No-op: use_diffs() returns false when cache_for_liveness is true,
        // so this method is never called on the diff path.
        Ok(())
    }

    fn cache_full_liveness(
        &self,
        parent_fp: Fingerprint,
        successors: &[(ArrayState, Fingerprint)],
        mc: &mut ModelChecker,
    ) -> Result<(), crate::check::CheckError> {
        if !mc.liveness_cache.cache_for_liveness {
            return Ok(());
        }
        let succ_fps: Vec<Fingerprint> = successors.iter().map(|(_, fp)| *fp).collect();
        mc.liveness_cache.successors.insert(parent_fp, succ_fps)?;
        // No-trace mode does not cache symmetry witness states — symmetry
        // liveness requires full-state mode for witness reconstruction.
        Ok(())
    }
}
