// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Full-state BFS storage backend.
//!
//! Part of #3436: extracted from `storage_modes.rs`.

use super::super::super::frontier::BfsFrontier;
use super::super::super::{ArrayState, CheckResult, Fingerprint, ModelChecker, State, VecDeque};
use super::super::checkpoint_view;
use super::BfsStorage;

/// Full-state BFS storage: states live in a `FxHashMap<Fingerprint, ArrayState>`.
///
/// Queue entries are fingerprints — the actual state is retrieved from the HashMap.
/// This mode supports trace reconstruction via parent pointers.
pub(in crate::check::model_checker) struct FullStateStorage;

impl BfsStorage for FullStateStorage {
    /// Queue entries carry `(Fingerprint, depth)` — the depth travels with the
    /// entry rather than being looked up from `trace.depths` at dequeue time.
    ///
    /// Part of #2881 Step 3: eliminates the per-dequeue `FxHashMap::get` on the
    /// `depths` HashMap, matching TLC's approach of carrying per-state metadata
    /// on the state/queue object rather than in a side table.
    type QueueEntry = (Fingerprint, usize);

    fn dequeue(
        &mut self,
        (fp, depth): (Fingerprint, usize),
        mc: &mut ModelChecker,
    ) -> Result<Option<(Fingerprint, ArrayState, usize)>, CheckResult> {
        let current_array = match mc.state_storage.seen.remove(&fp) {
            Some(arr) => arr,
            None => {
                mc.stats.phantom_dequeues += 1;
                return Ok(None);
            }
        };
        Ok(Some((fp, current_array, depth)))
    }

    fn return_current(&mut self, fp: Fingerprint, state: ArrayState, mc: &mut ModelChecker) {
        mc.state_storage.seen.insert(fp, state);
    }

    fn admit_successor(
        &mut self,
        fp: Fingerprint,
        state: ArrayState,
        parent_fp: Option<Fingerprint>,
        depth: usize,
        mc: &mut ModelChecker,
    ) -> Result<Option<(Fingerprint, usize)>, CheckResult> {
        if mc.mark_state_seen_owned_checked(fp, state, parent_fp, depth)? {
            Ok(Some((fp, depth)))
        } else {
            Ok(None)
        }
    }

    fn use_diffs(&self, mc: &ModelChecker) -> bool {
        if crate::check::debug::force_no_diffs() {
            return false;
        }
        mc.compiled.cached_view_name.is_none()
            && mc.symmetry.perms.is_empty()
            && !mc.inline_liveness_active()
    }

    fn checkpoint_frontier(
        &self,
        current: &ArrayState,
        queue: &impl BfsFrontier<Entry = (Fingerprint, usize)>,
        registry: &crate::var_index::VarRegistry,
        mc: &ModelChecker,
    ) -> VecDeque<State> {
        checkpoint_view::build_checkpoint_frontier(current, queue, registry, |(q_fp, _depth)| {
            mc.state_storage
                .seen
                .get(q_fp)
                .map(|arr| arr.to_state(registry))
        })
    }

    fn cache_diff_liveness(
        &self,
        parent_fp: Fingerprint,
        succ_fps: Option<Vec<Fingerprint>>,
        mc: &mut ModelChecker,
    ) -> Result<(), crate::check::CheckError> {
        // Symmetry is excluded from the diff path, so we only cache fingerprints.
        if let Some(fps) = succ_fps {
            mc.liveness_cache.successors.insert(parent_fp, fps)?;
        }
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
        if !mc.symmetry.perms.is_empty() {
            let witness_list: Vec<(Fingerprint, ArrayState)> = successors
                .iter()
                .map(|(arr, canon_fp)| (*canon_fp, arr.clone()))
                .collect();
            mc.liveness_cache
                .successor_witnesses
                .insert(parent_fp, witness_list);
        }
        Ok(())
    }
}
