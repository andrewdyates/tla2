// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Storage-mode abstractions for BFS exploration.
//!
//! Part of #2351: extracted from `run_bfs_common.rs`.
//! Part of #3436: split into submodules (contract, full-state, fp-only, tests).
//!
//! Defines the `BfsStorage` trait and its two implementations:
//! - `FullStateStorage`: HashMap-backed with trace reconstruction.
//! - `FingerprintOnlyStorage`: fingerprint-set-backed with disk trace.
//!
//! The BFS loop in `bfs::engine` is generic over this trait, enabling a single
//! loop implementation for both storage modes (Part of #2133).

mod fingerprint_only;
mod full_state;
#[cfg(test)]
mod tests;

use super::super::frontier::BfsFrontier;
use super::super::{ArrayState, CheckResult, Fingerprint, ModelChecker, State, VecDeque};

// Re-export concrete backends for sibling modules.
pub(in crate::check::model_checker) use self::fingerprint_only::{
    FingerprintOnlyStorage, NoTraceQueueEntry,
};
pub(in crate::check::model_checker) use self::full_state::FullStateStorage;

/// Abstracts storage-mode differences between full-state and fingerprint-only BFS.
///
/// This trait enables a single generic BFS loop to work with both storage modes,
/// eliminating duplicated loop logic that has already drifted in `use_diffs` conditions,
/// `print_symmetry_stats()` calls, and state-limit handling patterns.
///
/// Implementations are zero-cost: the generic function is monomorphized for each
/// storage type, producing the same code as the hand-written variants.
pub(in crate::check::model_checker) trait BfsStorage {
    /// The type held in the BFS queue.
    type QueueEntry;

    /// Extract the current state for processing from a queue entry.
    ///
    /// Returns `Ok(Some((fingerprint, owned_state, depth)))` on success,
    /// `Ok(None)` for phantom dequeues (full-state: fp not found in HashMap),
    /// or `Err(CheckResult)` on error (materialization/fingerprint failure).
    #[allow(clippy::result_large_err)]
    fn dequeue(
        &mut self,
        entry: Self::QueueEntry,
        mc: &mut ModelChecker,
    ) -> Result<Option<(Fingerprint, ArrayState, usize)>, CheckResult>;

    /// Return/restore the current state after processing.
    ///
    /// Full-state: re-inserts the ArrayState into the seen HashMap.
    /// No-trace: no-op (state is not stored in a HashMap).
    fn return_current(&mut self, fp: Fingerprint, state: ArrayState, mc: &mut ModelChecker);

    /// Atomic test-and-set admission: check if seen, insert if new, and create queue entry.
    ///
    /// Part of #2881 Step 2: combines the dedup check with state admission in a
    /// single operation, matching TLC's `FPSet.put()` pattern. Returns `Ok(None)`
    /// if the state was already seen (no bookkeeping performed), or
    /// `Ok(Some(entry))` if newly admitted.
    ///
    /// This eliminates the need for a separate `is_state_seen_checked` call before
    /// admission, reducing lock acquisitions from 3 to 2 per new state.
    ///
    /// Ownership semantics differ by mode:
    /// - Full-state: moves state into HashMap, returns fingerprint as queue entry.
    /// - No-trace: records fingerprint in FPSet, returns Owned{state, fp} queue entry.
    #[allow(clippy::result_large_err)]
    fn admit_successor(
        &mut self,
        fp: Fingerprint,
        state: ArrayState,
        parent_fp: Option<Fingerprint>,
        depth: usize,
        mc: &mut ModelChecker,
    ) -> Result<Option<Self::QueueEntry>, CheckResult>;

    /// Whether diff-based successor generation is available in this mode.
    ///
    /// Full-state: true when no VIEW and no symmetry.
    /// No-trace: additionally requires no liveness caching (diff path doesn't
    /// record successor witnesses needed for liveness).
    fn use_diffs(&self, mc: &ModelChecker) -> bool;

    /// Build a checkpoint frontier from the current state and queue contents.
    fn checkpoint_frontier(
        &self,
        current: &ArrayState,
        queue: &impl BfsFrontier<Entry = Self::QueueEntry>,
        registry: &crate::var_index::VarRegistry,
        mc: &ModelChecker,
    ) -> VecDeque<State>;

    /// Cache successor fingerprints for liveness checking (diff path).
    ///
    /// Called after processing all diffs. Full-state: caches fps.
    /// No-trace: no-op (liveness excluded from diff path via `use_diffs`).
    fn cache_diff_liveness(
        &self,
        parent_fp: Fingerprint,
        succ_fps: Option<Vec<Fingerprint>>,
        mc: &mut ModelChecker,
    ) -> Result<(), crate::check::CheckError>;

    /// Cache successor info for liveness checking (full successor path).
    ///
    /// Full-state: caches fps + symmetry witness states if applicable.
    /// No-trace: caches fps only.
    fn cache_full_liveness(
        &self,
        parent_fp: Fingerprint,
        successors: &[(ArrayState, Fingerprint)],
        mc: &mut ModelChecker,
    ) -> Result<(), crate::check::CheckError>;
}
