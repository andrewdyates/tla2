// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Successor graph abstraction with in-memory and disk-backed backends.
//!
//! Part of #3176: replaces the raw `FxHashMap<Fingerprint, Vec<Fingerprint>>`
//! in `LivenessCacheState.successors` with a dispatch enum that can use either
//! an in-memory HashMap (default) or a disk-backed store for large state spaces.

use super::disk_successor_graph::DiskSuccessorGraph;
use crate::check::CheckError;
use crate::liveness::debug::liveness_inmemory_successor_limit;
use crate::state::Fingerprint;
use crate::EvalError;
use rustc_hash::{FxHashMap, FxHashSet};

/// In-memory successor cache with an optional debug/test entry budget.
pub(crate) struct InMemorySuccessorGraph {
    map: FxHashMap<Fingerprint, Vec<Fingerprint>>,
    entry_limit: Option<usize>,
}

impl InMemorySuccessorGraph {
    fn new() -> Self {
        Self {
            map: FxHashMap::default(),
            entry_limit: liveness_inmemory_successor_limit(),
        }
    }

    fn insert(
        &mut self,
        parent_fp: Fingerprint,
        successors: Vec<Fingerprint>,
    ) -> Result<(), CheckError> {
        if !self.map.contains_key(&parent_fp) {
            if let Some(limit) = self.entry_limit {
                if self.map.len() >= limit {
                    return Err(EvalError::Internal {
                        message: format!(
                            "in-memory liveness successor limit exceeded: limit={limit}, attempted parent {parent_fp}; enable disk-backed successors or raise TLA2_LIVENESS_INMEMORY_SUCCESSOR_LIMIT"
                        ),
                        span: None,
                    }
                    .into());
                }
            }
        }
        self.map.insert(parent_fp, successors);
        Ok(())
    }
}

/// Successor graph for BFS liveness caching.
///
/// Stores `parent_fp -> [child_fps]` relationships discovered during BFS.
/// Read during post-BFS liveness checking for behavior graph construction
/// and SCC analysis.
pub(crate) enum SuccessorGraph {
    /// In-memory HashMap (default, fast, but O(states × avg_succs × 8) bytes).
    InMemory(InMemorySuccessorGraph),
    /// Disk-backed store with in-memory index + LRU cache.
    /// Memory cost: O(states × 16) bytes (index only).
    Disk(DiskSuccessorGraph),
}

impl Default for SuccessorGraph {
    fn default() -> Self {
        Self::in_memory()
    }
}

impl SuccessorGraph {
    /// Create an in-memory successor graph (default).
    pub(crate) fn in_memory() -> Self {
        SuccessorGraph::InMemory(InMemorySuccessorGraph::new())
    }

    /// Create a disk-backed successor graph.
    ///
    /// Returns `Err` if the backing temp file cannot be created.
    pub(crate) fn disk() -> std::io::Result<Self> {
        Ok(SuccessorGraph::Disk(DiskSuccessorGraph::new()?))
    }

    /// Insert a parent fingerprint and its successor list.
    pub(crate) fn insert(
        &mut self,
        parent_fp: Fingerprint,
        successors: Vec<Fingerprint>,
    ) -> Result<(), CheckError> {
        match self {
            SuccessorGraph::InMemory(graph) => graph.insert(parent_fp, successors),
            SuccessorGraph::Disk(disk) => {
                disk.insert(parent_fp, successors);
                Ok(())
            }
        }
    }

    /// Look up successor fingerprints for a parent.
    ///
    /// Returns `None` if the parent was never inserted.
    ///
    /// For the in-memory backend this clones the Vec; for disk it reads from
    /// the file (or cache). Both paths return owned data.
    ///
    /// Takes `&self` (not `&mut self`) because the disk backend uses interior
    /// mutability (`RefCell`) for its read cache.
    pub(crate) fn get(&self, fp: &Fingerprint) -> Option<Vec<Fingerprint>> {
        match self {
            SuccessorGraph::InMemory(graph) => graph.map.get(fp).cloned(),
            SuccessorGraph::Disk(disk) => disk.get(fp),
        }
    }

    /// Borrow successor fingerprints for a parent (in-memory backend only).
    ///
    /// Returns `None` if the parent was never inserted or if the backend is
    /// disk-backed (disk reads require owned data). Callers that only iterate
    /// over successors should prefer this over [`get`] to avoid cloning the
    /// entire `Vec<Fingerprint>` on every lookup.
    ///
    /// Part of #4080: eliminates unnecessary clone() on the hot path for
    /// in-memory successor lookups during liveness checking.
    pub(crate) fn get_ref(&self, fp: &Fingerprint) -> Option<&[Fingerprint]> {
        match self {
            SuccessorGraph::InMemory(graph) => graph.map.get(fp).map(|v| v.as_slice()),
            SuccessorGraph::Disk(_) => None,
        }
    }

    /// Access the inner HashMap (in-memory backend only).
    ///
    /// Returns `None` for disk backend. Used by the safety-temporal path
    /// which iterates all entries — a pattern only feasible in-memory.
    /// When using disk backend, the safety-temporal path falls through
    /// to the SCC checker instead.
    pub(crate) fn as_inner_map(&self) -> Option<&FxHashMap<Fingerprint, Vec<Fingerprint>>> {
        match self {
            SuccessorGraph::InMemory(graph) => Some(&graph.map),
            SuccessorGraph::Disk(_) => None,
        }
    }

    /// Number of distinct parent entries.
    pub(crate) fn len(&self) -> usize {
        match self {
            SuccessorGraph::InMemory(graph) => graph.map.len(),
            SuccessorGraph::Disk(disk) => disk.len(),
        }
    }

    /// Total number of successor fingerprints across all entries (for diagnostics).
    pub(crate) fn total_successors(&self) -> usize {
        match self {
            SuccessorGraph::InMemory(graph) => graph.map.values().map(Vec::len).sum(),
            SuccessorGraph::Disk(disk) => disk.total_successors(),
        }
    }

    /// Collect all fingerprints referenced by the successor graph.
    ///
    /// This is used by cold-path fp-only replay fallback to identify states
    /// that must be reconstructed even when the primary BFS replay seed is
    /// unavailable. Both backends return the same parent+successor set.
    pub(crate) fn collect_all_fingerprints(&self) -> FxHashSet<Fingerprint> {
        match self {
            SuccessorGraph::InMemory(graph) => {
                let total_successors: usize = graph.map.values().map(Vec::len).sum();
                let mut fingerprints = FxHashSet::with_capacity_and_hasher(
                    graph.map.len().saturating_add(total_successors),
                    Default::default(),
                );
                for (&parent_fp, successors) in &graph.map {
                    fingerprints.insert(parent_fp);
                    fingerprints.extend(successors.iter().copied());
                }
                fingerprints
            }
            SuccessorGraph::Disk(disk) => disk.collect_all_fingerprints(),
        }
    }

    /// Discard all entries.
    pub(crate) fn clear(&mut self) {
        match self {
            SuccessorGraph::InMemory(graph) => graph.map.clear(),
            SuccessorGraph::Disk(disk) => disk.clear(),
        }
    }

    /// Whether this is the disk backend.
    pub(crate) fn is_disk(&self) -> bool {
        matches!(self, SuccessorGraph::Disk(_))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_ref_returns_slice_for_inmemory() {
        let mut graph = SuccessorGraph::in_memory();
        let parent = Fingerprint(1);
        let child_a = Fingerprint(10);
        let child_b = Fingerprint(20);
        graph.insert(parent, vec![child_a, child_b]).unwrap();

        let slice = graph.get_ref(&parent).expect("in-memory get_ref should return Some");
        assert_eq!(slice, &[child_a, child_b]);
    }

    #[test]
    fn test_get_ref_returns_none_for_missing() {
        let graph = SuccessorGraph::in_memory();
        assert!(graph.get_ref(&Fingerprint(999)).is_none());
    }

    #[test]
    fn test_get_ref_returns_none_for_disk() {
        let graph = SuccessorGraph::disk().unwrap();
        assert!(graph.get_ref(&Fingerprint(1)).is_none());
    }

    #[test]
    fn test_get_and_get_ref_consistent() {
        let mut graph = SuccessorGraph::in_memory();
        let parent = Fingerprint(42);
        let children = vec![Fingerprint(100), Fingerprint(200), Fingerprint(300)];
        graph.insert(parent, children.clone()).unwrap();

        let owned = graph.get(&parent).unwrap();
        let borrowed = graph.get_ref(&parent).unwrap();
        assert_eq!(owned, borrowed);
    }
}
