// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
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

/// In-memory successor cache with an optional entry budget.
///
/// When the entry count reaches 80% of the configured limit, the
/// `SuccessorGraph` auto-migrates all entries to a disk-backed store
/// instead of returning a hard error. This prevents BFS failures
/// while keeping memory bounded.
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

    /// Check if inserting a new entry would exceed the migration threshold.
    ///
    /// Returns `true` when the entry count reaches 80% of the configured limit,
    /// signaling that the caller should migrate to disk BEFORE inserting.
    fn should_migrate(&self, parent_fp: Fingerprint) -> bool {
        if self.map.contains_key(&parent_fp) {
            return false; // Overwrite of existing entry — no growth.
        }
        if let Some(limit) = self.entry_limit {
            let migration_threshold = (limit as f64 * 0.80) as usize;
            return self.map.len() >= migration_threshold;
        }
        false
    }

    /// Insert unconditionally (caller has already checked migration threshold).
    fn insert_unchecked(&mut self, parent_fp: Fingerprint, successors: Vec<Fingerprint>) {
        self.map.insert(parent_fp, successors);
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
    ///
    /// Part of #4080: When the in-memory backend approaches its entry limit
    /// (80% of `TLA2_LIVENESS_INMEMORY_SUCCESSOR_LIMIT`, default 5M), all
    /// entries are automatically migrated to a disk-backed store. This
    /// converts a previously hard BFS failure into graceful degradation —
    /// exploration continues with bounded memory instead of crashing.
    pub(crate) fn insert(
        &mut self,
        parent_fp: Fingerprint,
        successors: Vec<Fingerprint>,
    ) -> Result<(), CheckError> {
        match self {
            SuccessorGraph::InMemory(graph) => {
                if graph.should_migrate(parent_fp) {
                    // Migrate all existing entries to disk.
                    let mut disk = DiskSuccessorGraph::new().map_err(|e| EvalError::Internal {
                        message: format!(
                            "failed to create disk successor graph during \
                                 auto-migration: {e}"
                        ),
                        span: None,
                    })?;

                    let entry_count = graph.map.len();
                    eprintln!(
                        "Note: liveness successor cache auto-migrating to disk \
                         ({entry_count} entries at 80% of limit). \
                         Memory-bounded disk backend will be used for remaining BFS."
                    );

                    // Drain in-memory map into disk.
                    for (fp, succs) in graph.map.drain() {
                        disk.insert(fp, succs);
                    }
                    // Insert the current entry that triggered migration.
                    disk.insert(parent_fp, successors);

                    *self = SuccessorGraph::Disk(disk);
                    Ok(())
                } else {
                    graph.insert_unchecked(parent_fp, successors);
                    Ok(())
                }
            }
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

    /// Estimate the memory consumed by the in-memory successor graph.
    ///
    /// Part of #4080: OOM safety — liveness cache memory accounting.
    /// For the in-memory backend: HashMap overhead + per-entry Vec allocations.
    /// For the disk backend: only the in-memory index is counted.
    pub(crate) fn estimate_memory_bytes(&self) -> usize {
        match self {
            SuccessorGraph::InMemory(graph) => {
                let capacity = graph.map.capacity();
                let entry_size = std::mem::size_of::<Fingerprint>()
                    .saturating_add(std::mem::size_of::<Vec<Fingerprint>>())
                    .saturating_add(1);
                let table_bytes = capacity.saturating_mul(entry_size);
                let vec_heap_bytes: usize = graph
                    .map
                    .values()
                    .map(|v| {
                        v.capacity()
                            .saturating_mul(std::mem::size_of::<Fingerprint>())
                    })
                    .sum();
                crate::memory::apply_fragmentation_overhead(
                    table_bytes.saturating_add(vec_heap_bytes),
                )
            }
            SuccessorGraph::Disk(disk) => {
                // Disk backend: only the in-memory index (offset map).
                disk.len().saturating_mul(20)
            }
        }
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

        let slice = graph
            .get_ref(&parent)
            .expect("in-memory get_ref should return Some");
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

    #[test]
    fn test_auto_migration_to_disk_on_limit() {
        // Create in-memory graph with a tiny limit for testing.
        // 80% of 10 = 8, so migration triggers when len() >= 8 on a new insert.
        let mut graph = SuccessorGraph::InMemory(InMemorySuccessorGraph {
            map: FxHashMap::default(),
            entry_limit: Some(10),
        });

        // Insert 8 entries (fills to len=8).
        for i in 0..8 {
            graph
                .insert(Fingerprint(i), vec![Fingerprint(i + 100)])
                .expect("insert within limit should succeed");
        }

        // At 8 entries, graph may still be in-memory (80% check is >=).
        // The 9th insert (with len=8 >= threshold=8) triggers migration.
        graph
            .insert(Fingerprint(8), vec![Fingerprint(108)])
            .expect("insert that triggers migration should succeed");

        assert!(
            graph.is_disk(),
            "graph should have auto-migrated to disk backend after reaching 80% of limit"
        );

        // Verify all 9 entries survived migration.
        assert_eq!(graph.len(), 9);
        for i in 0..9 {
            let succs = graph
                .get(&Fingerprint(i))
                .expect("entry should survive migration");
            assert_eq!(succs, vec![Fingerprint(i + 100)]);
        }

        // Further inserts should work on the disk backend.
        graph
            .insert(Fingerprint(99), vec![Fingerprint(199)])
            .expect("post-migration insert should succeed");
        assert_eq!(graph.len(), 10);
        assert_eq!(graph.get(&Fingerprint(99)), Some(vec![Fingerprint(199)]));
    }

    #[test]
    fn test_no_migration_when_no_limit() {
        // No entry_limit means no migration.
        let mut graph = SuccessorGraph::InMemory(InMemorySuccessorGraph {
            map: FxHashMap::default(),
            entry_limit: None,
        });

        for i in 0..100 {
            graph
                .insert(Fingerprint(i), vec![Fingerprint(i + 1000)])
                .expect("insert without limit should succeed");
        }

        assert!(
            !graph.is_disk(),
            "graph without limit should stay in-memory"
        );
        assert_eq!(graph.len(), 100);
    }
}
