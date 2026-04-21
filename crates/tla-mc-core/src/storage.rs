// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use parking_lot::RwLock;
use rustc_hash::{FxHashSet, FxHasher};
use std::hash::{Hash, Hasher};

/// Structured storage fault surfaced by checked fingerprint operations.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{backend} {operation} fault: {detail}")]
#[non_exhaustive]
pub struct StorageFault {
    /// Backend name (for example: `mmap`, `disk`).
    pub backend: &'static str,
    /// Operation name (for example: `insert`, `contains`).
    pub operation: &'static str,
    /// Backend-specific detail.
    pub detail: String,
}

impl StorageFault {
    /// Create a structured storage fault.
    pub fn new(backend: &'static str, operation: &'static str, detail: impl Into<String>) -> Self {
        Self {
            backend,
            operation,
            detail: detail.into(),
        }
    }
}

/// Typed result for fingerprint insertion.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum InsertOutcome {
    /// Fingerprint was newly inserted.
    Inserted,
    /// Fingerprint already existed.
    AlreadyPresent,
    /// Storage subsystem fault occurred.
    StorageFault(StorageFault),
}

/// Typed result for fingerprint lookup.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum LookupOutcome {
    /// Fingerprint is present.
    Present,
    /// Fingerprint is absent.
    Absent,
    /// Storage subsystem fault occurred.
    StorageFault(StorageFault),
}

/// Capacity status for fingerprint storage.
#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
pub enum CapacityStatus {
    /// Normal operation.
    Normal,
    /// Approaching capacity.
    Warning {
        /// Current resident count.
        count: usize,
        /// Maximum capacity.
        capacity: usize,
        /// Usage fraction in the range `[0.0, 1.0]`.
        usage: f64,
    },
    /// Near or at capacity.
    Critical {
        /// Current resident count.
        count: usize,
        /// Maximum capacity.
        capacity: usize,
        /// Usage fraction in the range `[0.0, 1.0]`.
        usage: f64,
    },
}

/// Storage counters exposed through [`FingerprintSet`].
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct StorageStats {
    /// Fingerprints currently resident in the in-memory tier.
    pub memory_count: usize,
    /// Bytes reserved by the in-memory storage tier.
    pub memory_bytes: usize,
}

/// Trait for deduplication fingerprint sets.
pub trait FingerprintSet<F>: Send + Sync {
    /// Insert a fingerprint with typed outcome.
    fn insert_checked(&self, fingerprint: F) -> InsertOutcome;

    /// Check whether a fingerprint is present with typed outcome.
    fn contains_checked(&self, fingerprint: F) -> LookupOutcome;

    /// Return the number of fingerprints.
    fn len(&self) -> usize;

    /// Check if empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Check if any insert errors have occurred (e.g., table overflow).
    ///
    /// When this returns true, some fingerprints may not have been stored
    /// and the exploration may be incomplete.
    ///
    /// Default implementation returns false (no errors possible).
    fn has_errors(&self) -> bool {
        false
    }

    /// Get the count of dropped fingerprints due to errors.
    ///
    /// If this is non-zero, exploration results are unreliable.
    ///
    /// Default implementation returns 0 (no errors possible).
    fn dropped_count(&self) -> usize {
        0
    }

    /// Check the current capacity status.
    fn capacity_status(&self) -> CapacityStatus {
        CapacityStatus::Normal
    }

    /// Return backend storage counters for observability.
    fn stats(&self) -> StorageStats {
        StorageStats::default()
    }
}

/// In-memory fingerprint storage backed by `FxHashSet`.
pub struct InMemoryFingerprintSet<F> {
    inner: RwLock<FxHashSet<F>>,
}

impl<F> InMemoryFingerprintSet<F>
where
    F: Copy + Eq + Hash,
{
    /// Create an empty set.
    pub fn new() -> Self {
        Self {
            inner: RwLock::new(FxHashSet::default()),
        }
    }

    /// Create an empty set with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: RwLock::new(FxHashSet::with_capacity_and_hasher(
                capacity,
                Default::default(),
            )),
        }
    }
}

impl<F> Default for InMemoryFingerprintSet<F>
where
    F: Copy + Eq + Hash,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<F> FingerprintSet<F> for InMemoryFingerprintSet<F>
where
    F: Copy + Eq + Hash + Send + Sync,
{
    fn insert_checked(&self, fingerprint: F) -> InsertOutcome {
        if self.inner.write().insert(fingerprint) {
            InsertOutcome::Inserted
        } else {
            InsertOutcome::AlreadyPresent
        }
    }

    fn contains_checked(&self, fingerprint: F) -> LookupOutcome {
        if self.inner.read().contains(&fingerprint) {
            LookupOutcome::Present
        } else {
            LookupOutcome::Absent
        }
    }

    fn len(&self) -> usize {
        self.inner.read().len()
    }

    fn stats(&self) -> StorageStats {
        let guard = self.inner.read();
        StorageStats {
            memory_count: guard.len(),
            memory_bytes: guard.capacity() * std::mem::size_of::<F>(),
        }
    }
}

/// Sharded in-memory fingerprint storage tuned for parallel insert-heavy workloads.
pub struct ShardedFingerprintSet<F> {
    shards: Vec<RwLock<FxHashSet<F>>>,
}

impl<F> ShardedFingerprintSet<F>
where
    F: Copy + Eq + Hash,
{
    /// Create a sharded set with an explicit shard count.
    #[must_use]
    pub fn with_shard_count(shard_count: usize) -> Self {
        let shard_count = shard_count.max(1).next_power_of_two();
        let mut shards = Vec::with_capacity(shard_count);
        for _ in 0..shard_count {
            shards.push(RwLock::new(FxHashSet::default()));
        }
        Self { shards }
    }

    fn shard_index(&self, fingerprint: &F) -> usize {
        let mut hasher = FxHasher::default();
        fingerprint.hash(&mut hasher);
        (hasher.finish() as usize) & (self.shards.len() - 1)
    }
}

impl<F> Default for ShardedFingerprintSet<F>
where
    F: Copy + Eq + Hash,
{
    fn default() -> Self {
        let parallelism = std::thread::available_parallelism()
            .map(|parallelism| parallelism.get())
            .unwrap_or(4);
        Self::with_shard_count((parallelism * 4).clamp(4, 256))
    }
}

impl<F> FingerprintSet<F> for ShardedFingerprintSet<F>
where
    F: Copy + Eq + Hash + Send + Sync,
{
    fn insert_checked(&self, fingerprint: F) -> InsertOutcome {
        let shard = &self.shards[self.shard_index(&fingerprint)];
        if shard.write().insert(fingerprint) {
            InsertOutcome::Inserted
        } else {
            InsertOutcome::AlreadyPresent
        }
    }

    fn contains_checked(&self, fingerprint: F) -> LookupOutcome {
        let shard = &self.shards[self.shard_index(&fingerprint)];
        if shard.read().contains(&fingerprint) {
            LookupOutcome::Present
        } else {
            LookupOutcome::Absent
        }
    }

    fn len(&self) -> usize {
        self.shards.iter().map(|shard| shard.read().len()).sum()
    }

    fn stats(&self) -> StorageStats {
        let mut stats = StorageStats::default();
        for shard in &self.shards {
            let guard = shard.read();
            stats.memory_count += guard.len();
            stats.memory_bytes += guard.capacity() * std::mem::size_of::<F>();
        }
        stats
    }
}
