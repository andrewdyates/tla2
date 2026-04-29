// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;
use std::time::Instant;

use crate::marking::{PreparedMarking, TokenWidth};
use crate::memory::{compute_max_states, compute_max_states_for_full_graph};
use crate::petri_net::{PetriNet, TransitionIdx};
use crate::stubborn::PorStrategy;

/// Default memory fraction for auto-sizing (25% of available RAM).
///
/// Conservative to leave room for queue, graph adjacency lists, and
/// per-state marking vectors used by [`super::explore_full`].
const DEFAULT_MEMORY_FRACTION: f64 = 0.25;

/// Deadline check interval: check wall-clock every N states to amortize
/// the cost of `Instant::now()` (a syscall on most platforms).
pub(crate) const DEADLINE_CHECK_INTERVAL: u32 = 4096;

/// Private auto-sizing basis stored when `max_states` was computed from
/// available memory. Retains enough information to recompute the state budget
/// when configuration options (like fingerprint mode) change after construction.
#[derive(Debug, Clone, Copy)]
struct AutoSizingBasis {
    fraction: f64,
    packed_places: usize,
    width: TokenWidth,
}

/// Storage backend for fingerprint/state-ID deduplication.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum StorageMode {
    /// Pure in-memory hash-based deduplication.
    #[default]
    Memory,
    /// File-backed memory-mapped open-addressed tables.
    Mmap,
    /// Two-tier storage with mmap primary and sorted disk overflow.
    Disk,
    /// Fingerprint-only BFS using a lock-free `CasFingerprintSet` (8 bytes/state).
    ///
    /// Stores only a 64-bit fingerprint per seen state instead of a full 128-bit
    /// fingerprint in an `FxHashSet`. The BFS queue still carries packed markings
    /// for successor computation, but the seen-set is dramatically more
    /// memory-efficient for large state spaces.
    FingerprintOnly,
}

/// Fingerprint set backend for parallel BFS deduplication.
///
/// Controls the data structure used for fingerprint deduplication in parallel
/// exploration. `Sharded` is the existing `RwLock`-based default; `Cas` uses
/// lock-free CAS-based open addressing from [`tla_mc_core::PartitionedCasFingerprintSet`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum FpsetBackend {
    /// Existing `ShardedFingerprintSet` with `RwLock` per shard (default).
    #[default]
    Sharded,
    /// Lock-free CAS-based `PartitionedCasFingerprintSet` (16 partitions).
    ///
    /// Eliminates `RwLock` contention that caps `ShardedFingerprintSet`
    /// throughput at ~4 workers. Uses XOR-fold to reduce u128 fingerprints
    /// to u64 for the CAS table.
    Cas,
}

/// Checkpoint configuration for observer-based Petri net exploration.
#[derive(Debug, Clone)]
pub struct CheckpointConfig {
    pub(crate) dir: PathBuf,
    pub(crate) interval_states: usize,
    pub(crate) resume: bool,
    #[cfg(test)]
    pub(crate) stop_after_first_save: bool,
}

impl CheckpointConfig {
    /// Create checkpoint settings for the given directory and save interval.
    #[must_use]
    pub fn new(dir: PathBuf, interval_states: usize) -> Self {
        Self {
            dir,
            interval_states: interval_states.max(1),
            resume: false,
            #[cfg(test)]
            stop_after_first_save: false,
        }
    }

    /// Enable resume-from-checkpoint mode.
    #[must_use]
    pub fn with_resume(mut self, resume: bool) -> Self {
        self.resume = resume;
        self
    }

    #[cfg(test)]
    #[must_use]
    pub(crate) fn with_stop_after_first_save(mut self, stop: bool) -> Self {
        self.stop_after_first_save = stop;
        self
    }
}

/// Configuration for state space exploration.
///
/// Construct via [`ExplorationConfig::new`], [`ExplorationConfig::auto_sized`],
/// or [`ExplorationConfig::default`]. Use chainable setters (`with_deadline`,
/// `with_workers`, `with_fingerprint_dedup`) to customize.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub struct ExplorationConfig {
    /// Maximum number of unique states before giving up.
    max_states: usize,
    /// Wall-clock deadline (from [`crate::timeout::compute_deadline`]).
    deadline: Option<Instant>,
    /// Maximum worker count for BFS exploration.
    ///
    /// `1` forces sequential exploration. Values greater than `1` allow the
    /// observer-mode dispatcher to choose a smaller effective worker count when
    /// the pilot run predicts that extra coordination would cost more than it
    /// saves.
    workers: usize,
    /// Partial-order reduction strategy. `PorStrategy::None` disables POR (default).
    pub(crate) por_strategy: PorStrategy,
    /// Auto-sizing basis for recomputing `max_states` when config changes.
    /// `Some(basis)` means `max_states` was auto-computed. `None` means it was
    /// explicitly set and should not be overridden.
    auto_sizing: Option<AutoSizingBasis>,
    /// Use fingerprint-based state deduplication (u128 hash instead of full
    /// packed marking). Reduces per-state memory from `packed_size + 48` bytes
    /// to ~32 bytes. Default: `true`.
    fingerprint_dedup: bool,
    /// Fingerprint/state-ID storage backend.
    storage_mode: StorageMode,
    /// Optional primary-tier capacity override for mmap/disk storage.
    storage_primary_capacity: Option<usize>,
    /// Optional directory for mmap/disk backing files.
    storage_dir: Option<PathBuf>,
    /// Optional checkpoint/resume settings for sequential observer exploration.
    checkpoint: Option<CheckpointConfig>,
    /// Fingerprint set backend for parallel BFS deduplication.
    fpset_backend: FpsetBackend,
    /// Use diff-based successor computation with incremental fingerprinting.
    ///
    /// When enabled, transition firings produce [`DiffSuccessor`] diffs instead
    /// of full marking copies. The successor fingerprint is computed
    /// incrementally from the parent's XOR fingerprint and only the changed
    /// places, avoiding full-marking hashing. Full markings are materialized
    /// only for genuinely new states (~5% of successors in typical nets).
    ///
    /// Default: `false` (opt-in).
    diff_successors: bool,
}

impl Default for ExplorationConfig {
    fn default() -> Self {
        Self {
            max_states: 10_000_000,
            deadline: None,
            workers: 1,
            por_strategy: PorStrategy::None,
            auto_sizing: None,
            fingerprint_dedup: true,
            storage_mode: StorageMode::Memory,
            storage_primary_capacity: None,
            storage_dir: None,
            checkpoint: None,
            fpset_backend: FpsetBackend::default(),
            diff_successors: false,
        }
    }
}

impl ExplorationConfig {
    /// Create a configuration with the given state limit.
    ///
    /// Deadline defaults to `None` (no wall-clock limit) and workers to `1`
    /// (sequential BFS). Use [`with_deadline`](Self::with_deadline) and
    /// [`with_workers`](Self::with_workers) to customize.
    #[must_use]
    pub fn new(max_states: usize) -> Self {
        Self {
            max_states,
            deadline: None,
            workers: 1,
            por_strategy: PorStrategy::None,
            auto_sizing: None,
            fingerprint_dedup: true,
            storage_mode: StorageMode::Memory,
            storage_primary_capacity: None,
            storage_dir: None,
            checkpoint: None,
            fpset_backend: FpsetBackend::default(),
            diff_successors: false,
        }
    }

    /// Set the wall-clock deadline.
    #[must_use]
    pub fn with_deadline(mut self, deadline: Option<Instant>) -> Self {
        self.deadline = deadline;
        self
    }

    /// Return the configured state-space budget.
    #[must_use]
    pub fn max_states(&self) -> usize {
        self.max_states
    }

    /// Return the configured wall-clock deadline.
    #[must_use]
    pub fn deadline(&self) -> Option<Instant> {
        self.deadline
    }

    /// Return the configured maximum BFS worker count.
    ///
    /// `1` forces sequential exploration. Values greater than `1` are a cap:
    /// observer-mode exploration may choose a smaller parallel worker count or
    /// fall back to sequential execution after its pilot analysis.
    #[must_use]
    pub fn workers(&self) -> usize {
        self.workers
    }

    /// Set the maximum number of BFS worker threads.
    ///
    /// Values below `1` are clamped to `1`, which forces sequential
    /// exploration. Values above `1` opt into adaptive observer-mode
    /// exploration, where the configured value is treated as a parallelism cap
    /// rather than a fixed thread count.
    #[must_use]
    pub fn with_workers(mut self, workers: usize) -> Self {
        self.workers = workers.max(1);
        self
    }

    /// Set the partial-order reduction strategy.
    ///
    /// When set to anything other than [`PorStrategy::None`], the BFS explorer
    /// computes stubborn sets at each state and fires only the reduced
    /// transition set, preserving the correctness of the target property.
    #[must_use]
    pub(crate) fn with_por(mut self, strategy: PorStrategy) -> Self {
        self.por_strategy = strategy;
        self
    }

    /// Set the fingerprint deduplication mode.
    ///
    /// When enabled (default), states are stored as u128 fingerprints (~32
    /// bytes/state). When disabled, full packed markings are stored
    /// (`packed_size + 48` bytes/state).
    ///
    /// For auto-sized configs, changing the fingerprint mode automatically
    /// recomputes `max_states` to match the new per-state memory cost.
    #[must_use]
    pub fn with_fingerprint_dedup(mut self, enabled: bool) -> Self {
        if self.fingerprint_dedup == enabled {
            return self;
        }
        self.fingerprint_dedup = enabled;
        if let Some(basis) = self.auto_sizing {
            self.max_states =
                compute_max_states(basis.packed_places, basis.width, basis.fraction, enabled);
        }
        self
    }

    /// Returns the current fingerprint deduplication mode.
    #[must_use]
    pub fn fingerprint_dedup(&self) -> bool {
        self.fingerprint_dedup
    }

    /// Set the fingerprint/state-ID storage backend.
    #[must_use]
    pub fn with_storage_mode(mut self, mode: StorageMode) -> Self {
        self.storage_mode = mode;
        self
    }

    /// Return the configured fingerprint/state-ID storage backend.
    #[must_use]
    pub fn storage_mode(&self) -> StorageMode {
        self.storage_mode
    }

    /// Override the primary-tier capacity for mmap/disk storage.
    #[must_use]
    pub fn with_storage_primary_capacity(mut self, capacity: usize) -> Self {
        self.storage_primary_capacity = Some(capacity.max(1));
        self
    }

    /// Override the backing directory for mmap/disk storage.
    #[must_use]
    pub fn with_storage_dir(mut self, dir: Option<PathBuf>) -> Self {
        self.storage_dir = dir;
        self
    }

    /// Return the configured backing directory for mmap/disk/fingerprint-only storage.
    #[must_use]
    pub fn storage_dir(&self) -> Option<&PathBuf> {
        self.storage_dir.as_ref()
    }

    /// Attach checkpoint/resume settings to this exploration.
    #[must_use]
    pub fn with_checkpoint(mut self, checkpoint: CheckpointConfig) -> Self {
        self.checkpoint = Some(checkpoint);
        self
    }

    /// Returns the active checkpoint configuration, if any.
    #[must_use]
    pub fn checkpoint(&self) -> Option<&CheckpointConfig> {
        self.checkpoint.as_ref()
    }

    /// Set the fingerprint set backend for parallel BFS deduplication.
    ///
    /// [`FpsetBackend::Cas`] enables lock-free CAS-based deduplication,
    /// eliminating `RwLock` contention that caps `ShardedFingerprintSet`
    /// throughput at ~4 workers.
    #[must_use]
    pub fn with_fpset_backend(mut self, backend: FpsetBackend) -> Self {
        self.fpset_backend = backend;
        self
    }

    /// Returns the configured fingerprint set backend.
    #[must_use]
    pub fn fpset_backend(&self) -> FpsetBackend {
        self.fpset_backend
    }

    /// Enable diff-based successor computation with incremental fingerprinting.
    ///
    /// When enabled, transitions produce compact diffs (changed places only) and
    /// successor fingerprints are computed incrementally from the parent's XOR
    /// fingerprint. Full marking materialization is deferred until a state passes
    /// the deduplication check, avoiding allocation for the ~95% of successors
    /// that are duplicates.
    ///
    /// Default: `false`.
    #[must_use]
    pub fn with_diff_successors(mut self, enabled: bool) -> Self {
        self.diff_successors = enabled;
        self
    }

    /// Returns whether diff-based successor computation is enabled.
    #[must_use]
    pub fn diff_successors(&self) -> bool {
        self.diff_successors
    }

    /// Create a config with `max_states` auto-sized to available system memory.
    ///
    /// Computes the optimal state count based on the net's marking size and
    /// available RAM. Falls back to 10M if memory detection fails.
    ///
    /// `memory_fraction` controls what fraction of available memory to use
    /// (default 0.25). Pass `None` for the default.
    pub fn auto_sized(
        net: &PetriNet,
        deadline: Option<Instant>,
        memory_fraction: Option<f64>,
    ) -> Self {
        let prepared = PreparedMarking::analyze(net);
        let fraction = memory_fraction.unwrap_or(DEFAULT_MEMORY_FRACTION);
        let packed_places = prepared.packed_places();
        let max_states = compute_max_states(packed_places, prepared.width, fraction, true);
        Self {
            max_states,
            deadline,
            workers: 1,
            por_strategy: PorStrategy::None,
            auto_sizing: Some(AutoSizingBasis {
                fraction,
                packed_places,
                width: prepared.width,
            }),
            fingerprint_dedup: true,
            storage_mode: StorageMode::Memory,
            storage_primary_capacity: None,
            storage_dir: None,
            checkpoint: None,
            fpset_backend: FpsetBackend::default(),
            diff_successors: false,
        }
    }

    /// Re-compute `max_states` for a (potentially smaller) net.
    ///
    /// After structural reduction, the reduced net has fewer places, so each
    /// packed state is smaller and more states fit in the same memory budget.
    /// This recalculates `max_states` based on the reduced net's dimensions.
    ///
    /// Only applies to auto-sized configs. Configs with explicit `max_states`
    /// (via [`new`](Self::new)) are returned unchanged.
    #[must_use]
    pub fn refitted_for_net(&self, net: &PetriNet) -> Self {
        let Some(basis) = self.auto_sizing else {
            return self.clone();
        };
        let prepared = PreparedMarking::analyze(net);
        let packed_places = prepared.packed_places();
        let new_max = compute_max_states(
            packed_places,
            prepared.width,
            basis.fraction,
            self.fingerprint_dedup,
        );
        Self {
            max_states: new_max,
            deadline: self.deadline,
            workers: self.workers,
            por_strategy: self.por_strategy.clone(),
            auto_sizing: Some(AutoSizingBasis {
                fraction: basis.fraction,
                packed_places,
                width: prepared.width,
            }),
            fingerprint_dedup: self.fingerprint_dedup,
            storage_mode: self.storage_mode,
            storage_primary_capacity: self.storage_primary_capacity,
            storage_dir: self.storage_dir.clone(),
            checkpoint: self.checkpoint.clone(),
            fpset_backend: self.fpset_backend,
            diff_successors: self.diff_successors,
        }
    }

    /// Re-compute `max_states` for CTL/LTL full-graph exploration on `net`.
    ///
    /// `explore_full` stores unpacked `Vec<u64>` markings and adjacency in
    /// addition to fingerprint deduplication, so its auto-sized memory budget
    /// must be tighter than plain fingerprint-only exploration.
    ///
    /// Only applies to auto-sized configs. Configs with explicit `max_states`
    /// (via [`new`](Self::new)) are returned unchanged.
    #[must_use]
    pub(crate) fn refitted_for_full_graph(&self, net: &PetriNet) -> Self {
        let Some(basis) = self.auto_sizing else {
            return self.clone();
        };
        let prepared = PreparedMarking::analyze(net);
        let packed_places = prepared.packed_places();
        let new_max = compute_max_states_for_full_graph(
            net.num_places(),
            packed_places,
            prepared.width,
            basis.fraction,
        );
        Self {
            max_states: new_max,
            deadline: self.deadline,
            workers: self.workers,
            por_strategy: self.por_strategy.clone(),
            auto_sizing: Some(AutoSizingBasis {
                fraction: basis.fraction,
                packed_places,
                width: prepared.width,
            }),
            fingerprint_dedup: self.fingerprint_dedup,
            storage_mode: self.storage_mode,
            storage_primary_capacity: self.storage_primary_capacity,
            storage_dir: self.storage_dir.clone(),
            checkpoint: self.checkpoint.clone(),
            fpset_backend: self.fpset_backend,
            diff_successors: self.diff_successors,
        }
    }

    /// Return auto-sizing diagnostic info for logging.
    ///
    /// Useful for CLI output showing how many states will be explored.
    pub fn describe_auto(net: &PetriNet, memory_fraction: Option<f64>) -> AutoSizeInfo {
        let prepared = PreparedMarking::analyze(net);
        let fraction = memory_fraction.unwrap_or(DEFAULT_MEMORY_FRACTION);
        let packed_places = prepared.packed_places();
        let max_states = compute_max_states(packed_places, prepared.width, fraction, true);
        AutoSizeInfo {
            bytes_per_place: prepared.width.bytes(),
            num_places: net.num_places(),
            packed_places,
            max_states,
        }
    }
}

/// Diagnostic info from auto-sizing, for CLI output.
#[non_exhaustive]
pub struct AutoSizeInfo {
    /// Bytes per place in packed marking (1 for U8, 2 for U16, 8 for U64).
    pub bytes_per_place: usize,
    /// Number of places in the original net.
    pub num_places: usize,
    /// Number of places stored in the packed marking after implied-place exclusion.
    pub packed_places: usize,
    /// Computed max_states.
    pub max_states: usize,
}

/// Observer trait for exploration events. Implementations decide when
/// to stop early based on examination-specific criteria.
pub(crate) trait ExplorationObserver {
    /// Called when a new unique state is discovered.
    /// Return `false` to stop exploration immediately.
    fn on_new_state(&mut self, marking: &[u64]) -> bool;

    /// Called when a transition fires successfully.
    /// Return `false` to stop exploration immediately.
    fn on_transition_fire(&mut self, trans: TransitionIdx) -> bool;

    /// Called when a deadlock state is found (no enabled transitions).
    fn on_deadlock(&mut self, marking: &[u64]);

    /// Check if exploration should stop early.
    fn is_done(&self) -> bool;
}

/// Thread-local summary contract for observer-mode parallel BFS.
pub(crate) trait ParallelExplorationSummary: Send {
    /// Record a newly admitted unique state.
    fn on_new_state(&mut self, marking: &[u64]);

    /// Record a transition firing from an explored state.
    fn on_transition_fire(&mut self, trans: TransitionIdx);

    /// Record a deadlock state.
    fn on_deadlock(&mut self, marking: &[u64]);

    /// Whether the sequential observer would have requested an immediate stop
    /// while processing this frontier batch.
    fn stop_requested(&self) -> bool;
}

/// Observer support required by the frontier-parallel BFS backend.
pub(crate) trait ParallelExplorationObserver: ExplorationObserver {
    type Summary: ParallelExplorationSummary;

    /// Create a fresh batch summary using the observer's current state.
    fn new_summary(&self) -> Self::Summary;

    /// Merge a completed batch summary back into the canonical observer.
    fn merge_summary(&mut self, summary: Self::Summary);
}

/// Result of state space exploration.
#[derive(Debug, Clone)]
pub(crate) struct ExplorationResult {
    /// True if the entire reachable state space was explored.
    pub completed: bool,
    /// Number of unique states visited.
    #[cfg(test)]
    pub states_visited: usize,
    /// True if the observer requested early termination.
    #[cfg(test)]
    pub stopped_by_observer: bool,
}

impl ExplorationResult {
    pub(crate) fn new(completed: bool, _states_visited: usize, _stopped_by_observer: bool) -> Self {
        Self {
            completed,
            #[cfg(test)]
            states_visited: _states_visited,
            #[cfg(test)]
            stopped_by_observer: _stopped_by_observer,
        }
    }
}
