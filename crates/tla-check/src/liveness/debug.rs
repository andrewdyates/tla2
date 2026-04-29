// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Debug and profiling flags for liveness checking.

use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering::Relaxed};
use std::sync::OnceLock;

// feature_flag! macro defined in crate::debug_env (via #[macro_use])
feature_flag!(pub(crate) liveness_profile, "TLA2_LIVENESS_PROFILE");
// Part of #3746: When set, liveness checking panics on missing states instead
// of skipping them with a warning.  Use for debugging nondeterministic crashes.
// Set via `TLA2_STRICT_LIVENESS=1` or `--strict-liveness` CLI flag.
feature_flag!(pub(crate) strict_liveness, "TLA2_STRICT_LIVENESS");
feature_limit!(
    pub(crate) liveness_disk_graph_ptr_capacity,
    "TLA2_LIVENESS_DISK_PTR_CAPACITY",
    1 << 24
);

// Threshold (in estimated behavior-graph nodes) above which the liveness
// checker automatically switches to disk-backed graph storage.
// Default: 2M nodes.  Override with `TLA2_LIVENESS_AUTO_DISK_THRESHOLD`.
feature_limit!(
    pub(crate) liveness_auto_disk_threshold,
    "TLA2_LIVENESS_AUTO_DISK_THRESHOLD",
    2_000_000
);

const DISK_GRAPH_OVERRIDE_UNSET: u8 = 0;
const DISK_GRAPH_OVERRIDE_FALSE: u8 = 1;
const DISK_GRAPH_OVERRIDE_TRUE: u8 = 2;
const INMEMORY_NODE_LIMIT_OVERRIDE_UNSET: usize = usize::MAX;
const BITMASK_FLUSH_THRESHOLD_OVERRIDE_UNSET: usize = usize::MAX;

static FORCE_DISK_GRAPH: AtomicU8 = AtomicU8::new(DISK_GRAPH_OVERRIDE_UNSET);
static FORCE_DISK_SUCCESSORS: AtomicU8 = AtomicU8::new(DISK_GRAPH_OVERRIDE_UNSET);
static FORCE_DISK_BITMASKS: AtomicU8 = AtomicU8::new(DISK_GRAPH_OVERRIDE_UNSET);
static FORCE_INMEMORY_NODE_LIMIT: AtomicUsize =
    AtomicUsize::new(INMEMORY_NODE_LIMIT_OVERRIDE_UNSET);
static FORCE_INMEMORY_SUCCESSOR_LIMIT: AtomicUsize =
    AtomicUsize::new(INMEMORY_NODE_LIMIT_OVERRIDE_UNSET);
static FORCE_DISK_BITMASK_FLUSH_THRESHOLD: AtomicUsize =
    AtomicUsize::new(BITMASK_FLUSH_THRESHOLD_OVERRIDE_UNSET);

/// Whether the liveness checker should use the disk-backed behavior graph.
///
/// Production behavior is still controlled by `TLA2_LIVENESS_DISK_GRAPH`, but
/// tests can override it per-checker instance without fighting the cached env
/// lookup in a shared test binary.
pub(crate) fn use_disk_graph() -> bool {
    match FORCE_DISK_GRAPH.load(Relaxed) {
        DISK_GRAPH_OVERRIDE_TRUE => true,
        DISK_GRAPH_OVERRIDE_FALSE => false,
        _ => {
            static FLAG: OnceLock<bool> = OnceLock::new();
            crate::debug_env::env_flag_is_set(&FLAG, "TLA2_LIVENESS_DISK_GRAPH")
        }
    }
}

/// Set a process-local override for [`use_disk_graph`] until the returned guard
/// is dropped.
///
/// Hidden from normal docs via the crate root re-export; integration tests use
/// this instead of mutating `TLA2_LIVENESS_DISK_GRAPH` in-process.
#[cfg(any(test, feature = "testing"))]
pub fn set_use_disk_graph_override(value: bool) -> UseDiskGraphGuard {
    let previous = FORCE_DISK_GRAPH.swap(
        if value {
            DISK_GRAPH_OVERRIDE_TRUE
        } else {
            DISK_GRAPH_OVERRIDE_FALSE
        },
        Relaxed,
    );
    UseDiskGraphGuard { previous }
}

/// RAII guard that restores the previous disk-graph override on drop.
#[cfg(any(test, feature = "testing"))]
pub struct UseDiskGraphGuard {
    previous: u8,
}

#[cfg(any(test, feature = "testing"))]
impl Drop for UseDiskGraphGuard {
    fn drop(&mut self) {
        FORCE_DISK_GRAPH.store(self.previous, Relaxed);
    }
}

/// Whether the BFS successor cache should use a disk-backed store.
///
/// Part of #3176: separate from `TLA2_LIVENESS_DISK_GRAPH` (which controls the
/// post-BFS behavior graph). This controls the BFS-time `SuccessorGraph` used
/// to record parent→child transitions for liveness SCC analysis.
pub(crate) fn use_disk_successors() -> bool {
    match FORCE_DISK_SUCCESSORS.load(Relaxed) {
        DISK_GRAPH_OVERRIDE_TRUE => true,
        DISK_GRAPH_OVERRIDE_FALSE => false,
        _ => {
            static FLAG: OnceLock<bool> = OnceLock::new();
            crate::debug_env::env_flag_is_set(&FLAG, "TLA2_LIVENESS_DISK_SUCCESSORS")
        }
    }
}

/// Return the process-local disk-successor override when present.
pub(crate) fn disk_successors_override() -> Option<bool> {
    match FORCE_DISK_SUCCESSORS.load(Relaxed) {
        DISK_GRAPH_OVERRIDE_TRUE => Some(true),
        DISK_GRAPH_OVERRIDE_FALSE => Some(false),
        _ => None,
    }
}

/// Set a process-local override for [`use_disk_successors`] until the returned
/// guard is dropped.
#[cfg(any(test, feature = "testing"))]
pub fn set_use_disk_successors_override(value: bool) -> UseDiskSuccessorsGuard {
    let previous = FORCE_DISK_SUCCESSORS.swap(
        if value {
            DISK_GRAPH_OVERRIDE_TRUE
        } else {
            DISK_GRAPH_OVERRIDE_FALSE
        },
        Relaxed,
    );
    UseDiskSuccessorsGuard { previous }
}

/// RAII guard that restores the previous disk-successors override on drop.
#[cfg(any(test, feature = "testing"))]
pub struct UseDiskSuccessorsGuard {
    previous: u8,
}

#[cfg(any(test, feature = "testing"))]
impl Drop for UseDiskSuccessorsGuard {
    fn drop(&mut self) {
        FORCE_DISK_SUCCESSORS.store(self.previous, Relaxed);
    }
}

/// Whether the inline liveness bitmask maps should use disk-backed storage.
///
/// Part of #3177: separate from disk successors (#3176). Controls the
/// `StateBitmaskMap` and `ActionBitmaskMap` used during BFS inline liveness
/// recording. When enabled, bitmask entries spill to a sorted mmap file
/// to keep BFS memory bounded for billion-state specs.
pub(crate) fn use_disk_bitmasks() -> bool {
    match FORCE_DISK_BITMASKS.load(Relaxed) {
        DISK_GRAPH_OVERRIDE_TRUE => true,
        DISK_GRAPH_OVERRIDE_FALSE => false,
        _ => {
            static FLAG: OnceLock<bool> = OnceLock::new();
            crate::debug_env::env_flag_is_set(&FLAG, "TLA2_LIVENESS_DISK_BITMASKS")
        }
    }
}

/// Set a process-local override for [`use_disk_bitmasks`] until the returned
/// guard is dropped.
#[cfg(any(test, feature = "testing"))]
pub fn set_use_disk_bitmasks_override(value: bool) -> UseDiskBitmasksGuard {
    let previous = FORCE_DISK_BITMASKS.swap(
        if value {
            DISK_GRAPH_OVERRIDE_TRUE
        } else {
            DISK_GRAPH_OVERRIDE_FALSE
        },
        Relaxed,
    );
    UseDiskBitmasksGuard { previous }
}

/// RAII guard that restores the previous disk-bitmasks override on drop.
#[cfg(any(test, feature = "testing"))]
pub struct UseDiskBitmasksGuard {
    previous: u8,
}

#[cfg(any(test, feature = "testing"))]
impl Drop for UseDiskBitmasksGuard {
    fn drop(&mut self) {
        FORCE_DISK_BITMASKS.store(self.previous, Relaxed);
    }
}

/// Optional test/debug threshold for flushing liveness disk bitmask hot tiers.
///
/// Production uses the default threshold from `storage/disk_bitmask.rs`. Tests
/// can override it to force repeated hot->cold flushes on small specs so the
/// BFS boundary flush hooks are exercised deterministically.
pub(crate) fn liveness_disk_bitmask_flush_threshold() -> Option<usize> {
    let override_threshold = FORCE_DISK_BITMASK_FLUSH_THRESHOLD.load(Relaxed);
    if override_threshold != BITMASK_FLUSH_THRESHOLD_OVERRIDE_UNSET {
        return Some(override_threshold);
    }

    static LIMIT: OnceLock<Option<usize>> = OnceLock::new();
    *LIMIT.get_or_init(|| {
        std::env::var("TLA2_LIVENESS_DISK_BITMASK_FLUSH_THRESHOLD")
            .ok()
            .and_then(|value| value.trim().parse::<usize>().ok())
    })
}

/// Set a process-local override for [`liveness_disk_bitmask_flush_threshold`]
/// until the returned guard is dropped.
#[cfg(any(test, feature = "testing"))]
pub fn set_liveness_disk_bitmask_flush_threshold_override(
    value: Option<usize>,
) -> LivenessDiskBitmaskFlushThresholdGuard {
    let previous = FORCE_DISK_BITMASK_FLUSH_THRESHOLD.swap(
        value.unwrap_or(BITMASK_FLUSH_THRESHOLD_OVERRIDE_UNSET),
        Relaxed,
    );
    LivenessDiskBitmaskFlushThresholdGuard { previous }
}

/// RAII guard that restores the previous disk-bitmask flush-threshold override
/// on drop.
#[cfg(any(test, feature = "testing"))]
pub struct LivenessDiskBitmaskFlushThresholdGuard {
    previous: usize,
}

#[cfg(any(test, feature = "testing"))]
impl Drop for LivenessDiskBitmaskFlushThresholdGuard {
    fn drop(&mut self) {
        FORCE_DISK_BITMASK_FLUSH_THRESHOLD.store(self.previous, Relaxed);
    }
}

/// Limit for the in-memory liveness graph node count.
///
/// Defaults to 5 million nodes (~1 GB). Override with env var
/// `TLA2_LIVENESS_INMEMORY_NODE_LIMIT`. Set to `0` to disable.
///
/// Only the in-memory topology store enforces the budget.
/// The disk-backed backend ignores it, which lets tests deterministically prove
/// that disk-backed graph storage bypasses the in-memory graph wall.
pub(crate) fn liveness_inmemory_node_limit() -> Option<usize> {
    let override_limit = FORCE_INMEMORY_NODE_LIMIT.load(Relaxed);
    if override_limit != INMEMORY_NODE_LIMIT_OVERRIDE_UNSET {
        return Some(override_limit);
    }

    /// Default in-memory node limit: 5 million nodes.
    ///
    /// At ~200 bytes per `NodeInfo` (successors Vec, parent, depth, check masks),
    /// 5M nodes consumes ~1 GB. Beyond this, disk-backed mode should be used.
    /// Override with `TLA2_LIVENESS_INMEMORY_NODE_LIMIT` env var.
    /// Set to `0` to disable the limit entirely (not recommended).
    ///
    /// Part of #4080: previously defaulted to `None` (unlimited), which
    /// contributed to OOM kills when multiple agents ran in parallel.
    const DEFAULT_INMEMORY_NODE_LIMIT: usize = 5_000_000;

    static LIMIT: OnceLock<Option<usize>> = OnceLock::new();
    *LIMIT.get_or_init(|| {
        let from_env = std::env::var("TLA2_LIVENESS_INMEMORY_NODE_LIMIT")
            .ok()
            .and_then(|value| value.trim().parse::<usize>().ok());
        match from_env {
            Some(0) => None, // Explicit 0 disables the limit
            Some(n) => Some(n),
            None => Some(DEFAULT_INMEMORY_NODE_LIMIT),
        }
    })
}

/// Set a process-local override for [`liveness_inmemory_node_limit`] until the
/// returned guard is dropped.
#[cfg(any(test, feature = "testing"))]
pub fn set_liveness_inmemory_node_limit_override(
    value: Option<usize>,
) -> LivenessInMemoryNodeLimitGuard {
    let previous = FORCE_INMEMORY_NODE_LIMIT
        .swap(value.unwrap_or(INMEMORY_NODE_LIMIT_OVERRIDE_UNSET), Relaxed);
    LivenessInMemoryNodeLimitGuard { previous }
}

/// RAII guard that restores the previous in-memory node-limit override on drop.
#[cfg(any(test, feature = "testing"))]
pub struct LivenessInMemoryNodeLimitGuard {
    previous: usize,
}

#[cfg(any(test, feature = "testing"))]
impl Drop for LivenessInMemoryNodeLimitGuard {
    fn drop(&mut self) {
        FORCE_INMEMORY_NODE_LIMIT.store(self.previous, Relaxed);
    }
}

/// Limit for the in-memory BFS successor cache entry count.
///
/// Defaults to 5 million entries (~280 MB at avg 3 successors). Override with
/// env var `TLA2_LIVENESS_INMEMORY_SUCCESSOR_LIMIT`. Set to `0` to disable.
///
/// Only the in-memory successor cache enforces the budget.
/// The disk-backed successor cache ignores it, which lets tests
/// deterministically prove that disk-backed successor storage bypasses the
/// in-memory successor wall that motivated #3176.
pub(crate) fn liveness_inmemory_successor_limit() -> Option<usize> {
    let override_limit = FORCE_INMEMORY_SUCCESSOR_LIMIT.load(Relaxed);
    if override_limit != INMEMORY_NODE_LIMIT_OVERRIDE_UNSET {
        return Some(override_limit);
    }

    /// Default in-memory successor entry limit: 5 million entries.
    ///
    /// Each entry is `Fingerprint -> Vec<Fingerprint>` (16 bytes key + 24 bytes
    /// Vec header + N*8 bytes successors). At avg 3 successors per state, 5M
    /// entries is ~280 MB. Override with `TLA2_LIVENESS_INMEMORY_SUCCESSOR_LIMIT`.
    /// Set to `0` to disable the limit entirely (not recommended).
    ///
    /// Part of #4080: previously defaulted to `None` (unlimited).
    const DEFAULT_INMEMORY_SUCCESSOR_LIMIT: usize = 5_000_000;

    static LIMIT: OnceLock<Option<usize>> = OnceLock::new();
    *LIMIT.get_or_init(|| {
        let from_env = std::env::var("TLA2_LIVENESS_INMEMORY_SUCCESSOR_LIMIT")
            .ok()
            .and_then(|value| value.trim().parse::<usize>().ok());
        match from_env {
            Some(0) => None, // Explicit 0 disables the limit
            Some(n) => Some(n),
            None => Some(DEFAULT_INMEMORY_SUCCESSOR_LIMIT),
        }
    })
}

/// Set a process-local override for [`liveness_inmemory_successor_limit`]
/// until the returned guard is dropped.
#[cfg(any(test, feature = "testing"))]
pub fn set_liveness_inmemory_successor_limit_override(
    value: Option<usize>,
) -> LivenessInMemorySuccessorLimitGuard {
    let previous = FORCE_INMEMORY_SUCCESSOR_LIMIT
        .swap(value.unwrap_or(INMEMORY_NODE_LIMIT_OVERRIDE_UNSET), Relaxed);
    LivenessInMemorySuccessorLimitGuard { previous }
}

/// RAII guard that restores the previous in-memory successor-limit override on
/// drop.
#[cfg(any(test, feature = "testing"))]
pub struct LivenessInMemorySuccessorLimitGuard {
    previous: usize,
}

#[cfg(any(test, feature = "testing"))]
impl Drop for LivenessInMemorySuccessorLimitGuard {
    fn drop(&mut self) {
        FORCE_INMEMORY_SUCCESSOR_LIMIT.store(self.previous, Relaxed);
    }
}
