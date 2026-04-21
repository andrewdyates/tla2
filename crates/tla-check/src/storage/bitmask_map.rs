// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitmask map enums dispatching between in-memory and disk-backed backends.
//!
//! Part of #3177. Mirrors the `SuccessorGraph` pattern from #3176.

use super::disk_bitmask::DiskStateBitmaskMap;
use super::disk_bitmask_action::DiskActionBitmaskMap;
use crate::state::Fingerprint;
use rustc_hash::FxHashMap;
use std::io;

pub(crate) trait StateBitmaskLookup {
    fn get_bits(&self, fp: &Fingerprint) -> Option<u64>;
}

pub(crate) trait ActionBitmaskLookup {
    fn get_bits(&self, key: &(Fingerprint, Fingerprint)) -> Option<u64>;
}

// ── State Bitmask Map ────────────────────────────────────────────────────

/// State-level bitmask storage for inline liveness recording.
///
/// Maps `Fingerprint -> u64` where each bit represents the result of a
/// fairness state leaf. `InMemory` is the default; `Disk` activates for
/// billion-state specs to keep BFS memory bounded.
pub(crate) enum StateBitmaskMap {
    /// In-memory HashMap (default, fast).
    InMemory(FxHashMap<Fingerprint, u64>),
    /// Disk-backed two-tier storage (bounded memory).
    Disk(DiskStateBitmaskMap),
}

impl Default for StateBitmaskMap {
    fn default() -> Self {
        Self::in_memory()
    }
}

impl StateBitmaskMap {
    pub(crate) fn in_memory() -> Self {
        StateBitmaskMap::InMemory(FxHashMap::default())
    }

    pub(crate) fn disk() -> io::Result<Self> {
        let disk = if let Some(threshold) =
            crate::liveness::debug::liveness_disk_bitmask_flush_threshold()
        {
            DiskStateBitmaskMap::with_flush_threshold(threshold)?
        } else {
            DiskStateBitmaskMap::new()?
        };
        Ok(StateBitmaskMap::Disk(disk))
    }

    #[cfg(test)]
    pub(crate) fn is_disk(&self) -> bool {
        matches!(self, StateBitmaskMap::Disk(_))
    }

    pub(crate) fn contains_key(&self, fp: &Fingerprint) -> bool {
        match self {
            StateBitmaskMap::InMemory(map) => map.contains_key(fp),
            StateBitmaskMap::Disk(disk) => disk.contains_key(fp),
        }
    }

    pub(crate) fn get(&self, fp: &Fingerprint) -> Option<u64> {
        match self {
            StateBitmaskMap::InMemory(map) => map.get(fp).copied(),
            StateBitmaskMap::Disk(disk) => disk.get(fp),
        }
    }

    /// Get-or-insert-default. For InMemory, returns `&mut u64` via HashMap entry.
    /// For Disk, returns `&mut u64` in the hot tier.
    pub(crate) fn get_or_insert_default(&mut self, fp: Fingerprint) -> &mut u64 {
        match self {
            StateBitmaskMap::InMemory(map) => map.entry(fp).or_default(),
            StateBitmaskMap::Disk(disk) => disk.get_or_insert_default(fp),
        }
    }

    /// OR bits into an entry (creates with 0 if absent in hot tier).
    pub(crate) fn or_bits(&mut self, fp: Fingerprint, bits: u64) {
        match self {
            StateBitmaskMap::InMemory(map) => {
                *map.entry(fp).or_default() |= bits;
            }
            StateBitmaskMap::Disk(disk) => disk.or_bits(fp, bits),
        }
    }

    pub(crate) fn len(&self) -> usize {
        match self {
            StateBitmaskMap::InMemory(map) => map.len(),
            StateBitmaskMap::Disk(disk) => disk.len(),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub(crate) fn clear(&mut self) {
        match self {
            StateBitmaskMap::InMemory(map) => map.clear(),
            StateBitmaskMap::Disk(disk) => disk.clear(),
        }
    }

    /// Flush hot tier to cold if using disk backend and threshold exceeded.
    pub(crate) fn maybe_flush(&mut self) -> io::Result<()> {
        match self {
            StateBitmaskMap::InMemory(_) => Ok(()),
            StateBitmaskMap::Disk(disk) => disk.maybe_flush(),
        }
    }
}

impl StateBitmaskLookup for StateBitmaskMap {
    fn get_bits(&self, fp: &Fingerprint) -> Option<u64> {
        self.get(fp)
    }
}

impl StateBitmaskLookup for FxHashMap<Fingerprint, u64> {
    fn get_bits(&self, fp: &Fingerprint) -> Option<u64> {
        self.get(fp).copied()
    }
}

// ── Action Bitmask Map ───────────────────────────────────────────────────

/// Action-level bitmask storage for inline liveness recording.
///
/// Maps `(Fingerprint, Fingerprint) -> u64` where each bit represents the
/// result of a fairness action leaf.
pub(crate) enum ActionBitmaskMap {
    /// In-memory HashMap (default, fast).
    InMemory(FxHashMap<(Fingerprint, Fingerprint), u64>),
    /// Disk-backed two-tier storage (bounded memory).
    Disk(DiskActionBitmaskMap),
}

impl Default for ActionBitmaskMap {
    fn default() -> Self {
        Self::in_memory()
    }
}

impl ActionBitmaskMap {
    pub(crate) fn in_memory() -> Self {
        ActionBitmaskMap::InMemory(FxHashMap::default())
    }

    pub(crate) fn disk() -> io::Result<Self> {
        let disk = if let Some(threshold) =
            crate::liveness::debug::liveness_disk_bitmask_flush_threshold()
        {
            DiskActionBitmaskMap::with_flush_threshold(threshold)?
        } else {
            DiskActionBitmaskMap::new()?
        };
        Ok(ActionBitmaskMap::Disk(disk))
    }

    #[cfg(test)]
    pub(crate) fn is_disk(&self) -> bool {
        matches!(self, ActionBitmaskMap::Disk(_))
    }

    pub(crate) fn contains_key(&self, key: &(Fingerprint, Fingerprint)) -> bool {
        match self {
            ActionBitmaskMap::InMemory(map) => map.contains_key(key),
            ActionBitmaskMap::Disk(disk) => disk.contains_key(key),
        }
    }

    pub(crate) fn get(&self, key: &(Fingerprint, Fingerprint)) -> Option<u64> {
        match self {
            ActionBitmaskMap::InMemory(map) => map.get(key).copied(),
            ActionBitmaskMap::Disk(disk) => disk.get(key),
        }
    }

    pub(crate) fn get_or_insert_default(&mut self, key: (Fingerprint, Fingerprint)) -> &mut u64 {
        match self {
            ActionBitmaskMap::InMemory(map) => map.entry(key).or_default(),
            ActionBitmaskMap::Disk(disk) => disk.get_or_insert_default(key),
        }
    }

    /// Get a mutable reference to an existing entry in the hot/in-memory tier.
    ///
    /// For InMemory, this is the standard `get_mut`. For Disk, this only checks
    /// the hot tier — entries in the cold tier are finalized and immutable.
    pub(crate) fn get_mut(&mut self, key: &(Fingerprint, Fingerprint)) -> Option<&mut u64> {
        match self {
            ActionBitmaskMap::InMemory(map) => map.get_mut(key),
            ActionBitmaskMap::Disk(disk) => disk.get_hot_mut(key),
        }
    }

    pub(crate) fn or_bits(&mut self, key: (Fingerprint, Fingerprint), bits: u64) {
        match self {
            ActionBitmaskMap::InMemory(map) => {
                *map.entry(key).or_default() |= bits;
            }
            ActionBitmaskMap::Disk(disk) => disk.or_bits(key, bits),
        }
    }

    pub(crate) fn len(&self) -> usize {
        match self {
            ActionBitmaskMap::InMemory(map) => map.len(),
            ActionBitmaskMap::Disk(disk) => disk.len(),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub(crate) fn clear(&mut self) {
        match self {
            ActionBitmaskMap::InMemory(map) => map.clear(),
            ActionBitmaskMap::Disk(disk) => disk.clear(),
        }
    }

    pub(crate) fn maybe_flush(&mut self) -> io::Result<()> {
        match self {
            ActionBitmaskMap::InMemory(_) => Ok(()),
            ActionBitmaskMap::Disk(disk) => disk.maybe_flush(),
        }
    }
}

impl ActionBitmaskLookup for ActionBitmaskMap {
    fn get_bits(&self, key: &(Fingerprint, Fingerprint)) -> Option<u64> {
        self.get(key)
    }
}

impl ActionBitmaskLookup for FxHashMap<(Fingerprint, Fingerprint), u64> {
    fn get_bits(&self, key: &(Fingerprint, Fingerprint)) -> Option<u64> {
        self.get(key).copied()
    }
}
