// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bitmask map enums dispatching between in-memory and disk-backed backends.
//!
//! Part of #3177. Mirrors the `SuccessorGraph` pattern from #3176.
//!
//! Part of #4159: `LiveBitmask` extends bitmask storage beyond 64 tags using
//! `SmallVec<[u64; 1]>` for zero-overhead single-word case with dynamic growth.

use super::disk_bitmask::DiskStateBitmaskMap;
use super::disk_bitmask_action::DiskActionBitmaskMap;
use crate::liveness::LiveExpr;
use crate::state::Fingerprint;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::io;

// ── LiveBitmask ─────────────────────────────────────────────────────────

/// Variable-width bitmask for inline liveness recording.
///
/// Uses `SmallVec<[u64; 1]>` so specs with <=64 tags stay entirely on the stack
/// (zero heap allocation), while specs with >64 tags (e.g., AllocatorImpl with
/// 345 fairness tags) transparently grow to the heap.
///
/// Part of #4159: Removes the 64-tag ceiling that forced expensive per-tag
/// evaluator fallbacks.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct LiveBitmask {
    pub(crate) words: SmallVec<[u64; 1]>,
}

impl LiveBitmask {
    /// Set a specific tag bit.
    #[inline]
    pub(crate) fn set_tag(&mut self, tag: u32) {
        let word_idx = (tag / 64) as usize;
        let bit_idx = tag % 64;
        if word_idx >= self.words.len() {
            self.words.resize(word_idx + 1, 0);
        }
        self.words[word_idx] |= 1u64 << bit_idx;
    }

    /// Test whether a specific tag bit is set.
    #[inline]
    pub(crate) fn get_tag(&self, tag: u32) -> bool {
        let word_idx = (tag / 64) as usize;
        let bit_idx = tag % 64;
        word_idx < self.words.len() && self.words[word_idx] & (1u64 << bit_idx) != 0
    }

    /// Bitwise OR-assign another bitmask into this one.
    pub(crate) fn or_assign(&mut self, other: &LiveBitmask) {
        if other.words.len() > self.words.len() {
            self.words.resize(other.words.len(), 0);
        }
        for (i, &w) in other.words.iter().enumerate() {
            self.words[i] |= w;
        }
    }

    /// Return the first u64 word (backward compatibility with u64-based APIs).
    #[inline]
    pub(crate) fn first_word(&self) -> u64 {
        self.words.first().copied().unwrap_or(0)
    }

    /// Construct from a single u64 value (backward compatibility).
    #[inline]
    pub(crate) fn from_u64(val: u64) -> Self {
        if val == 0 {
            Self::default()
        } else {
            Self {
                words: SmallVec::from_buf([val]),
            }
        }
    }
}

/// Reconstruct a check result from a `LiveBitmask` (multi-word capable).
///
/// This is the multi-word counterpart of `reconstruct_check_from_tag_bits`
/// in `ea_precompute_cache.rs`. Tags beyond word 0 are correctly handled.
pub(crate) fn reconstruct_check_from_bitmask(
    expr: &LiveExpr,
    state_bm: &LiveBitmask,
    action_bm: &LiveBitmask,
) -> bool {
    match expr {
        LiveExpr::Bool(b) => *b,
        LiveExpr::StatePred { tag, .. } | LiveExpr::Enabled { tag, .. } => {
            state_bm.get_tag(*tag)
        }
        LiveExpr::ActionPred { tag, .. } | LiveExpr::StateChanged { tag, .. } => {
            action_bm.get_tag(*tag)
        }
        LiveExpr::Not(inner) => !reconstruct_check_from_bitmask(inner, state_bm, action_bm),
        LiveExpr::And(exprs) => exprs
            .iter()
            .all(|e| reconstruct_check_from_bitmask(e, state_bm, action_bm)),
        LiveExpr::Or(exprs) => exprs
            .iter()
            .any(|e| reconstruct_check_from_bitmask(e, state_bm, action_bm)),
        LiveExpr::Always(_) | LiveExpr::Eventually(_) | LiveExpr::Next(_) => false,
    }
}

// ── Lookup Traits ───────────────────────────────────────────────────────

pub(crate) trait StateBitmaskLookup {
    fn get_bits(&self, fp: &Fingerprint) -> Option<u64>;
}

pub(crate) trait ActionBitmaskLookup {
    fn get_bits(&self, key: &(Fingerprint, Fingerprint)) -> Option<u64>;
}

// ── State Bitmask Map ────────────────────────────────────────────────────

/// State-level bitmask storage for inline liveness recording.
///
/// Maps `Fingerprint -> LiveBitmask` where each bit represents the result of a
/// fairness state leaf. `InMemory` is the default; `Disk` activates for
/// billion-state specs to keep BFS memory bounded.
pub(crate) enum StateBitmaskMap {
    /// In-memory HashMap (default, fast).
    InMemory(FxHashMap<Fingerprint, LiveBitmask>),
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

    /// Get the first word of the bitmask (backward compatible u64 API).
    pub(crate) fn get(&self, fp: &Fingerprint) -> Option<u64> {
        match self {
            StateBitmaskMap::InMemory(map) => map.get(fp).map(|bm| bm.first_word()),
            StateBitmaskMap::Disk(disk) => disk.get(fp),
        }
    }

    /// Get a reference to the full `LiveBitmask` for a fingerprint.
    pub(crate) fn get_bitmask(&self, fp: &Fingerprint) -> Option<&LiveBitmask> {
        match self {
            StateBitmaskMap::InMemory(map) => map.get(fp),
            StateBitmaskMap::Disk(_disk) => None, // cold tier only stores first_word
        }
    }

    /// Ensure a fingerprint has an entry (creates with default if absent).
    /// Returns nothing -- use `get_bitmask` or `set_tag` for access.
    pub(crate) fn get_or_insert_default(&mut self, fp: Fingerprint) {
        match self {
            StateBitmaskMap::InMemory(map) => {
                map.entry(fp).or_default();
            }
            StateBitmaskMap::Disk(disk) => {
                disk.get_or_insert_default_bitmask(fp);
            }
        }
    }

    /// Get a mutable reference to the full `LiveBitmask`.
    pub(crate) fn get_or_insert_default_bitmask(&mut self, fp: Fingerprint) -> &mut LiveBitmask {
        match self {
            StateBitmaskMap::InMemory(map) => map.entry(fp).or_default(),
            StateBitmaskMap::Disk(disk) => disk.get_or_insert_default_bitmask(fp),
        }
    }

    /// Set a single tag bit for a fingerprint (creates entry if absent).
    pub(crate) fn set_tag(&mut self, fp: Fingerprint, tag: u32) {
        match self {
            StateBitmaskMap::InMemory(map) => {
                map.entry(fp).or_default().set_tag(tag);
            }
            StateBitmaskMap::Disk(disk) => disk.set_tag(fp, tag),
        }
    }

    /// OR bits into an entry (creates with 0 if absent in hot tier).
    /// Backward-compatible u64 API for JIT compiled bitmask results.
    pub(crate) fn or_bits(&mut self, fp: Fingerprint, bits: u64) {
        match self {
            StateBitmaskMap::InMemory(map) => {
                let bm = map.entry(fp).or_default();
                let existing = bm.first_word();
                if bm.words.is_empty() {
                    bm.words.push(existing | bits);
                } else {
                    bm.words[0] |= bits;
                }
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
/// Maps `(Fingerprint, Fingerprint) -> LiveBitmask` where each bit represents the
/// result of a fairness action leaf.
pub(crate) enum ActionBitmaskMap {
    /// In-memory HashMap (default, fast).
    InMemory(FxHashMap<(Fingerprint, Fingerprint), LiveBitmask>),
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

    /// Get the first word of the bitmask (backward compatible u64 API).
    pub(crate) fn get(&self, key: &(Fingerprint, Fingerprint)) -> Option<u64> {
        match self {
            ActionBitmaskMap::InMemory(map) => map.get(key).map(|bm| bm.first_word()),
            ActionBitmaskMap::Disk(disk) => disk.get(key),
        }
    }

    /// Get a reference to the full `LiveBitmask`.
    pub(crate) fn get_bitmask(&self, key: &(Fingerprint, Fingerprint)) -> Option<&LiveBitmask> {
        match self {
            ActionBitmaskMap::InMemory(map) => map.get(key),
            ActionBitmaskMap::Disk(_disk) => None, // cold tier only stores first_word
        }
    }

    /// Ensure a key has an entry (creates with default if absent).
    pub(crate) fn get_or_insert_default(&mut self, key: (Fingerprint, Fingerprint)) {
        match self {
            ActionBitmaskMap::InMemory(map) => {
                map.entry(key).or_default();
            }
            ActionBitmaskMap::Disk(disk) => {
                disk.get_or_insert_default_bitmask(key);
            }
        }
    }

    /// Get a mutable reference to the full `LiveBitmask`.
    pub(crate) fn get_or_insert_default_bitmask(
        &mut self,
        key: (Fingerprint, Fingerprint),
    ) -> &mut LiveBitmask {
        match self {
            ActionBitmaskMap::InMemory(map) => map.entry(key).or_default(),
            ActionBitmaskMap::Disk(disk) => disk.get_or_insert_default_bitmask(key),
        }
    }

    /// Get a mutable reference to an existing entry in the hot/in-memory tier.
    ///
    /// For InMemory, this is the standard `get_mut`. For Disk, this only checks
    /// the hot tier -- entries in the cold tier are finalized and immutable.
    pub(crate) fn get_mut_bitmask(
        &mut self,
        key: &(Fingerprint, Fingerprint),
    ) -> Option<&mut LiveBitmask> {
        match self {
            ActionBitmaskMap::InMemory(map) => map.get_mut(key),
            ActionBitmaskMap::Disk(disk) => disk.get_hot_mut_bitmask(key),
        }
    }

    /// Set a single tag bit for a key (creates entry if absent).
    pub(crate) fn set_tag(&mut self, key: (Fingerprint, Fingerprint), tag: u32) {
        match self {
            ActionBitmaskMap::InMemory(map) => {
                map.entry(key).or_default().set_tag(tag);
            }
            ActionBitmaskMap::Disk(disk) => disk.set_tag(key, tag),
        }
    }

    /// OR bits into an entry (backward-compatible u64 API for JIT).
    pub(crate) fn or_bits(&mut self, key: (Fingerprint, Fingerprint), bits: u64) {
        match self {
            ActionBitmaskMap::InMemory(map) => {
                let bm = map.entry(key).or_default();
                let existing = bm.first_word();
                if bm.words.is_empty() {
                    bm.words.push(existing | bits);
                } else {
                    bm.words[0] |= bits;
                }
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

// ── Tests ────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_live_bitmask_default_empty() {
        let bm = LiveBitmask::default();
        assert_eq!(bm.first_word(), 0);
        assert!(!bm.get_tag(0));
        assert!(!bm.get_tag(63));
        assert!(!bm.get_tag(64));
    }

    #[test]
    fn test_live_bitmask_set_get_low_tags() {
        let mut bm = LiveBitmask::default();
        bm.set_tag(0);
        bm.set_tag(5);
        bm.set_tag(63);
        assert!(bm.get_tag(0));
        assert!(bm.get_tag(5));
        assert!(bm.get_tag(63));
        assert!(!bm.get_tag(1));
        assert!(!bm.get_tag(64));
        assert_eq!(bm.first_word(), (1u64 << 0) | (1u64 << 5) | (1u64 << 63));
    }

    #[test]
    fn test_live_bitmask_set_get_high_tags() {
        let mut bm = LiveBitmask::default();
        bm.set_tag(64);
        bm.set_tag(127);
        bm.set_tag(200);
        assert!(bm.get_tag(64));
        assert!(bm.get_tag(127));
        assert!(bm.get_tag(200));
        assert!(!bm.get_tag(0));
        assert!(!bm.get_tag(63));
        assert_eq!(bm.first_word(), 0); // no low bits set
    }

    #[test]
    fn test_live_bitmask_or_assign() {
        let mut a = LiveBitmask::default();
        a.set_tag(5);
        a.set_tag(100);
        let mut b = LiveBitmask::default();
        b.set_tag(10);
        b.set_tag(200);
        a.or_assign(&b);
        assert!(a.get_tag(5));
        assert!(a.get_tag(10));
        assert!(a.get_tag(100));
        assert!(a.get_tag(200));
    }

    #[test]
    fn test_live_bitmask_from_u64() {
        let bm = LiveBitmask::from_u64(0xFF);
        assert_eq!(bm.first_word(), 0xFF);
        assert!(bm.get_tag(0));
        assert!(bm.get_tag(7));
        assert!(!bm.get_tag(8));
    }

    #[test]
    fn test_live_bitmask_from_u64_zero() {
        let bm = LiveBitmask::from_u64(0);
        assert_eq!(bm.first_word(), 0);
        assert!(!bm.get_tag(0));
    }

    #[test]
    fn test_state_bitmask_map_set_tag() {
        let mut map = StateBitmaskMap::in_memory();
        let fp = Fingerprint(42);
        map.set_tag(fp, 5);
        map.set_tag(fp, 100);
        assert!(map.contains_key(&fp));
        // .get() returns first_word only
        assert_eq!(map.get(&fp), Some(1u64 << 5));
        // .get_bitmask() returns full multi-word bitmask
        let bm = map.get_bitmask(&fp).unwrap();
        assert!(bm.get_tag(5));
        assert!(bm.get_tag(100));
    }

    #[test]
    fn test_action_bitmask_map_set_tag() {
        let mut map = ActionBitmaskMap::in_memory();
        let key = (Fingerprint(1), Fingerprint(2));
        map.set_tag(key, 10);
        map.set_tag(key, 130);
        assert!(map.contains_key(&key));
        assert_eq!(map.get(&key), Some(1u64 << 10));
        let bm = map.get_bitmask(&key).unwrap();
        assert!(bm.get_tag(10));
        assert!(bm.get_tag(130));
    }

    #[test]
    fn test_action_bitmask_map_get_mut_bitmask() {
        let mut map = ActionBitmaskMap::in_memory();
        let key = (Fingerprint(1), Fingerprint(2));
        map.get_or_insert_default(key);
        if let Some(bm) = map.get_mut_bitmask(&key) {
            bm.set_tag(77);
        }
        let bm = map.get_bitmask(&key).unwrap();
        assert!(bm.get_tag(77));
    }
}
