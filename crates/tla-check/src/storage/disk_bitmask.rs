// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Disk-backed state bitmask map for liveness inline recording.
//!
//! Part of #3177. Maps `Fingerprint -> LiveBitmask` with two-tier storage:
//!
//! - **Hot tier**: In-memory `FxHashMap<Fingerprint, LiveBitmask>` for active writes.
//! - **Cold tier**: Sorted fixed-size entries in an mmap file for overflow.
//!
//! When the hot tier exceeds its flush threshold, entries are sorted and
//! merge-interleaved with the existing cold file into a new mmap-backed file.
//! Lookups check hot first, then binary search on cold.
//!
//! The cold tier stores only the first u64 word of each `LiveBitmask` (via
//! `first_word()`). This is acceptable because disk backends activate only for
//! billion-state specs where multi-word bitmasks are unlikely (tag count is
//! spec-dependent, not state-count-dependent).
//!
//! The action bitmask map (`DiskActionBitmaskMap`) lives in the sibling
//! `disk_bitmask_action` module (Part of #3472 file split).
//!
//! ## File Format
//!
//! State bitmask entries: `[fp: u64, bitmask: u64]` — 16 bytes each, sorted by fp.
//!
//! ## Memory Savings
//!
//! During BFS, the hot tier stays bounded. Cold entries live on disk (OS pages
//! as needed). Post-BFS reads use binary search on the mmap view — no need to
//! load everything into memory.

use super::bitmask_map::LiveBitmask;
use crate::state::Fingerprint;
use memmap2::Mmap;
use rustc_hash::FxHashMap;
use std::io::{self, BufWriter, Write};

/// Default flush threshold: 2M entries.
const DEFAULT_FLUSH_THRESHOLD: usize = 2 * 1024 * 1024;

/// State bitmask entry size: `[fp: u64, bitmask: u64]` = 16 bytes.
const STATE_ENTRY_SIZE: usize = 16;

// ── State Bitmask Map ────────────────────────────────────────────────────

/// Disk-backed state bitmask map.
///
/// Maps `Fingerprint -> LiveBitmask` with two-tier storage. Hot tier for active BFS
/// writes, cold tier (sorted mmap file) for overflow.
pub(crate) struct DiskStateBitmaskMap {
    /// Hot tier: active entries being written/read during BFS.
    hot: FxHashMap<Fingerprint, LiveBitmask>,
    /// Cold tier: sorted entries in an mmap file.
    cold: Option<Mmap>,
    /// Number of entries in the cold tier.
    cold_count: usize,
    /// Backing file for the cold tier.
    backing_file: tempfile::NamedTempFile,
    /// Hot tier flush threshold.
    flush_threshold: usize,
}

impl DiskStateBitmaskMap {
    pub(crate) fn new() -> io::Result<Self> {
        Self::with_flush_threshold(DEFAULT_FLUSH_THRESHOLD)
    }

    pub(crate) fn with_flush_threshold(threshold: usize) -> io::Result<Self> {
        Ok(Self {
            hot: FxHashMap::default(),
            cold: None,
            cold_count: 0,
            backing_file: tempfile::NamedTempFile::new()?,
            flush_threshold: threshold,
        })
    }

    /// Check if a key exists in either tier.
    pub(crate) fn contains_key(&self, fp: &Fingerprint) -> bool {
        self.hot.contains_key(fp) || self.cold_contains(fp)
    }

    /// Get the first-word bitmask value for a key (checks hot first, then cold).
    pub(crate) fn get(&self, fp: &Fingerprint) -> Option<u64> {
        if let Some(bm) = self.hot.get(fp) {
            return Some(bm.first_word());
        }
        self.cold_get(fp)
    }

    /// Get a reference to the full `LiveBitmask` (hot tier only).
    pub(crate) fn get_bitmask(&self, fp: &Fingerprint) -> Option<&LiveBitmask> {
        self.hot.get(fp)
    }

    /// Get an owned `LiveBitmask` from either tier.
    pub(crate) fn get_bitmask_owned(&self, fp: &Fingerprint) -> Option<LiveBitmask> {
        if let Some(bm) = self.hot.get(fp) {
            return Some(bm.clone());
        }
        self.cold_get(fp).map(LiveBitmask::from_u64)
    }

    /// Insert or get-default in the hot tier. Returns a mutable reference.
    pub(crate) fn get_or_insert_default_bitmask(&mut self, fp: Fingerprint) -> &mut LiveBitmask {
        self.hot.entry(fp).or_default()
    }

    /// Set a single tag bit for a fingerprint.
    pub(crate) fn set_tag(&mut self, fp: Fingerprint, tag: u32) {
        self.hot.entry(fp).or_default().set_tag(tag);
    }

    /// OR bits into an existing or new entry (u64 backward compat).
    pub(crate) fn or_bits(&mut self, fp: Fingerprint, bits: u64) {
        let bm = self.hot.entry(fp).or_default();
        if bm.words.is_empty() {
            bm.words.push(bits);
        } else {
            bm.words[0] |= bits;
        }
    }

    /// OR a full bitmask into an existing or new entry.
    pub(crate) fn or_bitmask(&mut self, fp: Fingerprint, other: &LiveBitmask) {
        self.hot.entry(fp).or_default().or_assign(other);
    }

    /// Number of entries across both tiers.
    pub(crate) fn len(&self) -> usize {
        self.hot.len() + self.cold_count
    }

    /// Clear both tiers.
    pub(crate) fn clear(&mut self) {
        self.hot.clear();
        self.cold = None;
        self.cold_count = 0;
        self.backing_file
            .as_file()
            .set_len(0)
            .expect("disk state bitmask: truncate");
    }

    /// Flush hot tier to cold if threshold exceeded.
    ///
    /// Called periodically during BFS to keep memory bounded.
    pub(crate) fn maybe_flush(&mut self) -> io::Result<()> {
        if self.hot.len() >= self.flush_threshold {
            self.flush()?;
        }
        Ok(())
    }

    /// Force flush hot tier entries into the cold tier.
    fn flush(&mut self) -> io::Result<()> {
        if self.hot.is_empty() {
            return Ok(());
        }

        // Collect and sort hot entries by fingerprint. Extract first_word for cold storage.
        let mut hot_entries: Vec<(Fingerprint, u64)> = self
            .hot
            .drain()
            .map(|(fp, bm)| (fp, bm.first_word()))
            .collect();
        hot_entries.sort_unstable_by_key(|(fp, _)| fp.0);

        // Merge with existing cold entries.
        let merged = if self.cold_count > 0 {
            let cold_mmap = self
                .cold
                .as_ref()
                .expect("disk state bitmask: cold mmap missing");
            merge_state_entries(&hot_entries, cold_mmap.as_ref(), self.cold_count)
        } else {
            hot_entries
        };

        // Write merged entries to a new temp file, then swap.
        let new_file = tempfile::NamedTempFile::new()?;
        let total_bytes = merged.len() * STATE_ENTRY_SIZE;
        {
            let mut writer = BufWriter::with_capacity(64 * 1024, new_file.as_file().try_clone()?);
            for (fp, bitmask) in &merged {
                writer.write_all(&fp.0.to_le_bytes())?;
                writer.write_all(&bitmask.to_le_bytes())?;
            }
            writer.flush()?;
        }

        // Mmap the new file.
        let mmap = if total_bytes > 0 {
            Some(unsafe { Mmap::map(new_file.as_file())? })
        } else {
            None
        };

        self.cold = mmap;
        self.cold_count = merged.len();
        self.backing_file = new_file;
        Ok(())
    }

    /// Binary search for a fingerprint in the cold tier.
    fn cold_contains(&self, fp: &Fingerprint) -> bool {
        self.cold_get(fp).is_some()
    }

    /// Binary search lookup in the cold tier.
    fn cold_get(&self, fp: &Fingerprint) -> Option<u64> {
        let mmap = self.cold.as_ref()?;
        let bytes = mmap.as_ref();
        let target = fp.0;

        let mut lo = 0usize;
        let mut hi = self.cold_count;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let offset = mid * STATE_ENTRY_SIZE;
            let stored_fp = u64::from_le_bytes(
                bytes[offset..offset + 8]
                    .try_into()
                    .expect("disk state bitmask: read fp"),
            );
            match stored_fp.cmp(&target) {
                std::cmp::Ordering::Less => lo = mid + 1,
                std::cmp::Ordering::Greater => hi = mid,
                std::cmp::Ordering::Equal => {
                    let bitmask = u64::from_le_bytes(
                        bytes[offset + 8..offset + 16]
                            .try_into()
                            .expect("disk state bitmask: read bitmask"),
                    );
                    return Some(bitmask);
                }
            }
        }
        None
    }

    /// Iterate all entries (hot + cold). Used for post-BFS liveness checking.
    #[cfg(test)]
    pub(crate) fn iter(&self) -> impl Iterator<Item = (Fingerprint, u64)> + '_ {
        let hot_iter = self.hot.iter().map(|(&fp, bm)| (fp, bm.first_word()));
        let cold_iter = ColdStateIter {
            bytes: self.cold.as_ref().map(|m| m.as_ref()),
            count: self.cold_count,
            pos: 0,
        };
        hot_iter.chain(cold_iter)
    }
}

/// Merge sorted hot entries with sorted cold bytes into a single sorted Vec.
fn merge_state_entries(
    hot: &[(Fingerprint, u64)],
    cold_bytes: &[u8],
    cold_count: usize,
) -> Vec<(Fingerprint, u64)> {
    let mut result = Vec::with_capacity(hot.len() + cold_count);
    let mut hi = 0;
    let mut ci = 0;

    while hi < hot.len() && ci < cold_count {
        let cold_offset = ci * STATE_ENTRY_SIZE;
        let cold_fp =
            u64::from_le_bytes(cold_bytes[cold_offset..cold_offset + 8].try_into().unwrap());
        if hot[hi].0 .0 <= cold_fp {
            result.push(hot[hi]);
            hi += 1;
            // Skip duplicate in cold (shouldn't happen, but defensive).
            if hot[hi - 1].0 .0 == cold_fp {
                ci += 1;
            }
        } else {
            let bitmask = u64::from_le_bytes(
                cold_bytes[cold_offset + 8..cold_offset + 16]
                    .try_into()
                    .unwrap(),
            );
            result.push((Fingerprint(cold_fp), bitmask));
            ci += 1;
        }
    }

    // Drain remaining hot entries.
    while hi < hot.len() {
        result.push(hot[hi]);
        hi += 1;
    }

    // Drain remaining cold entries.
    while ci < cold_count {
        let cold_offset = ci * STATE_ENTRY_SIZE;
        let cold_fp =
            u64::from_le_bytes(cold_bytes[cold_offset..cold_offset + 8].try_into().unwrap());
        let bitmask = u64::from_le_bytes(
            cold_bytes[cold_offset + 8..cold_offset + 16]
                .try_into()
                .unwrap(),
        );
        result.push((Fingerprint(cold_fp), bitmask));
        ci += 1;
    }

    result
}

/// Iterator over cold state bitmask entries.
#[cfg(test)]
struct ColdStateIter<'a> {
    bytes: Option<&'a [u8]>,
    count: usize,
    pos: usize,
}

#[cfg(test)]
impl Iterator for ColdStateIter<'_> {
    type Item = (Fingerprint, u64);

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos >= self.count {
            return None;
        }
        let bytes = self.bytes?;
        let offset = self.pos * STATE_ENTRY_SIZE;
        let fp = u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap());
        let bitmask = u64::from_le_bytes(bytes[offset + 8..offset + 16].try_into().unwrap());
        self.pos += 1;
        Some((Fingerprint(fp), bitmask))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_state_insert_and_get() {
        let mut map = DiskStateBitmaskMap::with_flush_threshold(100).unwrap();
        let fp = Fingerprint(42);
        assert!(!map.contains_key(&fp));

        map.get_or_insert_default_bitmask(fp);
        assert!(map.contains_key(&fp));
        assert_eq!(map.get(&fp), Some(0));

        map.set_tag(fp, 3);
        assert_eq!(map.get(&fp), Some(1u64 << 3));

        map.set_tag(fp, 7);
        assert_eq!(map.get(&fp), Some((1u64 << 3) | (1u64 << 7)));
    }

    #[test]
    fn test_state_flush_and_cold_lookup() {
        let mut map = DiskStateBitmaskMap::with_flush_threshold(4).unwrap();

        // Insert entries up to threshold.
        for i in 0..4u64 {
            map.set_tag(Fingerprint(i * 10), i as u32);
        }
        assert_eq!(map.len(), 4);

        // Flush to cold.
        map.maybe_flush().unwrap();
        // Hot is drained, cold has 4 entries.
        assert_eq!(map.hot.len(), 0);
        assert_eq!(map.cold_count, 4);
        assert_eq!(map.len(), 4);

        // Lookups hit cold tier.
        assert_eq!(map.get(&Fingerprint(0)), Some(1u64 << 0));
        assert_eq!(map.get(&Fingerprint(10)), Some(1u64 << 1));
        assert_eq!(map.get(&Fingerprint(20)), Some(1u64 << 2));
        assert_eq!(map.get(&Fingerprint(30)), Some(1u64 << 3));
        assert!(map.get(&Fingerprint(99)).is_none());
    }

    #[test]
    fn test_state_merge_hot_and_cold() {
        let mut map = DiskStateBitmaskMap::with_flush_threshold(3).unwrap();

        // First batch -> cold.
        for i in [10u64, 30, 50] {
            map.or_bits(Fingerprint(i), i);
        }
        map.maybe_flush().unwrap();
        assert_eq!(map.cold_count, 3);

        // Second batch -> hot.
        for i in [20u64, 40, 60] {
            map.or_bits(Fingerprint(i), i);
        }
        map.maybe_flush().unwrap();
        // Merged: 10, 20, 30, 40, 50, 60.
        assert_eq!(map.cold_count, 6);
        assert_eq!(map.hot.len(), 0);

        // Verify all entries survived the merge.
        for i in [10, 20, 30, 40, 50, 60] {
            assert_eq!(map.get(&Fingerprint(i)), Some(i), "missing fp={i}");
        }
    }

    #[test]
    fn test_state_clear() {
        let mut map = DiskStateBitmaskMap::with_flush_threshold(100).unwrap();
        map.or_bits(Fingerprint(1), 42);
        map.flush().unwrap();
        map.or_bits(Fingerprint(2), 99);
        assert_eq!(map.len(), 2);

        map.clear();
        assert_eq!(map.len(), 0);
        assert!(!map.contains_key(&Fingerprint(1)));
        assert!(!map.contains_key(&Fingerprint(2)));
    }

    #[test]
    fn test_state_iter() {
        let mut map = DiskStateBitmaskMap::with_flush_threshold(3).unwrap();
        map.or_bits(Fingerprint(10), 1);
        map.or_bits(Fingerprint(20), 2);
        map.or_bits(Fingerprint(30), 3);
        map.flush().unwrap();
        map.or_bits(Fingerprint(40), 4);

        let mut entries: Vec<_> = map.iter().collect();
        entries.sort_by_key(|(fp, _)| fp.0);
        assert_eq!(entries.len(), 4);
        assert_eq!(entries[0], (Fingerprint(10), 1));
        assert_eq!(entries[3], (Fingerprint(40), 4));
    }

    #[test]
    fn test_state_multi_word_bitmask() {
        let mut map = DiskStateBitmaskMap::with_flush_threshold(100).unwrap();
        let fp = Fingerprint(42);
        map.set_tag(fp, 5);
        map.set_tag(fp, 100);

        // first_word via .get() only has tag 5
        assert_eq!(map.get(&fp), Some(1u64 << 5));

        // full bitmask via .get_bitmask() has both tags
        let bm = map.get_bitmask(&fp).unwrap();
        assert!(bm.get_tag(5));
        assert!(bm.get_tag(100));
        assert!(!bm.get_tag(6));
    }
}
