// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Disk-backed action bitmask map for liveness inline recording.
//!
//! Part of #3177. Extracted from `disk_bitmask.rs` (Part of #3472) to reduce
//! file size. See `disk_bitmask.rs` for the two-tier storage design overview.
//!
//! Part of #4159: Hot tier uses `LiveBitmask` for multi-word support.
//! Cold tier stores only `first_word()` (u64) — same as state bitmask.
//!
//! ## File Format
//!
//! Action bitmask entries: `[from_fp: u64, to_fp: u64, bitmask: u64]` — 24 bytes each,
//! sorted by (from_fp, to_fp).

use super::bitmask_map::LiveBitmask;
use crate::state::Fingerprint;
use memmap2::Mmap;
use rustc_hash::FxHashMap;
use std::io::{self, BufWriter, Write};

/// Action bitmask entry size: `[from_fp: u64, to_fp: u64, bitmask: u64]` = 24 bytes.
const ACTION_ENTRY_SIZE: usize = 24;

/// Default flush threshold: 2M entries.
const DEFAULT_FLUSH_THRESHOLD: usize = 2 * 1024 * 1024;

/// Disk-backed action bitmask map.
///
/// Maps `(Fingerprint, Fingerprint) -> LiveBitmask` with two-tier storage.
pub(crate) struct DiskActionBitmaskMap {
    /// Hot tier: active entries being written/read during BFS.
    hot: FxHashMap<(Fingerprint, Fingerprint), LiveBitmask>,
    /// Cold tier: sorted entries in an mmap file.
    cold: Option<Mmap>,
    /// Number of entries in the cold tier.
    cold_count: usize,
    /// Backing file for the cold tier.
    backing_file: tempfile::NamedTempFile,
    /// Hot tier flush threshold.
    flush_threshold: usize,
}

impl DiskActionBitmaskMap {
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
    pub(crate) fn contains_key(&self, key: &(Fingerprint, Fingerprint)) -> bool {
        self.hot.contains_key(key) || self.cold_contains(key)
    }

    /// Get the first-word bitmask value for a key.
    pub(crate) fn get(&self, key: &(Fingerprint, Fingerprint)) -> Option<u64> {
        if let Some(bm) = self.hot.get(key) {
            return Some(bm.first_word());
        }
        self.cold_get(key)
    }

    /// Get a reference to the full `LiveBitmask` (hot tier only).
    pub(crate) fn get_bitmask(&self, key: &(Fingerprint, Fingerprint)) -> Option<&LiveBitmask> {
        self.hot.get(key)
    }

    /// Get an owned `LiveBitmask` from either tier.
    pub(crate) fn get_bitmask_owned(
        &self,
        key: &(Fingerprint, Fingerprint),
    ) -> Option<LiveBitmask> {
        if let Some(bm) = self.hot.get(key) {
            return Some(bm.clone());
        }
        self.cold_get(key).map(LiveBitmask::from_u64)
    }

    /// Insert or get-default in the hot tier. Returns a mutable reference.
    pub(crate) fn get_or_insert_default_bitmask(
        &mut self,
        key: (Fingerprint, Fingerprint),
    ) -> &mut LiveBitmask {
        self.hot.entry(key).or_default()
    }

    /// Get a mutable reference to an existing hot tier entry.
    ///
    /// Returns `None` if the key is not in the hot tier (even if it's in cold).
    /// This is correct for the `update_action_bitmask` pattern: entries being
    /// updated are always in the hot tier (created in the same BFS step).
    pub(crate) fn get_hot_mut_bitmask(
        &mut self,
        key: &(Fingerprint, Fingerprint),
    ) -> Option<&mut LiveBitmask> {
        self.hot.get_mut(key)
    }

    /// Set a single tag bit for a key (creates entry if absent).
    pub(crate) fn set_tag(&mut self, key: (Fingerprint, Fingerprint), tag: u32) {
        self.hot.entry(key).or_default().set_tag(tag);
    }

    /// OR bits into an existing or new entry (u64 backward compat).
    pub(crate) fn or_bits(&mut self, key: (Fingerprint, Fingerprint), bits: u64) {
        let bm = self.hot.entry(key).or_default();
        if bm.words.is_empty() {
            bm.words.push(bits);
        } else {
            bm.words[0] |= bits;
        }
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
            .expect("disk action bitmask: truncate");
    }

    /// Flush hot tier to cold if threshold exceeded.
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

        let mut hot_entries: Vec<((Fingerprint, Fingerprint), u64)> = self
            .hot
            .drain()
            .map(|(key, bm)| (key, bm.first_word()))
            .collect();
        hot_entries.sort_unstable_by(|(a, _), (b, _)| (a.0 .0, a.1 .0).cmp(&(b.0 .0, b.1 .0)));

        let merged = if self.cold_count > 0 {
            let cold_mmap = self
                .cold
                .as_ref()
                .expect("disk action bitmask: cold mmap missing");
            merge_action_entries(&hot_entries, cold_mmap.as_ref(), self.cold_count)
        } else {
            hot_entries
        };

        let new_file = tempfile::NamedTempFile::new()?;
        let total_bytes = merged.len() * ACTION_ENTRY_SIZE;
        {
            let mut writer = BufWriter::with_capacity(64 * 1024, new_file.as_file().try_clone()?);
            for ((from_fp, to_fp), bitmask) in &merged {
                writer.write_all(&from_fp.0.to_le_bytes())?;
                writer.write_all(&to_fp.0.to_le_bytes())?;
                writer.write_all(&bitmask.to_le_bytes())?;
            }
            writer.flush()?;
        }

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

    fn cold_contains(&self, key: &(Fingerprint, Fingerprint)) -> bool {
        self.cold_get(key).is_some()
    }

    fn cold_get(&self, key: &(Fingerprint, Fingerprint)) -> Option<u64> {
        let mmap = self.cold.as_ref()?;
        let bytes = mmap.as_ref();
        let target = (key.0 .0, key.1 .0);

        let mut lo = 0usize;
        let mut hi = self.cold_count;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let offset = mid * ACTION_ENTRY_SIZE;
            let from_fp = u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap());
            let to_fp = u64::from_le_bytes(bytes[offset + 8..offset + 16].try_into().unwrap());
            let stored = (from_fp, to_fp);
            match stored.cmp(&target) {
                std::cmp::Ordering::Less => lo = mid + 1,
                std::cmp::Ordering::Greater => hi = mid,
                std::cmp::Ordering::Equal => {
                    let bitmask =
                        u64::from_le_bytes(bytes[offset + 16..offset + 24].try_into().unwrap());
                    return Some(bitmask);
                }
            }
        }
        None
    }
}

/// Merge sorted hot entries with sorted cold bytes.
fn merge_action_entries(
    hot: &[((Fingerprint, Fingerprint), u64)],
    cold_bytes: &[u8],
    cold_count: usize,
) -> Vec<((Fingerprint, Fingerprint), u64)> {
    let mut result = Vec::with_capacity(hot.len() + cold_count);
    let mut hi = 0;
    let mut ci = 0;

    while hi < hot.len() && ci < cold_count {
        let cold_offset = ci * ACTION_ENTRY_SIZE;
        let cold_from =
            u64::from_le_bytes(cold_bytes[cold_offset..cold_offset + 8].try_into().unwrap());
        let cold_to = u64::from_le_bytes(
            cold_bytes[cold_offset + 8..cold_offset + 16]
                .try_into()
                .unwrap(),
        );
        let hot_key = (hot[hi].0 .0 .0, hot[hi].0 .1 .0);
        let cold_key = (cold_from, cold_to);

        if hot_key <= cold_key {
            result.push(hot[hi]);
            hi += 1;
            // Skip duplicate in cold (defensive).
            if hot_key == cold_key {
                ci += 1;
            }
        } else {
            let bitmask = u64::from_le_bytes(
                cold_bytes[cold_offset + 16..cold_offset + 24]
                    .try_into()
                    .unwrap(),
            );
            result.push(((Fingerprint(cold_from), Fingerprint(cold_to)), bitmask));
            ci += 1;
        }
    }

    while hi < hot.len() {
        result.push(hot[hi]);
        hi += 1;
    }

    while ci < cold_count {
        let cold_offset = ci * ACTION_ENTRY_SIZE;
        let cold_from =
            u64::from_le_bytes(cold_bytes[cold_offset..cold_offset + 8].try_into().unwrap());
        let cold_to = u64::from_le_bytes(
            cold_bytes[cold_offset + 8..cold_offset + 16]
                .try_into()
                .unwrap(),
        );
        let bitmask = u64::from_le_bytes(
            cold_bytes[cold_offset + 16..cold_offset + 24]
                .try_into()
                .unwrap(),
        );
        result.push(((Fingerprint(cold_from), Fingerprint(cold_to)), bitmask));
        ci += 1;
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_action_insert_and_get() {
        let mut map = DiskActionBitmaskMap::with_flush_threshold(100).unwrap();
        let key = (Fingerprint(1), Fingerprint(2));
        assert!(!map.contains_key(&key));

        map.get_or_insert_default_bitmask(key);
        assert!(map.contains_key(&key));
        assert_eq!(map.get(&key), Some(0));

        map.set_tag(key, 5);
        assert_eq!(map.get(&key), Some(1u64 << 5));
    }

    #[test]
    fn test_action_flush_and_cold_lookup() {
        let mut map = DiskActionBitmaskMap::with_flush_threshold(3).unwrap();
        let keys = [
            (Fingerprint(1), Fingerprint(2)),
            (Fingerprint(1), Fingerprint(3)),
            (Fingerprint(2), Fingerprint(3)),
        ];
        for (i, &key) in keys.iter().enumerate() {
            map.or_bits(key, 1u64 << (i as u32));
        }
        map.maybe_flush().unwrap();

        assert_eq!(map.hot.len(), 0);
        assert_eq!(map.cold_count, 3);
        assert_eq!(map.get(&keys[0]), Some(1u64 << 0));
        assert_eq!(map.get(&keys[1]), Some(1u64 << 1));
        assert_eq!(map.get(&keys[2]), Some(1u64 << 2));
        assert!(map.get(&(Fingerprint(99), Fingerprint(99))).is_none());
    }

    #[test]
    fn test_action_get_hot_mut_bitmask() {
        let mut map = DiskActionBitmaskMap::with_flush_threshold(100).unwrap();
        let key = (Fingerprint(1), Fingerprint(2));
        map.get_or_insert_default_bitmask(key);

        if let Some(bm) = map.get_hot_mut_bitmask(&key) {
            bm.set_tag(10);
        }
        assert_eq!(map.get(&key), Some(1u64 << 10));

        // Key not in hot tier -> None.
        assert!(map
            .get_hot_mut_bitmask(&(Fingerprint(99), Fingerprint(99)))
            .is_none());
    }

    #[test]
    fn test_action_merge() {
        let mut map = DiskActionBitmaskMap::with_flush_threshold(2).unwrap();

        map.or_bits((Fingerprint(1), Fingerprint(2)), 0xA);
        map.or_bits((Fingerprint(3), Fingerprint(4)), 0xB);
        map.flush().unwrap();

        map.or_bits((Fingerprint(2), Fingerprint(3)), 0xC);
        map.or_bits((Fingerprint(4), Fingerprint(5)), 0xD);
        map.flush().unwrap();

        assert_eq!(map.cold_count, 4);
        assert_eq!(map.get(&(Fingerprint(1), Fingerprint(2))), Some(0xA));
        assert_eq!(map.get(&(Fingerprint(2), Fingerprint(3))), Some(0xC));
        assert_eq!(map.get(&(Fingerprint(3), Fingerprint(4))), Some(0xB));
        assert_eq!(map.get(&(Fingerprint(4), Fingerprint(5))), Some(0xD));
    }

    #[test]
    fn test_action_maybe_flush_merges_hot_and_cold() {
        let mut map = DiskActionBitmaskMap::with_flush_threshold(2).unwrap();

        map.or_bits((Fingerprint(1), Fingerprint(2)), 0xA);
        map.or_bits((Fingerprint(3), Fingerprint(4)), 0xB);
        map.maybe_flush().unwrap();

        assert_eq!(map.hot.len(), 0);
        assert_eq!(map.cold_count, 2);

        map.or_bits((Fingerprint(2), Fingerprint(3)), 0xC);
        map.or_bits((Fingerprint(4), Fingerprint(5)), 0xD);
        map.maybe_flush().unwrap();

        assert_eq!(map.hot.len(), 0);
        assert_eq!(map.cold_count, 4);
        assert_eq!(map.get(&(Fingerprint(1), Fingerprint(2))), Some(0xA));
        assert_eq!(map.get(&(Fingerprint(2), Fingerprint(3))), Some(0xC));
        assert_eq!(map.get(&(Fingerprint(3), Fingerprint(4))), Some(0xB));
        assert_eq!(map.get(&(Fingerprint(4), Fingerprint(5))), Some(0xD));
    }

    #[test]
    fn test_action_clear() {
        let mut map = DiskActionBitmaskMap::with_flush_threshold(100).unwrap();
        map.or_bits((Fingerprint(1), Fingerprint(2)), 1);
        map.flush().unwrap();
        map.or_bits((Fingerprint(3), Fingerprint(4)), 2);

        map.clear();
        assert_eq!(map.len(), 0);
        assert!(!map.contains_key(&(Fingerprint(1), Fingerprint(2))));
    }

    #[test]
    fn test_action_multi_word_bitmask() {
        let mut map = DiskActionBitmaskMap::with_flush_threshold(100).unwrap();
        let key = (Fingerprint(1), Fingerprint(2));
        map.set_tag(key, 10);
        map.set_tag(key, 130);

        // first_word via .get() only has tag 10
        assert_eq!(map.get(&key), Some(1u64 << 10));

        // full bitmask via .get_bitmask() has both tags
        let bm = map.get_bitmask(&key).unwrap();
        assert!(bm.get_tag(10));
        assert!(bm.get_tag(130));
        assert!(!bm.get_tag(11));
    }
}
