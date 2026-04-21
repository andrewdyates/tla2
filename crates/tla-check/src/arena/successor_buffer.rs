// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reusable successor buffer for arena-backed BFS successor collection.
//!
//! `SuccessorBuffer` batches heap-promoted compact successor states for a
//! single BFS step. The outer `Vec` allocation is retained across `clear()`
//! calls, while the contained `Box<[CompactValue]>` values are dropped
//! promptly via `Vec::clear()` so successor payloads do not leak across steps.
//!
//! Part of #3990.

use crate::state::Fingerprint;
use tla_value::CompactValue;

/// Heap-owned successor entry for a single BFS step.
///
/// Part of #3990.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SuccessorEntry {
    pub(crate) fingerprint: Fingerprint,
    pub(crate) values: Box<[CompactValue]>,
}

/// Reusable buffer for collecting successor states between BFS queue writes.
///
/// Part of #3990.
#[derive(Debug)]
pub(crate) struct SuccessorBuffer {
    entries: Vec<SuccessorEntry>,
    len: usize,
    total_pushed: usize,
    total_cleared: usize,
}

impl SuccessorBuffer {
    /// Create an empty successor buffer.
    #[must_use]
    #[inline]
    pub(crate) fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Create an empty successor buffer with capacity for `n` entries.
    #[must_use]
    #[inline]
    pub(crate) fn with_capacity(n: usize) -> Self {
        Self {
            entries: Vec::with_capacity(n),
            len: 0,
            total_pushed: 0,
            total_cleared: 0,
        }
    }

    /// Push a successor entry into the buffer.
    #[inline]
    pub(crate) fn push(&mut self, fingerprint: Fingerprint, values: Box<[CompactValue]>) {
        debug_assert_eq!(self.len, self.entries.len());
        self.entries.push(SuccessorEntry {
            fingerprint,
            values,
        });
        self.len += 1;
        self.total_pushed += 1;
    }

    /// Clear the buffer while retaining the outer `Vec` allocation.
    ///
    /// `Vec::clear()` drops each `SuccessorEntry`, which in turn drops the
    /// owned `Box<[CompactValue]>` payload for every buffered successor.
    #[inline]
    pub(crate) fn clear(&mut self) {
        debug_assert_eq!(self.len, self.entries.len());
        self.total_cleared += self.len;
        self.entries.clear();
        self.len = 0;
    }

    /// Number of entries currently buffered.
    #[must_use]
    #[inline]
    pub(crate) fn len(&self) -> usize {
        debug_assert_eq!(self.len, self.entries.len());
        self.len
    }

    /// Returns `true` when the buffer has no entries.
    #[must_use]
    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Iterate over buffered successor entries in insertion order.
    #[inline]
    pub(crate) fn iter(&self) -> std::slice::Iter<'_, SuccessorEntry> {
        debug_assert_eq!(self.len, self.entries.len());
        self.entries.iter()
    }

    /// Drain all buffered successor entries in insertion order.
    #[inline]
    pub(crate) fn drain(&mut self) -> std::vec::Drain<'_, SuccessorEntry> {
        debug_assert_eq!(self.len, self.entries.len());
        self.total_cleared += self.len;
        self.len = 0;
        self.entries.drain(..)
    }

    /// Total number of entries ever pushed into the buffer.
    #[must_use]
    #[inline]
    pub(crate) fn total_pushed(&self) -> usize {
        self.total_pushed
    }

    /// Total number of entries removed from the buffer by `clear()` or `drain()`.
    #[must_use]
    #[inline]
    pub(crate) fn total_cleared(&self) -> usize {
        self.total_cleared
    }
}

impl Default for SuccessorBuffer {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::{SuccessorBuffer, SuccessorEntry};
    use crate::state::Fingerprint;
    use tla_value::CompactValue;

    fn make_values(base: i64) -> Box<[CompactValue]> {
        vec![
            CompactValue::from_int(base),
            CompactValue::from_int(base + 1),
        ]
        .into_boxed_slice()
    }

    fn collect_ints(entry: &SuccessorEntry) -> Vec<i64> {
        entry.values.iter().map(CompactValue::as_int).collect()
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_successor_buffer_new_empty_expected() {
        let buffer = SuccessorBuffer::new();

        assert_eq!(buffer.len(), 0);
        assert!(buffer.is_empty());
        assert_eq!(buffer.total_pushed(), 0);
        assert_eq!(buffer.total_cleared(), 0);
        assert_eq!(buffer.iter().count(), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_successor_buffer_push_basic_expected() {
        let mut buffer = SuccessorBuffer::new();

        buffer.push(Fingerprint(11), make_values(3));

        assert_eq!(buffer.len(), 1);
        assert!(!buffer.is_empty());
        assert_eq!(buffer.total_pushed(), 1);
        assert_eq!(buffer.total_cleared(), 0);

        let entries: Vec<&SuccessorEntry> = buffer.iter().collect();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].fingerprint, Fingerprint(11));
        assert_eq!(collect_ints(entries[0]), vec![3, 4]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_successor_buffer_clear_retains_capacity_expected() {
        let mut buffer = SuccessorBuffer::with_capacity(8);
        let cap_before = buffer.entries.capacity();

        for idx in 0..5 {
            buffer.push(Fingerprint(idx as u64), make_values(idx as i64));
        }

        buffer.clear();

        assert_eq!(buffer.len(), 0);
        assert!(buffer.is_empty());
        assert_eq!(buffer.total_pushed(), 5);
        assert_eq!(buffer.total_cleared(), 5);
        assert!(buffer.entries.capacity() >= cap_before);

        buffer.push(Fingerprint(99), make_values(50));
        assert_eq!(buffer.len(), 1);
        assert_eq!(buffer.total_pushed(), 6);
        assert_eq!(buffer.total_cleared(), 5);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_successor_buffer_drain_semantics_expected() {
        let mut buffer = SuccessorBuffer::new();
        buffer.push(Fingerprint(1), make_values(10));
        buffer.push(Fingerprint(2), make_values(20));

        let drained: Vec<SuccessorEntry> = buffer.drain().collect();

        assert_eq!(drained.len(), 2);
        assert_eq!(drained[0].fingerprint, Fingerprint(1));
        assert_eq!(collect_ints(&drained[0]), vec![10, 11]);
        assert_eq!(drained[1].fingerprint, Fingerprint(2));
        assert_eq!(collect_ints(&drained[1]), vec![20, 21]);

        assert_eq!(buffer.len(), 0);
        assert!(buffer.is_empty());
        assert_eq!(buffer.iter().count(), 0);
        assert_eq!(buffer.total_pushed(), 2);
        assert_eq!(buffer.total_cleared(), 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_successor_buffer_empty_buffer_expected() {
        let mut buffer = SuccessorBuffer::with_capacity(4);
        let cap_before = buffer.entries.capacity();

        let drained: Vec<SuccessorEntry> = buffer.drain().collect();

        assert!(drained.is_empty());
        assert_eq!(buffer.len(), 0);
        assert!(buffer.is_empty());
        assert_eq!(buffer.total_pushed(), 0);
        assert_eq!(buffer.total_cleared(), 0);

        buffer.clear();
        assert_eq!(buffer.total_cleared(), 0);
        assert!(buffer.entries.capacity() >= cap_before);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_successor_buffer_stats_tracking_expected() {
        let mut buffer = SuccessorBuffer::new();

        buffer.push(Fingerprint(10), make_values(1));
        buffer.push(Fingerprint(11), make_values(2));
        buffer.push(Fingerprint(12), make_values(3));
        buffer.clear();

        assert_eq!(buffer.total_pushed(), 3);
        assert_eq!(buffer.total_cleared(), 3);

        buffer.push(Fingerprint(20), make_values(4));
        buffer.push(Fingerprint(21), make_values(5));

        let drained: Vec<SuccessorEntry> = buffer.drain().collect();

        assert_eq!(drained.len(), 2);
        assert_eq!(buffer.total_pushed(), 5);
        assert_eq!(buffer.total_cleared(), 5);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_successor_buffer_multiple_push_clear_cycles_expected() {
        let mut buffer = SuccessorBuffer::with_capacity(2);

        for cycle in 0..5 {
            for offset in 0..=cycle {
                let value = (cycle * 10 + offset) as i64;
                buffer.push(Fingerprint(value as u64), make_values(value));
            }
            assert_eq!(buffer.len(), cycle + 1);
            buffer.clear();
            assert!(buffer.is_empty());
        }

        assert_eq!(buffer.total_pushed(), 15);
        assert_eq!(buffer.total_cleared(), 15);
        assert!(buffer.entries.capacity() >= 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_successor_buffer_large_buffer_expected() {
        let mut buffer = SuccessorBuffer::with_capacity(1000);

        for idx in 0..1000 {
            buffer.push(Fingerprint(idx as u64), make_values(idx as i64));
        }

        assert_eq!(buffer.len(), 1000);
        assert_eq!(buffer.total_pushed(), 1000);
        assert!(!buffer.is_empty());

        let entries: Vec<&SuccessorEntry> = buffer.iter().collect();
        assert_eq!(entries.len(), 1000);
        assert_eq!(entries[0].fingerprint, Fingerprint(0));
        assert_eq!(collect_ints(entries[0]), vec![0, 1]);
        assert_eq!(entries[999].fingerprint, Fingerprint(999));
        assert_eq!(collect_ints(entries[999]), vec![999, 1000]);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_successor_buffer_iter_correctness_expected() {
        let mut buffer = SuccessorBuffer::new();
        buffer.push(Fingerprint(7), make_values(70));
        buffer.push(Fingerprint(8), make_values(80));
        buffer.push(Fingerprint(9), make_values(90));

        let observed: Vec<(u64, Vec<i64>)> = buffer
            .iter()
            .map(|entry| (entry.fingerprint.0, collect_ints(entry)))
            .collect();

        assert_eq!(
            observed,
            vec![(7, vec![70, 71]), (8, vec![80, 81]), (9, vec![90, 91]),]
        );
    }
}
