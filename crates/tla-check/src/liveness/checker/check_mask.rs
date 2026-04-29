// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Multi-word bitmask for liveness check indices (#2890).
//!
//! Replaces the previous `u64` bitmask that capped specs at 64 action/state
//! checks. TLC uses `BitVector` (backed by `long[]`) for the same purpose,
//! supporting arbitrary numbers of check expressions. This type provides
//! the same capability with O(1) per-bit access.
//!
//! For the common case (≤64 checks), this is a single-element `Vec<u64>`,
//! matching the previous `u64` performance with negligible overhead.

/// Multi-word bitmask supporting arbitrary numbers of check indices.
///
/// Mirrors TLC's `tlc2.util.BitVector` which uses `long[]` internally.
/// Auto-grows when bits beyond the current capacity are set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CheckMask {
    words: Vec<u64>,
}

impl Default for CheckMask {
    fn default() -> Self {
        Self::new()
    }
}

impl CheckMask {
    /// Create an empty (all-zero) bitmask.
    pub(crate) fn new() -> Self {
        Self { words: Vec::new() }
    }

    /// Set bit at index `idx`. Grows the internal storage as needed.
    #[inline]
    pub(crate) fn set(&mut self, idx: usize) {
        let word_idx = idx / 64;
        let bit_idx = idx % 64;
        if word_idx >= self.words.len() {
            self.words.resize(word_idx + 1, 0);
        }
        self.words[word_idx] |= 1u64 << bit_idx;
    }

    /// Check if bit at index `idx` is set.
    #[inline]
    pub(crate) fn get(&self, idx: usize) -> bool {
        let word_idx = idx / 64;
        let bit_idx = idx % 64;
        word_idx < self.words.len() && (self.words[word_idx] & (1u64 << bit_idx)) != 0
    }

    /// Check if all bits set in `required` are also set in `self`.
    /// Returns true if `self` is a superset of `required`.
    #[inline]
    pub(crate) fn contains_all(&self, required: &CheckMask) -> bool {
        for (i, &req_word) in required.words.iter().enumerate() {
            if req_word == 0 {
                continue;
            }
            let self_word = self.words.get(i).copied().unwrap_or(0);
            if (self_word & req_word) != req_word {
                return false;
            }
        }
        true
    }

    /// Bitwise OR-assign: set all bits that are set in `other`.
    ///
    /// Used to accumulate aggregate masks across SCC nodes.
    #[inline]
    pub(crate) fn or_assign(&mut self, other: &CheckMask) {
        if other.words.len() > self.words.len() {
            self.words.resize(other.words.len(), 0);
        }
        for (i, &w) in other.words.iter().enumerate() {
            self.words[i] |= w;
        }
    }

    /// Check if the mask has no bits set.
    #[cfg(test)]
    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.words.iter().all(|&w| w == 0)
    }

    /// Build a mask from a list of indices.
    pub(crate) fn from_indices(indices: &[usize]) -> Self {
        let mut mask = Self::new();
        for &idx in indices {
            mask.set(idx);
        }
        mask
    }

    /// Create a CheckMask from a raw `u64` value (for test compatibility).
    /// Bit `i` set in `raw` means index `i` is set in the mask.
    #[cfg(test)]
    pub(crate) fn from_u64(raw: u64) -> Self {
        if raw == 0 {
            Self::new()
        } else {
            Self { words: vec![raw] }
        }
    }

    /// Access the raw word storage for serialization.
    pub(crate) fn as_words(&self) -> &[u64] {
        &self.words
    }

    /// Construct from raw words (deserialization).
    pub(crate) fn from_words(words: Vec<u64>) -> Self {
        Self { words }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_set_get() {
        let mut mask = CheckMask::new();
        assert!(!mask.get(0));
        mask.set(0);
        assert!(mask.get(0));
        assert!(!mask.get(1));
    }

    #[test]
    fn test_beyond_64() {
        let mut mask = CheckMask::new();
        mask.set(64);
        assert!(!mask.get(63));
        assert!(mask.get(64));
        assert!(!mask.get(65));

        mask.set(127);
        assert!(mask.get(127));
        assert!(!mask.get(128));
    }

    #[test]
    fn test_contains_all() {
        let mut superset = CheckMask::new();
        superset.set(0);
        superset.set(5);
        superset.set(64);
        superset.set(100);

        let mut subset = CheckMask::new();
        subset.set(5);
        subset.set(64);
        assert!(superset.contains_all(&subset));

        subset.set(99); // not in superset
        assert!(!superset.contains_all(&subset));
    }

    #[test]
    fn test_empty() {
        let mask = CheckMask::new();
        assert!(mask.is_empty());

        let mut mask2 = CheckMask::new();
        mask2.set(10);
        assert!(!mask2.is_empty());
    }

    #[test]
    fn test_from_indices() {
        let mask = CheckMask::from_indices(&[3, 7, 65, 130]);
        assert!(mask.get(3));
        assert!(mask.get(7));
        assert!(mask.get(65));
        assert!(mask.get(130));
        assert!(!mask.get(4));
        assert!(!mask.get(66));
    }

    #[test]
    fn test_contains_all_empty() {
        let mask = CheckMask::new();
        let empty = CheckMask::new();
        assert!(mask.contains_all(&empty));
    }

    #[test]
    fn test_or_assign_basic() {
        let mut a = CheckMask::new();
        a.set(0);
        a.set(5);
        let mut b = CheckMask::new();
        b.set(3);
        b.set(5);
        b.set(7);
        a.or_assign(&b);
        assert!(a.get(0));
        assert!(a.get(3));
        assert!(a.get(5));
        assert!(a.get(7));
        assert!(!a.get(1));
    }

    #[test]
    fn test_or_assign_grows() {
        let mut a = CheckMask::new();
        a.set(0);
        let mut b = CheckMask::new();
        b.set(128);
        a.or_assign(&b);
        assert!(a.get(0));
        assert!(a.get(128));
        assert!(!a.get(64));
    }

    #[test]
    fn test_or_assign_empty() {
        let mut a = CheckMask::new();
        a.set(10);
        let empty = CheckMask::new();
        a.or_assign(&empty);
        assert!(a.get(10));
        assert!(!a.get(0));
    }
}
