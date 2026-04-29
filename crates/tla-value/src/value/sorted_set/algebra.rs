// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Interval/domain helpers and set algebra for `SortedSet`.
//!
//! Extracted from `sorted_set/mod.rs` per #3408. Contains `equals_integer_interval`,
//! `equals_sequence_domain`, `insert`, `without`, `remove`, `union`, `intersection`,
//! `difference`, and `is_subset`.

use super::{SortedSet, Value};
use std::cmp::Ordering;

impl SortedSet {
    /// Check whether this set is extensionally equal to the integer interval `[min, max]`.
    ///
    /// Accepts either `SmallInt` or `Int` elements so long as their numeric
    /// value matches the expected interval entry.
    pub fn equals_integer_interval(&self, min: i64, max: i64) -> bool {
        let expected_len = if max < min {
            0
        } else {
            match max
                .checked_sub(min)
                .and_then(|diff| diff.checked_add(1))
                .and_then(|len| usize::try_from(len).ok())
            {
                Some(len) => len,
                None => return false,
            }
        };

        let elements = self.as_slice();
        if elements.len() != expected_len {
            return false;
        }

        for (offset, value) in elements.iter().enumerate() {
            let expected = match i64::try_from(offset)
                .ok()
                .and_then(|offset| min.checked_add(offset))
            {
                Some(expected) => expected,
                None => return false,
            };
            if value.as_i64() != Some(expected) {
                return false;
            }
        }
        true
    }

    /// Check whether this set is extensionally equal to `{1, 2, ..., len}`.
    pub fn equals_sequence_domain(&self, len: usize) -> bool {
        match len {
            0 => self.is_empty(),
            _ => i64::try_from(len)
                .ok()
                .is_some_and(|upper| self.equals_integer_interval(1, upper)),
        }
    }

    /// Insert a value, returning a new set (O(n) array copy, O(1) fingerprint update).
    ///
    /// Part of #3246: When the parent set has a cached additive fingerprint, the new
    /// set's fingerprint is computed incrementally in O(1) instead of O(|set|).
    /// This is critical for specs with growing message sets (PaxosCommit pattern).
    pub fn insert(&self, v: Value) -> Self {
        let elements = self.normalized_slice();
        match elements.binary_search(&v) {
            Ok(_) => self.clone(), // Already present
            Err(pos) => {
                let mut vec = Vec::with_capacity(elements.len() + 1);
                vec.extend_from_slice(&elements[..pos]);
                vec.push(v.clone());
                vec.extend_from_slice(&elements[pos..]);
                let new_set = SortedSet::from_sorted_vec_canonical(vec);
                // Propagate additive fingerprint incrementally: O(1) update
                if let Some(old_fp) = self.get_additive_fp() {
                    if let Ok(elem_fp) = crate::dedup_fingerprint::state_value_fingerprint(&v) {
                        let old_len = elements.len() as u64;
                        let new_fp = old_fp
                            .wrapping_sub(crate::dedup_fingerprint::splitmix64(old_len))
                            .wrapping_add(crate::dedup_fingerprint::splitmix64(old_len + 1))
                            .wrapping_add(crate::dedup_fingerprint::splitmix64(elem_fp));
                        new_set.cache_additive_fp(new_fp);
                    }
                }
                new_set
            }
        }
    }

    /// Remove a value, returning a new set (O(n))
    pub fn without(&self, v: &Value) -> Self {
        let elements = self.normalized_slice();
        match elements.binary_search(v) {
            Ok(pos) => {
                let mut vec = Vec::with_capacity(elements.len() - 1);
                vec.extend_from_slice(&elements[..pos]);
                vec.extend_from_slice(&elements[pos + 1..]);
                if vec.is_empty() {
                    Self::new()
                } else {
                    SortedSet::from_sorted_vec_canonical(vec)
                }
            }
            Err(_) => self.clone(), // Not present
        }
    }

    /// Remove a value (alias for without, for OrdSet API compatibility)
    #[inline]
    pub fn remove(&self, v: &Value) -> Self {
        self.without(v)
    }

    /// Set union with smart dispatch based on normalization state.
    ///
    /// #3073: When both operands are already normalized (common in the model
    /// checking hot path — state variables are normalized by fingerprinting),
    /// uses O(n+m) sorted merge producing a Normalized result. When either
    /// operand is Unnormalized, concatenates raw storage and defers sort+dedup,
    /// matching TLC's `cup()` which always produces `isNorm=false`.
    pub fn union(&self, other: &Self) -> Self {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }
        if self.ptr_eq(other) {
            return self.clone();
        }

        // Fast path: both already normalized → O(n+m) sorted merge (optimal)
        if self.is_normalized() && other.is_normalized() {
            return self.union_merge(other);
        }

        // Either operand is Unnormalized → concatenate raw and defer sort.
        // Avoids paying O(n log n) normalization cost at union time when
        // the result may be used for membership testing (linear scan) or
        // combined with further set operations before any ordered observation.
        let raw_a = self.raw_slice();
        let raw_b = other.raw_slice();
        let mut combined = Vec::with_capacity(raw_a.len() + raw_b.len());
        combined.extend_from_slice(raw_a);
        combined.extend_from_slice(raw_b);
        Self::from_unnormalized_vec(combined)
    }

    /// Sorted merge of two normalized sets. O(n+m).
    fn union_merge(&self, other: &Self) -> Self {
        let a = self.as_slice();
        let b = other.as_slice();
        let mut result = Vec::with_capacity(a.len() + b.len());
        let mut i = 0;
        let mut j = 0;

        while i < a.len() && j < b.len() {
            match a[i].cmp(&b[j]) {
                Ordering::Less => {
                    result.push(a[i].clone());
                    i += 1;
                }
                Ordering::Greater => {
                    result.push(b[j].clone());
                    j += 1;
                }
                Ordering::Equal => {
                    result.push(a[i].clone());
                    i += 1;
                    j += 1;
                }
            }
        }
        result.extend_from_slice(&a[i..]);
        result.extend_from_slice(&b[j..]);

        SortedSet::from_sorted_vec_canonical(result)
    }

    /// Set intersection (O(n + m) merge)
    pub fn intersection(&self, other: &Self) -> Self {
        if self.is_empty() || other.is_empty() {
            return Self::new();
        }
        if self.ptr_eq(other) {
            return self.clone();
        }

        let mut result = Vec::new();
        let mut i = 0;
        let mut j = 0;
        let a = self.as_slice();
        let b = other.as_slice();

        while i < a.len() && j < b.len() {
            match a[i].cmp(&b[j]) {
                Ordering::Less => i += 1,
                Ordering::Greater => j += 1,
                Ordering::Equal => {
                    result.push(a[i].clone());
                    i += 1;
                    j += 1;
                }
            }
        }

        if result.is_empty() {
            Self::new()
        } else {
            SortedSet::from_sorted_vec_canonical(result)
        }
    }

    /// Set difference (self \ other) (O(n + m) merge)
    pub fn difference(&self, other: &Self) -> Self {
        if self.is_empty() || self.ptr_eq(other) {
            return Self::new();
        }
        if other.is_empty() {
            return self.clone();
        }

        let mut result = Vec::new();
        let mut i = 0;
        let mut j = 0;
        let a = self.as_slice();
        let b = other.as_slice();

        while i < a.len() && j < b.len() {
            match a[i].cmp(&b[j]) {
                Ordering::Less => {
                    result.push(a[i].clone());
                    i += 1;
                }
                Ordering::Greater => j += 1,
                Ordering::Equal => {
                    i += 1;
                    j += 1;
                }
            }
        }
        result.extend_from_slice(&a[i..]);

        if result.is_empty() {
            Self::new()
        } else {
            SortedSet::from_sorted_vec_canonical(result)
        }
    }

    /// Check if self is a subset of other
    pub fn is_subset(&self, other: &Self) -> bool {
        if self.len() > other.len() {
            return false;
        }
        if self.is_empty() {
            return true;
        }
        if self.ptr_eq(other) {
            return true;
        }

        let mut j = 0;
        let b = other.as_slice();
        for v in self {
            while j < b.len() && b[j] < *v {
                j += 1;
            }
            if j >= b.len() || b[j] != *v {
                return false;
            }
            j += 1;
        }
        true
    }
}
