// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `SeqValue` construction, accessors, iteration, and persistent O(log n) ops.

use super::super::Value;
use super::{SeqValue, SEQ_VALUE_FP_UNSET};
use std::sync::atomic::AtomicU64;
use std::sync::OnceLock;
use tla_core::kani_types::Vector;

impl SeqValue {
    #[inline]
    pub(super) fn with_elements(elements: Vector<Value>) -> Self {
        SeqValue {
            elements,
            additive_fp: AtomicU64::new(SEQ_VALUE_FP_UNSET),
            flat_view: OnceLock::new(),
        }
    }

    /// Create a new empty sequence.
    #[inline]
    pub(crate) fn new() -> Self {
        Self::with_elements(Vector::new())
    }

    /// Create a sequence from a vector of values.
    #[inline]
    pub fn from_vec(vec: Vec<Value>) -> Self {
        if vec.is_empty() {
            return Self::new();
        }
        Self::with_elements(Vector::from(vec))
    }

    /// Create a sequence from an im::Vector.
    #[inline]
    pub(crate) fn from_imvec(elements: Vector<Value>) -> Self {
        Self::with_elements(elements)
    }

    /// Get the number of elements.
    #[inline]
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Check if empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Get an element by 0-based index - O(log n).
    #[inline]
    pub fn get(&self, index: usize) -> Option<&Value> {
        self.elements.get(index)
    }

    /// Get the first element - O(log n).
    #[inline]
    pub fn first(&self) -> Option<&Value> {
        self.elements.front()
    }

    /// Get the last element - O(log n).
    #[inline]
    pub fn last(&self) -> Option<&Value> {
        self.elements.back()
    }

    /// Iterate over elements.
    #[inline]
    #[cfg(feature = "im")]
    pub fn iter(&self) -> im::vector::Iter<'_, Value> {
        self.elements.iter()
    }

    /// Iterate over elements (stub-compatible version when im feature is disabled).
    #[inline]
    #[cfg(not(feature = "im"))]
    pub fn iter(&self) -> std::slice::Iter<'_, Value> {
        self.elements.iter()
    }

    // ========================================================================
    // Efficient O(log n) operations for persistent sequences
    // ========================================================================

    /// Return a new sequence without the first element - O(log n).
    /// Equivalent to Tail in TLA+.
    #[inline]
    pub fn tail(&self) -> Self {
        if self.elements.is_empty() {
            return Self::new();
        }
        Self::with_elements(self.elements.clone().split_off(1))
    }

    /// Return a new sequence with element appended - O(log n).
    /// Equivalent to Append in TLA+.
    #[inline]
    pub fn append(&self, elem: Value) -> Self {
        let mut new_elements = self.elements.clone();
        new_elements.push_back(elem);
        Self::with_elements(new_elements)
    }

    /// Return a subsequence from start to end (0-indexed, exclusive end) - O(log n).
    /// Equivalent to SubSeq in TLA+ (adjusted for 0-indexing).
    #[inline]
    pub fn subseq(&self, start: usize, end: usize) -> Self {
        if start >= end || start >= self.elements.len() {
            return Self::new();
        }
        let end = end.min(self.elements.len());
        Self::with_elements(self.elements.clone().slice(start..end))
    }

    /// Return all but the last element - O(log n).
    /// Equivalent to Front in TLA+ (SequencesExt).
    #[inline]
    pub fn front(&self) -> Self {
        if self.elements.is_empty() {
            return Self::new();
        }
        let len = self.elements.len();
        Self::with_elements(self.elements.clone().slice(0..len - 1))
    }
}
