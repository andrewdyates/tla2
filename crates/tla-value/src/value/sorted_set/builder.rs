// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Value pooling helpers and `SetBuilder` for efficient set construction.
//!
//! Extracted from `sorted_set.rs` per #3326.

use super::{SortedSet, Value};
use num_traits::ToPrimitive;
use smallvec::SmallVec;
use std::sync::Arc;

// ============================================================================
// Value Pooling (Part of #346 - Performance Optimization Phase 3)
// ============================================================================
// TLC pools common values to avoid repeated allocation. For TLA2, Bool and
// SmallInt variants are already stack-allocated (no heap), but static singletons
// avoid construction overhead in hot paths.

/// Returns a pooled Value::Bool(true)
#[inline]
pub fn val_true() -> Value {
    Value::Bool(true)
}

/// Returns a pooled Value::Bool(false)
#[inline]
pub fn val_false() -> Value {
    Value::Bool(false)
}

/// Returns a Value for an integer, using SmallInt for values that fit in i64.
/// This is the canonical way to create integer values.
#[inline]
pub fn val_int(n: &num_bigint::BigInt) -> Value {
    if let Some(small) = n.to_i64() {
        Value::SmallInt(small)
    } else {
        Value::Int(Arc::new(n.clone()))
    }
}

// ============================================================================
// SetBuilder - Efficient set construction
// ============================================================================

/// Builder for constructing sets efficiently.
///
/// Collects values into a SmallVec, then hands them to `SortedSet::from_iter()`.
/// Ordered observation still yields a sorted, deduplicated view, but the
/// normalization work is deferred until the resulting set needs it.
/// More efficient than repeated insert() calls when building from scratch.
///
/// Part of #3805: Uses SmallVec<[Value; 8]> to avoid heap allocation for small sets
/// (the vast majority in TLA+ -- e.g., `{1,2,3}`, `{TRUE, FALSE}`, `{"a","b","c"}`).
/// Sets with <= 8 elements stay entirely on the stack.
pub struct SetBuilder(SmallVec<[Value; 8]>);

impl Default for SetBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl SetBuilder {
    /// Create a new empty builder
    #[inline]
    pub fn new() -> Self {
        SetBuilder(SmallVec::new())
    }

    /// Add a value
    #[inline]
    pub fn insert(&mut self, v: Value) {
        self.0.push(v);
    }

    /// Add multiple values
    #[inline]
    pub fn extend<I: IntoIterator<Item = Value>>(&mut self, iter: I) {
        self.0.extend(iter);
    }

    /// Build the final SortedSet.
    ///
    /// Uses `into_vec()` to avoid the double-collect in `SortedSet::from_iter()`:
    /// when the SmallVec has spilled to heap, `into_vec()` is a no-op pointer transfer.
    /// When inline, `into_vec()` allocates once and copies the inline elements.
    /// Either way, we pass ownership directly to `SortedSet` instead of iterating.
    #[inline]
    pub fn build(self) -> SortedSet {
        SortedSet::from_vec(self.0.into_vec())
    }

    /// Build into a Value::Set
    #[inline]
    pub fn build_value(self) -> Value {
        Value::from_sorted_set(self.build())
    }

    /// Check if empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Get current length (may include duplicates)
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }
}
