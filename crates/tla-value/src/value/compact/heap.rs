// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unsafe heap-ownership lifecycle for `CompactValue`.
//!
//! This module isolates all raw-pointer reconstruction: `from_heap`,
//! `as_heap_value`, `Clone`, `Drop`, and the `Send`/`Sync` markers.
#![allow(unsafe_code)]

use super::{CompactValue, TAG_HEAP, TAG_MASK};
use crate::Value;

impl CompactValue {
    /// Create a `CompactValue` from a heap-allocated `Value`.
    ///
    /// This is the fallback for compound types (Set, Func, Record, etc.).
    /// The `Value` is boxed and the pointer stored with tag bits cleared.
    #[inline]
    #[must_use]
    pub fn from_heap(value: Value) -> Self {
        let boxed = Box::new(value);
        let ptr = Box::into_raw(boxed) as u64;
        debug_assert!(
            ptr & TAG_MASK == 0,
            "Box<Value> pointer not 8-byte aligned: {ptr:#x}"
        );
        Self {
            bits: ptr | TAG_HEAP,
        }
    }

    /// Get a reference to the heap-allocated `Value`.
    ///
    /// # Safety
    ///
    /// The caller must ensure this is a heap-allocated value (tag == TAG_HEAP
    /// and bits != 0). Debug-mode assertions check this.
    #[inline(always)]
    #[must_use]
    pub fn as_heap_value(&self) -> &Value {
        debug_assert!(self.is_heap(), "CompactValue::as_heap_value on non-Heap");
        let ptr = (self.bits & !TAG_MASK) as *const Value;
        // SAFETY: The pointer was created by `Box::into_raw` in `from_heap`,
        // and we maintain exclusive ownership. The pointer is valid for reads
        // as long as this CompactValue exists (Drop will free it).
        unsafe { &*ptr }
    }
}

// === Clone ===

impl Clone for CompactValue {
    #[inline]
    fn clone(&self) -> Self {
        match self.tag() {
            TAG_HEAP if self.bits != 0 => {
                // Clone the heap-allocated Value into a new Box.
                let original = self.as_heap_value();
                Self::from_heap(original.clone())
            }
            _ => {
                // Inline values: bitwise copy.
                Self { bits: self.bits }
            }
        }
    }
}

// === Drop ===

impl Drop for CompactValue {
    #[inline]
    fn drop(&mut self) {
        if self.tag() == TAG_HEAP && self.bits != 0 {
            let ptr = (self.bits & !TAG_MASK) as *mut Value;
            // SAFETY: The pointer was created by `Box::into_raw` in
            // `from_heap`. We have exclusive ownership and this is the
            // only place that frees it.
            unsafe {
                drop(Box::from_raw(ptr));
            }
        }
    }
}

// === Closure discriminant check ===

impl CompactValue {
    /// Check if this heap-allocated value is a zero-arg Closure (lazy thunk)
    /// without cloning or converting to `Value`.
    ///
    /// Returns `true` only for `Value::Closure(c)` where `c.params().is_empty()`.
    /// Non-heap values and non-closure heap values return `false`.
    ///
    /// This enables the binding chain hot path to skip `force_lazy_thunk_if_needed`
    /// for the overwhelmingly common case of non-closure heap values (strings, sets,
    /// records, functions, tuples, intervals, etc.), eliminating a function call,
    /// a `Value::Closure` match, and a redundant clone.
    #[inline(always)]
    #[must_use]
    pub fn is_zero_arg_closure(&self) -> bool {
        if self.tag() != TAG_HEAP || self.bits == 0 {
            return false;
        }
        // SAFETY: We verified this is a valid heap pointer above.
        // Peeking at the discriminant is a read-only operation on the
        // owned Box<Value> — no aliasing concerns.
        matches!(self.as_heap_value(), Value::Closure(c) if c.params().is_empty())
    }
}

// === Send + Sync ===
//
// CompactValue is Send + Sync because:
// - Inline values are plain integers (trivially Send+Sync)
// - Heap values contain a Box<Value>, and Value is Send+Sync
//   (all Arc internals are thread-safe)

// SAFETY: Box<Value> is Send, and inline values are integers.
unsafe impl Send for CompactValue {}
// SAFETY: We only read the heap pointer through shared references.
// Value itself is Sync (all internal state is either immutable or
// uses atomic operations for caching).
unsafe impl Sync for CompactValue {}
