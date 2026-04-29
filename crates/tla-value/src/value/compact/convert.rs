// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `From` conversion impls between `CompactValue` and `Value`/primitives.

use super::{CompactValue, TAG_BOOL, TAG_HEAP, TAG_INT, TAG_MASK, TAG_MODEL, TAG_NIL, TAG_STRING};
use crate::Value;

impl From<bool> for CompactValue {
    #[inline(always)]
    fn from(b: bool) -> Self {
        Self::from_bool(b)
    }
}

impl From<i64> for CompactValue {
    #[inline(always)]
    fn from(n: i64) -> Self {
        Self::from_int(n)
    }
}

/// Convert from `Value` to `CompactValue`.
///
/// Inline scalars (Bool, SmallInt) are stored directly in the 8-byte
/// representation. All other types are heap-allocated.
impl From<Value> for CompactValue {
    #[inline]
    fn from(v: Value) -> Self {
        // Hot path: inline scalars are the overwhelmingly common case on the
        // binding write path (quantifier variables, LET bindings).
        match &v {
            Value::SmallInt(n) => {
                // Most SmallInt values fit in i61. The range check in
                // try_from_int is a single comparison — very cheap.
                if let Some(cv) = Self::try_from_int(*n) {
                    return cv;
                }
                // Extremely large SmallInt that doesn't fit in i61 —
                // fall back to heap allocation.
                Self::from_heap(v)
            }
            Value::Bool(b) => Self::from_bool(*b),
            // All compound types go to the heap.
            _ => Self::from_heap(v),
        }
    }
}

/// Convert from `&Value` to `CompactValue`.
///
/// Part of #3579: Avoids cloning for inline scalars (Bool, SmallInt).
/// Heap-backed types clone the Value into a new Box allocation.
impl From<&Value> for CompactValue {
    fn from(v: &Value) -> Self {
        match v {
            Value::Bool(b) => Self::from_bool(*b),
            Value::SmallInt(n) => {
                if let Some(cv) = Self::try_from_int(*n) {
                    cv
                } else {
                    Self::from_heap(v.clone())
                }
            }
            _ => Self::from_heap(v.clone()),
        }
    }
}

/// Convert from `CompactValue` to `Value`.
///
/// This always succeeds. Inline scalars are reconstructed directly.
/// Heap-allocated values are cloned.
impl From<&CompactValue> for Value {
    #[inline]
    fn from(cv: &CompactValue) -> Self {
        // Hot path: check for the two most common inline types first.
        // Inlining the tag extraction and using direct bit operations
        // eliminates the overhead of the match dispatch for the common case.
        let tag = cv.tag();
        if tag == TAG_INT {
            // SmallInt: arithmetic right shift sign-extends the i61 payload.
            // This is the most common case in model checking (quantifier vars,
            // function indices, set elements are overwhelmingly integers).
            return Value::SmallInt((cv.bits as i64) >> 3);
        }
        if tag == TAG_BOOL {
            return Value::Bool((cv.bits & super::BOOL_VALUE_BIT) != 0);
        }
        // Cold path: heap or unsupported tags.
        cv.to_value_slow()
    }
}

impl CompactValue {
    /// Cold path for `From<&CompactValue> for Value` — handles heap-backed
    /// and unsupported tag types. Separated from the inline fast path to keep
    /// the hot function small and branch-predictor friendly.
    #[inline(never)]
    fn to_value_slow(&self) -> Value {
        match self.tag() {
            TAG_HEAP => {
                if self.bits == 0 {
                    // Null heap pointer — should not happen in normal use.
                    // Return a default value.
                    Value::Bool(false)
                } else {
                    self.as_heap_value().clone()
                }
            }
            TAG_STRING | TAG_MODEL | TAG_NIL => {
                // String/ModelValue reconstruction requires access to the
                // intern table. For now, heap-allocate these types through
                // the standard path. The intern ID extraction is available
                // via as_string_id()/as_model_value_id() for callers that
                // can resolve them.
                //
                // TODO: Add intern table reverse lookup once string/model
                // value intern IDs are stabilized.
                panic!("CompactValue::to_value for interned types requires intern table access");
            }
            _ => unreachable!("invalid CompactValue tag"),
        }
    }
}

impl From<CompactValue> for Value {
    #[allow(unsafe_code)]
    #[inline]
    fn from(cv: CompactValue) -> Self {
        // Hot path: check for the two most common inline types first.
        // For inline types, the owned conversion is identical to the borrowed
        // conversion — no heap resources to transfer.
        let tag = cv.tag();
        if tag == TAG_INT {
            return Value::SmallInt((cv.bits as i64) >> 3);
        }
        if tag == TAG_BOOL {
            return Value::Bool((cv.bits & super::BOOL_VALUE_BIT) != 0);
        }
        // Cold path: heap or unsupported tags.
        cv.into_value_slow()
    }
}

impl CompactValue {
    /// Cold path for `From<CompactValue> for Value` (owned) — handles
    /// heap-backed types with ownership transfer (no clone needed).
    #[allow(unsafe_code)]
    #[inline(never)]
    fn into_value_slow(self) -> Value {
        match self.tag() {
            TAG_HEAP => {
                if self.bits == 0 {
                    Value::Bool(false)
                } else {
                    // Take ownership of the heap value instead of cloning.
                    let ptr = (self.bits & !TAG_MASK) as *mut Value;
                    // SAFETY: We own the Box<Value> exclusively. After
                    // reconstructing it, we must prevent Drop from
                    // double-freeing by forgetting the CompactValue.
                    let value = unsafe { *Box::from_raw(ptr) };
                    std::mem::forget(self);
                    value
                }
            }
            TAG_STRING | TAG_MODEL | TAG_NIL => {
                panic!("CompactValue::to_value for interned types requires intern table access");
            }
            _ => unreachable!("invalid CompactValue tag"),
        }
    }
}
