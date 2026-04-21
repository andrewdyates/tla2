// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trait impls for `CompactValue`: equality, hashing, formatting.

use super::{CompactValue, TAG_BOOL, TAG_HEAP, TAG_INT, TAG_MODEL, TAG_NIL, TAG_STRING};
use crate::value::Value;
use std::fmt;
use std::hash::{Hash, Hasher};

// === PartialEq / Eq ===

impl PartialEq for CompactValue {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // Fast path: identical bits means identical value (works for all
        // inline types and same-pointer heap values). Catches ~99% of cases
        // on the BFS state comparison hot path.
        if self.bits == other.bits {
            return true;
        }
        // Different tags means different values unconditionally.
        // (Previous code checked for "both heap with different tags" but
        // TAG_HEAP == 0 so both-heap-different-tags is impossible when we
        // already established self_tag != other_tag.)
        let self_tag = self.tag();
        if self_tag != other.tag() {
            return false;
        }
        // Same tag, different bits. Only heap values need deep comparison —
        // for inline types (Int, Bool, String, Model), same tag + different
        // bits always means different values.
        if self_tag == TAG_HEAP {
            return self.as_heap_value() == other.as_heap_value();
        }
        false
    }
}

impl Eq for CompactValue {}

// === Hash ===

impl Hash for CompactValue {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self.tag() {
            TAG_HEAP if self.bits != 0 => {
                // Delegate to Value's Hash implementation.
                self.as_heap_value().hash(state);
            }
            _ => {
                // Inline values: hash the raw bits directly.
                self.bits.hash(state);
            }
        }
    }
}

// === Cross-type comparison ===

impl CompactValue {
    /// Compare this compact value against a `Value` without constructing an
    /// intermediate `Value`. For inline types (Bool, SmallInt), this avoids the
    /// 24-byte Value construction entirely. For heap types, delegates to the
    /// inner Value's PartialEq.
    ///
    /// Part of #3579: Used by op_result_cache validation to skip Value
    /// materialization on the hot path.
    #[inline]
    pub fn matches_value(&self, other: &Value) -> bool {
        match self.tag() {
            TAG_BOOL => matches!(other, Value::Bool(b) if *b == self.as_bool()),
            TAG_INT => matches!(other, Value::SmallInt(n) if *n == self.as_int()),
            TAG_HEAP if self.bits != 0 => self.as_heap_value() == other,
            _ => false,
        }
    }
}

// === Debug / Display ===

impl fmt::Debug for CompactValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.tag() {
            TAG_BOOL => write!(f, "CompactValue::Bool({})", self.as_bool()),
            TAG_INT => write!(f, "CompactValue::Int({})", self.as_int()),
            TAG_STRING => write!(f, "CompactValue::String(id={})", self.as_string_id()),
            TAG_MODEL => write!(
                f,
                "CompactValue::ModelValue(id={})",
                self.as_model_value_id()
            ),
            TAG_HEAP if self.bits != 0 => {
                write!(f, "CompactValue::Heap({:?})", self.as_heap_value())
            }
            TAG_HEAP => write!(f, "CompactValue::Null"),
            TAG_NIL => write!(f, "CompactValue::Nil"),
            _ => write!(f, "CompactValue::Reserved({:#x})", self.bits),
        }
    }
}

impl fmt::Display for CompactValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.tag() {
            TAG_BOOL => write!(f, "{}", if self.as_bool() { "TRUE" } else { "FALSE" }),
            TAG_INT => write!(f, "{}", self.as_int()),
            TAG_STRING => write!(f, "<string:{}>", self.as_string_id()),
            TAG_MODEL => write!(f, "<model:{}>", self.as_model_value_id()),
            TAG_HEAP if self.bits != 0 => write!(f, "{}", self.as_heap_value()),
            TAG_HEAP => write!(f, "NULL"),
            TAG_NIL => write!(f, "NIL"),
            _ => write!(f, "???"),
        }
    }
}
