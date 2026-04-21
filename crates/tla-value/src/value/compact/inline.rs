// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Inline (non-heap) constructors, tag predicates, and scalar accessors
//! for `CompactValue`.

use super::{
    CompactValue, BOOL_VALUE_BIT, MAX_INTERN_ID, MAX_SMALL_INT, MIN_SMALL_INT, TAG_BOOL, TAG_HEAP,
    TAG_INT, TAG_MODEL, TAG_NIL, TAG_STRING,
};

impl CompactValue {
    // === Constructors ===

    /// Create a `CompactValue` representing boolean `false`.
    #[inline(always)]
    #[must_use]
    pub const fn bool_false() -> Self {
        Self { bits: TAG_BOOL }
    }

    /// Create a `CompactValue` representing boolean `true`.
    #[inline(always)]
    #[must_use]
    pub const fn bool_true() -> Self {
        Self {
            bits: TAG_BOOL | BOOL_VALUE_BIT,
        }
    }

    /// Create a `CompactValue` from a boolean.
    #[inline(always)]
    #[must_use]
    pub const fn from_bool(b: bool) -> Self {
        Self {
            bits: TAG_BOOL | ((b as u64) << 3),
        }
    }

    /// Create a `CompactValue` from a small integer.
    ///
    /// # Panics
    ///
    /// Panics if the value doesn't fit in 61 bits (i.e., outside ±2^60).
    /// This covers all practical TLA+ integer values.
    #[inline(always)]
    #[must_use]
    pub const fn from_int(n: i64) -> Self {
        assert!(
            n >= MIN_SMALL_INT && n <= MAX_SMALL_INT,
            "integer out of i61 range for CompactValue"
        );
        // Arithmetic shift preserves sign. We store the signed value in the
        // upper 61 bits, with the tag in the lower 3 bits.
        Self {
            bits: ((n as u64) << 3) | TAG_INT,
        }
    }

    /// Try to create a `CompactValue` from an integer, returning `None` if
    /// the value doesn't fit in i61.
    #[inline(always)]
    #[must_use]
    pub const fn try_from_int(n: i64) -> Option<Self> {
        if n >= MIN_SMALL_INT && n <= MAX_SMALL_INT {
            Some(Self {
                bits: ((n as u64) << 3) | TAG_INT,
            })
        } else {
            None
        }
    }

    /// Create a `CompactValue` from an interned string ID.
    ///
    /// The ID is an opaque handle into the global string intern table.
    #[inline(always)]
    #[must_use]
    pub const fn from_interned_string(id: u64) -> Self {
        assert!(id <= MAX_INTERN_ID, "string intern ID exceeds u61 capacity");
        Self {
            bits: (id << 3) | TAG_STRING,
        }
    }

    /// Create a `CompactValue` from a model value intern ID.
    #[inline(always)]
    #[must_use]
    pub const fn from_model_value(id: u64) -> Self {
        assert!(
            id <= MAX_INTERN_ID,
            "model value intern ID exceeds u61 capacity"
        );
        Self {
            bits: (id << 3) | TAG_MODEL,
        }
    }

    /// Create the nil sentinel value.
    ///
    /// Used for uninitialized array slots. Not a valid TLA+ value.
    #[inline(always)]
    #[must_use]
    pub const fn nil() -> Self {
        Self { bits: TAG_NIL }
    }

    // === Tag inspection ===

    /// Returns `true` if this is a boolean value.
    #[inline(always)]
    #[must_use]
    pub const fn is_bool(&self) -> bool {
        self.tag() == TAG_BOOL
    }

    /// Returns `true` if this is a small integer value.
    #[inline(always)]
    #[must_use]
    pub const fn is_int(&self) -> bool {
        self.tag() == TAG_INT
    }

    /// Returns `true` if this is an interned string.
    #[inline(always)]
    #[must_use]
    pub const fn is_string(&self) -> bool {
        self.tag() == TAG_STRING
    }

    /// Returns `true` if this is a model value.
    #[inline(always)]
    #[must_use]
    pub const fn is_model_value(&self) -> bool {
        self.tag() == TAG_MODEL
    }

    /// Returns `true` if this is a heap-allocated compound value.
    #[inline(always)]
    #[must_use]
    pub const fn is_heap(&self) -> bool {
        self.tag() == TAG_HEAP && self.bits != 0
    }

    /// Returns `true` if this is the nil sentinel.
    #[inline(always)]
    #[must_use]
    pub const fn is_nil(&self) -> bool {
        self.tag() == TAG_NIL
    }

    /// Returns `true` if this is an inline (non-heap) value.
    #[inline(always)]
    #[must_use]
    pub const fn is_inline(&self) -> bool {
        self.tag() != TAG_HEAP || self.bits == 0
    }

    // === Value extraction ===

    /// Extract the boolean value. Panics if not a Bool.
    #[inline(always)]
    #[must_use]
    pub const fn as_bool(&self) -> bool {
        debug_assert!(self.is_bool(), "CompactValue::as_bool on non-Bool");
        (self.bits & BOOL_VALUE_BIT) != 0
    }

    /// Extract the i64 integer value. Panics if not a SmallInt.
    #[inline(always)]
    #[must_use]
    pub const fn as_int(&self) -> i64 {
        debug_assert!(self.is_int(), "CompactValue::as_int on non-Int");
        // Arithmetic right shift sign-extends.
        (self.bits as i64) >> 3
    }

    /// Extract the string intern ID. Panics if not a String.
    #[inline(always)]
    #[must_use]
    pub const fn as_string_id(&self) -> u64 {
        debug_assert!(self.is_string(), "CompactValue::as_string_id on non-String");
        self.bits >> 3
    }

    /// Extract the model value intern ID. Panics if not a ModelValue.
    #[inline(always)]
    #[must_use]
    pub const fn as_model_value_id(&self) -> u64 {
        debug_assert!(
            self.is_model_value(),
            "CompactValue::as_model_value_id on non-ModelValue"
        );
        self.bits >> 3
    }

    /// Get the raw bits (for hashing/fingerprinting inline values).
    #[inline(always)]
    #[must_use]
    pub const fn raw_bits(&self) -> u64 {
        self.bits
    }

    /// Convert a known-inline CompactValue to Value without heap checks.
    ///
    /// # Safety contract (debug-only)
    ///
    /// The caller must ensure `!self.is_heap()`. In debug builds, this is
    /// asserted. In release builds, a heap-tagged value would hit the
    /// unreachable branch (which is UB-free — it just panics in debug or
    /// returns a wrong value in release, but the caller contract prevents this).
    ///
    /// This is the fastest possible CompactValue -> Value path for the
    /// binding chain hot path, where we already know the value is inline
    /// (Bool or SmallInt) from a prior `is_heap()` check.
    #[inline(always)]
    #[must_use]
    pub fn to_value_inline(&self) -> crate::Value {
        debug_assert!(
            !self.is_heap(),
            "to_value_inline called on heap-backed CompactValue"
        );
        let tag = self.tag();
        if tag == TAG_INT {
            crate::Value::SmallInt((self.bits as i64) >> 3)
        } else if tag == TAG_BOOL {
            crate::Value::Bool((self.bits & BOOL_VALUE_BIT) != 0)
        } else {
            // String/Model/Nil are all inline (non-heap) but cannot be
            // converted to Value without an intern table. This should not
            // happen on the binding chain hot path.
            unreachable!("to_value_inline: unexpected inline tag {tag}")
        }
    }
}
