// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cached singleton values for commonly constructed TLA+ values.
//!
//! Reduces `Value::clone`/`Value::drop` overhead by avoiding repeated heap
//! allocation and Arc construction for values that are semantically identical
//! across all uses. Each cached value is initialized once via `OnceLock` and
//! subsequent calls clone the `Arc` (a single atomic refcount bump).
//!
//! Part of #3980: Value interning -- reduce clone/drop overhead for common values.

use super::{SeqValue, SortedSet, Value};
use std::sync::{Arc, OnceLock};

// ============================================================================
// Static singletons
// ============================================================================

/// Cached `Value::Set(Arc::new(SortedSet::new()))` — the empty set `{}`.
static EMPTY_SET_VALUE: OnceLock<Value> = OnceLock::new();

/// Cached `Value::Set({FALSE, TRUE})` — the BOOLEAN set.
static BOOLEAN_SET_VALUE: OnceLock<Value> = OnceLock::new();

/// Cached `Value::Seq(Arc::new(SeqValue::new()))` — the empty sequence `<<>>`.
static EMPTY_SEQ_VALUE: OnceLock<Value> = OnceLock::new();

/// Cached `Value::Tuple(Arc::from([]))` — the empty tuple.
static EMPTY_TUPLE_VALUE: OnceLock<Value> = OnceLock::new();

// ============================================================================
// Public accessors
// ============================================================================

/// Return a cached empty set value.
///
/// Avoids `Arc::new(SortedSet::new())` on every call — the empty set is
/// one of the most frequently constructed values during model checking
/// (e.g., `{}` in message buffers, empty domain initialization).
#[inline]
pub(crate) fn cached_empty_set() -> Value {
    EMPTY_SET_VALUE
        .get_or_init(|| Value::Set(Arc::new(SortedSet::new())))
        .clone()
}

/// Return a cached BOOLEAN set value `{FALSE, TRUE}`.
///
/// BOOLEAN is referenced in nearly every spec. Caching avoids constructing
/// the 2-element SortedSet and its Arc wrapper on each reference.
#[inline]
pub(crate) fn cached_boolean_set() -> Value {
    BOOLEAN_SET_VALUE
        .get_or_init(|| {
            Value::Set(Arc::new(SortedSet::from_sorted_vec(vec![
                Value::Bool(false),
                Value::Bool(true),
            ])))
        })
        .clone()
}

/// Return a cached empty sequence value `<<>>`.
///
/// Empty sequences appear frequently during initialization and as base
/// cases for sequence-building operators (e.g., `SelectSeq`, `FoldSeq`).
#[inline]
pub(crate) fn cached_empty_seq() -> Value {
    EMPTY_SEQ_VALUE
        .get_or_init(|| Value::Seq(Arc::new(SeqValue::new())))
        .clone()
}

/// Return a cached empty tuple value.
///
/// Used by `cartesian_product` for the 0-component base case and by
/// various tuple construction paths.
#[inline]
pub(crate) fn cached_empty_tuple() -> Value {
    EMPTY_TUPLE_VALUE
        .get_or_init(|| Value::Tuple(Arc::<[Value]>::from([])))
        .clone()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cached_empty_set_is_empty() {
        let v = cached_empty_set();
        match &v {
            Value::Set(s) => assert!(s.is_empty()),
            _ => panic!("expected Value::Set"),
        }
    }

    #[test]
    fn test_cached_empty_set_equality() {
        let a = cached_empty_set();
        let b = cached_empty_set();
        assert_eq!(a, b);
        // Both should share the same Arc
        if let (Value::Set(sa), Value::Set(sb)) = (&a, &b) {
            assert!(Arc::ptr_eq(sa, sb), "cached empty sets should share Arc");
        }
    }

    #[test]
    fn test_cached_boolean_set_contents() {
        let v = cached_boolean_set();
        match &v {
            Value::Set(s) => {
                assert_eq!(s.len(), 2);
                assert!(s.contains(&Value::Bool(false)));
                assert!(s.contains(&Value::Bool(true)));
            }
            _ => panic!("expected Value::Set"),
        }
    }

    #[test]
    fn test_cached_boolean_set_equality() {
        let a = cached_boolean_set();
        let b = cached_boolean_set();
        assert_eq!(a, b);
        if let (Value::Set(sa), Value::Set(sb)) = (&a, &b) {
            assert!(Arc::ptr_eq(sa, sb), "cached BOOLEAN sets should share Arc");
        }
    }

    #[test]
    fn test_cached_empty_seq_is_empty() {
        let v = cached_empty_seq();
        match &v {
            Value::Seq(s) => assert!(s.is_empty()),
            _ => panic!("expected Value::Seq"),
        }
    }

    #[test]
    fn test_cached_empty_tuple_is_empty() {
        let v = cached_empty_tuple();
        match &v {
            Value::Tuple(t) => assert!(t.is_empty()),
            _ => panic!("expected Value::Tuple"),
        }
    }

    #[test]
    fn test_cached_empty_set_matches_constructor() {
        let pooled = cached_empty_set();
        let fresh = Value::empty_set();
        assert_eq!(pooled, fresh);
    }

    #[test]
    fn test_cached_empty_seq_matches_constructor() {
        let pooled = cached_empty_seq();
        let fresh = Value::seq(Vec::<Value>::new());
        assert_eq!(pooled, fresh);
    }

    #[test]
    fn test_cached_empty_tuple_matches_constructor() {
        let pooled = cached_empty_tuple();
        let fresh = Value::tuple(Vec::<Value>::new());
        assert_eq!(pooled, fresh);
    }
}
