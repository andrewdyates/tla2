// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Set-Set comparison fast path tests (Part of #1434).

use super::super::super::*;
use super::tlc_normalized;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_set_cmp_homogeneous_safe_fast_path() {
    // Homogeneous-safe integer sets: comparison should work in-place
    // without allocating via tlc_set_elems. Verifies the fast path
    // produces correct ordering (same as the general sort path).
    let a = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let b = Value::set([Value::int(1), Value::int(2), Value::int(4)]);
    let c = Value::set([Value::int(1), Value::int(2)]);

    // a < b (same length, third element differs: 3 < 4)
    let set_ab = Value::set([a.clone(), b.clone()]);
    let norm = tlc_normalized(&set_ab);
    assert_eq!(norm, vec![a.clone(), b.clone()]);

    // c < a (shorter set comes first in tlc_cmp)
    let set_ca = Value::set([a.clone(), c.clone()]);
    let norm = tlc_normalized(&set_ca);
    assert_eq!(norm, vec![c.clone(), a.clone()]);

    // String sets — Part of #3193: strings are no longer "safe" (they use
    // token order in tlc_cmp). Control token registration to get deterministic
    // ordering: register "x","y" before "a","b" so sa sorts first.
    {
        use super::super::super::strings::{clear_tlc_string_tokens, tlc_string_token};
        clear_tlc_string_tokens();
        tlc_string_token(&Arc::from("x"));
        tlc_string_token(&Arc::from("y"));
        tlc_string_token(&Arc::from("a"));
        tlc_string_token(&Arc::from("b"));
        let sa = Value::set([Value::string("x"), Value::string("y")]);
        let sb = Value::set([Value::string("a"), Value::string("b")]);
        let set_sab = Value::set([sa.clone(), sb.clone()]);
        let norm = tlc_normalized(&set_sab);
        // In token order: x(1) < y(2) < a(3) < b(4), so sa's first elem (x)
        // has lower token than sb's first elem (a), hence sa < sb.
        assert_eq!(norm, vec![sa, sb]);
        clear_tlc_string_tokens();
    }
}

// === Set-Set fast path edge cases (Part of #1434) ===
// Verifies correctness of the zero-allocation comparison for edge cases:
// empty sets, single-element sets, boolean sets, and unsafe fallthrough.

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_set_cmp_empty_sets() {
    // Two empty sets compared as elements of a parent set.
    // Both are trivially safe; length comparison returns Equal.
    let empty = Value::set(std::iter::empty::<Value>());
    // A single empty set in a parent set should normalize to itself.
    let parent = Value::set([empty.clone()]);
    let norm = tlc_normalized(&parent);
    assert_eq!(norm, vec![empty.clone()]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_set_cmp_empty_vs_nonempty() {
    // Empty set < non-empty set (cardinality 0 < cardinality N)
    let empty = Value::set(std::iter::empty::<Value>());
    let nonempty = Value::set([Value::int(1)]);
    let parent = Value::set([nonempty.clone(), empty.clone()]);
    let norm = tlc_normalized(&parent);
    assert_eq!(norm, vec![empty, nonempty]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_set_cmp_singletons() {
    // Single-element sets: trivially homogeneous, fast path applies.
    let a = Value::set([Value::int(5)]);
    let b = Value::set([Value::int(3)]);
    let parent = Value::set([a.clone(), b.clone()]);
    let norm = tlc_normalized(&parent);
    // {3} < {5} by element comparison (same cardinality)
    assert_eq!(norm, vec![b, a]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_set_cmp_boolean_sets() {
    // Boolean sets are homogeneous-safe (Bool type class 0).
    let a = Value::set([Value::bool(false)]);
    let b = Value::set([Value::bool(true)]);
    let full = Value::set([Value::bool(false), Value::bool(true)]);
    let parent = Value::set([full.clone(), a.clone(), b.clone()]);
    let norm = tlc_normalized(&parent);
    // Cardinality order: {F} and {T} (size 1) before {F,T} (size 2)
    // Within size 1: {F} < {T} (FALSE < TRUE)
    assert_eq!(norm, vec![a, b, full]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_set_cmp_unsafe_fallthrough() {
    // Sets containing tuples are NOT homogeneous-safe — must fall through
    // to the general (allocating) path and still produce correct results.
    let a = Value::set([Value::tuple([Value::int(1)])]);
    let b = Value::set([Value::tuple([Value::int(2)])]);
    let parent = Value::set([b.clone(), a.clone()]);
    let norm = tlc_normalized(&parent);
    // Same cardinality, element comparison: <<1>> < <<2>>
    assert_eq!(norm, vec![a, b]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_set_cmp_mixed_safe_and_unsafe() {
    // One safe (integer set) + one unsafe (tuple set):
    // a_safe=true, b_safe=false → fast path skipped, general path used.
    // Still must produce correct result.
    let safe_set = Value::set([Value::int(1), Value::int(2)]);
    let unsafe_set = Value::set([Value::tuple([Value::int(1)])]);
    let parent = Value::set([safe_set.clone(), unsafe_set.clone()]);
    let norm = tlc_normalized(&parent);
    // Cardinality: unsafe_set (size 1) < safe_set (size 2)
    assert_eq!(norm, vec![unsafe_set, safe_set]);
}
