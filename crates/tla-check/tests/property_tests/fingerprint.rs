// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use proptest::prelude::*;
use std::sync::Arc;
use tla_check::State;
use tla_check::Value;

use super::helpers::{func_from_pairs, sorted_set_from_values};

proptest! {

    // --- Determinism: Same state always produces same fingerprint ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_fingerprint_determinism(x in -1000i64..1000, y in -1000i64..1000) {
        // Building the same state twice should give the same fingerprint
        let s1 = State::from_pairs([("x", Value::int(x)), ("y", Value::int(y))]);
        let s2 = State::from_pairs([("x", Value::int(x)), ("y", Value::int(y))]);
        prop_assert_eq!(s1.fingerprint(), s2.fingerprint());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_fingerprint_order_independence(x in -100i64..100, y in -100i64..100) {
        // Variable insertion order should not affect fingerprint
        // (OrdMap sorts by key, so insertion order shouldn't matter)
        let s1 = State::from_pairs([("x", Value::int(x)), ("y", Value::int(y))]);
        let s2 = State::from_pairs([("y", Value::int(y)), ("x", Value::int(x))]);
        prop_assert_eq!(s1.fingerprint(), s2.fingerprint());
    }

    // --- Sensitivity: Different states produce different fingerprints ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_fingerprint_value_sensitivity(x in -100i64..100, y in -100i64..100) {
        // Different values should (almost always) produce different fingerprints
        prop_assume!(x != y); // Only test when x != y
        let s1 = State::from_pairs([("x", Value::int(x))]);
        let s2 = State::from_pairs([("x", Value::int(y))]);
        // While collisions are possible, they should be very rare for small integers
        prop_assert_ne!(s1.fingerprint(), s2.fingerprint(),
            "Collision detected for x={}, y={}", x, y);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_fingerprint_name_sensitivity(x in -100i64..100) {
        // Different variable names should produce different fingerprints
        let s1 = State::from_pairs([("x", Value::int(x))]);
        let s2 = State::from_pairs([("y", Value::int(x))]);
        prop_assert_ne!(s1.fingerprint(), s2.fingerprint());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_fingerprint_multi_var_sensitivity(
        x1 in -50i64..50, y1 in -50i64..50,
        x2 in -50i64..50, y2 in -50i64..50
    ) {
        // States with different (x,y) pairs should have different fingerprints
        prop_assume!(x1 != x2 || y1 != y2);
        let s1 = State::from_pairs([("x", Value::int(x1)), ("y", Value::int(y1))]);
        let s2 = State::from_pairs([("x", Value::int(x2)), ("y", Value::int(y2))]);
        prop_assert_ne!(s1.fingerprint(), s2.fingerprint());
    }

    // --- Type sensitivity: Fingerprints distinguish different types ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_fingerprint_type_sensitivity_bool_vs_int(v in prop::bool::ANY) {
        // Bool and Int should have different fingerprints even for 0/1 vs false/true
        let b = v as i64;
        let s1 = State::from_pairs([("x", Value::Bool(v))]);
        let s2 = State::from_pairs([("x", Value::int(b))]);
        prop_assert_ne!(s1.fingerprint(), s2.fingerprint());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_fingerprint_set_vs_seq(a in -10i64..10, b in -10i64..10) {
        // Set {a, b} and Sequence <<a, b>> should have different fingerprints
        let s1 = State::from_pairs([("x", Value::set([Value::int(a), Value::int(b)]))]);
        let s2 = State::from_pairs([("x", Value::seq([Value::int(a), Value::int(b)]))]);
        prop_assert_ne!(s1.fingerprint(), s2.fingerprint());
    }

    // --- Set element order independence ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_fingerprint_set_order_independence(
        vals in prop::collection::vec(-10i64..10, 2..5)
    ) {
        // Set elements should be fingerprinted in canonical order
        // regardless of how the set was constructed
        let set1 = sorted_set_from_values(vals.iter().map(|&v| Value::int(v)));
        let set2 = sorted_set_from_values(vals.iter().rev().map(|&v| Value::int(v)));
        let s1 = State::from_pairs([("x", Value::Set(set1.into()))]);
        let s2 = State::from_pairs([("x", Value::Set(set2.into()))]);
        prop_assert_eq!(s1.fingerprint(), s2.fingerprint());
    }

    // --- Complex nested structure tests ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_fingerprint_nested_set(
        vals in prop::collection::vec(-5i64..5, 1..4)
    ) {
        // Nested sets should fingerprint consistently
        let inner_set = sorted_set_from_values(vals.iter().map(|&v| Value::int(v)));
        let outer_set = sorted_set_from_values(vec![Value::Set(inner_set.into())]);

        let s1 = State::from_pairs([("x", Value::Set(outer_set.clone().into()))]);
        let s2 = State::from_pairs([("x", Value::Set(outer_set.into()))]);
        prop_assert_eq!(s1.fingerprint(), s2.fingerprint());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_fingerprint_func_vs_record(key in "[a-z]{1,3}", val in -10i64..10) {
        // In TLA+, records are functions with string domains.
        // A record [k |-> v] is semantically equivalent to a function with domain {k}.
        // Therefore, they should have the SAME fingerprint.
        use tla_value::RecordBuilder;
        use std::sync::Arc;

        let key_arc: Arc<str> = key.clone().into();

        let func = func_from_pairs(vec![
            (Value::string(key_arc.clone()), Value::int(val)),
        ]);

        let mut rec_builder = RecordBuilder::new();
        rec_builder.insert_arc(&key_arc, Value::int(val));

        let s1 = State::from_pairs([("x", Value::Func(Arc::new(func)))]);
        let s2 = State::from_pairs([("x", Value::Record(rec_builder.build()))]);

        // Records are functions with string domains - same fingerprint
        prop_assert_eq!(s1.fingerprint(), s2.fingerprint());
    }

    // --- Interval fingerprinting ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_fingerprint_interval_consistency(lo in -10i64..10, hi in -10i64..20) {
        // Same interval should always produce the same fingerprint
        let iv1 = tla_check::IntervalValue::new(lo.into(), hi.into());
        let iv2 = tla_check::IntervalValue::new(lo.into(), hi.into());
        let s1 = State::from_pairs([("x", Value::Interval(Arc::new(iv1)))]);
        let s2 = State::from_pairs([("x", Value::Interval(Arc::new(iv2)))]);
        prop_assert_eq!(s1.fingerprint(), s2.fingerprint());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_fingerprint_interval_vs_set(lo in 0i64..5, hi in 5i64..10) {
        // IntervalValue and equivalent Set should have the SAME fingerprint
        // (extensional equivalence)
        let iv = tla_check::IntervalValue::new(lo.into(), hi.into());
        let set = sorted_set_from_values((lo..=hi).map(Value::int));
        let s1 = State::from_pairs([("x", Value::Interval(Arc::new(iv)))]);
        let s2 = State::from_pairs([("x", Value::Set(set.into()))]);
        prop_assert_eq!(s1.fingerprint(), s2.fingerprint());
    }
}
