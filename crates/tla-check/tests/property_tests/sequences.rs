// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::helpers::{eval_str, int_set};
use tla_check::Value;

use num_bigint::BigInt;
use proptest::prelude::*;

proptest! {

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_sequence_len(elems in prop::collection::vec(-10i32..10, 0..8)) {
        // Len(<<e1, e2, ...>>) = n
        let seq_str = format!("<<{}>>", elems.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let result = eval_str(&format!("Len({})", seq_str)).unwrap();
        prop_assert_eq!(result, Value::SmallInt(elems.len() as i64));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_sequence_head(elems in prop::collection::vec(-10i32..10, 1..8)) {
        // Head(<<e1, e2, ...>>) = e1
        let seq_str = format!("<<{}>>", elems.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let result = eval_str(&format!("Head({})", seq_str)).unwrap();
        prop_assert_eq!(result, Value::int(elems[0].into()));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_sequence_index(elems in prop::collection::vec(-10i32..10, 1..8), idx in 1usize..8) {
        // s[i] returns the i-th element (1-indexed)
        if idx <= elems.len() {
            let seq_str = format!("<<{}>>", elems.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
            let result = eval_str(&format!("{}[{}]", seq_str, idx)).unwrap();
            prop_assert_eq!(result, Value::int(elems[idx - 1].into()));
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_append_len(elems in prop::collection::vec(-10i32..10, 0..6), v in -10i32..10) {
        // Len(Append(s, v)) = Len(s) + 1
        let seq_str = format!("<<{}>>", elems.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let result = eval_str(&format!("Len(Append({}, {}))", seq_str, v)).unwrap();
        prop_assert_eq!(result, Value::SmallInt((elems.len() + 1) as i64));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_domain_function(keys in prop::collection::vec(-5i32..5, 1..5)) {
        // DOMAIN [x \in S |-> e] = S
        let unique_keys: std::collections::HashSet<_> = keys.iter().copied().collect();
        let s_str = format!("{{{}}}", keys.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let result = eval_str(&format!(r#"DOMAIN [x \in {} |-> x * 2]"#, s_str)).unwrap();
        let expected = int_set(&unique_keys.into_iter().collect::<Vec<_>>());
        prop_assert_eq!(result, expected);
    }

    // ============================================================================
    // Cartesian Product (TupleSet) Tests
    // ============================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_cartesian_membership(
        s1 in prop::collection::vec(-5i32..5, 1..4),
        s2 in prop::collection::vec(-5i32..5, 1..4),
        a in -5i32..5,
        b in -5i32..5
    ) {
        // <<a, b>> \in S \X T <==> a \in S /\ b \in T
        let set1: std::collections::HashSet<_> = s1.iter().copied().collect();
        let set2: std::collections::HashSet<_> = s2.iter().copied().collect();

        let s1_str = format!("{{{}}}", s1.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let s2_str = format!("{{{}}}", s2.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));

        let result = eval_str(&format!("<<{}, {}>> \\in {} \\X {}", a, b, s1_str, s2_str)).unwrap();
        let expected = set1.contains(&a) && set2.contains(&b);
        prop_assert_eq!(result, Value::Bool(expected));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_cartesian_cardinality(
        s1 in prop::collection::vec(-5i32..5, 1..4),
        s2 in prop::collection::vec(-5i32..5, 1..4)
    ) {
        // Cardinality(S \X T) = Cardinality(S) * Cardinality(T)
        let set1: std::collections::HashSet<_> = s1.iter().copied().collect();
        let set2: std::collections::HashSet<_> = s2.iter().copied().collect();

        let s1_str = format!("{{{}}}", s1.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let s2_str = format!("{{{}}}", s2.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));

        let result = eval_str(&format!("Cardinality({} \\X {})", s1_str, s2_str)).unwrap();
        let expected = BigInt::from(set1.len() * set2.len());
        prop_assert_eq!(result, Value::big_int(expected));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_cartesian_empty_left(s in prop::collection::vec(-5i32..5, 1..4)) {
        // {} \X S = {}
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let _result = eval_str(&format!("{{}} \\X {}", s_str)).unwrap();
        // The result should be an empty set
        let card = eval_str(&format!("Cardinality({{}} \\X {})", s_str)).unwrap();
        prop_assert_eq!(card, Value::SmallInt(0));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_cartesian_empty_right(s in prop::collection::vec(-5i32..5, 1..4)) {
        // S \X {} = {}
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let _result = eval_str(&format!("{} \\X {{}}", s_str)).unwrap();
        // The result should be an empty set
        let card = eval_str(&format!("Cardinality({} \\X {{}})", s_str)).unwrap();
        prop_assert_eq!(card, Value::SmallInt(0));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_cartesian_singleton(a in -5i32..5, b in -5i32..5) {
        // {a} \X {b} = {<<a, b>>}
        let _result = eval_str(&format!("{{{}}} \\X {{{}}}", a, b)).unwrap();
        // Check that the tuple is in the result
        let contains = eval_str(&format!("<<{}, {}>> \\in {{{}}} \\X {{{}}}", a, b, a, b)).unwrap();
        prop_assert_eq!(contains, Value::Bool(true));
        // Check cardinality is 1
        let card = eval_str(&format!("Cardinality({{{}}} \\X {{{}}})", a, b)).unwrap();
        prop_assert_eq!(card, Value::SmallInt(1));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_cartesian_triple(
        s1 in prop::collection::vec(-3i32..3, 1..3),
        s2 in prop::collection::vec(-3i32..3, 1..3),
        s3 in prop::collection::vec(-3i32..3, 1..3)
    ) {
        // Cardinality(S1 \X S2 \X S3) = Cardinality(S1) * Cardinality(S2) * Cardinality(S3)
        let set1: std::collections::HashSet<_> = s1.iter().copied().collect();
        let set2: std::collections::HashSet<_> = s2.iter().copied().collect();
        let set3: std::collections::HashSet<_> = s3.iter().copied().collect();

        let s1_str = format!("{{{}}}", s1.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let s2_str = format!("{{{}}}", s2.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let s3_str = format!("{{{}}}", s3.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));

        let result = eval_str(&format!("Cardinality({} \\X {} \\X {})", s1_str, s2_str, s3_str)).unwrap();
        let expected = BigInt::from(set1.len() * set2.len() * set3.len());
        prop_assert_eq!(result, Value::big_int(expected));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_cartesian_with_interval(low in 0i32..3, high in 3i32..6) {
        // S \X (low..high) works with lazy intervals
        let result = eval_str(&format!("Cardinality({{1, 2}} \\X ({}..{}))", low, high)).unwrap();
        let interval_size = if high >= low { (high - low + 1) as usize } else { 0 };
        let expected = BigInt::from(2 * interval_size);
        prop_assert_eq!(result, Value::big_int(expected));
    }
}
