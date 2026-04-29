// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::helpers::{eval_str, int_set, small_int_set};
use proptest::prelude::*;
use std::sync::Arc;
use tla_check::Value;
use tla_value::SortedSet;

// ============================================================================
// Set operator property tests
// ============================================================================

proptest! {

    // --- Union properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_union_commutativity(s in small_int_set(), t in small_int_set()) {
        // S \cup T = T \cup S
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let t_str = format!("{{{}}}", t.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let lhs = eval_str(&format!(r#"{} \cup {}"#, s_str, t_str)).unwrap();
        let rhs = eval_str(&format!(r#"{} \cup {}"#, t_str, s_str)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_union_associativity(s in small_int_set(), t in small_int_set(), u in small_int_set()) {
        // (S \cup T) \cup U = S \cup (T \cup U)
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let t_str = format!("{{{}}}", t.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let u_str = format!("{{{}}}", u.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let lhs = eval_str(&format!(r#"({} \cup {}) \cup {}"#, s_str, t_str, u_str)).unwrap();
        let rhs = eval_str(&format!(r#"{} \cup ({} \cup {})"#, s_str, t_str, u_str)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_union_identity(s in small_int_set()) {
        // S \cup {} = S
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let result = eval_str(&format!(r#"{} \cup {{}}"#, s_str)).unwrap();
        let expected = int_set(&s);
        prop_assert_eq!(result, expected);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_union_idempotence(s in small_int_set()) {
        // S \cup S = S
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let result = eval_str(&format!(r#"{} \cup {}"#, s_str, s_str)).unwrap();
        let expected = int_set(&s);
        prop_assert_eq!(result, expected);
    }

    // --- Intersection properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_intersect_commutativity(s in small_int_set(), t in small_int_set()) {
        // S \cap T = T \cap S
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let t_str = format!("{{{}}}", t.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let lhs = eval_str(&format!(r#"{} \cap {}"#, s_str, t_str)).unwrap();
        let rhs = eval_str(&format!(r#"{} \cap {}"#, t_str, s_str)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_intersect_associativity(s in small_int_set(), t in small_int_set(), u in small_int_set()) {
        // (S \cap T) \cap U = S \cap (T \cap U)
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let t_str = format!("{{{}}}", t.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let u_str = format!("{{{}}}", u.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let lhs = eval_str(&format!(r#"({} \cap {}) \cap {}"#, s_str, t_str, u_str)).unwrap();
        let rhs = eval_str(&format!(r#"{} \cap ({} \cap {})"#, s_str, t_str, u_str)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_intersect_idempotence(s in small_int_set()) {
        // S \cap S = S
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let result = eval_str(&format!(r#"{} \cap {}"#, s_str, s_str)).unwrap();
        let expected = int_set(&s);
        prop_assert_eq!(result, expected);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_intersect_empty(s in small_int_set()) {
        // S \cap {} = {}
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let result = eval_str(&format!(r#"{} \cap {{}}"#, s_str)).unwrap();
        prop_assert_eq!(result, Value::Set(Arc::new(SortedSet::new())));
    }

    // --- Set difference properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_setminus_self(s in small_int_set()) {
        // S \ S = {}
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let result = eval_str(&format!(r#"{} \ {}"#, s_str, s_str)).unwrap();
        prop_assert_eq!(result, Value::Set(Arc::new(SortedSet::new())));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_setminus_empty(s in small_int_set()) {
        // S \ {} = S
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let result = eval_str(&format!(r#"{} \ {{}}"#, s_str)).unwrap();
        let expected = int_set(&s);
        prop_assert_eq!(result, expected);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_empty_setminus(s in small_int_set()) {
        // {} \ S = {}
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let result = eval_str(&format!(r#"{{}} \ {}"#, s_str)).unwrap();
        prop_assert_eq!(result, Value::Set(Arc::new(SortedSet::new())));
    }

    // --- Subset properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_subset_reflexive(s in small_int_set()) {
        // S \subseteq S
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let result = eval_str(&format!(r#"{} \subseteq {}"#, s_str, s_str)).unwrap();
        prop_assert_eq!(result, Value::Bool(true));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_empty_subset_all(s in small_int_set()) {
        // {} \subseteq S
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let result = eval_str(&format!(r#"{{}} \subseteq {}"#, s_str)).unwrap();
        prop_assert_eq!(result, Value::Bool(true));
    }

    // --- Distributive laws ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_union_intersect_distribute(s in small_int_set(), t in small_int_set(), u in small_int_set()) {
        // S \cap (T \cup U) = (S \cap T) \cup (S \cap U)
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let t_str = format!("{{{}}}", t.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let u_str = format!("{{{}}}", u.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let lhs = eval_str(&format!(r#"{} \cap ({} \cup {})"#, s_str, t_str, u_str)).unwrap();
        let rhs = eval_str(&format!(r#"({} \cap {}) \cup ({} \cap {})"#, s_str, t_str, s_str, u_str)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_intersect_union_distribute(s in small_int_set(), t in small_int_set(), u in small_int_set()) {
        // S \cup (T \cap U) = (S \cup T) \cap (S \cup U)
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let t_str = format!("{{{}}}", t.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let u_str = format!("{{{}}}", u.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let lhs = eval_str(&format!(r#"{} \cup ({} \cap {})"#, s_str, t_str, u_str)).unwrap();
        let rhs = eval_str(&format!(r#"({} \cup {}) \cap ({} \cup {})"#, s_str, t_str, s_str, u_str)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // --- Cardinality properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_cardinality_union_intersect(s in small_int_set(), t in small_int_set()) {
        // |S \cup T| + |S \cap T| = |S| + |T|
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let t_str = format!("{{{}}}", t.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));

        let union_card = eval_str(&format!(r#"Cardinality({} \cup {})"#, s_str, t_str)).unwrap();
        let intersect_card = eval_str(&format!(r#"Cardinality({} \cap {})"#, s_str, t_str)).unwrap();
        let s_card = eval_str(&format!(r#"Cardinality({})"#, s_str)).unwrap();
        let t_card = eval_str(&format!(r#"Cardinality({})"#, t_str)).unwrap();

        let lhs = union_card.to_bigint().expect("Expected integer") + intersect_card.to_bigint().expect("Expected integer");
        let rhs = s_card.to_bigint().expect("Expected integer") + t_card.to_bigint().expect("Expected integer");
        prop_assert_eq!(lhs, rhs);
    }
}
