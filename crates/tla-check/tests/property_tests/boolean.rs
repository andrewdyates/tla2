// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::helpers::{eval_str, tla_bool};
use proptest::prelude::*;
use tla_check::Value;

// ============================================================================
// Boolean operator property tests
// ============================================================================

proptest! {

    // --- AND (conjunction) properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_and_identity(a: bool) {
        // a /\ TRUE = a
        let result = eval_str(&format!(r#"{} /\ TRUE"#, tla_bool(a))).unwrap();
        prop_assert_eq!(result, Value::Bool(a));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_and_annihilation(a: bool) {
        // a /\ FALSE = FALSE
        let result = eval_str(&format!(r#"{} /\ FALSE"#, tla_bool(a))).unwrap();
        prop_assert_eq!(result, Value::Bool(false));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_and_commutativity(a: bool, b: bool) {
        // a /\ b = b /\ a
        let lhs = eval_str(&format!(r#"{} /\ {}"#, tla_bool(a), tla_bool(b))).unwrap();
        let rhs = eval_str(&format!(r#"{} /\ {}"#, tla_bool(b), tla_bool(a))).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_and_associativity(a: bool, b: bool, c: bool) {
        // (a /\ b) /\ c = a /\ (b /\ c)
        let lhs = eval_str(&format!(r#"({} /\ {}) /\ {}"#, tla_bool(a), tla_bool(b), tla_bool(c))).unwrap();
        let rhs = eval_str(&format!(r#"{} /\ ({} /\ {})"#, tla_bool(a), tla_bool(b), tla_bool(c))).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_and_idempotence(a: bool) {
        // a /\ a = a
        let result = eval_str(&format!(r#"{} /\ {}"#, tla_bool(a), tla_bool(a))).unwrap();
        prop_assert_eq!(result, Value::Bool(a));
    }

    // --- OR (disjunction) properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_or_identity(a: bool) {
        // a \/ FALSE = a
        let result = eval_str(&format!(r#"{} \/ FALSE"#, tla_bool(a))).unwrap();
        prop_assert_eq!(result, Value::Bool(a));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_or_annihilation(a: bool) {
        // a \/ TRUE = TRUE
        let result = eval_str(&format!(r#"{} \/ TRUE"#, tla_bool(a))).unwrap();
        prop_assert_eq!(result, Value::Bool(true));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_or_commutativity(a: bool, b: bool) {
        // a \/ b = b \/ a
        let lhs = eval_str(&format!(r#"{} \/ {}"#, tla_bool(a), tla_bool(b))).unwrap();
        let rhs = eval_str(&format!(r#"{} \/ {}"#, tla_bool(b), tla_bool(a))).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_or_associativity(a: bool, b: bool, c: bool) {
        // (a \/ b) \/ c = a \/ (b \/ c)
        let lhs = eval_str(&format!(r#"({} \/ {}) \/ {}"#, tla_bool(a), tla_bool(b), tla_bool(c))).unwrap();
        let rhs = eval_str(&format!(r#"{} \/ ({} \/ {})"#, tla_bool(a), tla_bool(b), tla_bool(c))).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_or_idempotence(a: bool) {
        // a \/ a = a
        let result = eval_str(&format!(r#"{} \/ {}"#, tla_bool(a), tla_bool(a))).unwrap();
        prop_assert_eq!(result, Value::Bool(a));
    }

    // --- NOT (negation) properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_not_involution(a: bool) {
        // ~~a = a
        let result = eval_str(&format!("~~{}", tla_bool(a))).unwrap();
        prop_assert_eq!(result, Value::Bool(a));
    }

    // --- De Morgan's Laws ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_de_morgan_and(a: bool, b: bool) {
        // ~(a /\ b) = ~a \/ ~b
        let lhs = eval_str(&format!(r#"~({} /\ {})"#, tla_bool(a), tla_bool(b))).unwrap();
        let rhs = eval_str(&format!(r#"~{} \/ ~{}"#, tla_bool(a), tla_bool(b))).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_de_morgan_or(a: bool, b: bool) {
        // ~(a \/ b) = ~a /\ ~b
        let lhs = eval_str(&format!(r#"~({} \/ {})"#, tla_bool(a), tla_bool(b))).unwrap();
        let rhs = eval_str(&format!(r#"~{} /\ ~{}"#, tla_bool(a), tla_bool(b))).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // --- Implication properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_implies_definition(a: bool, b: bool) {
        // (a => b) = (~a \/ b)
        let lhs = eval_str(&format!("{} => {}", tla_bool(a), tla_bool(b))).unwrap();
        let rhs = eval_str(&format!(r#"~{} \/ {}"#, tla_bool(a), tla_bool(b))).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_implies_reflexive(a: bool) {
        // a => a = TRUE
        let result = eval_str(&format!("{} => {}", tla_bool(a), tla_bool(a))).unwrap();
        prop_assert_eq!(result, Value::Bool(true));
    }

    // --- Equivalence properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_equiv_reflexive(a: bool) {
        // a <=> a = TRUE
        let result = eval_str(&format!("{} <=> {}", tla_bool(a), tla_bool(a))).unwrap();
        prop_assert_eq!(result, Value::Bool(true));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_equiv_symmetric(a: bool, b: bool) {
        // (a <=> b) = (b <=> a)
        let lhs = eval_str(&format!("{} <=> {}", tla_bool(a), tla_bool(b))).unwrap();
        let rhs = eval_str(&format!("{} <=> {}", tla_bool(b), tla_bool(a))).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // --- Absorption laws ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_absorption_and_or(a: bool, b: bool) {
        // a /\ (a \/ b) = a
        let result = eval_str(&format!(r#"{} /\ ({} \/ {})"#, tla_bool(a), tla_bool(a), tla_bool(b))).unwrap();
        prop_assert_eq!(result, Value::Bool(a));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_absorption_or_and(a: bool, b: bool) {
        // a \/ (a /\ b) = a
        let result = eval_str(&format!(r#"{} \/ ({} /\ {})"#, tla_bool(a), tla_bool(a), tla_bool(b))).unwrap();
        prop_assert_eq!(result, Value::Bool(a));
    }
}
