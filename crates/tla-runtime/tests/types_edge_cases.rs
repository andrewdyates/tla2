// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Edge-case tests for tla-runtime types: set operations, function domain,
//! cartesian product boundaries, powerset boundaries, boolean_set.
//!
//! Filed as Part of #1597 — coverage gaps in tla-runtime discovered during
//! Prover code-quality audit.

use tla_runtime::tla_set;
use tla_runtime::{boolean_set, cartesian_product, powerset, TlaFunc, TlaSet};

// --- TlaSet::difference ---

#[test]
fn test_set_difference_basic() {
    let a = tla_set![1, 2, 3, 4];
    let b = tla_set![2, 4];
    let diff = a.difference(&b);
    assert_eq!(diff.len(), 2);
    assert!(diff.contains(&1));
    assert!(diff.contains(&3));
    assert!(!diff.contains(&2));
    assert!(!diff.contains(&4));
}

#[test]
fn test_set_difference_disjoint() {
    let a = tla_set![1, 2];
    let b = tla_set![3, 4];
    let diff = a.difference(&b);
    assert_eq!(diff, a);
}

#[test]
fn test_set_difference_self() {
    let a = tla_set![1, 2, 3];
    let diff = a.difference(&a);
    assert!(diff.is_empty());
}

#[test]
fn test_set_difference_empty_rhs() {
    let a = tla_set![1, 2];
    let empty: TlaSet<i32> = TlaSet::new();
    let diff = a.difference(&empty);
    assert_eq!(diff, a);
}

#[test]
fn test_set_difference_empty_lhs() {
    let empty: TlaSet<i32> = TlaSet::new();
    let b = tla_set![1, 2];
    let diff = empty.difference(&b);
    assert!(diff.is_empty());
}

// --- TlaSet::is_subset ---

#[test]
fn test_is_subset_true() {
    let a = tla_set![1, 2];
    let b = tla_set![1, 2, 3];
    assert!(a.is_subset(&b));
}

#[test]
fn test_is_subset_equal() {
    let a = tla_set![1, 2, 3];
    assert!(a.is_subset(&a));
}

#[test]
fn test_is_subset_false() {
    let a = tla_set![1, 4];
    let b = tla_set![1, 2, 3];
    assert!(!a.is_subset(&b));
}

#[test]
fn test_is_subset_empty() {
    let empty: TlaSet<i32> = TlaSet::new();
    let a = tla_set![1, 2];
    assert!(empty.is_subset(&a));
    assert!(empty.is_subset(&empty));
}

// --- TlaFunc::domain ---

#[test]
fn test_func_domain() {
    let f: TlaFunc<i32, &str> = [(1, "a"), (2, "b"), (3, "c")].into_iter().collect();
    let dom = f.domain();
    assert_eq!(dom.len(), 3);
    assert!(dom.contains(&1));
    assert!(dom.contains(&2));
    assert!(dom.contains(&3));
}

#[test]
fn test_func_domain_empty() {
    let f: TlaFunc<i32, i32> = TlaFunc::new();
    let dom = f.domain();
    assert!(dom.is_empty());
}

#[test]
fn test_func_domain_after_except() {
    let f: TlaFunc<i32, &str> = [(1, "a"), (2, "b")].into_iter().collect();
    let g = f.except(3, "c");
    let dom = g.domain();
    assert_eq!(dom.len(), 3);
    assert!(dom.contains(&3));
}

// --- boolean_set ---

#[test]
fn test_boolean_set() {
    let bs = boolean_set();
    assert_eq!(bs.len(), 2);
    assert!(bs.contains(&false));
    assert!(bs.contains(&true));
}

// --- cartesian_product edge cases ---

#[test]
fn test_cartesian_product_all_elements() {
    // Strengthen: check ALL 4 elements, not just 2
    let a = tla_set![1, 2];
    let b = tla_set!["x", "y"];
    let cp = cartesian_product(&a, &b);
    assert_eq!(cp.len(), 4);
    assert!(cp.contains(&(1, "x")));
    assert!(cp.contains(&(1, "y")));
    assert!(cp.contains(&(2, "x")));
    assert!(cp.contains(&(2, "y")));
}

#[test]
fn test_cartesian_product_empty_lhs() {
    let a: TlaSet<i32> = TlaSet::new();
    let b = tla_set![1, 2];
    let cp = cartesian_product(&a, &b);
    assert!(cp.is_empty());
}

#[test]
fn test_cartesian_product_empty_rhs() {
    let a = tla_set![1, 2];
    let b: TlaSet<i32> = TlaSet::new();
    let cp = cartesian_product(&a, &b);
    assert!(cp.is_empty());
}

#[test]
fn test_cartesian_product_both_empty() {
    let a: TlaSet<i32> = TlaSet::new();
    let b: TlaSet<i32> = TlaSet::new();
    let cp = cartesian_product(&a, &b);
    assert!(cp.is_empty());
}

// --- powerset edge cases ---

#[test]
fn test_powerset_empty_set() {
    let s: TlaSet<i32> = TlaSet::new();
    let ps = powerset(&s);
    assert_eq!(ps.len(), 1);
    assert!(ps.contains(&TlaSet::new()));
}

#[test]
fn test_powerset_singleton() {
    let s = tla_set![42];
    let ps = powerset(&s);
    assert_eq!(ps.len(), 2);
    assert!(ps.contains(&TlaSet::new()));
    assert!(ps.contains(&tla_set![42]));
}

#[test]
#[should_panic(expected = "SUBSET of set with")]
fn test_powerset_too_large() {
    let s: TlaSet<i32> = (0..21).collect();
    let _ = powerset(&s);
}
