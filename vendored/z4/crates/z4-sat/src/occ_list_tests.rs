// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::test_util::lit_signed as lit;

#[test]
fn add_and_get() {
    let mut occ = OccList::new(5);
    occ.add_clause(0, &[lit(1), lit(2), lit(3)]);
    occ.add_clause(1, &[lit(1), lit(-2)]);

    assert_eq!(occ.get(lit(1)), &[0, 1]);
    assert_eq!(occ.get(lit(2)), &[0]);
    assert_eq!(occ.get(lit(-2)), &[1]);
    assert_eq!(occ.get(lit(3)), &[0]);
    assert_eq!(occ.count(lit(1)), 2);
}

#[test]
fn remove_clause_removes_from_all_literals() {
    let mut occ = OccList::new(5);
    occ.add_clause(0, &[lit(1), lit(2)]);
    occ.add_clause(1, &[lit(1), lit(3)]);

    occ.remove_clause(0, &[lit(1), lit(2)]);
    assert_eq!(occ.get(lit(1)), &[1]);
    assert!(occ.get(lit(2)).is_empty());
    assert_eq!(occ.get(lit(3)), &[1]);
}

#[test]
fn remove_nonexistent_is_noop() {
    let mut occ = OccList::new(5);
    occ.add_clause(0, &[lit(1), lit(2)]);
    occ.remove_clause(99, &[lit(1), lit(2)]);
    assert_eq!(occ.get(lit(1)), &[0]);
}

#[test]
fn clear_empties_all() {
    let mut occ = OccList::new(5);
    occ.add_clause(0, &[lit(1), lit(2)]);
    occ.clear();
    assert!(occ.get(lit(1)).is_empty());
    assert!(occ.get(lit(2)).is_empty());
}

#[test]
fn ensure_num_vars_extends() {
    let mut occ = OccList::new(2);
    occ.add_clause(0, &[lit(1)]);
    occ.ensure_num_vars(10);
    assert_eq!(occ.get(lit(1)), &[0]);
    occ.add_clause(1, &[lit(8)]);
    assert_eq!(occ.get(lit(8)), &[1]);
}

#[test]
fn swap_to_front_moves_element() {
    let mut occ = OccList::new(5);
    occ.add_clause(10, &[lit(1)]);
    occ.add_clause(20, &[lit(1)]);
    occ.add_clause(30, &[lit(1)]);
    assert_eq!(occ.get(lit(1)), &[10, 20, 30]);

    occ.swap_to_front(lit(1), 2);
    assert_eq!(occ.get(lit(1)), &[30, 20, 10]);
}

#[test]
fn swap_to_front_noop_at_zero() {
    let mut occ = OccList::new(5);
    occ.add_clause(10, &[lit(1)]);
    occ.add_clause(20, &[lit(1)]);
    occ.swap_to_front(lit(1), 0);
    assert_eq!(occ.get(lit(1)), &[10, 20]);
}

#[test]
fn swap_to_front_out_of_bounds_noop() {
    let mut occ = OccList::new(5);
    occ.add_clause(10, &[lit(1)]);
    occ.swap_to_front(lit(1), 5);
    assert_eq!(occ.get(lit(1)), &[10]);
}
