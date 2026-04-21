// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use hashbrown::HashMap;
use num_bigint::BigInt;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::{Duration, Instant};
use z4_bv::BvBits;

use crate::executor_types::{SolveResult, UnknownReason};

use super::super::Executor;

#[test]
fn test_extract_bv_model_empty_inputs() {
    let sat_model: Vec<bool> = vec![];
    let term_bits: HashMap<TermId, BvBits> = HashMap::new();
    let terms = TermStore::new();

    let result = Executor::extract_bv_model_from_bits(&sat_model, &term_bits, 0, &terms);

    assert!(result.values.is_empty());
    assert!(result.term_to_bits.is_empty());
}

#[test]
fn test_extract_bv_model_single_8bit_var() {
    let mut terms = TermStore::new();
    let var_term = terms.mk_var("x", Sort::bitvec(8));
    let sat_model = vec![true, true, false, true, false, false, false, true];
    let bits: BvBits = (1..=8i32).collect();
    let mut term_bits = HashMap::new();
    term_bits.insert(var_term, bits);

    let result = Executor::extract_bv_model_from_bits(&sat_model, &term_bits, 0, &terms);

    assert_eq!(result.values.len(), 1);
    assert!(result.values.contains_key(&var_term));
    assert_eq!(result.values[&var_term], BigInt::from(139));
}

#[test]
fn test_extract_bv_model_negative_literals() {
    let mut terms = TermStore::new();
    let var_term = terms.mk_var("y", Sort::bitvec(4));
    let sat_model = vec![false, false, false, false];
    let bits: BvBits = vec![-1, -2, -3, -4];
    let mut term_bits = HashMap::new();
    term_bits.insert(var_term, bits);

    let result = Executor::extract_bv_model_from_bits(&sat_model, &term_bits, 0, &terms);

    assert_eq!(result.values.len(), 1);
    assert_eq!(result.values[&var_term], BigInt::from(15));
}

#[test]
fn test_extract_bv_model_with_offset() {
    let mut terms = TermStore::new();
    let var_term = terms.mk_var("z", Sort::bitvec(4));
    let sat_model = vec![
        false, false, false, false, false, true, false, true, false, false,
    ];
    let bits: BvBits = vec![1, 2, 3, 4];
    let mut term_bits = HashMap::new();
    term_bits.insert(var_term, bits);

    let result = Executor::extract_bv_model_from_bits(&sat_model, &term_bits, 5, &terms);

    assert_eq!(result.values.len(), 1);
    assert_eq!(result.values[&var_term], BigInt::from(5));
}

#[test]
fn test_extract_bv_model_filters_non_bv() {
    let mut terms = TermStore::new();
    let var_term = terms.mk_var("x", Sort::bitvec(8));
    // Non-BV-sorted term should be filtered out even if it has bits
    let int_term = terms.mk_var("n", Sort::Int);
    let sat_model = vec![true; 16];
    let bits: BvBits = (1..=8i32).collect();
    let mut term_bits = HashMap::new();
    term_bits.insert(var_term, bits);
    term_bits.insert(int_term, (9..=16i32).collect());

    let result = Executor::extract_bv_model_from_bits(&sat_model, &term_bits, 0, &terms);

    assert_eq!(result.values.len(), 1);
    assert!(result.values.contains_key(&var_term));
    assert!(!result.values.contains_key(&int_term));
}

#[test]
fn test_extract_bv_model_out_of_bounds() {
    let mut terms = TermStore::new();
    let var_term = terms.mk_var("w", Sort::bitvec(4));
    let sat_model = vec![true, false];
    let bits: BvBits = vec![1, 2, 3, 4];
    let mut term_bits = HashMap::new();
    term_bits.insert(var_term, bits);

    let result = Executor::extract_bv_model_from_bits(&sat_model, &term_bits, 0, &terms);

    assert_eq!(result.values.len(), 1);
    assert_eq!(result.values[&var_term], BigInt::from(1));
}

#[test]
fn test_array_axiom_result_struct() {
    let result = ArrayAxiomResult {
        clauses: Vec::new(),
        num_vars: 0,
    };
    assert!(result.clauses.is_empty());
    assert_eq!(result.num_vars, 0);
}

#[test]
fn test_euf_axiom_result_struct() {
    let result = EufAxiomResult {
        clauses: vec![z4_core::CnfClause::new(vec![1, 2, 3])],
        num_vars: 5,
    };
    assert_eq!(result.clauses.len(), 1);
    assert_eq!(result.num_vars, 5);
}

#[test]
fn test_theory_loop_abort_on_interrupt_control() {
    let mut exec = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    exec.set_solve_controls(Some(interrupt.clone()), None);

    assert!(!exec.should_abort_theory_loop());

    interrupt.store(true, Ordering::Relaxed);
    assert!(exec.should_abort_theory_loop());
    assert_eq!(exec.last_result(), Some(SolveResult::Unknown));
    assert_eq!(exec.get_reason_unknown(), Some(UnknownReason::Interrupted));
}

#[test]
fn test_theory_loop_abort_on_expired_deadline_control() {
    let mut exec = Executor::new();
    let expired_deadline = Instant::now()
        .checked_sub(Duration::from_millis(1))
        .unwrap();
    exec.set_solve_controls(None, Some(expired_deadline));

    assert!(exec.should_abort_theory_loop());
    assert_eq!(exec.last_result(), Some(SolveResult::Unknown));
    assert_eq!(exec.get_reason_unknown(), Some(UnknownReason::Timeout));
}
