// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests_support::{extract_fp, make_concrete_f16, solve_fp_clauses};
use super::*;

#[test]
fn test_fp16_add_tie_rne_rounds_to_even() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RNE);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_tie_rna_rounds_away() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RNA);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 1);
}

#[test]
fn test_fp16_add_tie_rtp_rounds_up() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RTP);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 1);
}

#[test]
fn test_fp16_add_tie_rtn_truncates_positive() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RTN);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_tie_rtz_truncates() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RTZ);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_neg_tie_rne() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, true, 15, 0);
    let b = make_concrete_f16(&mut solver, true, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RNE);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_neg_tie_rna() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, true, 15, 0);
    let b = make_concrete_f16(&mut solver, true, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RNA);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 1);
}

#[test]
fn test_fp16_add_neg_tie_rtp() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, true, 15, 0);
    let b = make_concrete_f16(&mut solver, true, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RTP);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_neg_tie_rtn() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, true, 15, 0);
    let b = make_concrete_f16(&mut solver, true, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RTN);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 1);
}

#[test]
fn test_fp16_add_neg_tie_rtz() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, true, 15, 0);
    let b = make_concrete_f16(&mut solver, true, 4, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RTZ);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_above_halfway_rne() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0b1000000000);
    let result = solver.make_add(&a, &b, RoundingMode::RNE);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 1);
}

#[test]
fn test_fp16_add_above_halfway_rtz() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0b1000000000);
    let result = solver.make_add(&a, &b, RoundingMode::RTZ);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_add_above_halfway_rtn() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 15, 0);
    let b = make_concrete_f16(&mut solver, false, 4, 0b1000000000);
    let result = solver.make_add(&a, &b, RoundingMode::RTN);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
}

#[test]
fn test_fp16_mul_exact_all_modes_agree() {
    let terms = TermStore::new();
    let expected_sig = 272u64;

    for rm in [
        RoundingMode::RNE,
        RoundingMode::RNA,
        RoundingMode::RTP,
        RoundingMode::RTN,
        RoundingMode::RTZ,
    ] {
        let mut solver = FpSolver::new(&terms);
        let a = make_concrete_f16(&mut solver, false, 15, 128);
        let b = make_concrete_f16(&mut solver, false, 15, 128);
        let result = solver.make_mul(&a, &b, rm);
        let model = solve_fp_clauses(&solver);
        let (sign, exp, sig) = extract_fp(&model, &result);
        assert!(!sign);
        assert_eq!(exp, 15);
        assert_eq!(sig, expected_sig);
    }
}

#[test]
fn test_fp16_add_pos_zero_neg_zero_rne() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 0, 0);
    let b = make_concrete_f16(&mut solver, true, 0, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RNE);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert_eq!(exp, 0);
    assert_eq!(sig, 0);
    assert!(!sign);
}

#[test]
fn test_fp16_add_pos_zero_neg_zero_rtn() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let a = make_concrete_f16(&mut solver, false, 0, 0);
    let b = make_concrete_f16(&mut solver, true, 0, 0);
    let result = solver.make_add(&a, &b, RoundingMode::RTN);
    let model = solve_fp_clauses(&solver);
    let (sign, exp, sig) = extract_fp(&model, &result);
    assert_eq!(exp, 0);
    assert_eq!(sig, 0);
    assert!(sign);
}
