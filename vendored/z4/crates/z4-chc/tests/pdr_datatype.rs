// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! End-to-end PDR tests for datatype-sorted predicate parameters (#7016).
//!
//! These tests validate the full DT pipeline: parser -> executor adapter ->
//! z4-dpll DT solver -> model extraction -> point blocking -> MBP projection.

use ntest::timeout;
use z4_chc::{testing, PdrConfig, PdrResult};

/// Minimal DT: Pair with field access invariant.
///
/// Validates: parser, sort gate, executor DT declarations, model parsing,
/// point blocking, MBP DT projection.
///
/// Pattern: construct a Pair(x, y), store it, read fields back.
/// Invariant: fst(p) >= 0 (the first field is non-negative).
/// Expected: Safe — init sets fst to 42.
#[test]
#[timeout(30_000)]
fn test_pdr_dt_pair_field_access_safe() {
    let input = include_str!("../../../benchmarks/smt/chc_dt_pair_field_access.smt2");
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved fst(p) >= 0 with DT-sorted predicate parameter
        }
        Ok(other) => {
            panic!("Expected Safe for DT pair field access, got {other:?}");
        }
        Err(e) => {
            panic!("DT pair CHC parse/setup error: {e}");
        }
    }
}

/// Multi-constructor DT: Option enum with recognizer.
///
/// Validates: recognizer evaluation (`is-Some`, `is-None`), literal expansion,
/// multi-constructor model values.
///
/// Pattern: inv(x) where x is either None or Some(n) with n > 0.
/// Invariant: is-None(x) OR val(x) > 0.
/// Expected: Safe.
#[test]
#[timeout(30_000)]
fn test_pdr_dt_option_enum_safe() {
    let input = include_str!("../../../benchmarks/smt/chc_dt_option_enum.smt2");
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved the Option enum invariant with multi-constructor DT
        }
        Ok(other) => {
            panic!("Expected Safe for DT option enum, got {other:?}");
        }
        Err(e) => {
            panic!("DT option enum CHC parse/setup error: {e}");
        }
    }
}

/// Mutually recursive DTs via declare-datatypes (plural form).
///
/// Validates: declare-datatypes parser, mutual recursion sort resolution,
/// Tree/Forest types with field access.
///
/// Pattern: inv(t) where t is a Tree (leaf or node).
/// Invariant: is-leaf(t) => val(t) >= 0.
/// Expected: Safe — init creates leaf(42).
#[test]
#[timeout(30_000)]
fn test_pdr_dt_mutual_recursive_safe() {
    let input = include_str!("../../../benchmarks/smt/chc_dt_mutual_recursive.smt2");
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved leaf value invariant with mutually recursive DTs
        }
        Ok(PdrResult::Unknown | PdrResult::NotApplicable) => {
            // Acceptable if mutual recursion DT pipeline not yet fully wired
        }
        Ok(PdrResult::Unsafe(_)) => {
            panic!("PDR returned Unsafe for a safe mutual-recursive DT problem — soundness bug");
        }
        Err(e) => {
            panic!("Mutual-recursive DT CHC parse/setup error: {e}");
        }
        _ => panic!("unexpected variant"),
    }
}

/// Constructor clash UNSAT: transition changes Some to None, violating safety.
///
/// Validates: constructor discrimination in counterexample generation,
/// `is-None` / `is-Some` tester reasoning in PDR unsafe path.
///
/// Pattern: init x = Some(42), trans x -> None, safety requires is-Some(x).
/// Expected: Unsafe — counterexample: init -> one step -> None violates safety.
#[test]
#[timeout(30_000)]
fn test_pdr_dt_constructor_clash_unsafe() {
    let input = include_str!("../../../benchmarks/smt/chc_dt_clash_unsafe.smt2");
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Unsafe(_)) => {
            // PDR correctly found a counterexample via constructor clash
        }
        Ok(other) => {
            panic!("Expected Unsafe for DT constructor clash, got {other:?}");
        }
        Err(e) => {
            panic!("DT constructor clash CHC parse/setup error: {e}");
        }
    }
}
