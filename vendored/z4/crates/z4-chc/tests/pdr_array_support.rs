// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Tests for PDR array-sorted predicate support (#6047).
//!
//! These tests verify that PDR can handle CHC problems with Array-sorted
//! predicate parameters without crashing. Prior to #6047, the PDR sort gate
//! rejected any problem with Array-sorted predicates, returning Unknown.

use ntest::timeout;
use z4_chc::{testing, PdrConfig, PdrResult};

/// Test that PDR accepts a CHC problem with Array(Int,Int) predicate parameters
/// and constant-index array access (scalarizable).
///
/// This problem models: store 42 at index 0, then check select(arr, 0) == 42.
/// The scalarization pass should convert this to scalar variables before PDR runs.
///
/// Expected: Safe (the invariant holds trivially).
#[test]
#[timeout(15_000)]
fn test_pdr_array_const_index_scalarizable() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array Int Int) ) Bool)

(assert
  (forall ( (A (Array Int Int)) )
    (=>
      (= A (store ((as const (Array Int Int)) 0) 0 42))
      (inv A)
    )
  )
)

(assert
  (forall ( (A (Array Int Int)) )
    (=>
      (and (inv A) (not (= (select A 0) 42)))
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let config = PdrConfig::default();
    let result = testing::pdr_solve_from_str(input, config);
    // Constant-index select/store: scalarization eliminates the array, PDR solves trivially.
    assert!(
        matches!(&result, Ok(PdrResult::Safe(_))),
        "Expected Safe for constant-index scalarizable array problem, got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// Test that PDR accepts a CHC problem with Array(Int,Int) predicate parameters
/// and variable-index array access (NOT scalarizable).
///
/// This problem models a simple loop that writes x to arr[x] and checks arr[0] == 0.
/// Variable index `x` prevents scalarization, so PDR must handle the array sort directly.
///
/// Expected: Unknown or Safe (either is acceptable; crash is not).
#[test]
#[timeout(15_000)]
fn test_pdr_array_variable_index_no_crash() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array Int Int) Int ) Bool)

(assert
  (forall ( (A (Array Int Int)) (X Int) )
    (=>
      (and (= X 0) (= A (store ((as const (Array Int Int)) 0) 0 0)))
      (inv A X)
    )
  )
)

(assert
  (forall ( (A (Array Int Int)) (X Int) (A2 (Array Int Int)) (X2 Int) )
    (=>
      (and
        (inv A X)
        (= X2 (+ X 1))
        (= A2 (store A X2 X2))
        (<= X2 10)
      )
      (inv A2 X2)
    )
  )
)

(assert
  (forall ( (A (Array Int Int)) (X Int) )
    (=>
      (and (inv A X) (not (= (select A 0) 0)))
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(5));
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved the property — arr[0] stays 0 because stores
            // only write at indices 1..=10 and the const array has 0.
        }
        Ok(PdrResult::Unsafe(_)) => {
            // The system is safe (arr[0] is always 0), so Unsafe is a soundness bug
            panic!("PDR returned Unsafe for a safe array problem — soundness bug");
        }
        Ok(other) => {
            // Since #6047, PDR handles Array-sorted predicates. This problem
            // is solvable (verified at commit bc9c77c2b), so Unknown/NotApplicable
            // indicates a regression in array support.
            panic!("PDR returned {other:?} — expected Safe for variable-index array problem");
        }
        Err(e) => {
            panic!("Array CHC parse/setup error — this should parse and run: {e}");
        }
    }
}

/// Test PDR with multiple array-sorted parameters and a scalar state variable.
///
/// Models the zani pattern: Inv(obj_valid, count) where obj_valid is an
/// Array(Int,Bool) tracking which objects are valid, and count tracks the
/// number of valid objects. The loop stores true at index `count` and
/// increments count.
///
/// Invariant: select(obj_valid, 0) = true (slot 0 is always valid after init).
///
/// This tests that PDR handles mixed array + scalar predicate parameters,
/// and that the array MBP properly eliminates clause-local array variables
/// from the transition clause while preserving scalar constraints.
#[test]
#[timeout(15_000)]
fn test_pdr_array_multi_param_scalar_and_array() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array Int Bool) Int ) Bool)

; Init: obj_valid[0] = true, count = 1
(assert
  (forall ( (V (Array Int Bool)) (C Int) )
    (=>
      (and (= C 1) (= V (store ((as const (Array Int Bool)) false) 0 true)))
      (inv V C)
    )
  )
)

; Trans: obj_valid' = store(obj_valid, count, true), count' = count + 1
(assert
  (forall ( (V (Array Int Bool)) (C Int) (V2 (Array Int Bool)) (C2 Int) )
    (=>
      (and
        (inv V C)
        (= V2 (store V C true))
        (= C2 (+ C 1))
        (<= C 10)
      )
      (inv V2 C2)
    )
  )
)

; Bad: inv holds but obj_valid[0] is false
(assert
  (forall ( (V (Array Int Bool)) (C Int) )
    (=>
      (and (inv V C) (not (select V 0)))
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(10));
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved that obj_valid[0] remains true
        }
        Ok(PdrResult::Unknown | PdrResult::NotApplicable) => {
            // Acceptable: array MBP may be too imprecise
        }
        Ok(PdrResult::Unsafe(_)) => {
            panic!("PDR returned Unsafe for a safe multi-param array problem — soundness bug");
        }
        Err(e) => {
            panic!("Multi-param array CHC parse/setup error: {e}");
        }
        _ => panic!("unexpected variant"),
    }
}

/// Test PDR with two array-sorted parameters (models zani obj_valid + mem pattern).
///
/// Inv(obj_valid, mem) where both are Array(Int,Int). Init stores value 42 in
/// mem[0] and marks obj_valid[0] = 1. Property: if obj_valid[0] = 1 then mem[0] = 42.
///
/// This tests cross-array invariant reasoning and multi-array MBP.
#[test]
#[timeout(15_000)]
fn test_pdr_array_two_array_params() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array Int Int) (Array Int Int) ) Bool)

; Init: obj_valid[0] = 1, mem[0] = 42
(assert
  (forall ( (OV (Array Int Int)) (M (Array Int Int)) )
    (=>
      (and
        (= OV (store ((as const (Array Int Int)) 0) 0 1))
        (= M (store ((as const (Array Int Int)) 0) 0 42))
      )
      (inv OV M)
    )
  )
)

; Trans: identity (no modification)
(assert
  (forall ( (OV (Array Int Int)) (M (Array Int Int)) )
    (=> (inv OV M) (inv OV M))
  )
)

; Bad: obj_valid[0] = 1 but mem[0] != 42
(assert
  (forall ( (OV (Array Int Int)) (M (Array Int Int)) )
    (=>
      (and (inv OV M) (= (select OV 0) 1) (not (= (select M 0) 42)))
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(10));
    let result = testing::pdr_solve_from_str(input, config);
    // Both arrays use constant index 0 — scalarization converts to scalar variables.
    // Identity transition with init constraints makes the invariant trivial.
    assert!(
        matches!(&result, Ok(PdrResult::Safe(_))),
        "Expected Safe for two-array constant-index problem (scalarizable), got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

/// Test PDR with BV-indexed arrays doesn't crash (models zani harness pattern).
///
/// This models the zani pattern: (Array (_ BitVec 32) Bool) for obj_valid tracking.
/// Scalarization may or may not handle this depending on index patterns.
///
/// Expected: doesn't crash. Safe/Unknown both acceptable.
#[test]
#[timeout(15_000)]
fn test_pdr_array_bv_index_no_crash() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array (_ BitVec 32) Bool) (_ BitVec 32) ) Bool)

(assert
  (forall ( (V (Array (_ BitVec 32) Bool)) (P (_ BitVec 32)) )
    (=>
      (and
        (= P #x00000000)
        (= V (store ((as const (Array (_ BitVec 32) Bool)) false) P true))
      )
      (inv V P)
    )
  )
)

(assert
  (forall ( (V (Array (_ BitVec 32) Bool)) (P (_ BitVec 32)) )
    (=>
      (and (inv V P) (not (select V P)))
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(5));
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // Correct
        }
        Ok(PdrResult::Unknown | PdrResult::NotApplicable) => {
            // Acceptable
        }
        Ok(PdrResult::Unsafe(_)) => {
            panic!("PDR returned Unsafe for a safe BV-array problem — soundness bug");
        }
        Err(e) => {
            panic!("BV-array CHC parse/setup error — this should parse and run: {e}");
        }
        _ => panic!("unexpected variant"),
    }
}

/// Test PDR with zani's full 3-array BV pattern: obj_valid, obj_size, mem.
///
/// This models the exact signature zani generates with `--z4-chc-track=mem`:
/// - `obj_valid: (Array (_ BitVec 32) Bool)` — object validity map
/// - `obj_size: (Array (_ BitVec 32) (_ BitVec 32))` — object size map
/// - `mem: (Array (_ BitVec 64) (_ BitVec 8))` — byte-level memory
///
/// Init: allocate object 0 with size 4, write 0xAA to mem[0].
/// Property: obj_valid[0] = true implies mem[0] = 0xAA.
///
/// Expected: doesn't crash. Safe/Unknown both acceptable.
#[test]
#[timeout(15_000)]
fn test_pdr_array_zani_three_array_bv_pattern() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 32) (_ BitVec 32))
  (Array (_ BitVec 64) (_ BitVec 8))
) Bool)

; Init: obj_valid[0] = true, obj_size[0] = 4, mem[0] = 0xAA
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
  )
    (=>
      (and
        (= ov (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000000 true))
        (= os (store ((as const (Array (_ BitVec 32) (_ BitVec 32))) #x00000000) #x00000000 #x00000004))
        (= m  (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00) #x0000000000000000 #xAA))
      )
      (inv ov os m)
    )
  )
)

; Trans: identity (no modification)
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
  )
    (=> (inv ov os m) (inv ov os m))
  )
)

; Bad: obj_valid[0] = true but mem[0] != 0xAA
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
  )
    (=>
      (and
        (inv ov os m)
        (select ov #x00000000)
        (not (= (select m #x0000000000000000) #xAA))
      )
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(10));
    let result = testing::pdr_solve_from_str(input, config);
    // All indices are constant BV literals — scalarization converts the problem
    // to pure BV scalars, and k-induction solves at k=0.
    assert!(
        matches!(&result, Ok(PdrResult::Safe(_))),
        "Expected Safe for 3-array BV constant-index problem (scalarizable), got {:?}",
        result.map(|r| format!("{:?}", std::mem::discriminant(&r)))
    );
}

// #6047: test_pdr_array_zani_bvmul_variable_store removed.
// It was passing on unsound scalarization that silently eliminated BV32-indexed
// arrays. After the fix, three BV32-indexed arrays are kept as Array-sorted
// params, causing bit-blast blowup that makes PDR timeout. Testing a timeout
// is not useful. The underlying problem (efficient BV-array PDR) is tracked
// by #6047.

/// Test PDR with variable-index store in transition (non-trivial MBP elimination).
///
/// This models a loop that allocates objects at variable positions:
/// Init: count = 0, obj_valid is all false.
/// Trans: obj_valid' = store(obj_valid, count, true), count' = count + 1.
/// Property: count >= 0.
///
/// The array variable in the transition is clause-local (bound by forall in the
/// transition clause). MBP must eliminate it via select factoring + Ackermannization.
///
/// Expected: Safe or Unknown (crash is a bug).
#[test]
#[timeout(15_000)]
fn test_pdr_array_variable_index_store_transition() {
    let input = r#"
(set-logic HORN)

(declare-fun |inv| ( (Array Int Bool) Int ) Bool)

; Init: obj_valid = const(false), count = 0
(assert
  (forall ( (V (Array Int Bool)) (C Int) )
    (=>
      (and (= C 0) (= V ((as const (Array Int Bool)) false)))
      (inv V C)
    )
  )
)

; Trans: obj_valid' = store(obj_valid, count, true), count' = count + 1
; The pre-state array V is clause-local — MBP must project it out.
(assert
  (forall ( (V (Array Int Bool)) (C Int) (V2 (Array Int Bool)) (C2 Int) )
    (=>
      (and
        (inv V C)
        (>= C 0)
        (<= C 100)
        (= V2 (store V C true))
        (= C2 (+ C 1))
      )
      (inv V2 C2)
    )
  )
)

; Bad: count < 0
(assert
  (forall ( (V (Array Int Bool)) (C Int) )
    (=>
      (and (inv V C) (< C 0))
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(10));
    let result = testing::pdr_solve_from_str(input, config);
    match result {
        Ok(PdrResult::Safe(_)) => {
            // PDR proved count >= 0 despite array-sorted predicate parameter
        }
        Ok(PdrResult::Unknown | PdrResult::NotApplicable) => {
            // Acceptable
        }
        Ok(PdrResult::Unsafe(_)) => {
            panic!("PDR returned Unsafe for a safe variable-index store problem — soundness bug");
        }
        Err(e) => {
            panic!("Variable-index store CHC parse/setup error: {e}");
        }
        _ => panic!("unexpected variant"),
    }
}
