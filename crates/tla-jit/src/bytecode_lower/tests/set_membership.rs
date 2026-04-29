// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for set membership JIT lowering (SetEnum + SetIn).

use crate::abi::{JitCallOut, JitStatus};
use crate::bytecode_lower::BytecodeLowerer;
use tla_tir::bytecode::{BytecodeFunction, Opcode};

use super::compile_and_run_no_state;

/// Helper: compile and run a set membership test, returning the JitCallOut.
fn compile_and_run_with_state(func: &BytecodeFunction, state: &[i64]) -> JitCallOut {
    super::compile_and_run(func, state)
}

/// x \in {1, 2, 3} where x = 2 => TRUE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_in_member_found() {
    let mut func = BytecodeFunction::new("test_set_in".to_string(), 0);
    // r0 = 2 (the element to test)
    func.emit(Opcode::LoadImm { rd: 0, value: 2 });
    // r1 = 1, r2 = 2, r3 = 3 (set elements)
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 2 });
    func.emit(Opcode::LoadImm { rd: 3, value: 3 });
    // r4 = {r1, r2, r3} = {1, 2, 3}
    func.emit(Opcode::SetEnum {
        rd: 4,
        start: 1,
        count: 3,
    });
    // r5 = (r0 \in r4)
    func.emit(Opcode::SetIn {
        rd: 5,
        elem: 0,
        set: 4,
    });
    func.emit(Opcode::Ret { rs: 5 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "2 should be in {{1, 2, 3}}");
}

/// x \in {1, 2, 3} where x = 5 => FALSE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_in_member_not_found() {
    let mut func = BytecodeFunction::new("test_set_in".to_string(), 0);
    // r0 = 5 (the element to test)
    func.emit(Opcode::LoadImm { rd: 0, value: 5 });
    // r1 = 1, r2 = 2, r3 = 3
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 2 });
    func.emit(Opcode::LoadImm { rd: 3, value: 3 });
    // r4 = {1, 2, 3}
    func.emit(Opcode::SetEnum {
        rd: 4,
        start: 1,
        count: 3,
    });
    // r5 = (r0 \in r4)
    func.emit(Opcode::SetIn {
        rd: 5,
        elem: 0,
        set: 4,
    });
    func.emit(Opcode::Ret { rs: 5 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "5 should not be in {{1, 2, 3}}");
}

/// x \in {} => FALSE (empty set)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_in_empty_set() {
    let mut func = BytecodeFunction::new("test_set_in_empty".to_string(), 0);
    // r0 = 42
    func.emit(Opcode::LoadImm { rd: 0, value: 42 });
    // r1 = {} (empty set)
    func.emit(Opcode::SetEnum {
        rd: 1,
        start: 2,
        count: 0,
    });
    // r2 = (r0 \in r1)
    func.emit(Opcode::SetIn {
        rd: 2,
        elem: 0,
        set: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "nothing is in the empty set");
}

/// x \in {x} => TRUE (singleton set, same value)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_in_singleton() {
    let mut func = BytecodeFunction::new("test_singleton".to_string(), 0);
    // r0 = 7
    func.emit(Opcode::LoadImm { rd: 0, value: 7 });
    // r1 = 7
    func.emit(Opcode::LoadImm { rd: 1, value: 7 });
    // r2 = {r1} = {7}
    func.emit(Opcode::SetEnum {
        rd: 2,
        start: 1,
        count: 1,
    });
    // r3 = (r0 \in r2)
    func.emit(Opcode::SetIn {
        rd: 3,
        elem: 0,
        set: 2,
    });
    func.emit(Opcode::Ret { rs: 3 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "7 should be in {{7}}");
}

/// State variable membership: state[0] \in {10, 20, 30}
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_in_with_state_var_member() {
    let mut func = BytecodeFunction::new("test_state_set".to_string(), 0);
    // r0 = state[0]
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    // r1 = 10, r2 = 20, r3 = 30
    func.emit(Opcode::LoadImm { rd: 1, value: 10 });
    func.emit(Opcode::LoadImm { rd: 2, value: 20 });
    func.emit(Opcode::LoadImm { rd: 3, value: 30 });
    // r4 = {10, 20, 30}
    func.emit(Opcode::SetEnum {
        rd: 4,
        start: 1,
        count: 3,
    });
    // r5 = (state[0] \in {10, 20, 30})
    func.emit(Opcode::SetIn {
        rd: 5,
        elem: 0,
        set: 4,
    });
    func.emit(Opcode::Ret { rs: 5 });

    // state[0] = 20 (member)
    let out = compile_and_run_with_state(&func, &[20]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "20 should be in {{10, 20, 30}}");
}

/// State variable membership: state[0] \in {10, 20, 30} where state[0] = 15
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_in_with_state_var_nonmember() {
    let mut func = BytecodeFunction::new("test_state_set".to_string(), 0);
    // r0 = state[0]
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    // r1 = 10, r2 = 20, r3 = 30
    func.emit(Opcode::LoadImm { rd: 1, value: 10 });
    func.emit(Opcode::LoadImm { rd: 2, value: 20 });
    func.emit(Opcode::LoadImm { rd: 3, value: 30 });
    // r4 = {10, 20, 30}
    func.emit(Opcode::SetEnum {
        rd: 4,
        start: 1,
        count: 3,
    });
    // r5 = (state[0] \in {10, 20, 30})
    func.emit(Opcode::SetIn {
        rd: 5,
        elem: 0,
        set: 4,
    });
    func.emit(Opcode::Ret { rs: 5 });

    // state[0] = 15 (not a member)
    let out = compile_and_run_with_state(&func, &[15]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "15 should not be in {{10, 20, 30}}");
}

/// Negative numbers: -3 \in {-5, -3, 0, 3, 5}
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_in_negative_numbers() {
    let mut func = BytecodeFunction::new("test_neg".to_string(), 0);
    // r0 = -3
    func.emit(Opcode::LoadImm { rd: 0, value: -3 });
    // r1..-r5 = set elements
    func.emit(Opcode::LoadImm { rd: 1, value: -5 });
    func.emit(Opcode::LoadImm { rd: 2, value: -3 });
    func.emit(Opcode::LoadImm { rd: 3, value: 0 });
    func.emit(Opcode::LoadImm { rd: 4, value: 3 });
    func.emit(Opcode::LoadImm { rd: 5, value: 5 });
    // r6 = {-5, -3, 0, 3, 5}
    func.emit(Opcode::SetEnum {
        rd: 6,
        start: 1,
        count: 5,
    });
    // r7 = (-3 \in {-5, -3, 0, 3, 5})
    func.emit(Opcode::SetIn {
        rd: 7,
        elem: 0,
        set: 6,
    });
    func.emit(Opcode::Ret { rs: 7 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "-3 should be in {{-5, -3, 0, 3, 5}}");
}

/// Combined with boolean logic: (x \in S) /\ (x > 0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_in_combined_with_comparison() {
    let mut func = BytecodeFunction::new("test_combined".to_string(), 0);
    // r0 = 3
    func.emit(Opcode::LoadImm { rd: 0, value: 3 });
    // r1 = 1, r2 = 3, r3 = 5
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 3 });
    func.emit(Opcode::LoadImm { rd: 3, value: 5 });
    // r4 = {1, 3, 5}
    func.emit(Opcode::SetEnum {
        rd: 4,
        start: 1,
        count: 3,
    });
    // r5 = (3 \in {1, 3, 5})
    func.emit(Opcode::SetIn {
        rd: 5,
        elem: 0,
        set: 4,
    });
    // r6 = 0
    func.emit(Opcode::LoadImm { rd: 6, value: 0 });
    // r7 = (r0 > r6) = (3 > 0) = TRUE
    func.emit(Opcode::GtInt {
        rd: 7,
        r1: 0,
        r2: 6,
    });
    // r8 = r5 /\ r7
    func.emit(Opcode::And {
        rd: 8,
        r1: 5,
        r2: 7,
    });
    func.emit(Opcode::Ret { rs: 8 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(
        out.value, 1,
        "(3 \\in {{1,3,5}}) /\\ (3 > 0) should be TRUE"
    );
}

/// Eligibility: SetEnum + SetIn should pass eligibility check
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_ops_eligibility() {
    let mut func = BytecodeFunction::new("test_elig".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    func.emit(Opcode::SetEnum {
        rd: 2,
        start: 0,
        count: 2,
    });
    func.emit(Opcode::SetIn {
        rd: 3,
        elem: 0,
        set: 2,
    });
    func.emit(Opcode::Ret { rs: 3 });

    let lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    assert!(
        lowerer.is_eligible(&func),
        "SetEnum + SetIn should be JIT-eligible"
    );
}

/// SetUnion is JIT-eligible with FallbackNeeded at runtime.
/// Part of #3909 Phase 2: compound-producing opcodes emit fallback.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_union_eligible_with_fallback() {
    let mut func = BytecodeFunction::new("test_set_union".to_string(), 2);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    func.emit(Opcode::SetUnion {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    assert!(
        lowerer.is_eligible(&func),
        "SetUnion should be JIT-eligible (emits FallbackNeeded at runtime)"
    );

    // When compiled and run, should produce FallbackNeeded
    let out = compile_and_run_no_state(&func);
    assert!(
        out.needs_fallback(),
        "SetUnion should produce FallbackNeeded at runtime"
    );
}

/// First element match: x \in {x, y, z} where x matches first element
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_in_first_element_match() {
    let mut func = BytecodeFunction::new("test_first".to_string(), 0);
    // r0 = 100 (element to test)
    func.emit(Opcode::LoadImm { rd: 0, value: 100 });
    // r1 = 100, r2 = 200, r3 = 300
    func.emit(Opcode::LoadImm { rd: 1, value: 100 });
    func.emit(Opcode::LoadImm { rd: 2, value: 200 });
    func.emit(Opcode::LoadImm { rd: 3, value: 300 });
    // r4 = {100, 200, 300}
    func.emit(Opcode::SetEnum {
        rd: 4,
        start: 1,
        count: 3,
    });
    // r5 = (100 \in {100, 200, 300})
    func.emit(Opcode::SetIn {
        rd: 5,
        elem: 0,
        set: 4,
    });
    func.emit(Opcode::Ret { rs: 5 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1);
}

/// Last element match: x \in {a, b, x} where x matches last element
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_in_last_element_match() {
    let mut func = BytecodeFunction::new("test_last".to_string(), 0);
    // r0 = 300
    func.emit(Opcode::LoadImm { rd: 0, value: 300 });
    // r1 = 100, r2 = 200, r3 = 300
    func.emit(Opcode::LoadImm { rd: 1, value: 100 });
    func.emit(Opcode::LoadImm { rd: 2, value: 200 });
    func.emit(Opcode::LoadImm { rd: 3, value: 300 });
    // r4 = {100, 200, 300}
    func.emit(Opcode::SetEnum {
        rd: 4,
        start: 1,
        count: 3,
    });
    // r5 = (300 \in {100, 200, 300})
    func.emit(Opcode::SetIn {
        rd: 5,
        elem: 0,
        set: 4,
    });
    func.emit(Opcode::Ret { rs: 5 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1);
}

// =====================================================================
// Range set tests
// =====================================================================

/// 5 \in 1..10 => TRUE (in range)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_set_in_member() {
    let mut func = BytecodeFunction::new("test_range_in".to_string(), 0);
    // r0 = 5 (element to test)
    func.emit(Opcode::LoadImm { rd: 0, value: 5 });
    // r1 = 1 (lo), r2 = 10 (hi)
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 10 });
    // r3 = 1..10
    func.emit(Opcode::Range {
        rd: 3,
        lo: 1,
        hi: 2,
    });
    // r4 = (5 \in 1..10)
    func.emit(Opcode::SetIn {
        rd: 4,
        elem: 0,
        set: 3,
    });
    func.emit(Opcode::Ret { rs: 4 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "5 should be in 1..10");
}

/// 0 \in 1..10 => FALSE (below range)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_set_in_below() {
    let mut func = BytecodeFunction::new("test_range_below".to_string(), 0);
    // r0 = 0
    func.emit(Opcode::LoadImm { rd: 0, value: 0 });
    // r1 = 1, r2 = 10
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 10 });
    func.emit(Opcode::Range {
        rd: 3,
        lo: 1,
        hi: 2,
    });
    func.emit(Opcode::SetIn {
        rd: 4,
        elem: 0,
        set: 3,
    });
    func.emit(Opcode::Ret { rs: 4 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "0 should not be in 1..10");
}

/// 11 \in 1..10 => FALSE (above range)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_set_in_above() {
    let mut func = BytecodeFunction::new("test_range_above".to_string(), 0);
    // r0 = 11
    func.emit(Opcode::LoadImm { rd: 0, value: 11 });
    // r1 = 1, r2 = 10
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 10 });
    func.emit(Opcode::Range {
        rd: 3,
        lo: 1,
        hi: 2,
    });
    func.emit(Opcode::SetIn {
        rd: 4,
        elem: 0,
        set: 3,
    });
    func.emit(Opcode::Ret { rs: 4 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "11 should not be in 1..10");
}

/// Boundary: 1 \in 1..10 => TRUE (lo endpoint inclusive)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_set_in_lo_boundary() {
    let mut func = BytecodeFunction::new("test_range_lo".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 10 });
    func.emit(Opcode::Range {
        rd: 3,
        lo: 1,
        hi: 2,
    });
    func.emit(Opcode::SetIn {
        rd: 4,
        elem: 0,
        set: 3,
    });
    func.emit(Opcode::Ret { rs: 4 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "1 should be in 1..10 (lo boundary)");
}

/// Boundary: 10 \in 1..10 => TRUE (hi endpoint inclusive)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_set_in_hi_boundary() {
    let mut func = BytecodeFunction::new("test_range_hi".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 10 });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 10 });
    func.emit(Opcode::Range {
        rd: 3,
        lo: 1,
        hi: 2,
    });
    func.emit(Opcode::SetIn {
        rd: 4,
        elem: 0,
        set: 3,
    });
    func.emit(Opcode::Ret { rs: 4 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "10 should be in 1..10 (hi boundary)");
}

/// Negative range: -3 \in -5..5 => TRUE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_set_in_negative() {
    let mut func = BytecodeFunction::new("test_range_neg".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: -3 });
    func.emit(Opcode::LoadImm { rd: 1, value: -5 });
    func.emit(Opcode::LoadImm { rd: 2, value: 5 });
    func.emit(Opcode::Range {
        rd: 3,
        lo: 1,
        hi: 2,
    });
    func.emit(Opcode::SetIn {
        rd: 4,
        elem: 0,
        set: 3,
    });
    func.emit(Opcode::Ret { rs: 4 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "-3 should be in -5..5");
}

/// Range with state variable: state[0] \in 1..100
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_set_in_with_state_var() {
    let mut func = BytecodeFunction::new("test_range_state".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 100 });
    func.emit(Opcode::Range {
        rd: 3,
        lo: 1,
        hi: 2,
    });
    func.emit(Opcode::SetIn {
        rd: 4,
        elem: 0,
        set: 3,
    });
    func.emit(Opcode::Ret { rs: 4 });

    // state[0] = 50 (in range)
    let out = compile_and_run_with_state(&func, &[50]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "50 should be in 1..100");

    // state[0] = 0 (below range)
    let out = compile_and_run_with_state(&func, &[0]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "0 should not be in 1..100");

    // state[0] = 101 (above range)
    let out = compile_and_run_with_state(&func, &[101]);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "101 should not be in 1..100");
}

// =====================================================================
// Subseteq tests
// =====================================================================

/// {1, 2} \subseteq {1, 2, 3} => TRUE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseteq_true() {
    let mut func = BytecodeFunction::new("test_subseteq".to_string(), 0);
    // LHS elements: r0 = 1, r1 = 2
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    // r2 = {1, 2}
    func.emit(Opcode::SetEnum {
        rd: 2,
        start: 0,
        count: 2,
    });
    // RHS elements: r3 = 1, r4 = 2, r5 = 3
    func.emit(Opcode::LoadImm { rd: 3, value: 1 });
    func.emit(Opcode::LoadImm { rd: 4, value: 2 });
    func.emit(Opcode::LoadImm { rd: 5, value: 3 });
    // r6 = {1, 2, 3}
    func.emit(Opcode::SetEnum {
        rd: 6,
        start: 3,
        count: 3,
    });
    // r7 = ({1, 2} \subseteq {1, 2, 3})
    func.emit(Opcode::Subseteq {
        rd: 7,
        r1: 2,
        r2: 6,
    });
    func.emit(Opcode::Ret { rs: 7 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "{{1,2}} should be a subset of {{1,2,3}}");
}

/// {1, 4} \subseteq {1, 2, 3} => FALSE
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseteq_false() {
    let mut func = BytecodeFunction::new("test_subseteq_f".to_string(), 0);
    // LHS: r0 = 1, r1 = 4
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 4 });
    func.emit(Opcode::SetEnum {
        rd: 2,
        start: 0,
        count: 2,
    });
    // RHS: r3 = 1, r4 = 2, r5 = 3
    func.emit(Opcode::LoadImm { rd: 3, value: 1 });
    func.emit(Opcode::LoadImm { rd: 4, value: 2 });
    func.emit(Opcode::LoadImm { rd: 5, value: 3 });
    func.emit(Opcode::SetEnum {
        rd: 6,
        start: 3,
        count: 3,
    });
    func.emit(Opcode::Subseteq {
        rd: 7,
        r1: 2,
        r2: 6,
    });
    func.emit(Opcode::Ret { rs: 7 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "{{1,4}} should not be a subset of {{1,2,3}}");
}

/// {} \subseteq {1, 2, 3} => TRUE (empty set is subset of everything)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseteq_empty_lhs() {
    let mut func = BytecodeFunction::new("test_subseteq_empty".to_string(), 0);
    // LHS: empty set
    func.emit(Opcode::SetEnum {
        rd: 0,
        start: 1,
        count: 0,
    });
    // RHS: r1 = 1, r2 = 2
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 2 });
    func.emit(Opcode::SetEnum {
        rd: 3,
        start: 1,
        count: 2,
    });
    func.emit(Opcode::Subseteq {
        rd: 4,
        r1: 0,
        r2: 3,
    });
    func.emit(Opcode::Ret { rs: 4 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "empty set should be subset of any set");
}

/// {2, 5} \subseteq 1..10 => TRUE (enum subset of range)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseteq_enum_subset_of_range() {
    let mut func = BytecodeFunction::new("test_subseteq_range".to_string(), 0);
    // LHS: r0 = 2, r1 = 5
    func.emit(Opcode::LoadImm { rd: 0, value: 2 });
    func.emit(Opcode::LoadImm { rd: 1, value: 5 });
    func.emit(Opcode::SetEnum {
        rd: 2,
        start: 0,
        count: 2,
    });
    // RHS: range 1..10
    func.emit(Opcode::LoadImm { rd: 3, value: 1 });
    func.emit(Opcode::LoadImm { rd: 4, value: 10 });
    func.emit(Opcode::Range {
        rd: 5,
        lo: 3,
        hi: 4,
    });
    // r6 = ({2, 5} \subseteq 1..10)
    func.emit(Opcode::Subseteq {
        rd: 6,
        r1: 2,
        r2: 5,
    });
    func.emit(Opcode::Ret { rs: 6 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1, "{{2,5}} should be subset of 1..10");
}

/// {2, 15} \subseteq 1..10 => FALSE (one element out of range)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseteq_enum_not_subset_of_range() {
    let mut func = BytecodeFunction::new("test_subseteq_range_f".to_string(), 0);
    // LHS: r0 = 2, r1 = 15
    func.emit(Opcode::LoadImm { rd: 0, value: 2 });
    func.emit(Opcode::LoadImm { rd: 1, value: 15 });
    func.emit(Opcode::SetEnum {
        rd: 2,
        start: 0,
        count: 2,
    });
    // RHS: range 1..10
    func.emit(Opcode::LoadImm { rd: 3, value: 1 });
    func.emit(Opcode::LoadImm { rd: 4, value: 10 });
    func.emit(Opcode::Range {
        rd: 5,
        lo: 3,
        hi: 4,
    });
    func.emit(Opcode::Subseteq {
        rd: 6,
        r1: 2,
        r2: 5,
    });
    func.emit(Opcode::Ret { rs: 6 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 0, "{{2,15}} should not be subset of 1..10");
}

// =====================================================================
// Eligibility tests for new opcodes
// =====================================================================

/// Range opcode should be JIT-eligible
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_eligibility() {
    let mut func = BytecodeFunction::new("test_range_elig".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 10 });
    func.emit(Opcode::Range {
        rd: 2,
        lo: 0,
        hi: 1,
    });
    func.emit(Opcode::LoadImm { rd: 3, value: 5 });
    func.emit(Opcode::SetIn {
        rd: 4,
        elem: 3,
        set: 2,
    });
    func.emit(Opcode::Ret { rs: 4 });

    let lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    assert!(
        lowerer.is_eligible(&func),
        "Range + SetIn should be JIT-eligible"
    );
}

/// Subseteq opcode should be JIT-eligible
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseteq_eligibility() {
    let mut func = BytecodeFunction::new("test_subseteq_elig".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::SetEnum {
        rd: 1,
        start: 0,
        count: 1,
    });
    func.emit(Opcode::LoadImm { rd: 2, value: 1 });
    func.emit(Opcode::LoadImm { rd: 3, value: 2 });
    func.emit(Opcode::SetEnum {
        rd: 4,
        start: 2,
        count: 2,
    });
    func.emit(Opcode::Subseteq {
        rd: 5,
        r1: 1,
        r2: 4,
    });
    func.emit(Opcode::Ret { rs: 5 });

    let lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    assert!(
        lowerer.is_eligible(&func),
        "Subseteq should be JIT-eligible"
    );
}

/// SetEnum with > MAX_SET_ENUM_SIZE elements should be ineligible
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_enum_too_large_ineligible() {
    use crate::bytecode_lower::set_ops::MAX_SET_ENUM_SIZE;

    let mut func = BytecodeFunction::new("test_large_set".to_string(), 0);
    // Load enough elements to exceed the limit
    for i in 0..=(MAX_SET_ENUM_SIZE as u8) {
        func.emit(Opcode::LoadImm {
            rd: i,
            value: i as i64,
        });
    }
    func.emit(Opcode::SetEnum {
        rd: MAX_SET_ENUM_SIZE + 1,
        start: 0,
        count: MAX_SET_ENUM_SIZE + 1,
    });
    func.emit(Opcode::Ret {
        rs: MAX_SET_ENUM_SIZE + 1,
    });

    let lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    assert!(
        !lowerer.is_eligible(&func),
        "SetEnum with {} elements should be ineligible (max {})",
        MAX_SET_ENUM_SIZE + 1,
        MAX_SET_ENUM_SIZE,
    );
}

/// SetEnum at exactly MAX_SET_ENUM_SIZE should be eligible
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_enum_at_limit_eligible() {
    use crate::bytecode_lower::set_ops::MAX_SET_ENUM_SIZE;

    let mut func = BytecodeFunction::new("test_max_set".to_string(), 0);
    for i in 0..MAX_SET_ENUM_SIZE {
        func.emit(Opcode::LoadImm {
            rd: i,
            value: i as i64,
        });
    }
    func.emit(Opcode::SetEnum {
        rd: MAX_SET_ENUM_SIZE,
        start: 0,
        count: MAX_SET_ENUM_SIZE,
    });
    func.emit(Opcode::Ret {
        rs: MAX_SET_ENUM_SIZE,
    });

    let lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    assert!(
        lowerer.is_eligible(&func),
        "SetEnum with exactly {} elements should be eligible",
        MAX_SET_ENUM_SIZE,
    );
}

// =====================================================================
// Compound set membership tests (jit_set_contains_i64 runtime helper)
// Part of #3909 Phase 2.
// =====================================================================

/// Helper: compile with state layout and run.
fn compile_and_run_with_layout(
    func: &BytecodeFunction,
    state: &[i64],
    state_layout: &crate::compound_layout::StateLayout,
    field_name_ids: &[u32],
) -> crate::abi::JitCallOut {
    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let empty_domains = crate::bytecode_lower::QuantifierDomains::new();
    let jit_fn = lowerer
        .compile_invariant_with_layout(func, &empty_domains, state_layout, field_name_ids)
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = crate::abi::JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }
    out
}

/// x \in S where S is a compound set from the state buffer and x IS a member.
///
/// State layout: one Set variable {10, 20, 30}
/// Serialized: [TAG_SET=3, 3, TAG_INT=5, 10, TAG_INT=5, 20, TAG_INT=5, 30]
///
/// Bytecode: LoadVar r0 (the set), LoadImm r1 = 20, SetIn r2 = (r1 \in r0), Ret r2
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_set_membership_found() {
    use crate::compound_layout::*;

    let state = vec![TAG_SET, 3, TAG_INT, 10, TAG_INT, 20, TAG_INT, 30];

    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Set {
        element_layout: Box::new(CompoundLayout::Int),
        element_count: None,
    })]);

    let mut func = BytecodeFunction::new("test_compound_set_in".to_string(), 2);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 }); // r0 = the set
    func.emit(Opcode::LoadImm { rd: 1, value: 20 }); // r1 = 20
    func.emit(Opcode::SetIn {
        rd: 2,
        elem: 1,
        set: 0,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_with_layout(&func, &state, &layout, &[]);
    assert!(
        out.is_ok(),
        "compound set SetIn should produce Ok, got: {:?}",
        out.status
    );
    assert_eq!(out.value, 1, "20 should be in {{10, 20, 30}}");
}

/// x \in S where S is a compound set from the state buffer and x is NOT a member.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_set_membership_not_found() {
    use crate::compound_layout::*;

    let state = vec![TAG_SET, 3, TAG_INT, 10, TAG_INT, 20, TAG_INT, 30];

    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Set {
        element_layout: Box::new(CompoundLayout::Int),
        element_count: None,
    })]);

    let mut func = BytecodeFunction::new("test_compound_set_not_in".to_string(), 2);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadImm { rd: 1, value: 99 });
    func.emit(Opcode::SetIn {
        rd: 2,
        elem: 1,
        set: 0,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_with_layout(&func, &state, &layout, &[]);
    assert!(
        out.is_ok(),
        "compound set SetIn should produce Ok, got: {:?}",
        out.status
    );
    assert_eq!(out.value, 0, "99 should not be in {{10, 20, 30}}");
}

/// x \in S where S is a compound set with a single element.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_set_membership_singleton() {
    use crate::compound_layout::*;

    let state = vec![TAG_SET, 1, TAG_INT, 42];

    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Set {
        element_layout: Box::new(CompoundLayout::Int),
        element_count: None,
    })]);

    let mut func = BytecodeFunction::new("test_singleton_set".to_string(), 2);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadImm { rd: 1, value: 42 });
    func.emit(Opcode::SetIn {
        rd: 2,
        elem: 1,
        set: 0,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_with_layout(&func, &state, &layout, &[]);
    assert!(
        out.is_ok(),
        "singleton set SetIn should produce Ok, got: {:?}",
        out.status
    );
    assert_eq!(out.value, 1, "42 should be in {{42}}");
}

/// x \in S where S is a compound empty set.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_set_membership_empty() {
    use crate::compound_layout::*;

    let state = vec![
        TAG_SET, 0, // empty set
    ];

    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Set {
        element_layout: Box::new(CompoundLayout::Int),
        element_count: None,
    })]);

    let mut func = BytecodeFunction::new("test_empty_compound_set".to_string(), 2);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::SetIn {
        rd: 2,
        elem: 1,
        set: 0,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_with_layout(&func, &state, &layout, &[]);
    assert!(
        out.is_ok(),
        "empty compound set SetIn should produce Ok, got: {:?}",
        out.status
    );
    assert_eq!(out.value, 0, "nothing is in the empty set");
}

/// Compound set membership with state variable as element.
/// state[0] = set {1, 2, 3}, state[1] = 2.  Tests: state[1] \in state[0].
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_set_membership_state_elem() {
    use crate::compound_layout::*;

    // state[0] = set {1, 2, 3}, state[1] = scalar 2
    // Set takes slots 0-7, scalar at slot 8.
    let state = vec![
        TAG_SET, 3, TAG_INT, 1, TAG_INT, 2, TAG_INT, 3,
        2, // state[1] = 2 (scalar at slot index 8)
    ];

    let layout = StateLayout::new(vec![
        VarLayout::Compound(CompoundLayout::Set {
            element_layout: Box::new(CompoundLayout::Int),
            element_count: None,
        }),
        VarLayout::ScalarInt,
    ]);

    let mut func = BytecodeFunction::new("test_state_elem_in_set".to_string(), 2);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 }); // r0 = the set
    func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 }); // r1 = state[1] = 2
    func.emit(Opcode::SetIn {
        rd: 2,
        elem: 1,
        set: 0,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_with_layout(&func, &state, &layout, &[]);
    assert!(
        out.is_ok(),
        "state elem compound set SetIn should produce Ok, got: {:?}",
        out.status
    );
    assert_eq!(out.value, 1, "state[1]=2 should be in state[0]={{1,2,3}}");
}

// =====================================================================
// FuncSet membership peephole optimization tests
// `x \in [A -> B]` without constructing the full function set.
// =====================================================================

/// f \in [Nodes -> BOOLEAN] where f = [1 |-> TRUE, 2 |-> FALSE].
/// Nodes = {1, 2}, BOOLEAN = {0, 1} (FALSE, TRUE).
/// Should return TRUE.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_set_membership_bool_range_true() {
    use crate::compound_layout::*;

    // State: f = [1 |-> TRUE, 2 |-> FALSE]
    // Serialized: [TAG_FUNC=4, 2, TAG_INT=5, 1, TAG_BOOL=6, 1, TAG_INT=5, 2, TAG_BOOL=6, 0]
    let state = vec![
        TAG_FUNC, 2, TAG_INT, 1, TAG_BOOL, 1, TAG_INT, 2, TAG_BOOL, 0,
    ];

    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
        key_layout: Box::new(CompoundLayout::Int),
        value_layout: Box::new(CompoundLayout::Bool),
        pair_count: None,
        domain_lo: None,
    })]);

    // Bytecode:
    //   r0 = LoadVar 0 (the function)
    //   r1 = 1, r2 = 2 (domain elements = Nodes)
    //   r3 = SetEnum {r1, r2}  (domain set)
    //   r4 = 0, r5 = 1 (range elements = BOOLEAN)
    //   r6 = SetEnum {r4, r5}  (range set)
    //   r7 = FuncSet {domain=r3, range=r6}  ([Nodes -> BOOLEAN])
    //   r8 = SetIn {elem=r0, set=r7}  (f \in [Nodes -> BOOLEAN])
    //   Ret r8
    let mut func = BytecodeFunction::new("test_func_set_bool".to_string(), 8);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 2 });
    func.emit(Opcode::SetEnum {
        rd: 3,
        start: 1,
        count: 2,
    });
    func.emit(Opcode::LoadImm { rd: 4, value: 0 }); // FALSE
    func.emit(Opcode::LoadImm { rd: 5, value: 1 }); // TRUE
    func.emit(Opcode::SetEnum {
        rd: 6,
        start: 4,
        count: 2,
    });
    func.emit(Opcode::FuncSet {
        rd: 7,
        domain: 3,
        range: 6,
    });
    func.emit(Opcode::SetIn {
        rd: 8,
        elem: 0,
        set: 7,
    });
    func.emit(Opcode::Ret { rs: 8 });

    let out = compile_and_run_with_layout(&func, &state, &layout, &[]);
    assert!(
        out.is_ok(),
        "FuncSet membership should produce Ok, got: {:?}",
        out.status
    );
    assert_eq!(
        out.value, 1,
        "[1 |-> TRUE, 2 |-> FALSE] should be in [{{1,2}} -> BOOLEAN]"
    );
}

/// f \in [Nodes -> BOOLEAN] where f has wrong domain size.
/// f = [1 |-> TRUE] but Nodes = {1, 2}.
/// Should return FALSE (pair count 1 != domain count 2).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_set_membership_wrong_domain_size() {
    use crate::compound_layout::*;

    // State: f = [1 |-> TRUE]
    let state = vec![TAG_FUNC, 1, TAG_INT, 1, TAG_BOOL, 1];

    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
        key_layout: Box::new(CompoundLayout::Int),
        value_layout: Box::new(CompoundLayout::Bool),
        pair_count: None,
        domain_lo: None,
    })]);

    let mut func = BytecodeFunction::new("test_wrong_domain".to_string(), 8);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 2 });
    func.emit(Opcode::SetEnum {
        rd: 3,
        start: 1,
        count: 2,
    });
    func.emit(Opcode::LoadImm { rd: 4, value: 0 });
    func.emit(Opcode::LoadImm { rd: 5, value: 1 });
    func.emit(Opcode::SetEnum {
        rd: 6,
        start: 4,
        count: 2,
    });
    func.emit(Opcode::FuncSet {
        rd: 7,
        domain: 3,
        range: 6,
    });
    func.emit(Opcode::SetIn {
        rd: 8,
        elem: 0,
        set: 7,
    });
    func.emit(Opcode::Ret { rs: 8 });

    let out = compile_and_run_with_layout(&func, &state, &layout, &[]);
    assert!(
        out.is_ok(),
        "FuncSet membership should produce Ok, got: {:?}",
        out.status
    );
    assert_eq!(
        out.value, 0,
        "[1 |-> TRUE] should NOT be in [{{1,2}} -> BOOLEAN] (wrong domain size)"
    );
}

/// f \in [Nodes -> BOOLEAN] where a value is not BOOLEAN.
/// f = [1 |-> 42, 2 |-> TRUE] — value 42 not in {0, 1}.
/// Should return FALSE.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_set_membership_value_out_of_range() {
    use crate::compound_layout::*;

    // State: f = [1 |-> 42, 2 |-> TRUE]
    // Serialized as int values (using TAG_INT for 42, TAG_BOOL for TRUE)
    // But runtime helper checks the VALUE slot (offset+3), so we need
    // consistent tag+value pairs.
    // Actually the helper reads offset+3 which is the value slot.
    // For [1 |-> 42, 2 |-> 1]:
    // [TAG_FUNC, 2, TAG_INT, 1, TAG_INT, 42, TAG_INT, 2, TAG_BOOL, 1]
    let state = vec![
        TAG_FUNC, 2, TAG_INT, 1, TAG_INT, 42, TAG_INT, 2, TAG_BOOL, 1,
    ];

    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
        key_layout: Box::new(CompoundLayout::Int),
        value_layout: Box::new(CompoundLayout::Int),
        pair_count: None,
        domain_lo: None,
    })]);

    let mut func = BytecodeFunction::new("test_val_oob".to_string(), 8);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 2 });
    func.emit(Opcode::SetEnum {
        rd: 3,
        start: 1,
        count: 2,
    });
    func.emit(Opcode::LoadImm { rd: 4, value: 0 }); // FALSE
    func.emit(Opcode::LoadImm { rd: 5, value: 1 }); // TRUE
    func.emit(Opcode::SetEnum {
        rd: 6,
        start: 4,
        count: 2,
    });
    func.emit(Opcode::FuncSet {
        rd: 7,
        domain: 3,
        range: 6,
    });
    func.emit(Opcode::SetIn {
        rd: 8,
        elem: 0,
        set: 7,
    });
    func.emit(Opcode::Ret { rs: 8 });

    let out = compile_and_run_with_layout(&func, &state, &layout, &[]);
    assert!(
        out.is_ok(),
        "FuncSet membership should produce Ok, got: {:?}",
        out.status
    );
    assert_eq!(
        out.value, 0,
        "function with value 42 should NOT be in [{{1,2}} -> {{0,1}}]"
    );
}

/// f \in [Nodes -> BOOLEAN] where a key is not in Nodes.
/// f = [1 |-> TRUE, 99 |-> FALSE] but Nodes = {1, 2}.
/// Should return FALSE (key 99 not in domain).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_set_membership_key_not_in_domain() {
    use crate::compound_layout::*;

    let state = vec![
        TAG_FUNC, 2, TAG_INT, 1, TAG_BOOL, 1, TAG_INT, 99, TAG_BOOL, 0,
    ];

    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
        key_layout: Box::new(CompoundLayout::Int),
        value_layout: Box::new(CompoundLayout::Bool),
        pair_count: None,
        domain_lo: None,
    })]);

    let mut func = BytecodeFunction::new("test_bad_key".to_string(), 8);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 2 });
    func.emit(Opcode::SetEnum {
        rd: 3,
        start: 1,
        count: 2,
    });
    func.emit(Opcode::LoadImm { rd: 4, value: 0 });
    func.emit(Opcode::LoadImm { rd: 5, value: 1 });
    func.emit(Opcode::SetEnum {
        rd: 6,
        start: 4,
        count: 2,
    });
    func.emit(Opcode::FuncSet {
        rd: 7,
        domain: 3,
        range: 6,
    });
    func.emit(Opcode::SetIn {
        rd: 8,
        elem: 0,
        set: 7,
    });
    func.emit(Opcode::Ret { rs: 8 });

    let out = compile_and_run_with_layout(&func, &state, &layout, &[]);
    assert!(
        out.is_ok(),
        "FuncSet membership should produce Ok, got: {:?}",
        out.status
    );
    assert_eq!(
        out.value, 0,
        "function with key 99 should NOT be in [{{1,2}} -> BOOLEAN]"
    );
}

/// f \in [Nodes -> 1..10] with range as a Range set.
/// f = [1 |-> 5, 2 |-> 8], Nodes = {1, 2}, range = 1..10.
/// Should return TRUE.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_set_membership_range_range_true() {
    use crate::compound_layout::*;

    let state = vec![TAG_FUNC, 2, TAG_INT, 1, TAG_INT, 5, TAG_INT, 2, TAG_INT, 8];

    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
        key_layout: Box::new(CompoundLayout::Int),
        value_layout: Box::new(CompoundLayout::Int),
        pair_count: None,
        domain_lo: None,
    })]);

    // r0 = LoadVar 0 (function)
    // r1=1, r2=2 → r3 = SetEnum{1,2} (domain)
    // r4=1, r5=10 → r6 = Range{1..10} (range)
    // r7 = FuncSet{domain=r3, range=r6}
    // r8 = SetIn{elem=r0, set=r7}
    let mut func = BytecodeFunction::new("test_range_range".to_string(), 8);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 2 });
    func.emit(Opcode::SetEnum {
        rd: 3,
        start: 1,
        count: 2,
    });
    func.emit(Opcode::LoadImm { rd: 4, value: 1 });
    func.emit(Opcode::LoadImm { rd: 5, value: 10 });
    func.emit(Opcode::Range {
        rd: 6,
        lo: 4,
        hi: 5,
    });
    func.emit(Opcode::FuncSet {
        rd: 7,
        domain: 3,
        range: 6,
    });
    func.emit(Opcode::SetIn {
        rd: 8,
        elem: 0,
        set: 7,
    });
    func.emit(Opcode::Ret { rs: 8 });

    let out = compile_and_run_with_layout(&func, &state, &layout, &[]);
    assert!(
        out.is_ok(),
        "FuncSet range membership should produce Ok, got: {:?}",
        out.status
    );
    assert_eq!(
        out.value, 1,
        "[1 |-> 5, 2 |-> 8] should be in [{{1,2}} -> 1..10]"
    );
}

/// f \in [Nodes -> 1..10] where a value is out of range.
/// f = [1 |-> 5, 2 |-> 15], value 15 > 10.
/// Should return FALSE.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_set_membership_range_range_out_of_bounds() {
    use crate::compound_layout::*;

    let state = vec![TAG_FUNC, 2, TAG_INT, 1, TAG_INT, 5, TAG_INT, 2, TAG_INT, 15];

    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
        key_layout: Box::new(CompoundLayout::Int),
        value_layout: Box::new(CompoundLayout::Int),
        pair_count: None,
        domain_lo: None,
    })]);

    let mut func = BytecodeFunction::new("test_range_oob".to_string(), 8);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::LoadImm { rd: 2, value: 2 });
    func.emit(Opcode::SetEnum {
        rd: 3,
        start: 1,
        count: 2,
    });
    func.emit(Opcode::LoadImm { rd: 4, value: 1 });
    func.emit(Opcode::LoadImm { rd: 5, value: 10 });
    func.emit(Opcode::Range {
        rd: 6,
        lo: 4,
        hi: 5,
    });
    func.emit(Opcode::FuncSet {
        rd: 7,
        domain: 3,
        range: 6,
    });
    func.emit(Opcode::SetIn {
        rd: 8,
        elem: 0,
        set: 7,
    });
    func.emit(Opcode::Ret { rs: 8 });

    let out = compile_and_run_with_layout(&func, &state, &layout, &[]);
    assert!(
        out.is_ok(),
        "FuncSet range membership should produce Ok, got: {:?}",
        out.status
    );
    assert_eq!(
        out.value, 0,
        "[1 |-> 5, 2 |-> 15] should NOT be in [{{1,2}} -> 1..10]"
    );
}

/// Empty domain: f \in [{} -> BOOLEAN].
/// Only the empty function qualifies. f = [] (pair_count=0).
/// Should return TRUE.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_set_membership_empty_domain_empty_func() {
    use crate::compound_layout::*;

    // Empty function
    let state = vec![TAG_FUNC, 0];

    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
        key_layout: Box::new(CompoundLayout::Int),
        value_layout: Box::new(CompoundLayout::Bool),
        pair_count: None,
        domain_lo: None,
    })]);

    let mut func = BytecodeFunction::new("test_empty_domain".to_string(), 8);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    // Empty domain
    func.emit(Opcode::SetEnum {
        rd: 3,
        start: 1,
        count: 0,
    });
    func.emit(Opcode::LoadImm { rd: 4, value: 0 });
    func.emit(Opcode::LoadImm { rd: 5, value: 1 });
    func.emit(Opcode::SetEnum {
        rd: 6,
        start: 4,
        count: 2,
    });
    func.emit(Opcode::FuncSet {
        rd: 7,
        domain: 3,
        range: 6,
    });
    func.emit(Opcode::SetIn {
        rd: 8,
        elem: 0,
        set: 7,
    });
    func.emit(Opcode::Ret { rs: 8 });

    let out = compile_and_run_with_layout(&func, &state, &layout, &[]);
    assert!(
        out.is_ok(),
        "empty domain FuncSet membership should produce Ok, got: {:?}",
        out.status
    );
    assert_eq!(
        out.value, 1,
        "empty function should be in [{{}} -> BOOLEAN]"
    );
}

/// Empty domain but non-empty function: f = [1 |-> TRUE] \in [{} -> BOOLEAN].
/// Should return FALSE (pair_count 1 != 0).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_set_membership_empty_domain_nonempty_func() {
    use crate::compound_layout::*;

    let state = vec![TAG_FUNC, 1, TAG_INT, 1, TAG_BOOL, 1];

    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
        key_layout: Box::new(CompoundLayout::Int),
        value_layout: Box::new(CompoundLayout::Bool),
        pair_count: None,
        domain_lo: None,
    })]);

    let mut func = BytecodeFunction::new("test_empty_dom_nonempty".to_string(), 8);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::SetEnum {
        rd: 3,
        start: 1,
        count: 0,
    });
    func.emit(Opcode::LoadImm { rd: 4, value: 0 });
    func.emit(Opcode::LoadImm { rd: 5, value: 1 });
    func.emit(Opcode::SetEnum {
        rd: 6,
        start: 4,
        count: 2,
    });
    func.emit(Opcode::FuncSet {
        rd: 7,
        domain: 3,
        range: 6,
    });
    func.emit(Opcode::SetIn {
        rd: 8,
        elem: 0,
        set: 7,
    });
    func.emit(Opcode::Ret { rs: 8 });

    let out = compile_and_run_with_layout(&func, &state, &layout, &[]);
    assert!(
        out.is_ok(),
        "empty domain non-empty func should produce Ok, got: {:?}",
        out.status
    );
    assert_eq!(
        out.value, 0,
        "[1 |-> TRUE] should NOT be in [{{}} -> BOOLEAN]"
    );
}
