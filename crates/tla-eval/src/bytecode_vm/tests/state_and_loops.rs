// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State-reading and iterator-loop tests: LoadVar, LoadPrime, quantifiers,
//! FuncDefBegin/LoopNext.

use super::{
    exec, exec_simple, exec_with_next, BytecodeChunk, BytecodeVm, ConstantPool, Opcode, Value,
    VmError,
};
use crate::StateEnvRef;
use tla_tir::bytecode::BytecodeFunction;
use tla_value::CompactValue;

#[test]
fn test_vm_load_var() {
    let state = vec![Value::SmallInt(100), Value::Bool(true)];
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.max_register = 0;
    func.instructions = vec![Opcode::LoadVar { rd: 0, var_idx: 0 }, Opcode::Ret { rs: 0 }];
    let result = exec(func, ConstantPool::new(), &state);
    assert_eq!(result, Value::SmallInt(100));
}

#[test]
fn test_vm_load_prime_reads_next_state() {
    let state = vec![Value::SmallInt(100)];
    let next_state = vec![Value::SmallInt(200)];
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.max_register = 0;
    func.instructions = vec![
        Opcode::LoadPrime { rd: 0, var_idx: 0 },
        Opcode::Ret { rs: 0 },
    ];
    let result = exec_with_next(func, ConstantPool::new(), &state, Some(&next_state));
    assert_eq!(result, Value::SmallInt(200));
}

#[test]
fn test_vm_loads_from_compact_state_env_without_materializing_full_state() {
    let compact_state = [CompactValue::from(100_i64), CompactValue::from(false)];
    let compact_next_state = [CompactValue::from(200_i64), CompactValue::from(true)];
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.max_register = 2;
    func.instructions = vec![
        Opcode::LoadVar { rd: 0, var_idx: 0 },
        Opcode::LoadPrime { rd: 1, var_idx: 0 },
        Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1,
        },
        Opcode::Ret { rs: 2 },
    ];

    let mut chunk = BytecodeChunk::new();
    chunk.constants = ConstantPool::new();
    chunk.add_function(func);
    let mut vm = BytecodeVm::from_state_env(
        &chunk,
        StateEnvRef::from_compact_slice(&compact_state),
        Some(StateEnvRef::from_compact_slice(&compact_next_state)),
    );
    let result = vm.execute_function(0).expect("VM execution failed");
    assert_eq!(result, Value::SmallInt(300));
}

#[test]
fn test_vm_forall_all_true() {
    // \A x \in {1, 2, 3} : x > 0
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::LoadImm { rd: 2, value: 3 },
            Opcode::SetEnum {
                rd: 3,
                start: 0,
                count: 3,
            },
            Opcode::ForallBegin {
                rd: 4,
                r_binding: 5,
                r_domain: 3,
                loop_end: 5,
            },
            Opcode::LoadImm { rd: 6, value: 0 },
            Opcode::GtInt {
                rd: 7,
                r1: 5,
                r2: 6,
            },
            Opcode::ForallNext {
                rd: 4,
                r_binding: 5,
                r_body: 7,
                loop_begin: -2,
            },
            Opcode::Ret { rs: 4 },
        ],
        7,
    );
    assert_eq!(result, Value::Bool(true));
}

#[test]
fn test_vm_forall_empty_domain() {
    // \A x \in {} : FALSE  == TRUE (vacuously true)
    let result = exec_simple(
        vec![
            Opcode::SetEnum {
                rd: 0,
                start: 0,
                count: 0,
            },
            Opcode::ForallBegin {
                rd: 1,
                r_binding: 2,
                r_domain: 0,
                loop_end: 3,
            },
            Opcode::LoadBool {
                rd: 3,
                value: false,
            },
            Opcode::ForallNext {
                rd: 1,
                r_binding: 2,
                r_body: 3,
                loop_begin: -1,
            },
            Opcode::Ret { rs: 1 },
        ],
        3,
    );
    assert_eq!(result, Value::Bool(true));
}

#[test]
fn test_vm_exists_short_circuits_on_first_match() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::LoadImm { rd: 2, value: 3 },
            Opcode::SetEnum {
                rd: 3,
                start: 0,
                count: 3,
            },
            Opcode::ExistsBegin {
                rd: 4,
                r_binding: 5,
                r_domain: 3,
                loop_end: 5,
            },
            Opcode::LoadImm { rd: 6, value: 2 },
            Opcode::Eq {
                rd: 7,
                r1: 5,
                r2: 6,
            },
            Opcode::ExistsNext {
                rd: 4,
                r_binding: 5,
                r_body: 7,
                loop_begin: -2,
            },
            Opcode::Ret { rs: 4 },
        ],
        7,
    );
    assert_eq!(result, Value::Bool(true));
}

#[test]
fn test_vm_func_def_then_apply() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::SetEnum {
                rd: 2,
                start: 0,
                count: 2,
            },
            Opcode::FuncDefBegin {
                rd: 3,
                r_binding: 4,
                r_domain: 2,
                loop_end: 4,
            },
            Opcode::LoadImm { rd: 5, value: 1 },
            Opcode::AddInt {
                rd: 6,
                r1: 4,
                r2: 5,
            },
            Opcode::LoopNext {
                r_binding: 4,
                r_body: 6,
                loop_begin: -2,
            },
            Opcode::LoadImm { rd: 7, value: 2 },
            Opcode::FuncApply {
                rd: 8,
                func: 3,
                arg: 7,
            },
            Opcode::Ret { rs: 8 },
        ],
        8,
    );
    assert_eq!(result, Value::SmallInt(3));
}

#[test]
fn test_vm_choose_uses_tlc_normalized_order() {
    let mut constants = ConstantPool::new();
    let tuple_len_two = constants.add_value(Value::tuple([Value::int(1), Value::int(1)]));
    let tuple_len_one = constants.add_value(Value::tuple([Value::int(2)]));

    let mut func = BytecodeFunction::new("choose".to_string(), 0);
    func.max_register = 5;
    func.instructions = vec![
        Opcode::LoadConst {
            rd: 0,
            idx: tuple_len_two,
        },
        Opcode::LoadConst {
            rd: 1,
            idx: tuple_len_one,
        },
        Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        },
        Opcode::ChooseBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 3,
        },
        Opcode::LoadBool { rd: 5, value: true },
        Opcode::ChooseNext {
            rd: 3,
            r_binding: 4,
            r_body: 5,
            loop_begin: -1,
        },
        Opcode::Ret { rs: 3 },
    ];

    let result = exec(func, constants, &[]);
    assert_eq!(result, Value::tuple([Value::int(2)]));
}

#[test]
fn test_vm_choose_failure_returns_choose_failed() {
    let mut func = BytecodeFunction::new("choose_fail".to_string(), 0);
    func.max_register = 4;
    func.instructions = vec![
        Opcode::LoadImm { rd: 0, value: 1 },
        Opcode::LoadImm { rd: 1, value: 2 },
        Opcode::SetEnum {
            rd: 2,
            start: 0,
            count: 2,
        },
        Opcode::ChooseBegin {
            rd: 3,
            r_binding: 4,
            r_domain: 2,
            loop_end: 3,
        },
        Opcode::LoadBool {
            rd: 0,
            value: false,
        },
        Opcode::ChooseNext {
            rd: 3,
            r_binding: 4,
            r_body: 0,
            loop_begin: -1,
        },
        Opcode::Ret { rs: 3 },
    ];

    let mut chunk = BytecodeChunk::new();
    chunk.constants = ConstantPool::new();
    chunk.add_function(func);
    let mut vm = BytecodeVm::new(&chunk, &[], None);
    let err = vm
        .execute_function(0)
        .expect_err("CHOOSE without a witness should fail");
    assert!(matches!(err, VmError::ChooseFailed));
}

#[test]
fn test_vm_choose_over_finite_set_with_predicate() {
    // CHOOSE x \in {1, 2, 3} : x > 1
    // TLC-normalized order for integers is ascending, so first match is 2.
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::LoadImm { rd: 2, value: 3 },
            Opcode::SetEnum {
                rd: 3,
                start: 0,
                count: 3,
            },
            Opcode::ChooseBegin {
                rd: 4,
                r_binding: 5,
                r_domain: 3,
                loop_end: 5,
            },
            // body: x > 1
            Opcode::LoadImm { rd: 6, value: 1 },
            Opcode::GtInt {
                rd: 7,
                r1: 5,
                r2: 6,
            },
            Opcode::ChooseNext {
                rd: 4,
                r_binding: 5,
                r_body: 7,
                loop_begin: -2,
            },
            Opcode::Ret { rs: 4 },
        ],
        7,
    );
    assert_eq!(result, Value::SmallInt(2));
}

#[test]
fn test_vm_choose_true_predicate_picks_first_element() {
    // CHOOSE x \in {10, 20, 30} : TRUE
    // Should return the first element in TLC-normalized order.
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 20 },
            Opcode::LoadImm { rd: 2, value: 30 },
            Opcode::SetEnum {
                rd: 3,
                start: 0,
                count: 3,
            },
            Opcode::ChooseBegin {
                rd: 4,
                r_binding: 5,
                r_domain: 3,
                loop_end: 3,
            },
            Opcode::LoadBool { rd: 6, value: true },
            Opcode::ChooseNext {
                rd: 4,
                r_binding: 5,
                r_body: 6,
                loop_begin: -1,
            },
            Opcode::Ret { rs: 4 },
        ],
        6,
    );
    assert_eq!(result, Value::SmallInt(10));
}

#[test]
fn test_vm_choose_over_integer_range() {
    // CHOOSE x \in 1..5 : x > 3
    // Range set, predicate x > 3. First match should be 4.
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 5 },
            Opcode::Range {
                rd: 2,
                lo: 0,
                hi: 1,
            },
            Opcode::ChooseBegin {
                rd: 3,
                r_binding: 4,
                r_domain: 2,
                loop_end: 5,
            },
            // body: x > 3
            Opcode::LoadImm { rd: 5, value: 3 },
            Opcode::GtInt {
                rd: 6,
                r1: 4,
                r2: 5,
            },
            Opcode::ChooseNext {
                rd: 3,
                r_binding: 4,
                r_body: 6,
                loop_begin: -2,
            },
            Opcode::Ret { rs: 3 },
        ],
        6,
    );
    assert_eq!(result, Value::SmallInt(4));
}

#[test]
fn test_vm_choose_with_compound_and_predicate() {
    // CHOOSE x \in {1, 2, 3, 4} : x > 1 /\ x < 4
    // Short-circuit AND: first compute x > 1, then if true compute x < 4.
    // First satisfying element in order: 2.
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::LoadImm { rd: 2, value: 3 },
            Opcode::LoadImm { rd: 3, value: 4 },
            Opcode::SetEnum {
                rd: 4,
                start: 0,
                count: 4,
            },
            Opcode::ChooseBegin {
                rd: 5,
                r_binding: 6,
                r_domain: 4,
                loop_end: 10,
            },
            // body: x > 1 /\ x < 4  (short-circuit AND)
            Opcode::LoadImm { rd: 7, value: 1 },
            Opcode::GtInt {
                rd: 8,
                r1: 6,
                r2: 7,
            },
            // Short-circuit AND: move result, jump to end if false
            Opcode::Move { rd: 9, rs: 8 },
            Opcode::JumpFalse {
                rs: 9,
                offset: 4, // jump past x < 4 check to ChooseNext
            },
            Opcode::LoadImm { rd: 10, value: 4 },
            Opcode::LtInt {
                rd: 11,
                r1: 6,
                r2: 10,
            },
            Opcode::Move { rd: 9, rs: 11 },
            // ChooseNext at pc=13, loop back to first body instr at pc=6
            Opcode::ChooseNext {
                rd: 5,
                r_binding: 6,
                r_body: 9,
                loop_begin: -7,
            },
            Opcode::Ret { rs: 5 },
        ],
        11,
    );
    assert_eq!(result, Value::SmallInt(2));
}

#[test]
fn test_vm_choose_with_or_predicate() {
    // CHOOSE x \in {1, 2, 3} : x = 1 \/ x = 3
    // Should pick 1 (first match in order).
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::LoadImm { rd: 2, value: 3 },
            Opcode::SetEnum {
                rd: 3,
                start: 0,
                count: 3,
            },
            Opcode::ChooseBegin {
                rd: 4,
                r_binding: 5,
                r_domain: 3,
                loop_end: 9,
            },
            // body: x = 1 \/ x = 3 (short-circuit OR)
            Opcode::LoadImm { rd: 6, value: 1 },
            Opcode::Eq {
                rd: 7,
                r1: 5,
                r2: 6,
            },
            Opcode::Move { rd: 8, rs: 7 },
            Opcode::JumpTrue {
                rs: 8,
                offset: 4, // skip to ChooseNext at pc=12 if x = 1
            },
            Opcode::LoadImm { rd: 9, value: 3 },
            Opcode::Eq {
                rd: 10,
                r1: 5,
                r2: 9,
            },
            Opcode::Move { rd: 8, rs: 10 },
            Opcode::ChooseNext {
                rd: 4,
                r_binding: 5,
                r_body: 8,
                loop_begin: -7,
            },
            Opcode::Ret { rs: 4 },
        ],
        10,
    );
    assert_eq!(result, Value::SmallInt(1));
}

#[test]
fn test_vm_choose_with_if_then_else_predicate() {
    // CHOOSE x \in {1, 2, 3, 4} : IF x > 2 THEN x < 4 ELSE FALSE
    // x=1: IF FALSE THEN ... ELSE FALSE -> FALSE
    // x=2: IF FALSE THEN ... ELSE FALSE -> FALSE
    // x=3: IF TRUE THEN 3<4=TRUE ELSE ... -> TRUE  (first match)
    // x=4: IF TRUE THEN 4<4=FALSE ELSE ... -> FALSE
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::LoadImm { rd: 2, value: 3 },
            Opcode::LoadImm { rd: 3, value: 4 },
            Opcode::SetEnum {
                rd: 4,
                start: 0,
                count: 4,
            },
            Opcode::ChooseBegin {
                rd: 5,
                r_binding: 6,
                r_domain: 4,
                loop_end: 13,
            },
            // IF x > 2
            Opcode::LoadImm { rd: 7, value: 2 },
            Opcode::GtInt {
                rd: 8,
                r1: 6,
                r2: 7,
            },
            Opcode::JumpFalse {
                rs: 8,
                offset: 5, // jump to else
            },
            // THEN x < 4
            Opcode::LoadImm { rd: 9, value: 4 },
            Opcode::LtInt {
                rd: 10,
                r1: 6,
                r2: 9,
            },
            Opcode::Move { rd: 11, rs: 10 },
            Opcode::Jump { offset: 2 }, // jump to ChooseNext at pc=14
            // ELSE FALSE
            Opcode::LoadBool {
                rd: 11,
                value: false,
            },
            // ChooseNext at pc=14, loop back to first body instr at pc=6
            Opcode::ChooseNext {
                rd: 5,
                r_binding: 6,
                r_body: 11,
                loop_begin: -8,
            },
            Opcode::Ret { rs: 5 },
        ],
        11,
    );
    assert_eq!(result, Value::SmallInt(3));
}

#[test]
fn test_vm_choose_last_element_satisfies() {
    // CHOOSE x \in {1, 2, 3} : x = 3
    // Only the last element satisfies the predicate.
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::LoadImm { rd: 2, value: 3 },
            Opcode::SetEnum {
                rd: 3,
                start: 0,
                count: 3,
            },
            Opcode::ChooseBegin {
                rd: 4,
                r_binding: 5,
                r_domain: 3,
                loop_end: 5,
            },
            Opcode::LoadImm { rd: 6, value: 3 },
            Opcode::Eq {
                rd: 7,
                r1: 5,
                r2: 6,
            },
            Opcode::ChooseNext {
                rd: 4,
                r_binding: 5,
                r_body: 7,
                loop_begin: -2,
            },
            Opcode::Ret { rs: 4 },
        ],
        7,
    );
    assert_eq!(result, Value::SmallInt(3));
}

#[test]
fn test_vm_choose_empty_domain_fails() {
    // CHOOSE x \in {} : TRUE
    // Empty domain should return ChooseFailed immediately.
    let mut func = BytecodeFunction::new("choose_empty".to_string(), 0);
    func.max_register = 4;
    func.instructions = vec![
        Opcode::SetEnum {
            rd: 0,
            start: 0,
            count: 0,
        },
        Opcode::ChooseBegin {
            rd: 1,
            r_binding: 2,
            r_domain: 0,
            loop_end: 3,
        },
        Opcode::LoadBool { rd: 3, value: true },
        Opcode::ChooseNext {
            rd: 1,
            r_binding: 2,
            r_body: 3,
            loop_begin: -1,
        },
        Opcode::Ret { rs: 1 },
    ];

    let mut chunk = BytecodeChunk::new();
    chunk.constants = ConstantPool::new();
    chunk.add_function(func);
    let mut vm = BytecodeVm::new(&chunk, &[], None);
    let err = vm
        .execute_function(0)
        .expect_err("CHOOSE on empty domain should fail");
    assert!(matches!(err, VmError::ChooseFailed));
}

#[test]
fn test_vm_nested_choose() {
    // CHOOSE x \in {1, 2, 3} : x = CHOOSE y \in {2, 3} : y < 3
    // Inner CHOOSE: y \in {2, 3} : y < 3 -> picks 2
    // Outer CHOOSE: x \in {1, 2, 3} : x = 2 -> picks 2
    let result = exec_simple(
        vec![
            // Build outer domain {1, 2, 3}
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::LoadImm { rd: 2, value: 3 },
            Opcode::SetEnum {
                rd: 3,
                start: 0,
                count: 3,
            },
            // Outer ChooseBegin
            Opcode::ChooseBegin {
                rd: 4,
                r_binding: 5,
                r_domain: 3,
                loop_end: 15,
            },
            // --- Inner CHOOSE: CHOOSE y \in {2, 3} : y < 3 ---
            Opcode::LoadImm { rd: 6, value: 2 },
            Opcode::LoadImm { rd: 7, value: 3 },
            Opcode::SetEnum {
                rd: 8,
                start: 6,
                count: 2,
            },
            Opcode::ChooseBegin {
                rd: 9,
                r_binding: 10,
                r_domain: 8,
                loop_end: 5,
            },
            // inner body: y < 3
            Opcode::LoadImm { rd: 11, value: 3 },
            Opcode::LtInt {
                rd: 12,
                r1: 10,
                r2: 11,
            },
            Opcode::ChooseNext {
                rd: 9,
                r_binding: 10,
                r_body: 12,
                loop_begin: -2,
            },
            // --- End inner CHOOSE, result in r9 ---
            // Outer body: x = inner_result
            Opcode::Eq {
                rd: 13,
                r1: 5,
                r2: 9,
            },
            // Outer ChooseNext at pc=13, loop back to first outer body instr at pc=5
            Opcode::ChooseNext {
                rd: 4,
                r_binding: 5,
                r_body: 13,
                loop_begin: -8,
            },
            Opcode::Ret { rs: 4 },
        ],
        13,
    );
    assert_eq!(result, Value::SmallInt(2));
}

#[test]
fn test_vm_choose_singleton_domain() {
    // CHOOSE x \in {42} : TRUE
    // Single-element domain, always picks that element.
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 42 },
            Opcode::SetEnum {
                rd: 1,
                start: 0,
                count: 1,
            },
            Opcode::ChooseBegin {
                rd: 2,
                r_binding: 3,
                r_domain: 1,
                loop_end: 3,
            },
            Opcode::LoadBool { rd: 4, value: true },
            Opcode::ChooseNext {
                rd: 2,
                r_binding: 3,
                r_body: 4,
                loop_begin: -1,
            },
            Opcode::Ret { rs: 2 },
        ],
        4,
    );
    assert_eq!(result, Value::SmallInt(42));
}

#[test]
fn test_vm_unchanged_equal_vars() {
    // UNCHANGED <<x, y>> where x=10, y=20 in both state and next_state → TRUE
    let state = vec![Value::SmallInt(10), Value::SmallInt(20)];
    let next_state = vec![Value::SmallInt(10), Value::SmallInt(20)];
    let mut constants = ConstantPool::new();
    let start = constants.add_value(Value::SmallInt(0)); // var_idx 0
    constants.add_value(Value::SmallInt(1)); // var_idx 1
    let func = super::make_func(
        "test".to_string(),
        0,
        vec![
            Opcode::Unchanged {
                rd: 0,
                start,
                count: 2,
            },
            Opcode::Ret { rs: 0 },
        ],
        0,
    );
    let result = exec_with_next(func, constants, &state, Some(&next_state));
    assert_eq!(result, Value::Bool(true));
}

#[test]
fn test_vm_unchanged_different_vars() {
    // UNCHANGED x where x=10 in state but x=99 in next_state → FALSE
    let state = vec![Value::SmallInt(10)];
    let next_state = vec![Value::SmallInt(99)];
    let mut constants = ConstantPool::new();
    let start = constants.add_value(Value::SmallInt(0)); // var_idx 0
    let func = super::make_func(
        "test".to_string(),
        0,
        vec![
            Opcode::Unchanged {
                rd: 0,
                start,
                count: 1,
            },
            Opcode::Ret { rs: 0 },
        ],
        0,
    );
    let result = exec_with_next(func, constants, &state, Some(&next_state));
    assert_eq!(result, Value::Bool(false));
}

#[test]
fn test_vm_unchanged_partial_mismatch() {
    // UNCHANGED <<x, y>> where x matches but y differs → FALSE
    let state = vec![Value::SmallInt(10), Value::SmallInt(20)];
    let next_state = vec![Value::SmallInt(10), Value::SmallInt(99)];
    let mut constants = ConstantPool::new();
    let start = constants.add_value(Value::SmallInt(0));
    constants.add_value(Value::SmallInt(1));
    let func = super::make_func(
        "test".to_string(),
        0,
        vec![
            Opcode::Unchanged {
                rd: 0,
                start,
                count: 2,
            },
            Opcode::Ret { rs: 0 },
        ],
        0,
    );
    let result = exec_with_next(func, constants, &state, Some(&next_state));
    assert_eq!(result, Value::Bool(false));
}
