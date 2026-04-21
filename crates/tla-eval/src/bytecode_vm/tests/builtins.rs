// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for CallBuiltin and Concat opcodes.

use super::{exec_simple, ConstantPool, Opcode, Value};
use tla_tir::bytecode::{BuiltinOp, BytecodeFunction};

// === Concat opcode ===

#[test]
fn test_vm_concat_strings() {
    let mut pool = ConstantPool::new();
    let idx_a = pool.add_value(Value::string("hello"));
    let idx_b = pool.add_value(Value::string(" world"));
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.max_register = 2;
    func.instructions = vec![
        Opcode::LoadConst { rd: 0, idx: idx_a },
        Opcode::LoadConst { rd: 1, idx: idx_b },
        Opcode::Concat {
            rd: 2,
            r1: 0,
            r2: 1,
        },
        Opcode::Ret { rs: 2 },
    ];
    let chunk = super::exec(func, pool, &[]);
    assert_eq!(chunk, Value::string("hello world"));
}

#[test]
fn test_vm_concat_sequences() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::SeqNew {
                rd: 2,
                start: 0,
                count: 2,
            },
            Opcode::LoadImm { rd: 3, value: 3 },
            Opcode::LoadImm { rd: 4, value: 4 },
            Opcode::SeqNew {
                rd: 5,
                start: 3,
                count: 2,
            },
            Opcode::Concat {
                rd: 6,
                r1: 2,
                r2: 5,
            },
            Opcode::Ret { rs: 6 },
        ],
        6,
    );
    assert_eq!(
        result,
        Value::seq(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
            Value::SmallInt(4),
        ])
    );
}

// === Len builtin ===

#[test]
fn test_vm_builtin_len_seq() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 20 },
            Opcode::LoadImm { rd: 2, value: 30 },
            Opcode::SeqNew {
                rd: 3,
                start: 0,
                count: 3,
            },
            Opcode::CallBuiltin {
                rd: 4,
                builtin: BuiltinOp::Len,
                args_start: 3,
                argc: 1,
            },
            Opcode::Ret { rs: 4 },
        ],
        4,
    );
    assert_eq!(result, Value::SmallInt(3));
}

#[test]
fn test_vm_builtin_len_string() {
    let mut pool = ConstantPool::new();
    let idx = pool.add_value(Value::string("abc"));
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.max_register = 1;
    func.instructions = vec![
        Opcode::LoadConst { rd: 0, idx },
        Opcode::CallBuiltin {
            rd: 1,
            builtin: BuiltinOp::Len,
            args_start: 0,
            argc: 1,
        },
        Opcode::Ret { rs: 1 },
    ];
    let result = super::exec(func, pool, &[]);
    assert_eq!(result, Value::SmallInt(3));
}

// === Head / Tail builtins ===

#[test]
fn test_vm_builtin_head() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 42 },
            Opcode::LoadImm { rd: 1, value: 99 },
            Opcode::SeqNew {
                rd: 2,
                start: 0,
                count: 2,
            },
            Opcode::CallBuiltin {
                rd: 3,
                builtin: BuiltinOp::Head,
                args_start: 2,
                argc: 1,
            },
            Opcode::Ret { rs: 3 },
        ],
        3,
    );
    assert_eq!(result, Value::SmallInt(42));
}

#[test]
fn test_vm_builtin_tail() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::LoadImm { rd: 2, value: 3 },
            Opcode::SeqNew {
                rd: 3,
                start: 0,
                count: 3,
            },
            Opcode::CallBuiltin {
                rd: 4,
                builtin: BuiltinOp::Tail,
                args_start: 3,
                argc: 1,
            },
            Opcode::Ret { rs: 4 },
        ],
        4,
    );
    assert_eq!(
        result,
        Value::seq(vec![Value::SmallInt(2), Value::SmallInt(3)])
    );
}

// === Append builtin ===

#[test]
fn test_vm_builtin_append() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::SeqNew {
                rd: 2,
                start: 0,
                count: 2,
            },
            // args: seq at r2, elem at r3
            Opcode::LoadImm { rd: 3, value: 3 },
            Opcode::CallBuiltin {
                rd: 4,
                builtin: BuiltinOp::Append,
                args_start: 2,
                argc: 2,
            },
            Opcode::Ret { rs: 4 },
        ],
        4,
    );
    assert_eq!(
        result,
        Value::seq(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ])
    );
}

// === SubSeq builtin ===

#[test]
fn test_vm_builtin_subseq() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 20 },
            Opcode::LoadImm { rd: 2, value: 30 },
            Opcode::LoadImm { rd: 3, value: 40 },
            Opcode::SeqNew {
                rd: 4,
                start: 0,
                count: 4,
            },
            // SubSeq(s, 2, 3) => <<20, 30>>
            Opcode::LoadImm { rd: 5, value: 2 },
            Opcode::LoadImm { rd: 6, value: 3 },
            Opcode::CallBuiltin {
                rd: 7,
                builtin: BuiltinOp::SubSeq,
                args_start: 4,
                argc: 3,
            },
            Opcode::Ret { rs: 7 },
        ],
        7,
    );
    assert_eq!(
        result,
        Value::seq(vec![Value::SmallInt(20), Value::SmallInt(30)])
    );
}

// === Cardinality builtin ===

#[test]
fn test_vm_builtin_cardinality() {
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
            Opcode::CallBuiltin {
                rd: 4,
                builtin: BuiltinOp::Cardinality,
                args_start: 3,
                argc: 1,
            },
            Opcode::Ret { rs: 4 },
        ],
        4,
    );
    // Cardinality returns BigInt via Value::big_int
    assert_eq!(result, Value::SmallInt(3));
}

// === IsFiniteSet builtin ===

#[test]
fn test_vm_builtin_is_finite_set() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::SetEnum {
                rd: 1,
                start: 0,
                count: 1,
            },
            Opcode::CallBuiltin {
                rd: 2,
                builtin: BuiltinOp::IsFiniteSet,
                args_start: 1,
                argc: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    assert_eq!(result, Value::Bool(true));
}

// === ToString builtin ===

#[test]
fn test_vm_builtin_to_string() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 42 },
            Opcode::CallBuiltin {
                rd: 1,
                builtin: BuiltinOp::ToString,
                args_start: 0,
                argc: 1,
            },
            Opcode::Ret { rs: 1 },
        ],
        1,
    );
    assert_eq!(result, Value::string("42"));
}

// === Seq builtin ===

#[test]
fn test_vm_builtin_seq() {
    // Seq(S) returns Value::SeqSet — the set of all finite sequences over S.
    // We test: build {1, 2}, call Seq, build <<1>>, check membership with SetIn.
    let result = exec_simple(
        vec![
            // Build base set {1, 2}
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::SetEnum {
                rd: 2,
                start: 0,
                count: 2,
            },
            // Seq({1, 2})
            Opcode::CallBuiltin {
                rd: 3,
                builtin: BuiltinOp::Seq,
                args_start: 2,
                argc: 1,
            },
            // Build sequence <<1>>
            Opcode::LoadImm { rd: 4, value: 1 },
            Opcode::SeqNew {
                rd: 5,
                start: 4,
                count: 1,
            },
            // <<1>> \in Seq({1, 2}) should be TRUE
            Opcode::SetIn {
                rd: 6,
                elem: 5,
                set: 3,
            },
            Opcode::Ret { rs: 6 },
        ],
        6,
    );
    assert_eq!(result, Value::Bool(true));
}

// === Set equality (no longer requires AST fallback) ===

#[test]
fn test_vm_set_equality_in_vm() {
    // Previously this would fail with VmError::Unsupported.
    // Now Value::PartialEq handles set comparison correctly.
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::SetEnum {
                rd: 2,
                start: 0,
                count: 2,
            },
            Opcode::LoadImm { rd: 3, value: 2 },
            Opcode::LoadImm { rd: 4, value: 1 },
            Opcode::SetEnum {
                rd: 5,
                start: 3,
                count: 2,
            },
            Opcode::Eq {
                rd: 6,
                r1: 2,
                r2: 5,
            },
            Opcode::Ret { rs: 6 },
        ],
        6,
    );
    assert_eq!(result, Value::Bool(true));
}

#[test]
fn test_vm_set_inequality_in_vm() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::SetEnum {
                rd: 1,
                start: 0,
                count: 1,
            },
            Opcode::LoadImm { rd: 2, value: 2 },
            Opcode::SetEnum {
                rd: 3,
                start: 2,
                count: 1,
            },
            Opcode::Neq {
                rd: 4,
                r1: 1,
                r2: 3,
            },
            Opcode::Ret { rs: 4 },
        ],
        4,
    );
    assert_eq!(result, Value::Bool(true));
}
