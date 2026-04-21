// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scalar opcode smoke tests: LoadImm, LoadBool, arithmetic, comparison,
//! boolean/control flow, Move, division-by-zero, and constant-pool loading.

use super::{
    exec, exec_simple, BytecodeChunk, BytecodeFunction, BytecodeVm, ConstantPool, Opcode, Value,
};

#[test]
fn test_vm_load_imm_ret() {
    let result = exec_simple(
        vec![Opcode::LoadImm { rd: 0, value: 42 }, Opcode::Ret { rs: 0 }],
        0,
    );
    assert_eq!(result, Value::SmallInt(42));
}

#[test]
fn test_vm_load_bool() {
    let result = exec_simple(
        vec![
            Opcode::LoadBool { rd: 0, value: true },
            Opcode::Ret { rs: 0 },
        ],
        0,
    );
    assert_eq!(result, Value::Bool(true));
}

#[test]
fn test_vm_add_int() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 32 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    assert_eq!(result, Value::SmallInt(42));
}

#[test]
fn test_vm_sub_int() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 50 },
            Opcode::LoadImm { rd: 1, value: 8 },
            Opcode::SubInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    assert_eq!(result, Value::SmallInt(42));
}

#[test]
fn test_vm_mul_int() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 6 },
            Opcode::LoadImm { rd: 1, value: 7 },
            Opcode::MulInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    assert_eq!(result, Value::SmallInt(42));
}

#[test]
fn test_vm_eq_true() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 5 },
            Opcode::LoadImm { rd: 1, value: 5 },
            Opcode::Eq {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    assert_eq!(result, Value::Bool(true));
}

#[test]
fn test_vm_eq_false() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 5 },
            Opcode::LoadImm { rd: 1, value: 6 },
            Opcode::Eq {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    assert_eq!(result, Value::Bool(false));
}

#[test]
fn test_vm_lt_int() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 3 },
            Opcode::LoadImm { rd: 1, value: 5 },
            Opcode::LtInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    assert_eq!(result, Value::Bool(true));
}

#[test]
fn test_vm_and_short_circuit() {
    // FALSE /\ anything = FALSE (via JumpFalse)
    let result = exec_simple(
        vec![
            Opcode::LoadBool {
                rd: 0,
                value: false,
            },
            Opcode::Move { rd: 1, rs: 0 },
            Opcode::JumpFalse { rs: 1, offset: 3 }, // skip to Ret
            Opcode::LoadBool { rd: 2, value: true },
            Opcode::Move { rd: 1, rs: 2 },
            // end:
            Opcode::Ret { rs: 1 },
        ],
        2,
    );
    assert_eq!(result, Value::Bool(false));
}

#[test]
fn test_vm_if_then_else() {
    // IF TRUE THEN 1 ELSE 2
    let result = exec_simple(
        vec![
            Opcode::LoadBool { rd: 0, value: true },
            Opcode::JumpFalse { rs: 0, offset: 4 }, // jump to else
            // then:
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::Move { rd: 2, rs: 1 },
            Opcode::Jump { offset: 3 }, // jump to end
            // else:
            Opcode::LoadImm { rd: 3, value: 2 },
            Opcode::Move { rd: 2, rs: 3 },
            // end:
            Opcode::Ret { rs: 2 },
        ],
        3,
    );
    assert_eq!(result, Value::SmallInt(1));
}

#[test]
fn test_vm_neg_int() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 42 },
            Opcode::NegInt { rd: 1, rs: 0 },
            Opcode::Ret { rs: 1 },
        ],
        1,
    );
    assert_eq!(result, Value::SmallInt(-42));
}

#[test]
fn test_vm_not_bool() {
    let result = exec_simple(
        vec![
            Opcode::LoadBool { rd: 0, value: true },
            Opcode::Not { rd: 1, rs: 0 },
            Opcode::Ret { rs: 1 },
        ],
        1,
    );
    assert_eq!(result, Value::Bool(false));
}

#[test]
fn test_vm_implies() {
    // FALSE => anything = TRUE
    let result = exec_simple(
        vec![
            Opcode::LoadBool {
                rd: 0,
                value: false,
            },
            Opcode::LoadBool {
                rd: 1,
                value: false,
            },
            Opcode::Implies {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    assert_eq!(result, Value::Bool(true));
}

#[test]
fn test_vm_move() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 99 },
            Opcode::Move { rd: 1, rs: 0 },
            Opcode::Ret { rs: 1 },
        ],
        1,
    );
    assert_eq!(result, Value::SmallInt(99));
}

#[test]
fn test_vm_division_by_zero() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.max_register = 2;
    func.instructions = vec![
        Opcode::LoadImm { rd: 0, value: 10 },
        Opcode::LoadImm { rd: 1, value: 0 },
        Opcode::DivInt {
            rd: 2,
            r1: 0,
            r2: 1,
        },
        Opcode::Ret { rs: 2 },
    ];
    let mut chunk = BytecodeChunk::new();
    chunk.add_function(func);
    let mut vm = BytecodeVm::new(&chunk, &[], None);
    let result = vm.execute_function(0);
    assert!(result.is_err());
}

#[test]
fn test_vm_load_const() {
    let mut pool = ConstantPool::new();
    pool.add_value(Value::string("hello"));

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.max_register = 0;
    func.instructions = vec![Opcode::LoadConst { rd: 0, idx: 0 }, Opcode::Ret { rs: 0 }];
    let result = exec(func, pool, &[]);
    assert_eq!(result, Value::string("hello"));
}

#[test]
fn test_vm_eq_set_values_compared_correctly() {
    // Value::PartialEq handles set comparison correctly via extensional
    // equality (eq_same_type/cmp delegation). No AST fallback needed.
    let mut pool = ConstantPool::new();
    let left = pool.add_value(Value::set([Value::int(1)]));
    let right = pool.add_value(Value::set(std::iter::empty::<Value>()));

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.max_register = 2;
    func.instructions = vec![
        Opcode::LoadConst { rd: 0, idx: left },
        Opcode::LoadConst { rd: 1, idx: right },
        Opcode::Eq {
            rd: 2,
            r1: 0,
            r2: 1,
        },
        Opcode::Ret { rs: 2 },
    ];

    let result = exec(func, pool, &[]);
    assert_eq!(result, Value::Bool(false));
}
