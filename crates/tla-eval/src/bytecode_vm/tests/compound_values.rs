// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compound-value construction tests: sets, tuples, records.

use super::{exec, exec_simple, intern_name, Arc, ConstantPool, Opcode, SortedSet, Value};
use tla_tir::bytecode::BytecodeFunction;

#[test]
fn test_vm_set_enum() {
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
            Opcode::Ret { rs: 3 },
        ],
        3,
    );
    let expected = Value::Set(Arc::new(SortedSet::from_iter(vec![
        Value::SmallInt(1),
        Value::SmallInt(2),
        Value::SmallInt(3),
    ])));
    assert_eq!(result, expected);
}

#[test]
fn test_vm_set_in_true() {
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
            Opcode::LoadImm { rd: 4, value: 2 },
            Opcode::SetIn {
                rd: 5,
                elem: 4,
                set: 3,
            },
            Opcode::Ret { rs: 5 },
        ],
        5,
    );
    assert_eq!(result, Value::Bool(true));
}

#[test]
fn test_vm_set_in_false() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::SetEnum {
                rd: 2,
                start: 0,
                count: 2,
            },
            Opcode::LoadImm { rd: 3, value: 5 },
            Opcode::SetIn {
                rd: 4,
                elem: 3,
                set: 2,
            },
            Opcode::Ret { rs: 4 },
        ],
        4,
    );
    assert_eq!(result, Value::Bool(false));
}

#[test]
fn test_vm_set_union() {
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
            Opcode::LoadImm { rd: 4, value: 3 },
            Opcode::SetEnum {
                rd: 5,
                start: 3,
                count: 2,
            },
            Opcode::SetUnion {
                rd: 6,
                r1: 2,
                r2: 5,
            },
            Opcode::Ret { rs: 6 },
        ],
        6,
    );
    let expected = Value::Set(Arc::new(SortedSet::from_iter(vec![
        Value::SmallInt(1),
        Value::SmallInt(2),
        Value::SmallInt(3),
    ])));
    assert_eq!(result, expected);
}

#[test]
fn test_vm_tuple_new() {
    let result = exec_simple(
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 20 },
            Opcode::TupleNew {
                rd: 2,
                start: 0,
                count: 2,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );
    assert_eq!(
        result,
        Value::Tuple(vec![Value::SmallInt(10), Value::SmallInt(20)].into())
    );
}

#[test]
fn test_vm_record_new_then_get_field() {
    let mut pool = ConstantPool::new();
    let fields_start = pool.add_value(Value::string("foo"));
    let field_idx = pool.add_field_id(intern_name("foo").0);

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.max_register = 2;
    func.instructions = vec![
        Opcode::LoadImm { rd: 0, value: 42 },
        Opcode::RecordNew {
            rd: 1,
            fields_start,
            values_start: 0,
            count: 1,
        },
        Opcode::RecordGet {
            rd: 2,
            rs: 1,
            field_idx,
        },
        Opcode::Ret { rs: 2 },
    ];

    let result = exec(func, pool, &[]);
    assert_eq!(result, Value::SmallInt(42));
}
