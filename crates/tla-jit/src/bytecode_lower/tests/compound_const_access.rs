// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for JIT compilation of RecordGet/FuncApply/TupleGet on non-state variables.
//!
//! When a compound value (record, function, tuple) is loaded via `LoadConst`,
//! it is serialized to a stack buffer with compound tracking. Subsequent
//! `RecordGet`, `FuncApply`, and `TupleGet` operations can then use native
//! access instead of emitting `FallbackNeeded`.
//!
//! Part of #3949.

use crate::abi::JitStatus;
use std::sync::Arc;
use tla_tir::bytecode::{BytecodeFunction, ConstantPool, Opcode};
use tla_value::value::{FuncValue, RecordValue, Value};

use super::compile_with_constants_and_field_ids_no_state;

// ============================================================
// RecordGet after LoadConst (Record constant)
// ============================================================

/// LoadConst(record) -> RecordGet(field) should return the field value natively.
/// Record: [a |-> 42, b |-> 7]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_get_from_const_record() {
    let rec = RecordValue::from_sorted_str_entries(vec![
        (Arc::from("a"), Value::SmallInt(42)),
        (Arc::from("b"), Value::SmallInt(7)),
    ]);
    let val = Value::Record(rec);

    let mut pool = ConstantPool::new();
    let const_idx = pool.add_value(val);

    // Resolve field name IDs. RecordGet uses field_idx to look up in field_name_ids.
    // Fields are sorted by NameId: a, b
    let nid_a = tla_core::intern_name("a");
    let nid_b = tla_core::intern_name("b");
    let field_name_ids = vec![nid_a.0, nid_b.0];

    // Bytecode: LoadConst r0 = record, RecordGet r1 = r0.a (field_idx=0), Ret r1
    let mut func = BytecodeFunction::new("test_record_get_const".to_string(), 1);
    func.emit(Opcode::LoadConst {
        rd: 0,
        idx: const_idx,
    });
    func.emit(Opcode::RecordGet {
        rd: 1,
        rs: 0,
        field_idx: 0, // field "a"
    });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_with_constants_and_field_ids_no_state(&func, &pool, &field_name_ids);
    assert!(
        out.is_ok(),
        "RecordGet on const record should succeed natively, got status: {:?}",
        out.status
    );
    assert_eq!(out.value, 42, "field 'a' should be 42");
}

/// Test accessing the second field of a constant record.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_get_second_field_from_const_record() {
    let rec = RecordValue::from_sorted_str_entries(vec![
        (Arc::from("a"), Value::SmallInt(42)),
        (Arc::from("b"), Value::SmallInt(7)),
    ]);
    let val = Value::Record(rec);

    let mut pool = ConstantPool::new();
    let const_idx = pool.add_value(val);

    let nid_a = tla_core::intern_name("a");
    let nid_b = tla_core::intern_name("b");
    let field_name_ids = vec![nid_a.0, nid_b.0];

    // Access field "b" (field_idx=1)
    let mut func = BytecodeFunction::new("test_record_get_b".to_string(), 1);
    func.emit(Opcode::LoadConst {
        rd: 0,
        idx: const_idx,
    });
    func.emit(Opcode::RecordGet {
        rd: 1,
        rs: 0,
        field_idx: 1, // field "b"
    });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_with_constants_and_field_ids_no_state(&func, &pool, &field_name_ids);
    assert!(
        out.is_ok(),
        "RecordGet on const record field 'b' should succeed natively, got status: {:?}",
        out.status
    );
    assert_eq!(out.value, 7, "field 'b' should be 7");
}

// ============================================================
// FuncApply after LoadConst (Function constant)
// ============================================================

/// LoadConst(func) -> FuncApply(key) should return the value natively.
/// Function: [1 |-> 10, 2 |-> 20, 3 |-> 30]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_apply_from_const_function() {
    let func_val = FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), Value::SmallInt(10)),
        (Value::SmallInt(2), Value::SmallInt(20)),
        (Value::SmallInt(3), Value::SmallInt(30)),
    ]);
    let val = Value::Func(Arc::new(func_val));

    let mut pool = ConstantPool::new();
    let const_idx = pool.add_value(val);

    // Bytecode: LoadConst r0 = func, LoadImm r1 = 2, FuncApply r2 = r0[r1], Ret r2
    let mut func = BytecodeFunction::new("test_func_apply_const".to_string(), 2);
    func.emit(Opcode::LoadConst {
        rd: 0,
        idx: const_idx,
    });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    func.emit(Opcode::FuncApply {
        rd: 2,
        func: 0,
        arg: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_with_constants_and_field_ids_no_state(&func, &pool, &[]);
    assert!(
        out.is_ok(),
        "FuncApply on const function should succeed natively, got status: {:?}",
        out.status
    );
    assert_eq!(out.value, 20, "func[2] should be 20");
}

/// FuncApply with first key of a contiguous integer-domain function.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_apply_const_first_key() {
    let func_val = FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), Value::SmallInt(100)),
        (Value::SmallInt(2), Value::SmallInt(200)),
    ]);
    let val = Value::Func(Arc::new(func_val));

    let mut pool = ConstantPool::new();
    let const_idx = pool.add_value(val);

    let mut func = BytecodeFunction::new("test_func_apply_first".to_string(), 2);
    func.emit(Opcode::LoadConst {
        rd: 0,
        idx: const_idx,
    });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::FuncApply {
        rd: 2,
        func: 0,
        arg: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_with_constants_and_field_ids_no_state(&func, &pool, &[]);
    assert!(
        out.is_ok(),
        "FuncApply on const function key 1 should succeed natively, got status: {:?}",
        out.status
    );
    assert_eq!(out.value, 100, "func[1] should be 100");
}

// ============================================================
// TupleGet after LoadConst (Tuple constant)
// ============================================================

/// LoadConst(tuple) -> TupleGet(idx) should return the element natively.
/// Tuple: <<10, 20, 30>>
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_get_from_const_tuple() {
    let val = Value::Tuple(
        vec![
            Value::SmallInt(10),
            Value::SmallInt(20),
            Value::SmallInt(30),
        ]
        .into(),
    );

    let mut pool = ConstantPool::new();
    let const_idx = pool.add_value(val);

    // Bytecode: LoadConst r0 = tuple, TupleGet r1 = r0[2], Ret r1
    // TLA+ tuples are 1-indexed.
    let mut func = BytecodeFunction::new("test_tuple_get_const".to_string(), 1);
    func.emit(Opcode::LoadConst {
        rd: 0,
        idx: const_idx,
    });
    func.emit(Opcode::TupleGet {
        rd: 1,
        rs: 0,
        idx: 2, // 1-indexed: element at position 2 = 20
    });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_with_constants_and_field_ids_no_state(&func, &pool, &[]);
    assert!(
        out.is_ok(),
        "TupleGet on const tuple should succeed natively, got status: {:?}",
        out.status
    );
    assert_eq!(out.value, 20, "tuple[2] should be 20");
}

/// TupleGet for first element of a constant tuple.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_get_first_element_from_const_tuple() {
    let val = Value::Tuple(vec![Value::SmallInt(99), Value::SmallInt(88)].into());

    let mut pool = ConstantPool::new();
    let const_idx = pool.add_value(val);

    let mut func = BytecodeFunction::new("test_tuple_get_first".to_string(), 1);
    func.emit(Opcode::LoadConst {
        rd: 0,
        idx: const_idx,
    });
    func.emit(Opcode::TupleGet {
        rd: 1,
        rs: 0,
        idx: 1, // 1-indexed: element at position 1 = 99
    });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_with_constants_and_field_ids_no_state(&func, &pool, &[]);
    assert!(
        out.is_ok(),
        "TupleGet first element should succeed natively, got status: {:?}",
        out.status
    );
    assert_eq!(out.value, 99, "tuple[1] should be 99");
}

// ============================================================
// Move propagation: compound tracking through Move
// ============================================================

/// LoadConst(record) -> Move -> RecordGet should still work natively.
/// This tests that the Move opcode propagates compound tracking.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_get_after_move_from_const() {
    let rec = RecordValue::from_sorted_str_entries(vec![(Arc::from("x"), Value::SmallInt(55))]);
    let val = Value::Record(rec);

    let mut pool = ConstantPool::new();
    let const_idx = pool.add_value(val);

    let nid_x = tla_core::intern_name("x");
    let field_name_ids = vec![nid_x.0];

    // LoadConst r0 = record, Move r1 = r0, RecordGet r2 = r1.x
    let mut func = BytecodeFunction::new("test_move_record_get".to_string(), 2);
    func.emit(Opcode::LoadConst {
        rd: 0,
        idx: const_idx,
    });
    func.emit(Opcode::Move { rd: 1, rs: 0 });
    func.emit(Opcode::RecordGet {
        rd: 2,
        rs: 1,
        field_idx: 0,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_with_constants_and_field_ids_no_state(&func, &pool, &field_name_ids);
    assert!(
        out.is_ok(),
        "RecordGet after Move from const record should succeed natively, got status: {:?}",
        out.status
    );
    assert_eq!(out.value, 55, "field 'x' should be 55");
}

// ============================================================
// RecordGet with boolean field
// ============================================================

/// LoadConst(record with bool) -> RecordGet should return 0/1 for bool.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_get_bool_field_from_const() {
    let rec = RecordValue::from_sorted_str_entries(vec![
        (Arc::from("flag"), Value::Bool(true)),
        (Arc::from("val"), Value::SmallInt(5)),
    ]);
    let val = Value::Record(rec);

    let mut pool = ConstantPool::new();
    let const_idx = pool.add_value(val);

    let nid_flag = tla_core::intern_name("flag");
    let nid_val = tla_core::intern_name("val");
    // Fields sorted by NameId
    let mut sorted = vec![(nid_flag, nid_flag.0), (nid_val, nid_val.0)];
    sorted.sort_by_key(|(nid, _)| *nid);
    let field_name_ids: Vec<u32> = sorted.iter().map(|(_, raw)| *raw).collect();

    // Determine which field_idx corresponds to "flag"
    let flag_idx = sorted.iter().position(|(nid, _)| *nid == nid_flag).unwrap() as u16;

    let mut func = BytecodeFunction::new("test_record_bool_field".to_string(), 1);
    func.emit(Opcode::LoadConst {
        rd: 0,
        idx: const_idx,
    });
    func.emit(Opcode::RecordGet {
        rd: 1,
        rs: 0,
        field_idx: flag_idx,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_with_constants_and_field_ids_no_state(&func, &pool, &field_name_ids);
    assert!(
        out.is_ok(),
        "RecordGet on bool field should succeed natively, got status: {:?}",
        out.status
    );
    assert_eq!(out.value, 1, "field 'flag' should be 1 (true)");
}

// ============================================================
// FuncSet is now tracked as a virtual set for membership tests
// ============================================================

/// FuncSet is handled natively (virtual set tracking) and should
/// not emit FallbackNeeded when followed by Ret.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_set_tracked_natively() {
    let mut func = BytecodeFunction::new("func_set".to_string(), 2);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 }); // domain placeholder
    func.emit(Opcode::LoadImm { rd: 1, value: 2 }); // range placeholder
    func.emit(Opcode::FuncSet {
        rd: 2,
        domain: 0,
        range: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = super::compile_and_run_no_state(&func);
    assert!(
        out.is_ok(),
        "FuncSet should be handled natively (virtual set tracking), got status: {:?}",
        out.status
    );
}
