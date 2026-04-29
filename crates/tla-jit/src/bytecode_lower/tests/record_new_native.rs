// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for native RecordNew lowering via compound scratch buffer.
//!
//! RecordNew with all-scalar fields compiles natively when the constant pool
//! and state layout are available, writing serialized data to a thread-local
//! scratch buffer and returning COMPOUND_SCRATCH_BASE + offset.
//!
//! Part of #3908.

use crate::abi::{self, JitStatus};
use crate::bytecode_lower::BytecodeLowerer;
use crate::compound_layout::{
    CompoundLayout, StateLayout, VarLayout, TAG_BOOL, TAG_INT, TAG_RECORD,
};
use tla_tir::bytecode::{BytecodeFunction, ConstantPool, Opcode};
use tla_value::Value;

use super::compile_and_run_next_state_with_layout;

/// RecordNew with 2 integer fields produces a scratch buffer offset in state_out.
///
/// Bytecode:
///   r0 = 42       (field "x" value)
///   r1 = 99       (field "y" value)
///   r2 = RecordNew(fields=["x","y"], values=[r0,r1])
///   StoreVar(0, r2)
///   return TRUE
///
/// The state layout has one variable: a Record with fields {x: Int, y: Int}.
/// After execution, state_out[0] should be >= COMPOUND_SCRATCH_BASE.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_new_native_two_int_fields() {
    let mut pool = ConstantPool::new();
    // RecordNew fields_start indexes into the value constants.
    // Add field name strings at indices 0 and 1.
    let _idx0 = pool.add_value(Value::String("x".into()));
    let _idx1 = pool.add_value(Value::String("y".into()));

    let mut func = BytecodeFunction::new("record_new_native".to_string(), 5);
    // r0 = 42 (value for field "x")
    func.emit(Opcode::LoadImm { rd: 0, value: 42 });
    // r1 = 99 (value for field "y")
    func.emit(Opcode::LoadImm { rd: 1, value: 99 });
    // r2 = RecordNew { fields_start=0, values_start=0, count=2 }
    func.emit(Opcode::RecordNew {
        rd: 2,
        fields_start: 0,
        values_start: 0,
        count: 2,
    });
    // StoreVar(0, r2) — write the encoded offset to state_out[0]
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
    // return TRUE
    func.emit(Opcode::LoadBool { rd: 3, value: true });
    func.emit(Opcode::Ret { rs: 3 });

    // Build a state layout with one Record variable: {x: Int, y: Int}
    let x_nid = tla_core::intern_name("x");
    let y_nid = tla_core::intern_name("y");
    let mut fields = vec![(x_nid, CompoundLayout::Int), (y_nid, CompoundLayout::Int)];
    fields.sort_by_key(|(nid, _)| *nid);
    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record { fields })]);

    // State_in has 1 slot (compound variable — just a placeholder offset)
    let state_in = [0i64];

    // Clear scratch before test
    abi::clear_compound_scratch();

    let (out, state_out) = compile_and_run_next_state_with_layout(&func, &state_in, &pool, &layout);

    assert_eq!(out.status, JitStatus::Ok, "action should complete natively");
    assert_eq!(out.value, 1, "action should return TRUE");

    // state_out[0] should be a scratch buffer offset
    let offset = state_out[0];
    assert!(
        offset >= abi::COMPOUND_SCRATCH_BASE,
        "state_out[0] should be a scratch buffer offset, got {offset:#x}"
    );

    // Verify the scratch buffer contains the correct serialized record
    let scratch = abi::read_compound_scratch();
    let scratch_pos = (offset - abi::COMPOUND_SCRATCH_BASE) as usize;
    assert!(scratch_pos < scratch.len(), "scratch_pos out of bounds");

    // Verify the serialized format: TAG_RECORD, count, then fields
    assert_eq!(
        scratch[scratch_pos], TAG_RECORD,
        "first slot should be TAG_RECORD"
    );
    assert_eq!(scratch[scratch_pos + 1], 2, "field count should be 2");

    // Fields are sorted by NameId. Check both fields exist with correct tags.
    // Each field is: name_id, tag, value
    let field0_tag = scratch[scratch_pos + 3];
    let field1_tag = scratch[scratch_pos + 6];
    assert_eq!(field0_tag, TAG_INT, "first field tag should be TAG_INT");
    assert_eq!(field1_tag, TAG_INT, "second field tag should be TAG_INT");

    // Verify the values are present (order depends on NameId sort order)
    let field0_val = scratch[scratch_pos + 4];
    let field1_val = scratch[scratch_pos + 7];
    // x and y values should be 42 and 99 in some order
    let mut vals = [field0_val, field1_val];
    vals.sort();
    assert_eq!(vals, [42, 99], "field values should be 42 and 99");
}

/// RecordNew with mixed Int/Bool fields uses correct type tags from layout.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_new_native_mixed_int_bool() {
    let mut pool = ConstantPool::new();
    let _idx0 = pool.add_value(Value::String("active".into()));
    let _idx1 = pool.add_value(Value::String("count".into()));

    let mut func = BytecodeFunction::new("record_new_mixed".to_string(), 5);
    // r0 = 1 (TRUE for "active" bool field)
    func.emit(Opcode::LoadBool { rd: 0, value: true });
    // r1 = 7 (value for "count" int field)
    func.emit(Opcode::LoadImm { rd: 1, value: 7 });
    // r2 = RecordNew { fields_start=0, values_start=0, count=2 }
    func.emit(Opcode::RecordNew {
        rd: 2,
        fields_start: 0,
        values_start: 0,
        count: 2,
    });
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
    func.emit(Opcode::LoadBool { rd: 3, value: true });
    func.emit(Opcode::Ret { rs: 3 });

    // Layout: Record { active: Bool, count: Int }
    let active_nid = tla_core::intern_name("active");
    let count_nid = tla_core::intern_name("count");
    let mut fields = vec![
        (active_nid, CompoundLayout::Bool),
        (count_nid, CompoundLayout::Int),
    ];
    fields.sort_by_key(|(nid, _)| *nid);
    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record { fields })]);

    let state_in = [0i64];
    abi::clear_compound_scratch();

    let (out, state_out) = compile_and_run_next_state_with_layout(&func, &state_in, &pool, &layout);

    assert_eq!(out.status, JitStatus::Ok, "action should complete natively");

    let offset = state_out[0];
    assert!(
        offset >= abi::COMPOUND_SCRATCH_BASE,
        "state_out[0] should be a scratch buffer offset"
    );

    // Verify scratch buffer has correct tags
    let scratch = abi::read_compound_scratch();
    let pos = (offset - abi::COMPOUND_SCRATCH_BASE) as usize;
    assert_eq!(scratch[pos], TAG_RECORD);
    assert_eq!(scratch[pos + 1], 2);

    // Find the Bool field and verify its tag
    let tag0 = scratch[pos + 3];
    let tag1 = scratch[pos + 6];
    let mut tags = [tag0, tag1];
    tags.sort();
    assert_eq!(
        tags,
        [TAG_INT, TAG_BOOL],
        "should have one TAG_INT and one TAG_BOOL field"
    );
}

/// RecordNew without constants or layout still falls back to FallbackNeeded.
///
/// This verifies backward compatibility: when no constant pool is available,
/// RecordNew cannot resolve field names and emits FallbackNeeded.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_new_without_constants_still_fallback() {
    let mut func = BytecodeFunction::new("record_new_no_const".to_string(), 2);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    func.emit(Opcode::RecordNew {
        rd: 2,
        fields_start: 0,
        values_start: 0,
        count: 2,
    });
    func.emit(Opcode::Ret { rs: 2 });

    // Compile without constants — should still work but fall back
    let out = super::compile_and_run_no_state(&func);
    assert_eq!(
        out.status,
        JitStatus::FallbackNeeded,
        "RecordNew without constants should fall back"
    );
}

/// RecordNew result can be deserialized from scratch buffer via deserialize_value.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_new_scratch_deserialization() {
    let mut pool = ConstantPool::new();
    let _idx0 = pool.add_value(Value::String("a".into()));
    let _idx1 = pool.add_value(Value::String("b".into()));

    let mut func = BytecodeFunction::new("record_deser".to_string(), 5);
    func.emit(Opcode::LoadImm { rd: 0, value: 10 });
    func.emit(Opcode::LoadImm { rd: 1, value: 20 });
    func.emit(Opcode::RecordNew {
        rd: 2,
        fields_start: 0,
        values_start: 0,
        count: 2,
    });
    func.emit(Opcode::StoreVar { var_idx: 0, rs: 2 });
    func.emit(Opcode::LoadBool { rd: 3, value: true });
    func.emit(Opcode::Ret { rs: 3 });

    let a_nid = tla_core::intern_name("a");
    let b_nid = tla_core::intern_name("b");
    let mut fields = vec![(a_nid, CompoundLayout::Int), (b_nid, CompoundLayout::Int)];
    fields.sort_by_key(|(nid, _)| *nid);
    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record { fields })]);

    let state_in = [0i64];
    abi::clear_compound_scratch();

    let (out, state_out) = compile_and_run_next_state_with_layout(&func, &state_in, &pool, &layout);
    assert_eq!(out.status, JitStatus::Ok);

    // Deserialize the record from the scratch buffer
    let offset = state_out[0];
    let scratch = abi::read_compound_scratch();
    let scratch_pos = (offset - abi::COMPOUND_SCRATCH_BASE) as usize;

    let (deserialized, slots_consumed) =
        crate::compound_layout::deserialize_value(&scratch, scratch_pos)
            .expect("deserialization should succeed");

    // Should consume TAG_RECORD(1) + count(1) + 2 fields * 3 slots = 8 slots
    assert_eq!(slots_consumed, 8, "should consume 8 slots");

    // The deserialized value should be a Record
    assert!(
        matches!(deserialized, tla_value::Value::Record(_)),
        "deserialized value should be a record, got {:?}",
        deserialized
    );
}

// ============================================================
// RecordNew -> RecordGet: inline stack serialization enables native access
// Part of #3949
// ============================================================

/// RecordNew followed by RecordGet should produce a native result when
/// layout tags are available. The inline stack serialization path enables
/// compound tracking with is_direct_ptr=true, so RecordGet can use
/// native indexed load instead of FallbackNeeded.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_new_then_record_get_native() {
    let mut pool = ConstantPool::new();
    let _idx0 = pool.add_value(Value::String("a".into()));
    let _idx1 = pool.add_value(Value::String("b".into()));

    let a_nid = tla_core::intern_name("a");
    let b_nid = tla_core::intern_name("b");
    let mut fields = vec![(a_nid, CompoundLayout::Int), (b_nid, CompoundLayout::Int)];
    fields.sort_by_key(|(nid, _)| *nid);

    // Build field_name_ids in sorted NameId order
    let field_name_ids: Vec<u32> = fields.iter().map(|(nid, _)| nid.0).collect();

    // Determine which sorted index corresponds to "b"
    let b_sorted_idx = fields.iter().position(|(nid, _)| *nid == b_nid).unwrap() as u16;

    // Bytecode: LoadImm r0=42, LoadImm r1=99, RecordNew r2, RecordGet r3=r2.b, Ret r3
    let mut func = BytecodeFunction::new("record_new_get".to_string(), 5);
    func.emit(Opcode::LoadImm { rd: 0, value: 42 });
    func.emit(Opcode::LoadImm { rd: 1, value: 99 });
    func.emit(Opcode::RecordNew {
        rd: 2,
        fields_start: 0,
        values_start: 0,
        count: 2,
    });
    // RecordGet field "b" from the just-created record
    func.emit(Opcode::RecordGet {
        rd: 3,
        rs: 2,
        field_idx: b_sorted_idx,
    });
    func.emit(Opcode::Ret { rs: 3 });

    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
        fields: fields.clone(),
    })]);

    let mut lowerer =
        crate::bytecode_lower::BytecodeLowerer::new().expect("failed to create lowerer");
    let jit_fn = lowerer
        .compile_invariant_with_constants_and_layout(&func, &pool, &layout, &field_name_ids)
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = crate::abi::JitCallOut::default();
    unsafe {
        jit_fn(&mut out, [].as_ptr(), 0);
    }

    assert!(
        out.is_ok(),
        "RecordNew -> RecordGet should succeed natively, got status: {:?}",
        out.status
    );
    assert_eq!(out.value, 99, "field 'b' should be 99");
}

/// RecordNew -> RecordGet for first field (field "a").
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_new_then_record_get_first_field() {
    let mut pool = ConstantPool::new();
    let _idx0 = pool.add_value(Value::String("a".into()));
    let _idx1 = pool.add_value(Value::String("b".into()));

    let a_nid = tla_core::intern_name("a");
    let b_nid = tla_core::intern_name("b");
    let mut fields = vec![(a_nid, CompoundLayout::Int), (b_nid, CompoundLayout::Int)];
    fields.sort_by_key(|(nid, _)| *nid);

    let field_name_ids: Vec<u32> = fields.iter().map(|(nid, _)| nid.0).collect();
    let a_sorted_idx = fields.iter().position(|(nid, _)| *nid == a_nid).unwrap() as u16;

    let mut func = BytecodeFunction::new("record_new_get_a".to_string(), 5);
    func.emit(Opcode::LoadImm { rd: 0, value: 42 });
    func.emit(Opcode::LoadImm { rd: 1, value: 99 });
    func.emit(Opcode::RecordNew {
        rd: 2,
        fields_start: 0,
        values_start: 0,
        count: 2,
    });
    func.emit(Opcode::RecordGet {
        rd: 3,
        rs: 2,
        field_idx: a_sorted_idx,
    });
    func.emit(Opcode::Ret { rs: 3 });

    let layout = StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
        fields: fields.clone(),
    })]);

    let mut lowerer =
        crate::bytecode_lower::BytecodeLowerer::new().expect("failed to create lowerer");
    let jit_fn = lowerer
        .compile_invariant_with_constants_and_layout(&func, &pool, &layout, &field_name_ids)
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = crate::abi::JitCallOut::default();
    unsafe {
        jit_fn(&mut out, [].as_ptr(), 0);
    }

    assert!(
        out.is_ok(),
        "RecordNew -> RecordGet(a) should succeed natively, got status: {:?}",
        out.status
    );
    assert_eq!(out.value, 42, "field 'a' should be 42");
}
