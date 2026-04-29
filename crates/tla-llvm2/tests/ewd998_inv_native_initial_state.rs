// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Native LLVM2 regression for executing the EWD998 `Inv` shape on compact state.

#![cfg(feature = "native")]

use tla_jit_abi::{CompoundLayout, JitCallOut, JitInvariantFn, JitStatus, StateLayout, VarLayout};
use tla_tir::bytecode::{BuiltinOp, BytecodeChunk, BytecodeFunction, Opcode};
use tla_value::Value;

const SYMBOL: &str = "ewd998_inv_native_initial_state";
const CALL_ARG_START: u8 = 60;

fn int_function(value_layout: CompoundLayout) -> VarLayout {
    VarLayout::Compound(CompoundLayout::Function {
        key_layout: Box::new(CompoundLayout::Int),
        value_layout: Box::new(value_layout),
        pair_count: Some(3),
        domain_lo: Some(0),
    })
}

fn ewd998_layout() -> StateLayout {
    StateLayout::new(vec![
        int_function(CompoundLayout::Bool),
        int_function(CompoundLayout::String),
        int_function(CompoundLayout::Int),
        int_function(CompoundLayout::Int),
        VarLayout::Compound(CompoundLayout::Record {
            fields: vec![
                (tla_core::intern_name("pos"), CompoundLayout::Int),
                (tla_core::intern_name("color"), CompoundLayout::String),
                (tla_core::intern_name("q"), CompoundLayout::Int),
            ],
        }),
    ])
}

fn token_tail_from_layout(layout: &StateLayout, pos: i64, color: i64, q: i64) -> Vec<i64> {
    let token_layout = layout
        .var_layout(4)
        .expect("EWD998 layout should include token variable");
    let VarLayout::Compound(CompoundLayout::Record { fields }) = token_layout else {
        panic!("EWD998 token should use compact record layout");
    };

    let pos_field = tla_core::intern_name("pos");
    let color_field = tla_core::intern_name("color");
    let q_field = tla_core::intern_name("q");

    fields
        .iter()
        .map(|(field, _)| {
            if *field == pos_field {
                pos
            } else if *field == color_field {
                color
            } else if *field == q_field {
                q
            } else {
                panic!("unexpected EWD998 token field: {field:?}");
            }
        })
        .collect()
}

fn emit_call2(func: &mut BytecodeFunction, rd: u8, op_idx: u16, lhs: u8, rhs: u8) {
    func.emit(Opcode::Move {
        rd: CALL_ARG_START,
        rs: lhs,
    });
    func.emit(Opcode::Move {
        rd: CALL_ARG_START + 1,
        rs: rhs,
    });
    func.emit(Opcode::Call {
        rd,
        op_idx,
        args_start: CALL_ARG_START,
        argc: 2,
    });
}

fn add_sum(chunk: &mut BytecodeChunk) -> u16 {
    let mut sum = BytecodeFunction::new("Sum".to_string(), 2);
    sum.emit(Opcode::CallBuiltin {
        rd: 2,
        builtin: BuiltinOp::FoldFunctionOnSetSum,
        args_start: 0,
        argc: 2,
    });
    sum.emit(Opcode::Ret { rs: 2 });
    chunk.add_function(sum)
}

fn ewd998_inv_chunk() -> (BytecodeChunk, usize) {
    let mut chunk = BytecodeChunk::new();
    let black = chunk.constants.add_value(Value::String("black".into()));
    let color_field = chunk
        .constants
        .add_field_id(tla_core::intern_name("color").0);
    let pos_field = chunk.constants.add_field_id(tla_core::intern_name("pos").0);
    let q_field = chunk.constants.add_field_id(tla_core::intern_name("q").0);

    let sum_idx = add_sum(&mut chunk);

    let mut inv = BytecodeFunction::new(SYMBOL.to_string(), 0);

    inv.emit(Opcode::LoadImm { rd: 0, value: 0 });
    inv.emit(Opcode::LoadImm { rd: 1, value: 2 });
    inv.emit(Opcode::Range {
        rd: 2,
        lo: 0,
        hi: 1,
    });

    inv.emit(Opcode::LoadVar { rd: 3, var_idx: 3 });
    emit_call2(&mut inv, 4, sum_idx, 3, 2);
    inv.emit(Opcode::LoadVar { rd: 5, var_idx: 2 });
    emit_call2(&mut inv, 6, sum_idx, 5, 2);
    inv.emit(Opcode::Eq {
        rd: 7,
        r1: 4,
        r2: 6,
    });

    inv.emit(Opcode::LoadVar { rd: 8, var_idx: 4 });
    inv.emit(Opcode::RecordGet {
        rd: 9,
        rs: 8,
        field_idx: pos_field,
    });
    inv.emit(Opcode::RecordGet {
        rd: 10,
        rs: 8,
        field_idx: q_field,
    });
    inv.emit(Opcode::RecordGet {
        rd: 11,
        rs: 8,
        field_idx: color_field,
    });

    inv.emit(Opcode::LoadImm { rd: 12, value: 1 });
    inv.emit(Opcode::AddInt {
        rd: 13,
        r1: 9,
        r2: 12,
    });
    inv.emit(Opcode::Range {
        rd: 14,
        lo: 13,
        hi: 1,
    });

    inv.emit(Opcode::LoadVar { rd: 15, var_idx: 0 });
    let forall_begin = inv.emit(Opcode::ForallBegin {
        rd: 16,
        r_binding: 17,
        r_domain: 14,
        loop_end: 0,
    });
    inv.emit(Opcode::FuncApply {
        rd: 18,
        func: 15,
        arg: 17,
    });
    inv.emit(Opcode::LoadBool {
        rd: 19,
        value: false,
    });
    inv.emit(Opcode::Eq {
        rd: 20,
        r1: 18,
        r2: 19,
    });
    let forall_next = inv.emit(Opcode::ForallNext {
        rd: 16,
        r_binding: 17,
        r_body: 20,
        loop_begin: 0,
    });
    inv.patch_jump(forall_begin, forall_next + 1);
    inv.patch_jump(forall_next, forall_begin + 1);

    inv.emit(Opcode::Eq {
        rd: 21,
        r1: 9,
        r2: 1,
    });
    inv.emit(Opcode::Eq {
        rd: 22,
        r1: 10,
        r2: 0,
    });
    emit_call2(&mut inv, 23, sum_idx, 5, 14);
    inv.emit(Opcode::Eq {
        rd: 24,
        r1: 10,
        r2: 23,
    });
    inv.emit(Opcode::Move { rd: 25, rs: 24 });
    inv.emit(Opcode::CondMove {
        rd: 25,
        cond: 21,
        rs: 22,
    });
    inv.emit(Opcode::And {
        rd: 26,
        r1: 16,
        r2: 25,
    });

    inv.emit(Opcode::Range {
        rd: 27,
        lo: 0,
        hi: 9,
    });
    emit_call2(&mut inv, 28, sum_idx, 5, 27);
    inv.emit(Opcode::AddInt {
        rd: 29,
        r1: 28,
        r2: 10,
    });
    inv.emit(Opcode::GtInt {
        rd: 30,
        r1: 29,
        r2: 0,
    });

    inv.emit(Opcode::LoadVar { rd: 31, var_idx: 1 });
    inv.emit(Opcode::LoadConst { rd: 32, idx: black });
    let exists_begin = inv.emit(Opcode::ExistsBegin {
        rd: 33,
        r_binding: 34,
        r_domain: 27,
        loop_end: 0,
    });
    inv.emit(Opcode::FuncApply {
        rd: 35,
        func: 31,
        arg: 34,
    });
    inv.emit(Opcode::Eq {
        rd: 36,
        r1: 35,
        r2: 32,
    });
    let exists_next = inv.emit(Opcode::ExistsNext {
        rd: 33,
        r_binding: 34,
        r_body: 36,
        loop_begin: 0,
    });
    inv.patch_jump(exists_begin, exists_next + 1);
    inv.patch_jump(exists_next, exists_begin + 1);

    inv.emit(Opcode::Eq {
        rd: 37,
        r1: 11,
        r2: 32,
    });
    inv.emit(Opcode::Or {
        rd: 38,
        r1: 26,
        r2: 30,
    });
    inv.emit(Opcode::Or {
        rd: 39,
        r1: 38,
        r2: 33,
    });
    inv.emit(Opcode::Or {
        rd: 40,
        r1: 39,
        r2: 37,
    });
    inv.emit(Opcode::And {
        rd: 41,
        r1: 7,
        r2: 40,
    });
    inv.emit(Opcode::Ret { rs: 41 });
    let entry_idx = usize::from(chunk.add_function(inv));

    (chunk, entry_idx)
}

fn eval(f: JitInvariantFn, state: &[i64]) -> JitCallOut {
    let mut out = JitCallOut::default();
    unsafe { f(&mut out, state.as_ptr(), state.len() as u32) };
    out
}

fn compile_ewd998_inv(layout: &StateLayout) -> (tla_llvm2::NativeLibrary, JitInvariantFn) {
    let (chunk, entry_idx) = ewd998_inv_chunk();
    let entry = &chunk.functions[entry_idx];
    let lib = tla_llvm2::compile_entry_invariant_native_with_chunk_and_layout(
        entry,
        &chunk,
        SYMBOL,
        layout,
        tla_llvm2::OptLevel::O1,
    )
    .expect("EWD998 Inv should compile natively");

    let f = unsafe {
        let raw = lib
            .get_symbol(SYMBOL)
            .expect("compiled EWD998 Inv symbol should be present");
        std::mem::transmute::<*mut std::ffi::c_void, JitInvariantFn>(raw)
    };

    (lib, f)
}

fn assert_native_inv_ok(layout: &StateLayout, f: JitInvariantFn, state: &[i64]) {
    assert_eq!(state.len(), layout.compact_slot_count());
    let out = eval(f, state);
    assert_eq!(out.status, JitStatus::Ok, "native callout: {out:?}");
    assert_eq!(out.value, 1, "native callout: {out:?}");
}

#[test]
fn native_ewd998_inv_accepts_black_token_zero_counter_initial_state() {
    let layout = ewd998_layout();
    let (_lib, f) = compile_ewd998_inv(&layout);
    let white = i64::from(tla_core::intern_name("white").0);
    let black = i64::from(tla_core::intern_name("black").0);
    let mut initial_state = vec![
        0, 0, 0, // active
        white, white, white, // color
        0, 0, 0, // counter
        0, 0, 0, // pending
    ];
    initial_state.extend(token_tail_from_layout(&layout, 0, black, 0));

    assert_native_inv_ok(&layout, f, &initial_state);
}

#[test]
fn native_ewd998_inv_accepts_white_token_successor_state() {
    let layout = ewd998_layout();
    let (_lib, f) = compile_ewd998_inv(&layout);
    let white = i64::from(tla_core::intern_name("white").0);
    let black = i64::from(tla_core::intern_name("black").0);
    let mut successor_state = vec![
        0, 0, 0, // active
        white, black, black, // color
        0, 0, 0, // counter
        0, 0, 0, // pending
    ];
    successor_state.extend(token_tail_from_layout(&layout, 2, white, 0));

    assert_native_inv_ok(&layout, f, &successor_state);
}

#[test]
fn native_ewd998_inv_accepts_black_token_p4_only_state() {
    let layout = ewd998_layout();
    let (_lib, f) = compile_ewd998_inv(&layout);
    let white = i64::from(tla_core::intern_name("white").0);
    let black = i64::from(tla_core::intern_name("black").0);
    let mut p4_only_state = vec![
        0, 1, 0, // active: falsifies P1 for token.pos = 0
        white, white, white, // color: no process is black
        0, 0, 0, // counter: P2 remains false with token.q = 0
        0, 0, 0, // pending
    ];
    p4_only_state.extend(token_tail_from_layout(&layout, 0, black, 0));

    assert_native_inv_ok(&layout, f, &p4_only_state);
}
