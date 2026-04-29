// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Native LLVM2 regressions for compact record-set TypeInvariant shapes.

#![cfg(feature = "native")]

use std::sync::Arc;

use num_bigint::BigInt;
use tla_jit_abi::{CompoundLayout, JitCallOut, JitInvariantFn, JitStatus, StateLayout, VarLayout};
use tla_tir::bytecode::{BytecodeChunk, BytecodeFunction, ConstantPool, Opcode};
use tla_value::value::{IntervalValue, Value};

const COFFEECAN_SYMBOL: &str = "coffeecan_record_set_typeinvariant_native";
const MCL_SYMBOL: &str = "mcl_nested_typeok_native_compile";

fn interval(lo: i64, hi: i64) -> Value {
    Value::Interval(Arc::new(IntervalValue::new(
        BigInt::from(lo),
        BigInt::from(hi),
    )))
}

fn coffeecan_typeinvariant() -> (BytecodeFunction, ConstantPool) {
    let mut pool = ConstantPool::new();
    let domain_idx = pool.add_value(Value::record_set([
        ("black", interval(0, 1000)),
        ("white", interval(0, 1000)),
    ]));

    let mut func = BytecodeFunction::new(COFFEECAN_SYMBOL.to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadConst {
        rd: 1,
        idx: domain_idx,
    });
    func.emit(Opcode::SetIn {
        rd: 2,
        elem: 0,
        set: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    (func, pool)
}

fn coffeecan_layout() -> StateLayout {
    StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Record {
        fields: vec![
            (tla_core::intern_name("black"), CompoundLayout::Int),
            (tla_core::intern_name("white"), CompoundLayout::Int),
        ],
    })])
}

fn compile_coffeecan_typeinvariant() -> (tla_llvm2::NativeLibrary, JitInvariantFn) {
    let (func, pool) = coffeecan_typeinvariant();
    let layout = coffeecan_layout();
    let lib = tla_llvm2::compile_invariant_native_with_constants_and_layout(
        &func,
        COFFEECAN_SYMBOL,
        &pool,
        &layout,
        tla_llvm2::OptLevel::O1,
    )
    .expect("CoffeeCan compact record-set TypeInvariant should compile natively");

    unsafe {
        let raw = lib
            .get_symbol(COFFEECAN_SYMBOL)
            .expect("compiled CoffeeCan invariant symbol should be present");
        (
            lib,
            std::mem::transmute::<*mut std::ffi::c_void, JitInvariantFn>(raw),
        )
    }
}

fn eval(f: JitInvariantFn, state: &[i64]) -> JitCallOut {
    let mut out = JitCallOut::default();
    unsafe { f(&mut out, state.as_ptr(), state.len() as u32) };
    out
}

#[test]
fn native_typeinvariant_executes_coffeecan_compact_record_layout() {
    let (_lib, f) = compile_coffeecan_typeinvariant();

    for state in [&[0, 0][..], &[500, 501], &[1000, 1000]] {
        let out = eval(f, state);
        assert_eq!(out.status, JitStatus::Ok);
        assert_eq!(out.value, 1, "valid compact CoffeeCan state {state:?}");
    }

    for state in [&[-1, 0][..], &[0, -1], &[1001, 0], &[0, 1001]] {
        let out = eval(f, state);
        assert_eq!(out.status, JitStatus::Ok);
        assert_eq!(out.value, 0, "invalid compact CoffeeCan state {state:?}");
    }
}

fn mcl_nested_typeok_chunk() -> (BytecodeChunk, usize) {
    let mut chunk = BytecodeChunk::new();

    let mut nat_override = BytecodeFunction::new("NatOverride".to_string(), 0);
    nat_override.emit(Opcode::LoadImm { rd: 0, value: 0 });
    nat_override.emit(Opcode::LoadImm { rd: 1, value: 7 });
    nat_override.emit(Opcode::Range {
        rd: 2,
        lo: 0,
        hi: 1,
    });
    nat_override.emit(Opcode::Ret { rs: 2 });
    let nat_idx = chunk.add_function(nat_override);

    let mut clock = BytecodeFunction::new("Clock".to_string(), 0);
    clock.emit(Opcode::Call {
        rd: 0,
        op_idx: nat_idx,
        args_start: 0,
        argc: 0,
    });
    clock.emit(Opcode::LoadImm { rd: 1, value: 0 });
    clock.emit(Opcode::SetEnum {
        rd: 2,
        start: 1,
        count: 1,
    });
    clock.emit(Opcode::SetDiff {
        rd: 3,
        r1: 0,
        r2: 2,
    });
    clock.emit(Opcode::Ret { rs: 3 });
    let clock_idx = chunk.add_function(clock);

    let mut typeok = BytecodeFunction::new(MCL_SYMBOL.to_string(), 0);
    typeok.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    typeok.emit(Opcode::LoadImm { rd: 1, value: 1 });
    typeok.emit(Opcode::LoadImm { rd: 2, value: 3 });
    typeok.emit(Opcode::Range {
        rd: 3,
        lo: 1,
        hi: 2,
    });
    typeok.emit(Opcode::Call {
        rd: 4,
        op_idx: clock_idx,
        args_start: 0,
        argc: 0,
    });
    typeok.emit(Opcode::FuncSet {
        rd: 5,
        domain: 3,
        range: 4,
    });
    typeok.emit(Opcode::SetIn {
        rd: 6,
        elem: 0,
        set: 5,
    });

    typeok.emit(Opcode::LoadVar { rd: 7, var_idx: 1 });
    typeok.emit(Opcode::Call {
        rd: 8,
        op_idx: nat_idx,
        args_start: 0,
        argc: 0,
    });
    typeok.emit(Opcode::FuncSet {
        rd: 9,
        domain: 3,
        range: 8,
    });
    typeok.emit(Opcode::FuncSet {
        rd: 10,
        domain: 3,
        range: 9,
    });
    typeok.emit(Opcode::SetIn {
        rd: 11,
        elem: 7,
        set: 10,
    });
    typeok.emit(Opcode::And {
        rd: 12,
        r1: 6,
        r2: 11,
    });
    typeok.emit(Opcode::Ret { rs: 12 });
    let entry_idx = usize::from(chunk.add_function(typeok));

    (chunk, entry_idx)
}

fn mcl_nested_typeok_layout() -> StateLayout {
    let proc_to_nat = CompoundLayout::Function {
        key_layout: Box::new(CompoundLayout::Int),
        value_layout: Box::new(CompoundLayout::Int),
        pair_count: Some(3),
        domain_lo: Some(1),
    };

    StateLayout::new(vec![
        VarLayout::Compound(proc_to_nat.clone()),
        VarLayout::Compound(CompoundLayout::Function {
            key_layout: Box::new(CompoundLayout::Int),
            value_layout: Box::new(proc_to_nat),
            pair_count: Some(3),
            domain_lo: Some(1),
        }),
    ])
}

#[test]
fn native_compile_only_mcl_nested_typeok() {
    let (chunk, entry_idx) = mcl_nested_typeok_chunk();
    let entry = &chunk.functions[entry_idx];
    let layout = mcl_nested_typeok_layout();
    let lib = tla_llvm2::compile_entry_invariant_native_with_chunk_and_layout(
        entry,
        &chunk,
        MCL_SYMBOL,
        &layout,
        tla_llvm2::OptLevel::O1,
    )
    .expect("MCL nested TypeOK should compile natively with compact function layouts");

    unsafe {
        lib.get_symbol(MCL_SYMBOL)
            .expect("compiled MCL TypeOK symbol should be present");
    }
}
