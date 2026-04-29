// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Native LLVM2 regression for compact `Seq(SUBSET allowed)` invariant checks.

#![cfg(feature = "native")]

use tla_jit_abi::{
    CompoundLayout, JitCallOut, JitInvariantFn, JitStatus, SetBitmaskElement, StateLayout,
    VarLayout,
};
use tla_tir::bytecode::{BuiltinOp, BytecodeChunk, BytecodeFunction, ConstantPool, Opcode};

fn seq_subset_proc_invariant() -> BytecodeFunction {
    let mut func = BytecodeFunction::new("seq_subset_proc_native".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::LoadVar { rd: 1, var_idx: 1 });
    func.emit(Opcode::Powerset { rd: 2, rs: 1 });
    func.emit(Opcode::CallBuiltin {
        rd: 3,
        builtin: BuiltinOp::Seq,
        args_start: 2,
        argc: 1,
    });
    func.emit(Opcode::SetIn {
        rd: 4,
        elem: 0,
        set: 3,
    });
    func.emit(Opcode::Ret { rs: 4 });
    func
}

fn proc_set_bitmask_layout() -> CompoundLayout {
    CompoundLayout::SetBitmask {
        universe: vec![
            SetBitmaskElement::Int(1),
            SetBitmaskElement::Int(2),
            SetBitmaskElement::Int(3),
        ],
    }
}

fn seq_subset_proc_layout() -> StateLayout {
    StateLayout::new(vec![
        VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(proc_set_bitmask_layout()),
            element_count: Some(3),
        }),
        VarLayout::Compound(proc_set_bitmask_layout()),
    ])
}

#[test]
fn native_invariant_accepts_and_rejects_compact_seq_subset_proc() {
    let func = seq_subset_proc_invariant();
    let layout = seq_subset_proc_layout();
    let lib = tla_llvm2::compile_invariant_native_with_constants_and_layout(
        &func,
        "seq_subset_proc_native",
        &ConstantPool::new(),
        &layout,
        tla_llvm2::OptLevel::O1,
    )
    .expect("Seq(SUBSET allowed) invariant should compile natively");

    let f: JitInvariantFn = unsafe {
        let raw = lib
            .get_symbol("seq_subset_proc_native")
            .expect("compiled invariant symbol should be present");
        std::mem::transmute::<*mut std::ffi::c_void, JitInvariantFn>(raw)
    };

    let eval = |state: &[i64]| {
        let mut out = JitCallOut::default();
        unsafe { f(&mut out, state.as_ptr(), state.len() as u32) };
        out
    };

    let assert_true = |out: JitCallOut| {
        assert_eq!(out.status, JitStatus::Ok);
        assert_eq!(out.value, 1);
    };
    let assert_rejected = |out: JitCallOut| match out.status {
        JitStatus::Ok => assert_eq!(out.value, 0),
        JitStatus::RuntimeError => {}
        status => panic!("unexpected JIT status for invalid Seq(SUBSET allowed): {status:?}"),
    };
    let assert_false = |out: JitCallOut| {
        assert_eq!(out.status, JitStatus::Ok);
        assert_eq!(out.value, 0);
    };
    let assert_runtime_error = |out: JitCallOut| {
        assert_eq!(out.status, JitStatus::RuntimeError);
    };

    assert_true(eval(&[3, 1, 5, 7, 7]));
    assert_true(eval(&[0, 8, 8, 8, 0]));
    assert_false(eval(&[1, 4, 0, 0, 3]));
    assert_runtime_error(eval(&[4, 1, 2, 4, 7]));
    assert_runtime_error(eval(&[-1, 0, 0, 0, 7]));
    assert_rejected(eval(&[1, 8, 0, 0, 7]));
    assert_rejected(eval(&[3, 1, 8, 0, 7]));
}

fn called_interval_return_chunk() -> (BytecodeChunk, usize) {
    let mut chunk = BytecodeChunk::new();

    let mut interval_domain = BytecodeFunction::new("IntervalDomain".to_string(), 0);
    interval_domain.emit(Opcode::LoadImm { rd: 0, value: 1 });
    interval_domain.emit(Opcode::LoadImm { rd: 1, value: 3 });
    interval_domain.emit(Opcode::Range {
        rd: 2,
        lo: 0,
        hi: 1,
    });
    interval_domain.emit(Opcode::Ret { rs: 2 });
    let interval_idx = chunk.add_function(interval_domain);

    let mut stack_clobber = BytecodeFunction::new("StackClobber".to_string(), 0);
    stack_clobber.emit(Opcode::LoadImm { rd: 0, value: 10 });
    stack_clobber.emit(Opcode::LoadImm { rd: 1, value: 40 });
    stack_clobber.emit(Opcode::Range {
        rd: 2,
        lo: 0,
        hi: 1,
    });
    stack_clobber.emit(Opcode::Ret { rs: 2 });
    let clobber_idx = chunk.add_function(stack_clobber);

    let mut entry = BytecodeFunction::new("called_interval_return_native".to_string(), 0);
    entry.emit(Opcode::Call {
        rd: 0,
        op_idx: interval_idx,
        args_start: 0,
        argc: 0,
    });
    entry.emit(Opcode::Call {
        rd: 1,
        op_idx: clobber_idx,
        args_start: 0,
        argc: 0,
    });
    entry.emit(Opcode::LoadImm { rd: 2, value: 2 });
    entry.emit(Opcode::SetIn {
        rd: 3,
        elem: 2,
        set: 0,
    });
    entry.emit(Opcode::LoadImm { rd: 4, value: 4 });
    entry.emit(Opcode::SetIn {
        rd: 5,
        elem: 4,
        set: 0,
    });
    entry.emit(Opcode::Not { rd: 6, rs: 5 });
    entry.emit(Opcode::And {
        rd: 7,
        r1: 3,
        r2: 6,
    });
    entry.emit(Opcode::Ret { rs: 7 });
    let entry_idx = usize::from(chunk.add_function(entry));

    (chunk, entry_idx)
}

fn called_materialized_set_returns_chunk() -> (BytecodeChunk, usize) {
    let mut chunk = BytecodeChunk::new();

    let mut exact_set_enum = BytecodeFunction::new("ExactSetEnum".to_string(), 0);
    exact_set_enum.emit(Opcode::LoadImm { rd: 0, value: 2 });
    exact_set_enum.emit(Opcode::LoadImm { rd: 1, value: 4 });
    exact_set_enum.emit(Opcode::SetEnum {
        rd: 2,
        start: 0,
        count: 2,
    });
    exact_set_enum.emit(Opcode::Ret { rs: 2 });
    let exact_set_enum_idx = chunk.add_function(exact_set_enum);

    let mut materialized_set_diff = BytecodeFunction::new("MaterializedSetDiff".to_string(), 1);
    materialized_set_diff.emit(Opcode::LoadImm { rd: 1, value: 1 });
    materialized_set_diff.emit(Opcode::LoadImm { rd: 2, value: 4 });
    materialized_set_diff.emit(Opcode::Range {
        rd: 3,
        lo: 1,
        hi: 2,
    });
    materialized_set_diff.emit(Opcode::SetEnum {
        rd: 4,
        start: 0,
        count: 1,
    });
    materialized_set_diff.emit(Opcode::SetDiff {
        rd: 5,
        r1: 3,
        r2: 4,
    });
    materialized_set_diff.emit(Opcode::Ret { rs: 5 });
    let materialized_set_diff_idx = chunk.add_function(materialized_set_diff);

    let mut stack_clobber = BytecodeFunction::new("SetStackClobber".to_string(), 0);
    stack_clobber.emit(Opcode::LoadImm { rd: 0, value: 10 });
    stack_clobber.emit(Opcode::LoadImm { rd: 1, value: 20 });
    stack_clobber.emit(Opcode::LoadImm { rd: 2, value: 30 });
    stack_clobber.emit(Opcode::SetEnum {
        rd: 3,
        start: 0,
        count: 3,
    });
    stack_clobber.emit(Opcode::Ret { rs: 3 });
    let clobber_idx = chunk.add_function(stack_clobber);

    let mut entry = BytecodeFunction::new("called_materialized_set_returns_native".to_string(), 0);
    entry.emit(Opcode::Call {
        rd: 0,
        op_idx: exact_set_enum_idx,
        args_start: 0,
        argc: 0,
    });
    entry.emit(Opcode::LoadImm { rd: 1, value: 2 });
    entry.emit(Opcode::Call {
        rd: 2,
        op_idx: materialized_set_diff_idx,
        args_start: 1,
        argc: 1,
    });
    entry.emit(Opcode::Call {
        rd: 3,
        op_idx: clobber_idx,
        args_start: 0,
        argc: 0,
    });

    entry.emit(Opcode::LoadImm { rd: 4, value: 2 });
    entry.emit(Opcode::SetIn {
        rd: 5,
        elem: 4,
        set: 0,
    });
    entry.emit(Opcode::LoadImm { rd: 6, value: 4 });
    entry.emit(Opcode::SetIn {
        rd: 7,
        elem: 6,
        set: 0,
    });
    entry.emit(Opcode::LoadImm { rd: 8, value: 3 });
    entry.emit(Opcode::SetIn {
        rd: 9,
        elem: 8,
        set: 0,
    });
    entry.emit(Opcode::Not { rd: 10, rs: 9 });
    entry.emit(Opcode::LoadImm { rd: 11, value: 10 });
    entry.emit(Opcode::SetIn {
        rd: 12,
        elem: 11,
        set: 0,
    });
    entry.emit(Opcode::Not { rd: 13, rs: 12 });
    entry.emit(Opcode::And {
        rd: 14,
        r1: 5,
        r2: 7,
    });
    entry.emit(Opcode::And {
        rd: 15,
        r1: 14,
        r2: 10,
    });
    entry.emit(Opcode::And {
        rd: 16,
        r1: 15,
        r2: 13,
    });

    entry.emit(Opcode::LoadImm { rd: 17, value: 1 });
    entry.emit(Opcode::SetIn {
        rd: 18,
        elem: 17,
        set: 2,
    });
    entry.emit(Opcode::LoadImm { rd: 19, value: 3 });
    entry.emit(Opcode::SetIn {
        rd: 20,
        elem: 19,
        set: 2,
    });
    entry.emit(Opcode::LoadImm { rd: 21, value: 4 });
    entry.emit(Opcode::SetIn {
        rd: 22,
        elem: 21,
        set: 2,
    });
    entry.emit(Opcode::LoadImm { rd: 23, value: 2 });
    entry.emit(Opcode::SetIn {
        rd: 24,
        elem: 23,
        set: 2,
    });
    entry.emit(Opcode::Not { rd: 25, rs: 24 });
    entry.emit(Opcode::LoadImm { rd: 26, value: 10 });
    entry.emit(Opcode::SetIn {
        rd: 27,
        elem: 26,
        set: 2,
    });
    entry.emit(Opcode::Not { rd: 28, rs: 27 });
    entry.emit(Opcode::LoadImm { rd: 29, value: 2 });
    entry.emit(Opcode::MulInt {
        rd: 30,
        r1: 7,
        r2: 29,
    });
    entry.emit(Opcode::AddInt {
        rd: 31,
        r1: 5,
        r2: 30,
    });
    entry.emit(Opcode::LoadImm { rd: 32, value: 4 });
    entry.emit(Opcode::MulInt {
        rd: 33,
        r1: 10,
        r2: 32,
    });
    entry.emit(Opcode::AddInt {
        rd: 34,
        r1: 31,
        r2: 33,
    });
    entry.emit(Opcode::LoadImm { rd: 35, value: 8 });
    entry.emit(Opcode::MulInt {
        rd: 36,
        r1: 13,
        r2: 35,
    });
    entry.emit(Opcode::AddInt {
        rd: 37,
        r1: 34,
        r2: 36,
    });
    entry.emit(Opcode::LoadImm { rd: 38, value: 16 });
    entry.emit(Opcode::MulInt {
        rd: 39,
        r1: 18,
        r2: 38,
    });
    entry.emit(Opcode::AddInt {
        rd: 40,
        r1: 37,
        r2: 39,
    });
    entry.emit(Opcode::LoadImm { rd: 41, value: 32 });
    entry.emit(Opcode::MulInt {
        rd: 42,
        r1: 20,
        r2: 41,
    });
    entry.emit(Opcode::AddInt {
        rd: 43,
        r1: 40,
        r2: 42,
    });
    entry.emit(Opcode::LoadImm { rd: 44, value: 64 });
    entry.emit(Opcode::MulInt {
        rd: 45,
        r1: 22,
        r2: 44,
    });
    entry.emit(Opcode::AddInt {
        rd: 46,
        r1: 43,
        r2: 45,
    });
    entry.emit(Opcode::LoadImm { rd: 47, value: 128 });
    entry.emit(Opcode::MulInt {
        rd: 48,
        r1: 25,
        r2: 47,
    });
    entry.emit(Opcode::AddInt {
        rd: 49,
        r1: 46,
        r2: 48,
    });
    entry.emit(Opcode::LoadImm { rd: 50, value: 256 });
    entry.emit(Opcode::MulInt {
        rd: 51,
        r1: 28,
        r2: 50,
    });
    entry.emit(Opcode::AddInt {
        rd: 52,
        r1: 49,
        r2: 51,
    });
    entry.emit(Opcode::Ret { rs: 52 });
    let entry_idx = usize::from(chunk.add_function(entry));

    (chunk, entry_idx)
}

#[test]
fn native_invariant_keeps_called_interval_return_alive_across_later_helper_call() {
    let (chunk, entry_idx) = called_interval_return_chunk();
    let entry = &chunk.functions[entry_idx];
    let layout = StateLayout::new(vec![]);
    let lib = tla_llvm2::compile_entry_invariant_native_with_chunk_and_layout(
        entry,
        &chunk,
        "called_interval_return_native",
        &layout,
        tla_llvm2::OptLevel::O1,
    )
    .expect("called Interval helper return should compile natively");

    let f: JitInvariantFn = unsafe {
        let raw = lib
            .get_symbol("called_interval_return_native")
            .expect("compiled invariant symbol should be present");
        std::mem::transmute::<*mut std::ffi::c_void, JitInvariantFn>(raw)
    };

    let mut out = JitCallOut::default();
    unsafe { f(&mut out, std::ptr::NonNull::<i64>::dangling().as_ptr(), 0) };
    assert_eq!(out.status, JitStatus::Ok);
    assert_eq!(out.value, 1);
}

#[test]
fn native_invariant_keeps_exact_and_bounded_set_returns_alive_across_later_helper_call() {
    let (chunk, entry_idx) = called_materialized_set_returns_chunk();
    let entry = &chunk.functions[entry_idx];
    let layout = StateLayout::new(vec![]);

    for opt_level in [tla_llvm2::OptLevel::O1, tla_llvm2::OptLevel::O3] {
        let lib = tla_llvm2::compile_entry_invariant_native_with_chunk_and_layout(
            entry,
            &chunk,
            "called_materialized_set_returns_native",
            &layout,
            opt_level,
        )
        .unwrap_or_else(|err| {
            panic!(
                "called materialized set returns should compile natively at {opt_level:?}: {err}"
            )
        });

        let f: JitInvariantFn = unsafe {
            let raw = lib
                .get_symbol("called_materialized_set_returns_native")
                .expect("compiled invariant symbol should be present");
            std::mem::transmute::<*mut std::ffi::c_void, JitInvariantFn>(raw)
        };

        let mut out = JitCallOut::default();
        unsafe { f(&mut out, std::ptr::NonNull::<i64>::dangling().as_ptr(), 0) };
        assert_eq!(
            out.status,
            JitStatus::Ok,
            "native call failed at {opt_level:?}: status={:?} value={} err_kind={:?}",
            out.status,
            out.value,
            out.err_kind
        );
        assert_eq!(
            out.value, 511,
            "materialized helper return payload was not preserved at {opt_level:?}: status={:?} value={} err_kind={:?}",
            out.status,
            out.value,
            out.err_kind
        );
    }
}
