// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Native LLVM2 regression for compact EWD-style `pending -> Sum` helper calls.

#![cfg(feature = "native")]

use tla_jit_abi::{CompoundLayout, JitCallOut, JitInvariantFn, JitStatus, StateLayout, VarLayout};
use tla_tir::bytecode::{BuiltinOp, BytecodeChunk, BytecodeFunction, Opcode};

fn pending_sum_chunk() -> (BytecodeChunk, usize) {
    let mut chunk = BytecodeChunk::new();

    let mut sum = BytecodeFunction::new("Sum".to_string(), 2);
    sum.emit(Opcode::CallBuiltin {
        rd: 2,
        builtin: BuiltinOp::FoldFunctionOnSetSum,
        args_start: 0,
        argc: 2,
    });
    sum.emit(Opcode::Ret { rs: 2 });
    let sum_idx = chunk.add_function(sum);

    let mut inv = BytecodeFunction::new("ewd_pending_sum_native".to_string(), 0);
    inv.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    inv.emit(Opcode::LoadImm { rd: 2, value: 0 });
    inv.emit(Opcode::LoadImm { rd: 3, value: 2 });
    inv.emit(Opcode::Range {
        rd: 1,
        lo: 2,
        hi: 3,
    });
    inv.emit(Opcode::Call {
        rd: 4,
        op_idx: sum_idx,
        args_start: 0,
        argc: 2,
    });
    inv.emit(Opcode::LoadImm { rd: 5, value: 6 });
    inv.emit(Opcode::Eq {
        rd: 6,
        r1: 4,
        r2: 5,
    });
    inv.emit(Opcode::Ret { rs: 6 });
    let entry_idx = usize::from(chunk.add_function(inv));

    (chunk, entry_idx)
}

fn pending_layout() -> StateLayout {
    StateLayout::new(vec![VarLayout::Compound(CompoundLayout::Function {
        key_layout: Box::new(CompoundLayout::Int),
        value_layout: Box::new(CompoundLayout::Int),
        pair_count: Some(3),
        domain_lo: Some(0),
    })])
}

#[test]
fn native_invariant_materializes_compact_pending_before_sum_helper() {
    let (chunk, entry_idx) = pending_sum_chunk();
    let entry = &chunk.functions[entry_idx];
    let layout = pending_layout();
    let lib = tla_llvm2::compile_entry_invariant_native_with_chunk_and_layout(
        entry,
        &chunk,
        "ewd_pending_sum_native",
        &layout,
        tla_llvm2::OptLevel::O1,
    )
    .expect("EWD-style pending Sum invariant should compile natively");

    let f: JitInvariantFn = unsafe {
        let raw = lib
            .get_symbol("ewd_pending_sum_native")
            .expect("compiled invariant symbol should be present");
        std::mem::transmute::<*mut std::ffi::c_void, JitInvariantFn>(raw)
    };

    let eval = |state: &[i64]| {
        let mut out = JitCallOut::default();
        unsafe { f(&mut out, state.as_ptr(), state.len() as u32) };
        assert_eq!(out.status, JitStatus::Ok);
        out.value
    };

    assert_eq!(eval(&[1, 2, 3]), 1);
    assert_eq!(eval(&[1, 2, 4]), 0);
}
