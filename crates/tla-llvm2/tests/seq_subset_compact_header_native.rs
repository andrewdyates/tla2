// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Native LLVM2 regression for malformed compact `Seq(SUBSET base)` headers.

#![cfg(feature = "native")]

use tla_jit_abi::{
    CompoundLayout, JitCallOut, JitInvariantFn, JitStatus, SetBitmaskElement, StateLayout,
    VarLayout,
};
use tla_tir::bytecode::{BuiltinOp, BytecodeFunction, ConstantPool, Opcode};

const SYMBOL: &str = "seq_subset_compact_header_native";

fn seq_subset_base_invariant() -> BytecodeFunction {
    let mut func = BytecodeFunction::new(SYMBOL.to_string(), 0);
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

fn compact_subset_base_layout() -> CompoundLayout {
    CompoundLayout::SetBitmask {
        universe: vec![
            SetBitmaskElement::Int(1),
            SetBitmaskElement::Int(2),
            SetBitmaskElement::Int(3),
        ],
    }
}

fn compact_seq_subset_state_layout() -> StateLayout {
    StateLayout::new(vec![
        VarLayout::Compound(CompoundLayout::Sequence {
            element_layout: Box::new(compact_subset_base_layout()),
            element_count: Some(3),
        }),
        VarLayout::Compound(compact_subset_base_layout()),
    ])
}

fn compile_invariant() -> (tla_llvm2::NativeLibrary, JitInvariantFn) {
    let func = seq_subset_base_invariant();
    let layout = compact_seq_subset_state_layout();
    let lib = tla_llvm2::compile_invariant_native_with_constants_and_layout(
        &func,
        SYMBOL,
        &ConstantPool::new(),
        &layout,
        tla_llvm2::OptLevel::O1,
    )
    .expect("Seq(SUBSET base) invariant should compile natively");

    unsafe {
        let raw = lib
            .get_symbol(SYMBOL)
            .expect("compiled invariant symbol should be present");
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
fn malformed_compact_seq_subset_lengths_trap_as_runtime_error() {
    let (_lib, f) = compile_invariant();

    let valid = eval(f, &[3, 1, 5, 7, 7]);
    assert_eq!(valid.status, JitStatus::Ok);
    assert_eq!(valid.value, 1);

    for (name, state) in [
        ("negative length", [-1, 0, 0, 0, 7]),
        ("over-capacity length", [4, 1, 2, 4, 7]),
    ] {
        let out = eval(f, &state);
        assert_eq!(
            out.status,
            JitStatus::RuntimeError,
            "{name} compact Seq(SUBSET base) header should trap"
        );
    }
}
