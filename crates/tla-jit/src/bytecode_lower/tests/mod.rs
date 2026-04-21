// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for bytecode → Cranelift lowerer.
//!
//! Each test builds a BytecodeFunction, compiles it via BytecodeLowerer,
//! and verifies the native function produces the expected result.

use crate::abi::JitCallOut;
use crate::bytecode_lower::BytecodeLowerer;
use tla_tir::bytecode::{BytecodeFunction, ConstantPool, Opcode};

/// Helper: compile a bytecode function and execute it with the given state array.
pub(super) fn compile_and_run(func: &BytecodeFunction, state: &[i64]) -> JitCallOut {
    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let jit_fn = lowerer
        .compile_invariant(func)
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }
    out
}

/// Helper: compile and run with no state.
pub(super) fn compile_and_run_no_state(func: &BytecodeFunction) -> JitCallOut {
    compile_and_run(func, &[])
}

/// Helper: compile with constant pool and run with no state.
pub(super) fn compile_with_constants_and_run_no_state(
    func: &BytecodeFunction,
    constants: &ConstantPool,
) -> JitCallOut {
    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let jit_fn = lowerer
        .compile_invariant_with_constants(func, constants)
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, [].as_ptr(), 0);
    }
    out
}

/// Helper: compile a next-state bytecode function and execute it.
pub(super) fn compile_and_run_next_state(
    func: &BytecodeFunction,
    state_in: &[i64],
) -> (JitCallOut, Vec<i64>) {
    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let jit_fn = lowerer
        .compile_next_state(func)
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    let mut state_out = vec![0i64; state_in.len()];
    unsafe {
        jit_fn(
            &mut out,
            state_in.as_ptr(),
            state_out.as_mut_ptr(),
            state_in.len() as u32,
        );
    }
    (out, state_out)
}

/// Helper: compile a next-state function with constants and state layout, then execute.
pub(super) fn compile_and_run_next_state_with_layout(
    func: &BytecodeFunction,
    state_in: &[i64],
    constants: &ConstantPool,
    state_layout: &crate::compound_layout::StateLayout,
) -> (JitCallOut, Vec<i64>) {
    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let empty_unchanged = crate::bytecode_lower::UnchangedVarMap::new();
    let jit_fn = lowerer
        .compile_next_state_with_layout(func, &empty_unchanged, Some(constants), Some(state_layout))
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    let mut state_out = vec![0i64; state_in.len()];
    unsafe {
        jit_fn(
            &mut out,
            state_in.as_ptr(),
            state_out.as_mut_ptr(),
            state_in.len() as u32,
        );
    }
    (out, state_out)
}

/// Helper: compile a next-state function with constants (no layout), then execute.
/// Used for testing ForallBegin with model value domains in action context.
/// Part of #3958.
pub(super) fn compile_and_run_next_state_with_constants(
    func: &BytecodeFunction,
    state_in: &[i64],
    constants: &ConstantPool,
) -> (JitCallOut, Vec<i64>) {
    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let empty_unchanged = crate::bytecode_lower::UnchangedVarMap::new();
    let jit_fn = lowerer
        .compile_next_state_with_unchanged_and_constants(func, &empty_unchanged, Some(constants))
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    let mut state_out = vec![0i64; state_in.len()];
    unsafe {
        jit_fn(
            &mut out,
            state_in.as_ptr(),
            state_out.as_mut_ptr(),
            state_in.len() as u32,
        );
    }
    (out, state_out)
}

/// Helper: compile with constant pool, field name IDs, and empty state layout.
/// Used for testing RecordGet/FuncApply/TupleGet on non-state compound values.
/// Part of #3949.
pub(super) fn compile_with_constants_and_field_ids_no_state(
    func: &BytecodeFunction,
    constants: &ConstantPool,
    field_name_ids: &[u32],
) -> JitCallOut {
    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let empty_layout = crate::compound_layout::StateLayout::new(vec![]);
    let jit_fn = lowerer
        .compile_invariant_with_constants_and_layout(func, constants, &empty_layout, field_name_ids)
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, [].as_ptr(), 0);
    }
    out
}

mod arithmetic;
mod call_builtin;
mod compound_const_access;
mod compound_fallback;
mod func_record;
mod load_const_pow;
mod logic_control;
mod next_state;
mod quantifier_loops;
mod record_new_native;
mod scalar_cmp;
mod set_membership;
mod set_quantifier_audit;
mod state_eligibility;
mod string_interning;
