// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for CallBuiltin JIT lowering (Phase 2.3).
//!
//! Tests both the fallback path (no compound layout) and the native path
//! (with compound layout providing direct state buffer access).

use super::*;
use crate::abi::JitStatus;
use crate::bytecode_lower::BytecodeLowerer;
use crate::compound_layout::{CompoundLayout, StateLayout, VarLayout, TAG_INT, TAG_SEQ, TAG_SET};
use tla_tir::bytecode::BuiltinOp;

// ============================================================
// CallBuiltin fallback (no layout — emits FallbackNeeded)
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_cardinality_fallback_no_layout() {
    // Without compound layout info, CallBuiltin should emit FallbackNeeded.
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Cardinality,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    // Compile without layout — should produce FallbackNeeded
    let out = compile_and_run(&func, &[42]);
    assert_eq!(
        out.status,
        JitStatus::FallbackNeeded,
        "Cardinality without layout should fallback"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_len_fallback_no_layout() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Len,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_and_run(&func, &[42]);
    assert_eq!(
        out.status,
        JitStatus::FallbackNeeded,
        "Len without layout should fallback"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_is_finite_set_always_true() {
    // In TLA+ model checking, all materialized sets are finite.
    // IsFiniteSet always returns TRUE (1) regardless of layout info.
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::IsFiniteSet,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_and_run(&func, &[42]);
    assert!(out.is_ok(), "IsFiniteSet should always succeed");
    assert_eq!(out.value, 1, "IsFiniteSet always returns TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_head_fallback_no_layout() {
    // Without compound layout info, Head falls back to the interpreter.
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Head,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_and_run(&func, &[42]);
    assert_eq!(
        out.status,
        JitStatus::FallbackNeeded,
        "Head without layout should fallback"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_tail_always_fallback() {
    // Tail produces a new sequence — always fallback.
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Tail,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_and_run(&func, &[42]);
    assert_eq!(
        out.status,
        JitStatus::FallbackNeeded,
        "Tail should always fallback"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_append_always_fallback() {
    // Append produces a new sequence — always fallback.
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Append,
        args_start: 0,
        argc: 2,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_and_run(&func, &[42]);
    assert_eq!(
        out.status,
        JitStatus::FallbackNeeded,
        "Append should always fallback"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_subseq_always_fallback() {
    // SubSeq produces a new sequence — always fallback.
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::SubSeq,
        args_start: 0,
        argc: 3,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_and_run(&func, &[42]);
    assert_eq!(
        out.status,
        JitStatus::FallbackNeeded,
        "SubSeq should always fallback"
    );
}

// ============================================================
// CallBuiltin with compound layout (native lowering)
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_cardinality_native_with_layout() {
    // Build a state buffer with a set: {1, 2, 3}
    // Layout: [TAG_SET, 3, TAG_INT, 1, TAG_INT, 2, TAG_INT, 3]
    let state: Vec<i64> = vec![TAG_SET, 3, TAG_INT, 1, TAG_INT, 2, TAG_INT, 3];

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Cardinality,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    // Build state layout: var 0 is a compound set of ints
    let set_layout = CompoundLayout::Set {
        element_layout: Box::new(CompoundLayout::Int),
        element_count: None,
    };
    let layout = StateLayout::new(vec![VarLayout::Compound(set_layout)]);

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let domains = crate::bytecode_lower::QuantifierDomains::new();
    let jit_fn = lowerer
        .compile_invariant_with_layout(&func, &domains, &layout, &[])
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }

    assert!(out.is_ok(), "Cardinality with layout should succeed");
    assert_eq!(out.value, 3, "Cardinality({{1,2,3}}) = 3");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_cardinality_empty_set() {
    // Empty set: [TAG_SET, 0]
    let state: Vec<i64> = vec![TAG_SET, 0];

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Cardinality,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let set_layout = CompoundLayout::Set {
        element_layout: Box::new(CompoundLayout::Int),
        element_count: None,
    };
    let layout = StateLayout::new(vec![VarLayout::Compound(set_layout)]);

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let domains = crate::bytecode_lower::QuantifierDomains::new();
    let jit_fn = lowerer
        .compile_invariant_with_layout(&func, &domains, &layout, &[])
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }

    assert!(out.is_ok(), "Cardinality with layout should succeed");
    assert_eq!(out.value, 0, "Cardinality(empty set) = 0");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_len_native_sequence() {
    // Sequence <<10, 20, 30>>: [TAG_SEQ, 3, TAG_INT, 10, TAG_INT, 20, TAG_INT, 30]
    let state: Vec<i64> = vec![TAG_SEQ, 3, TAG_INT, 10, TAG_INT, 20, TAG_INT, 30];

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Len,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let seq_layout = CompoundLayout::Sequence {
        element_layout: Box::new(CompoundLayout::Int),
        element_count: None,
    };
    let layout = StateLayout::new(vec![VarLayout::Compound(seq_layout)]);

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let domains = crate::bytecode_lower::QuantifierDomains::new();
    let jit_fn = lowerer
        .compile_invariant_with_layout(&func, &domains, &layout, &[])
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }

    assert!(out.is_ok(), "Len with seq layout should succeed");
    assert_eq!(out.value, 3, "Len(<<10, 20, 30>>) = 3");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_is_finite_set_native() {
    // Any set with known layout: IsFiniteSet always returns TRUE
    let state: Vec<i64> = vec![
        TAG_SET, 5, TAG_INT, 1, TAG_INT, 2, TAG_INT, 3, TAG_INT, 4, TAG_INT, 5,
    ];

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::IsFiniteSet,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let set_layout = CompoundLayout::Set {
        element_layout: Box::new(CompoundLayout::Int),
        element_count: None,
    };
    let layout = StateLayout::new(vec![VarLayout::Compound(set_layout)]);

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let domains = crate::bytecode_lower::QuantifierDomains::new();
    let jit_fn = lowerer
        .compile_invariant_with_layout(&func, &domains, &layout, &[])
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }

    assert!(out.is_ok(), "IsFiniteSet with set layout should succeed");
    assert_eq!(out.value, 1, "IsFiniteSet of any materialized set is TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_cardinality_with_comparison() {
    // Cardinality(S) > 2 where S = {1, 2, 3}
    let state: Vec<i64> = vec![TAG_SET, 3, TAG_INT, 1, TAG_INT, 2, TAG_INT, 3];

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Cardinality,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::LoadImm { rd: 2, value: 2 });
    func.emit(Opcode::GtInt {
        rd: 3,
        r1: 1,
        r2: 2,
    });
    func.emit(Opcode::Ret { rs: 3 });

    let set_layout = CompoundLayout::Set {
        element_layout: Box::new(CompoundLayout::Int),
        element_count: None,
    };
    let layout = StateLayout::new(vec![VarLayout::Compound(set_layout)]);

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let domains = crate::bytecode_lower::QuantifierDomains::new();
    let jit_fn = lowerer
        .compile_invariant_with_layout(&func, &domains, &layout, &[])
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }

    assert!(out.is_ok(), "Cardinality + comparison should succeed");
    assert_eq!(out.value, 1, "Cardinality({{1,2,3}}) > 2 is TRUE");
}

// ============================================================
// Head native lowering with compound layout
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_head_native_int_sequence() {
    // Sequence <<10, 20, 30>>: [TAG_SEQ, 3, TAG_INT, 10, TAG_INT, 20, TAG_INT, 30]
    let state: Vec<i64> = vec![TAG_SEQ, 3, TAG_INT, 10, TAG_INT, 20, TAG_INT, 30];

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Head,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let seq_layout = CompoundLayout::Sequence {
        element_layout: Box::new(CompoundLayout::Int),
        element_count: None,
    };
    let layout = StateLayout::new(vec![VarLayout::Compound(seq_layout)]);

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let domains = crate::bytecode_lower::QuantifierDomains::new();
    let jit_fn = lowerer
        .compile_invariant_with_layout(&func, &domains, &layout, &[])
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }

    assert!(out.is_ok(), "Head with seq layout should succeed");
    assert_eq!(out.value, 10, "Head(<<10, 20, 30>>) = 10");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_head_native_single_element() {
    // Sequence <<42>>: [TAG_SEQ, 1, TAG_INT, 42]
    let state: Vec<i64> = vec![TAG_SEQ, 1, TAG_INT, 42];

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Head,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let seq_layout = CompoundLayout::Sequence {
        element_layout: Box::new(CompoundLayout::Int),
        element_count: None,
    };
    let layout = StateLayout::new(vec![VarLayout::Compound(seq_layout)]);

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let domains = crate::bytecode_lower::QuantifierDomains::new();
    let jit_fn = lowerer
        .compile_invariant_with_layout(&func, &domains, &layout, &[])
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }

    assert!(out.is_ok(), "Head of single-element seq should succeed");
    assert_eq!(out.value, 42, "Head(<<42>>) = 42");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_head_empty_seq_fallback() {
    // Empty sequence <<>>: [TAG_SEQ, 0]
    // Head of empty seq is an error — should fallback to interpreter.
    let state: Vec<i64> = vec![TAG_SEQ, 0];

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Head,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let seq_layout = CompoundLayout::Sequence {
        element_layout: Box::new(CompoundLayout::Int),
        element_count: None,
    };
    let layout = StateLayout::new(vec![VarLayout::Compound(seq_layout)]);

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let domains = crate::bytecode_lower::QuantifierDomains::new();
    let jit_fn = lowerer
        .compile_invariant_with_layout(&func, &domains, &layout, &[])
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }

    assert_eq!(
        out.status,
        JitStatus::FallbackNeeded,
        "Head of empty seq should fallback for proper error handling"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_head_native_bool_sequence() {
    // Sequence <<TRUE, FALSE>>: [TAG_SEQ, 2, TAG_BOOL, 1, TAG_BOOL, 0]
    use crate::compound_layout::TAG_BOOL;
    let state: Vec<i64> = vec![TAG_SEQ, 2, TAG_BOOL, 1, TAG_BOOL, 0];

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Head,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let seq_layout = CompoundLayout::Sequence {
        element_layout: Box::new(CompoundLayout::Bool),
        element_count: None,
    };
    let layout = StateLayout::new(vec![VarLayout::Compound(seq_layout)]);

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let domains = crate::bytecode_lower::QuantifierDomains::new();
    let jit_fn = lowerer
        .compile_invariant_with_layout(&func, &domains, &layout, &[])
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }

    assert!(out.is_ok(), "Head of bool seq should succeed");
    assert_eq!(out.value, 1, "Head(<<TRUE, FALSE>>) = TRUE (1)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_head_with_comparison() {
    // Head(seq) = 10 where seq = <<10, 20, 30>>
    let state: Vec<i64> = vec![TAG_SEQ, 3, TAG_INT, 10, TAG_INT, 20, TAG_INT, 30];

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Head,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::LoadImm { rd: 2, value: 10 });
    func.emit(Opcode::Eq {
        rd: 3,
        r1: 1,
        r2: 2,
    });
    func.emit(Opcode::Ret { rs: 3 });

    let seq_layout = CompoundLayout::Sequence {
        element_layout: Box::new(CompoundLayout::Int),
        element_count: None,
    };
    let layout = StateLayout::new(vec![VarLayout::Compound(seq_layout)]);

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let domains = crate::bytecode_lower::QuantifierDomains::new();
    let jit_fn = lowerer
        .compile_invariant_with_layout(&func, &domains, &layout, &[])
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }

    assert!(out.is_ok(), "Head + comparison should succeed");
    assert_eq!(out.value, 1, "Head(<<10,20,30>>) = 10 is TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_builtin_head_negative_value() {
    // Sequence <<-5, 100>>: [TAG_SEQ, 2, TAG_INT, -5, TAG_INT, 100]
    let state: Vec<i64> = vec![TAG_SEQ, 2, TAG_INT, -5, TAG_INT, 100];

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 });
    func.emit(Opcode::CallBuiltin {
        rd: 1,
        builtin: BuiltinOp::Head,
        args_start: 0,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 1 });

    let seq_layout = CompoundLayout::Sequence {
        element_layout: Box::new(CompoundLayout::Int),
        element_count: None,
    };
    let layout = StateLayout::new(vec![VarLayout::Compound(seq_layout)]);

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let domains = crate::bytecode_lower::QuantifierDomains::new();
    let jit_fn = lowerer
        .compile_invariant_with_layout(&func, &domains, &layout, &[])
        .expect("compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }

    assert!(out.is_ok(), "Head with negative value should succeed");
    assert_eq!(out.value, -5, "Head(<<-5, 100>>) = -5");
}
