// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Runtime fallback tests for compound-producing opcodes.
//!
//! Part of #3909 Phase 2: these opcodes are JIT-eligible but emit
//! FallbackNeeded at runtime because they produce compound values
//! (sets, sequences, records, functions) that cannot be represented
//! as a single i64 in the JIT register file.

use crate::abi::JitStatus;
use tla_tir::bytecode::{BytecodeFunction, Opcode};

use super::compile_and_run_no_state;

/// SetUnion emits FallbackNeeded at runtime.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_union_fallback() {
    let mut func = BytecodeFunction::new("set_union".to_string(), 2);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    func.emit(Opcode::SetUnion {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// SetIntersect emits FallbackNeeded at runtime.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_intersect_fallback() {
    let mut func = BytecodeFunction::new("set_intersect".to_string(), 2);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    func.emit(Opcode::SetIntersect {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// SetDiff emits FallbackNeeded at runtime.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_diff_fallback() {
    let mut func = BytecodeFunction::new("set_diff".to_string(), 2);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    func.emit(Opcode::SetDiff {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// Powerset emits FallbackNeeded at runtime.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_powerset_fallback() {
    let mut func = BytecodeFunction::new("powerset".to_string(), 1);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::Powerset { rd: 1, rs: 0 });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// RecordNew emits FallbackNeeded at runtime.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_new_fallback() {
    let mut func = BytecodeFunction::new("record_new".to_string(), 0);
    func.emit(Opcode::RecordNew {
        rd: 0,
        fields_start: 0,
        values_start: 0,
        count: 0,
    });
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// TupleNew emits FallbackNeeded at runtime.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_new_fallback() {
    let mut func = BytecodeFunction::new("tuple_new".to_string(), 0);
    func.emit(Opcode::TupleNew {
        rd: 0,
        start: 0,
        count: 0,
    });
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// SeqNew emits FallbackNeeded at runtime.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_new_fallback() {
    let mut func = BytecodeFunction::new("seq_new".to_string(), 0);
    func.emit(Opcode::SeqNew {
        rd: 0,
        start: 0,
        count: 0,
    });
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// FuncExcept emits FallbackNeeded at runtime.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_except_fallback() {
    let mut func = BytecodeFunction::new("func_except".to_string(), 2);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    func.emit(Opcode::LoadImm { rd: 2, value: 3 });
    func.emit(Opcode::FuncExcept {
        rd: 3,
        func: 0,
        path: 1,
        val: 2,
    });
    func.emit(Opcode::Ret { rs: 3 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// Call opcode emits FallbackNeeded at runtime.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_fallback() {
    let mut func = BytecodeFunction::new("call".to_string(), 1);
    func.emit(Opcode::Call {
        rd: 0,
        op_idx: 0,
        args_start: 1,
        argc: 0,
    });
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// ValueApply opcode emits FallbackNeeded at runtime.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_apply_fallback() {
    let mut func = BytecodeFunction::new("value_apply".to_string(), 2);
    func.emit(Opcode::ValueApply {
        rd: 0,
        func: 1,
        args_start: 2,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// Unchanged in invariant context emits FallbackNeeded at runtime.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_invariant_fallback() {
    let mut func = BytecodeFunction::new("unchanged_inv".to_string(), 0);
    func.emit(Opcode::Unchanged {
        rd: 0,
        start: 0,
        count: 1,
    });
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// Halt emits RuntimeError at runtime.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_halt_runtime_error() {
    let mut func = BytecodeFunction::new("halt".to_string(), 0);
    func.emit(Opcode::Halt);
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::RuntimeError);
}

/// SetPrimeMode emits FallbackNeeded at runtime.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_prime_mode_fallback() {
    let mut func = BytecodeFunction::new("spm".to_string(), 0);
    func.emit(Opcode::SetPrimeMode { enable: true });
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// Concat (polymorphic sequence/string concatenation) emits FallbackNeeded.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_concat_fallback() {
    let mut func = BytecodeFunction::new("concat".to_string(), 1);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    func.emit(Opcode::Concat {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// StrConcat emits FallbackNeeded.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_str_concat_fallback() {
    let mut func = BytecodeFunction::new("str_concat".to_string(), 1);
    func.emit(Opcode::LoadImm { rd: 0, value: 1 });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    func.emit(Opcode::StrConcat {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// MakeClosure emits FallbackNeeded.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_make_closure_fallback() {
    let mut func = BytecodeFunction::new("closure".to_string(), 1);
    func.emit(Opcode::MakeClosure {
        rd: 0,
        template_idx: 0,
        captures_start: 1,
        capture_count: 0,
    });
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// CallExternal emits FallbackNeeded.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_external_fallback() {
    let mut func = BytecodeFunction::new("callext".to_string(), 1);
    func.emit(Opcode::CallExternal {
        rd: 0,
        name_idx: 0,
        args_start: 1,
        argc: 0,
    });
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(out.status, JitStatus::FallbackNeeded);
}

/// Scalar-only paths execute natively even when the function contains
/// compound opcodes on other branches. This is the key value proposition:
/// the JIT handles the fast path, fallback only on compound paths.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scalar_path_avoids_fallback_with_compound_in_other_branch() {
    // IF TRUE THEN 42 ELSE SetUnion(...)
    // The TRUE path should execute natively and return 42.
    //
    // PC 0: LoadBool r0 = TRUE
    // PC 1: JumpFalse r0, +3 -> PC 4 (SetUnion)
    // PC 2: LoadImm r3 = 42       (TRUE path)
    // PC 3: Ret r3                 (TRUE path return)
    // PC 4: SetUnion r3 = r0 ∪ r1 (FALSE path — fallback)
    // PC 5: Ret r3                 (FALSE path return)
    let mut func = BytecodeFunction::new("branch_test".to_string(), 3);
    func.emit(Opcode::LoadBool { rd: 0, value: true });
    func.emit(Opcode::JumpFalse { rs: 0, offset: 3 });
    func.emit(Opcode::LoadImm { rd: 3, value: 42 });
    func.emit(Opcode::Ret { rs: 3 });
    func.emit(Opcode::SetUnion {
        rd: 3,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 3 });

    let out = compile_and_run_no_state(&func);
    assert_eq!(
        out.status,
        JitStatus::Ok,
        "scalar path should execute natively"
    );
    assert_eq!(out.value, 42);
}

/// When the FALSE branch is taken and hits a compound op, FallbackNeeded.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compound_path_triggers_fallback() {
    // IF FALSE THEN 42 ELSE SetUnion(...)
    //
    // PC 0: LoadBool r0 = FALSE
    // PC 1: JumpFalse r0, +3 -> PC 4 (SetUnion)
    // PC 2: LoadImm r3 = 42       (TRUE path)
    // PC 3: Ret r3                 (TRUE path return)
    // PC 4: SetUnion r3 = r0 ∪ r1 (FALSE path — fallback)
    // PC 5: Ret r3                 (FALSE path return)
    let mut func = BytecodeFunction::new("branch_test2".to_string(), 3);
    func.emit(Opcode::LoadBool {
        rd: 0,
        value: false,
    });
    func.emit(Opcode::JumpFalse { rs: 0, offset: 3 });
    func.emit(Opcode::LoadImm { rd: 3, value: 42 });
    func.emit(Opcode::Ret { rs: 3 });
    func.emit(Opcode::SetUnion {
        rd: 3,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 3 });

    let out = compile_and_run_no_state(&func);
    // After the JumpFalse at PC 1, conjuncts_passed is 1, so the
    // compound SetUnion op emits PartialPass rather than FallbackNeeded.
    assert!(
        out.status == JitStatus::FallbackNeeded || out.status == JitStatus::PartialPass,
        "compound path should trigger fallback or partial pass, got {:?}",
        out.status
    );
}
