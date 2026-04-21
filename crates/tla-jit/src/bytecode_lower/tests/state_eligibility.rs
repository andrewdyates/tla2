// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================
// State variable access
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_var() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 1 });
    func.emit(Opcode::Ret { rs: 0 });

    let state = [10i64, 32];
    let out = compile_and_run(&func, &state);
    assert!(out.is_ok());
    assert_eq!(out.value, 32);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_invariant_check_pattern() {
    // Typical invariant: x >= 0 /\ x <= 100
    let mut func = BytecodeFunction::new("TypeOK".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 }); // x
    func.emit(Opcode::LoadImm { rd: 1, value: 0 });
    func.emit(Opcode::GeInt {
        rd: 2,
        r1: 0,
        r2: 1,
    }); // x >= 0
    func.emit(Opcode::LoadImm { rd: 3, value: 100 });
    func.emit(Opcode::LeInt {
        rd: 4,
        r1: 0,
        r2: 3,
    }); // x <= 100
    func.emit(Opcode::And {
        rd: 5,
        r1: 2,
        r2: 4,
    }); // x >= 0 /\ x <= 100
    func.emit(Opcode::Ret { rs: 5 });

    // State where x = 50 → TRUE
    let out = compile_and_run(&func, &[50]);
    assert!(out.is_ok());
    assert_eq!(out.value, 1);

    // State where x = -1 → FALSE
    let out = compile_and_run(&func, &[-1]);
    assert!(out.is_ok());
    assert_eq!(out.value, 0);

    // State where x = 101 → FALSE
    let out = compile_and_run(&func, &[101]);
    assert!(out.is_ok());
    assert_eq!(out.value, 0);
}

// ============================================================
// Eligibility
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_call_compiles_with_fallback() {
    // Call is now JIT-eligible (emits FallbackNeeded at runtime).
    // Part of #3909 Phase 2.
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::Call {
        rd: 0,
        op_idx: 0,
        args_start: 1,
        argc: 0,
    });
    func.emit(Opcode::Ret { rs: 0 });

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let result = lowerer
        .try_compile_invariant(&func)
        .expect("should not error");
    assert!(
        result.is_some(),
        "Call should compile (emits FallbackNeeded)"
    );

    // Verify it produces FallbackNeeded at runtime
    let jit_fn = result.unwrap();
    let mut out = crate::abi::JitCallOut::default();
    unsafe { jit_fn(&mut out, std::ptr::null(), 0) };
    assert!(out.needs_fallback(), "Call should produce FallbackNeeded");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_apply_compiles_with_fallback() {
    // ValueApply is now JIT-eligible (emits FallbackNeeded at runtime).
    // Part of #3909 Phase 2.
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::ValueApply {
        rd: 0,
        func: 1,
        args_start: 2,
        argc: 1,
    });
    func.emit(Opcode::Ret { rs: 0 });

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let result = lowerer
        .try_compile_invariant(&func)
        .expect("should not error");
    assert!(
        result.is_some(),
        "ValueApply should compile (emits FallbackNeeded)"
    );

    // Verify it produces FallbackNeeded at runtime
    let jit_fn = result.unwrap();
    let mut out = crate::abi::JitCallOut::default();
    unsafe { jit_fn(&mut out, std::ptr::null(), 0) };
    assert!(
        out.needs_fallback(),
        "ValueApply should produce FallbackNeeded"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_try_compile_empty_returns_none() {
    // Empty functions remain ineligible.
    let func = BytecodeFunction::new("test".to_string(), 0);

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let result = lowerer
        .try_compile_invariant(&func)
        .expect("should not error");
    assert!(result.is_none(), "Empty function should be ineligible");
}

// ============================================================
// Combined: multi-variable invariant with branches
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multi_var_invariant_with_branch() {
    // IF x > 0 THEN y > 0 ELSE TRUE
    let mut func = BytecodeFunction::new("Inv".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 }); // PC 0: x
    func.emit(Opcode::LoadImm { rd: 1, value: 0 }); // PC 1
    func.emit(Opcode::GtInt {
        rd: 2,
        r1: 0,
        r2: 1,
    }); // PC 2: x > 0
    func.emit(Opcode::JumpFalse { rs: 2, offset: 4 }); // PC 3 → PC 7
                                                       // Then branch: y > 0
    func.emit(Opcode::LoadVar { rd: 3, var_idx: 1 }); // PC 4: y
    func.emit(Opcode::GtInt {
        rd: 4,
        r1: 3,
        r2: 1,
    }); // PC 5: y > 0
    func.emit(Opcode::Ret { rs: 4 }); // PC 6
                                      // Else branch: TRUE
    func.emit(Opcode::LoadBool { rd: 4, value: true }); // PC 7
    func.emit(Opcode::Ret { rs: 4 }); // PC 8

    // x=5, y=3 → TRUE
    assert_eq!(compile_and_run(&func, &[5, 3]).value, 1);
    // x=5, y=-1 → FALSE
    assert_eq!(compile_and_run(&func, &[5, -1]).value, 0);
    // x=-1, y=-1 → TRUE (else branch)
    assert_eq!(compile_and_run(&func, &[-1, -1]).value, 1);
}
