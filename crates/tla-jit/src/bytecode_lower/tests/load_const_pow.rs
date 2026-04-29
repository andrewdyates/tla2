// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for LoadConst scalar constants (Phase 2.1) and PowInt (Phase 2.2).

use super::*;
use crate::bytecode_lower::eligibility::{check_eligibility, check_eligibility_with_constants};
use tla_value::Value;

// ============================================================
// LoadConst eligibility
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_const_smallint_eligible_with_pool() {
    let mut pool = ConstantPool::new();
    let idx = pool.add_value(Value::SmallInt(42));

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadConst { rd: 0, idx });
    func.emit(Opcode::Ret { rs: 0 });

    // Without pool: still eligible (LoadConst emits FallbackNeeded at runtime)
    assert!(check_eligibility(&func).is_ok());

    // With pool: eligible (SmallInt is scalar, compiled to native i64)
    assert!(check_eligibility_with_constants(&func, Some(&pool)).is_ok());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_const_bool_eligible_with_pool() {
    let mut pool = ConstantPool::new();
    let idx = pool.add_value(Value::Bool(true));

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadConst { rd: 0, idx });
    func.emit(Opcode::Ret { rs: 0 });

    assert!(check_eligibility_with_constants(&func, Some(&pool)).is_ok());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_const_string_ineligible() {
    let mut pool = ConstantPool::new();
    let idx = pool.add_value(Value::String(std::sync::Arc::from("hello")));

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadConst { rd: 0, idx });
    func.emit(Opcode::Ret { rs: 0 });

    // String constants are now eligible: the JIT emits FallbackNeeded at runtime
    // for compound constants, so the eligibility gate no longer rejects them.
    assert!(
        check_eligibility_with_constants(&func, Some(&pool)).is_ok(),
        "LoadConst with string should be eligible (emits FallbackNeeded at runtime)"
    );
}

// ============================================================
// LoadConst lowering
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_const_smallint_lowering() {
    let mut pool = ConstantPool::new();
    let idx = pool.add_value(Value::SmallInt(99));

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadConst { rd: 0, idx });
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_with_constants_and_run_no_state(&func, &pool);
    assert!(out.is_ok());
    assert_eq!(out.value, 99);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_const_bool_true_lowering() {
    let mut pool = ConstantPool::new();
    let idx = pool.add_value(Value::Bool(true));

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadConst { rd: 0, idx });
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_with_constants_and_run_no_state(&func, &pool);
    assert!(out.is_ok());
    assert_eq!(out.value, 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_const_bool_false_lowering() {
    let mut pool = ConstantPool::new();
    let idx = pool.add_value(Value::Bool(false));

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadConst { rd: 0, idx });
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_with_constants_and_run_no_state(&func, &pool);
    assert!(out.is_ok());
    assert_eq!(out.value, 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_const_negative_int_lowering() {
    let mut pool = ConstantPool::new();
    let idx = pool.add_value(Value::SmallInt(-42));

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadConst { rd: 0, idx });
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_with_constants_and_run_no_state(&func, &pool);
    assert!(out.is_ok());
    assert_eq!(out.value, -42);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_const_with_arithmetic() {
    // LoadConst(42) + LoadImm(8) = 50
    let mut pool = ConstantPool::new();
    let idx = pool.add_value(Value::SmallInt(42));

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadConst { rd: 0, idx });
    func.emit(Opcode::LoadImm { rd: 1, value: 8 });
    func.emit(Opcode::AddInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_with_constants_and_run_no_state(&func, &pool);
    assert!(out.is_ok());
    assert_eq!(out.value, 50);
}

// ============================================================
// PowInt eligibility
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pow_int_eligible() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 2 });
    func.emit(Opcode::LoadImm { rd: 1, value: 10 });
    func.emit(Opcode::PowInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    assert!(check_eligibility(&func).is_ok());
}

// ============================================================
// PowInt lowering
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pow_int_basic() {
    // 2^10 = 1024
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 2 });
    func.emit(Opcode::LoadImm { rd: 1, value: 10 });
    func.emit(Opcode::PowInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 1024);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pow_int_zero_exponent() {
    // TLA+: x^0 = 1 for any x
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 42 });
    func.emit(Opcode::LoadImm { rd: 1, value: 0 });
    func.emit(Opcode::PowInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 1, "x^0 = 1 for any x");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pow_int_zero_base_zero_exp() {
    // TLA+: 0^0 = 1
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 0 });
    func.emit(Opcode::LoadImm { rd: 1, value: 0 });
    func.emit(Opcode::PowInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 1, "0^0 = 1 in TLA+");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pow_int_one_exponent() {
    // x^1 = x
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 7 });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::PowInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 7);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pow_int_negative_exponent() {
    // Negative exponent: returns 0 (TLA+ convention)
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 2 });
    func.emit(Opcode::LoadImm { rd: 1, value: -3 });
    func.emit(Opcode::PowInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 0, "negative exponent yields 0");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pow_int_large_exponent() {
    // 3^20 = 3,486,784,401
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 3 });
    func.emit(Opcode::LoadImm { rd: 1, value: 20 });
    func.emit(Opcode::PowInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 3_486_784_401);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pow_int_negative_base_even_exp() {
    // (-2)^4 = 16
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: -2 });
    func.emit(Opcode::LoadImm { rd: 1, value: 4 });
    func.emit(Opcode::PowInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 16);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pow_int_negative_base_odd_exp() {
    // (-2)^3 = -8
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: -2 });
    func.emit(Opcode::LoadImm { rd: 1, value: 3 });
    func.emit(Opcode::PowInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, -8);
}

// ============================================================
// Combined LoadConst + PowInt
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_const_and_pow_int_combined() {
    // Load base=3 from constant pool, exp=4 from LoadImm, compute 3^4 = 81
    let mut pool = ConstantPool::new();
    let idx = pool.add_value(Value::SmallInt(3));

    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadConst { rd: 0, idx });
    func.emit(Opcode::LoadImm { rd: 1, value: 4 });
    func.emit(Opcode::PowInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_with_constants_and_run_no_state(&func, &pool);
    assert!(out.is_ok());
    assert_eq!(out.value, 81, "3^4 = 81");
}

// ============================================================
// jit_pow_i64 direct tests
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_jit_pow_i64_helper_directly() {
    use crate::bytecode_lower::scalar_ops::jit_pow_i64;

    assert_eq!(jit_pow_i64(2, 0), 1);
    assert_eq!(jit_pow_i64(2, 1), 2);
    assert_eq!(jit_pow_i64(2, 10), 1024);
    assert_eq!(jit_pow_i64(0, 0), 1);
    assert_eq!(jit_pow_i64(0, 5), 0);
    assert_eq!(jit_pow_i64(1, 100), 1);
    assert_eq!(jit_pow_i64(-1, 3), -1);
    assert_eq!(jit_pow_i64(-1, 4), 1);
    assert_eq!(jit_pow_i64(2, -1), 0);
    assert_eq!(jit_pow_i64(3, 20), 3_486_784_401);
}
