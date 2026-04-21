// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::abi::JitRuntimeErrorKind;

// ============================================================
// Euclidean arithmetic edge cases (TLA+ semantics)
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mod_int_euclidean_positive() {
    // 7 % 3 = 1 (same as C)
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 7 });
    func.emit(Opcode::LoadImm { rd: 1, value: 3 });
    func.emit(Opcode::ModInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mod_int_euclidean_negative_dividend() {
    // TLA+: (-7) % 3 = 2 (Euclidean), NOT -1 (C truncated)
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: -7 });
    func.emit(Opcode::LoadImm { rd: 1, value: 3 });
    func.emit(Opcode::ModInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 2, "TLA+ Euclidean mod: (-7) % 3 = 2");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mod_int_euclidean_second_negative_dividend() {
    // (-10) % 3: srem = -1, r < 0, adjusted = -1 + 3 = 2
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: -10 });
    func.emit(Opcode::LoadImm { rd: 1, value: 3 });
    func.emit(Opcode::ModInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 2, "TLA+ Euclidean mod: (-10) % 3 = 2");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_div_euclidean_second_negative_dividend() {
    // Euclidean: -10 = 3 * (-4) + 2, so (-10) \div 3 = -4
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: -10 });
    func.emit(Opcode::LoadImm { rd: 1, value: 3 });
    func.emit(Opcode::IntDiv {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, -4, "TLA+ Euclidean div: (-10) \\div 3 = -4");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mod_int_exact_multiple() {
    // (-9) % 3 = 0 (exact multiple, no adjustment needed)
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: -9 });
    func.emit(Opcode::LoadImm { rd: 1, value: 3 });
    func.emit(Opcode::ModInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 0, "(-9) % 3 = 0");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_div_int_exact() {
    // TLA+ `/` on integers: 10 / 2 = 5 (exact division)
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 10 });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    func.emit(Opcode::DivInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 5);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_div_int_division_by_zero() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 10 });
    func.emit(Opcode::LoadImm { rd: 1, value: 0 });
    func.emit(Opcode::DivInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_err());
    assert_eq!(out.err_kind, JitRuntimeErrorKind::DivisionByZero);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_div_division_by_zero() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 10 });
    func.emit(Opcode::LoadImm { rd: 1, value: 0 });
    func.emit(Opcode::IntDiv {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_err());
    assert_eq!(out.err_kind, JitRuntimeErrorKind::DivisionByZero);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mod_int_division_by_zero() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 10 });
    func.emit(Opcode::LoadImm { rd: 1, value: 0 });
    func.emit(Opcode::ModInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_err());
    assert_eq!(out.err_kind, JitRuntimeErrorKind::DivisionByZero);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sub_int() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 50 });
    func.emit(Opcode::LoadImm { rd: 1, value: 8 });
    func.emit(Opcode::SubInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 42);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mul_int() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 6 });
    func.emit(Opcode::LoadImm { rd: 1, value: 7 });
    func.emit(Opcode::MulInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 42);
}

// ============================================================
// Arithmetic overflow detection (Part of #3817)
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_add_int_overflow() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm {
        rd: 0,
        value: i64::MAX,
    });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::AddInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_err(), "i64::MAX + 1 should overflow");
    assert_eq!(out.err_kind, JitRuntimeErrorKind::ArithmeticOverflow);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sub_int_overflow() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm {
        rd: 0,
        value: i64::MIN,
    });
    func.emit(Opcode::LoadImm { rd: 1, value: 1 });
    func.emit(Opcode::SubInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_err(), "i64::MIN - 1 should overflow");
    assert_eq!(out.err_kind, JitRuntimeErrorKind::ArithmeticOverflow);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mul_int_overflow() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm {
        rd: 0,
        value: i64::MAX,
    });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    func.emit(Opcode::MulInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_err(), "i64::MAX * 2 should overflow");
    assert_eq!(out.err_kind, JitRuntimeErrorKind::ArithmeticOverflow);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_neg_int_min_overflow() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm {
        rd: 0,
        value: i64::MIN,
    });
    func.emit(Opcode::NegInt { rd: 1, rs: 0 });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_err(), "negating i64::MIN should overflow");
    assert_eq!(out.err_kind, JitRuntimeErrorKind::ArithmeticOverflow);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_div_int_min_overflow() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm {
        rd: 0,
        value: i64::MIN,
    });
    func.emit(Opcode::LoadImm { rd: 1, value: -1 });
    func.emit(Opcode::DivInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_err());
    assert_eq!(out.err_kind, JitRuntimeErrorKind::ArithmeticOverflow);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_neg_int() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 42 });
    func.emit(Opcode::NegInt { rd: 1, rs: 0 });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, -42);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_neq() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 5 });
    func.emit(Opcode::LoadImm { rd: 1, value: 6 });
    func.emit(Opcode::Neq {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_neq_equal() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 5 });
    func.emit(Opcode::LoadImm { rd: 1, value: 5 });
    func.emit(Opcode::Neq {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_if_join_merges_register_values_from_both_predecessors() {
    // Matches the bytecode compiler's IF shape:
    // both branches Move into the same destination register, then execution
    // rejoins and returns that merged register.
    let mut func = BytecodeFunction::new("IfJoin".to_string(), 0);
    func.emit(Opcode::LoadVar { rd: 0, var_idx: 0 }); // PC 0: cond
    func.emit(Opcode::JumpFalse { rs: 0, offset: 4 }); // PC 1 -> PC 5
    func.emit(Opcode::LoadImm { rd: 1, value: 10 }); // PC 2
    func.emit(Opcode::Move { rd: 2, rs: 1 }); // PC 3
    func.emit(Opcode::Jump { offset: 3 }); // PC 4 -> PC 7
    func.emit(Opcode::LoadImm { rd: 1, value: 20 }); // PC 5
    func.emit(Opcode::Move { rd: 2, rs: 1 }); // PC 6
    func.emit(Opcode::Ret { rs: 2 }); // PC 7

    assert_eq!(compile_and_run(&func, &[1]).value, 10);
    assert_eq!(compile_and_run(&func, &[0]).value, 20);
}
