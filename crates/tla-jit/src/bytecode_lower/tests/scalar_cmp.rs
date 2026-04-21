// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================
// Scalar + eligibility basics
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_load_imm_and_ret() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 42 });
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 42);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_add_int() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 10 });
    func.emit(Opcode::LoadImm { rd: 1, value: 32 });
    func.emit(Opcode::AddInt {
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
fn test_int_div_euclidean() {
    // TLA+ \div: -7 \div 2 = -4 (Euclidean)
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: -7 });
    func.emit(Opcode::LoadImm { rd: 1, value: 2 });
    func.emit(Opcode::IntDiv {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, -4);
}

// ============================================================
// Comparisons
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eq_true() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 5 });
    func.emit(Opcode::LoadImm { rd: 1, value: 5 });
    func.emit(Opcode::Eq {
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
fn test_eq_false() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 5 });
    func.emit(Opcode::LoadImm { rd: 1, value: 6 });
    func.emit(Opcode::Eq {
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
fn test_lt_int() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 3 });
    func.emit(Opcode::LoadImm { rd: 1, value: 5 });
    func.emit(Opcode::LtInt {
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
fn test_ge_int() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 5 });
    func.emit(Opcode::LoadImm { rd: 1, value: 5 });
    func.emit(Opcode::GeInt {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 1);
}
