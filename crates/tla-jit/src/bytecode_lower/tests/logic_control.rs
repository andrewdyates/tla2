// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================
// Boolean operations
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_and_bool() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadBool { rd: 0, value: true });
    func.emit(Opcode::LoadBool {
        rd: 1,
        value: false,
    });
    func.emit(Opcode::And {
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
fn test_or_bool() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadBool {
        rd: 0,
        value: false,
    });
    func.emit(Opcode::LoadBool { rd: 1, value: true });
    func.emit(Opcode::Or {
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
fn test_not_bool() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadBool { rd: 0, value: true });
    func.emit(Opcode::Not { rd: 1, rs: 0 });
    func.emit(Opcode::Ret { rs: 1 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_implies() {
    // FALSE => anything = TRUE
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadBool {
        rd: 0,
        value: false,
    });
    func.emit(Opcode::LoadBool {
        rd: 1,
        value: false,
    });
    func.emit(Opcode::Implies {
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
fn test_equiv() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadBool { rd: 0, value: true });
    func.emit(Opcode::LoadBool { rd: 1, value: true });
    func.emit(Opcode::Equiv {
        rd: 2,
        r1: 0,
        r2: 1,
    });
    func.emit(Opcode::Ret { rs: 2 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 1);
}

// ============================================================
// Control flow
// ============================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_jump_false_taken() {
    // if FALSE then 1 else 0
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadBool {
        rd: 0,
        value: false,
    }); // PC 0
    func.emit(Opcode::JumpFalse { rs: 0, offset: 3 }); // PC 1 → PC 4
    func.emit(Opcode::LoadImm { rd: 1, value: 1 }); // PC 2
    func.emit(Opcode::Ret { rs: 1 }); // PC 3
    func.emit(Opcode::LoadImm { rd: 1, value: 0 }); // PC 4
    func.emit(Opcode::Ret { rs: 1 }); // PC 5

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_jump_false_not_taken() {
    // if TRUE then 1 else 0
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadBool { rd: 0, value: true }); // PC 0
    func.emit(Opcode::JumpFalse { rs: 0, offset: 3 }); // PC 1 → PC 4
    func.emit(Opcode::LoadImm { rd: 1, value: 1 }); // PC 2
    func.emit(Opcode::Ret { rs: 1 }); // PC 3
    func.emit(Opcode::LoadImm { rd: 1, value: 0 }); // PC 4
    func.emit(Opcode::Ret { rs: 1 }); // PC 5

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unconditional_jump() {
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::Jump { offset: 2 }); // PC 0 → PC 2
    func.emit(Opcode::LoadImm { rd: 0, value: 99 }); // PC 1 (skipped)
    func.emit(Opcode::LoadImm { rd: 0, value: 42 }); // PC 2
    func.emit(Opcode::Ret { rs: 0 }); // PC 3

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 42);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cond_move() {
    // rd = IF cond THEN rs ELSE rd
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadImm { rd: 0, value: 10 }); // original
    func.emit(Opcode::LoadBool { rd: 1, value: true }); // cond
    func.emit(Opcode::LoadImm { rd: 2, value: 42 }); // replacement
    func.emit(Opcode::CondMove {
        rd: 0,
        cond: 1,
        rs: 2,
    }); // r0 = true ? r2 : r0 = 42
    func.emit(Opcode::Ret { rs: 0 });

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 42);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_branch_merge_uses_edge_specific_register_value() {
    // Mirrors the bytecode compiler's IF lowering:
    // if cond then rd := 1 else rd := 2; return rd
    let mut func = BytecodeFunction::new("test".to_string(), 0);
    func.emit(Opcode::LoadBool { rd: 0, value: true }); // PC 0
    func.emit(Opcode::JumpFalse { rs: 0, offset: 4 }); // PC 1 -> PC 5
    func.emit(Opcode::LoadImm { rd: 2, value: 1 }); // PC 2
    func.emit(Opcode::Move { rd: 1, rs: 2 }); // PC 3
    func.emit(Opcode::Jump { offset: 3 }); // PC 4 -> PC 7
    func.emit(Opcode::LoadImm { rd: 3, value: 2 }); // PC 5
    func.emit(Opcode::Move { rd: 1, rs: 3 }); // PC 6
    func.emit(Opcode::Ret { rs: 1 }); // PC 7

    let out = compile_and_run_no_state(&func);
    assert!(out.is_ok());
    assert_eq!(out.value, 1);
}
