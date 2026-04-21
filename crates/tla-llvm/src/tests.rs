// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the LLVM AOT backend.

use crate::compiler::{AotLibrary, LlvmCompiler, OptLevel};
use crate::lower;
use tla_jit::abi::{JitCallOut, JitRuntimeErrorKind, JitStatus};
use tla_tir::bytecode::{BytecodeFunction, Opcode};

/// Helper to build a simple bytecode function with the given instructions.
fn make_func(name: &str, max_register: u8, instructions: Vec<Opcode>) -> BytecodeFunction {
    BytecodeFunction {
        name: name.to_string(),
        arity: 0,
        max_register,
        instructions,
    }
}

// =========================================================================
// IR emission tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_constant_return() {
    // Function: return 42
    let func = make_func(
        "const42",
        0,
        vec![
            Opcode::LoadImm { rd: 0, value: 42 },
            Opcode::Ret { rs: 0 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_const42")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    // Verify the IR contains key elements
    assert!(ir.contains("define void @test_const42("), "missing function definition");
    assert!(ir.contains("store i64 42"), "missing constant store");
    assert!(ir.contains("ret void"), "missing return");
    assert!(ir.contains("store i8 0"), "missing JitStatus::Ok write");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_add_with_overflow() {
    // Function: r0 = 10, r1 = 20, r2 = r0 + r1, return r2
    let func = make_func(
        "add_test",
        2,
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 20 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_add")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    // Should use overflow intrinsic
    assert!(
        ir.contains("@llvm.sadd.with.overflow.i64"),
        "should use overflow-detecting add: {}",
        ir
    );
    assert!(ir.contains("extractvalue"), "should extract result and overflow flag");
    assert!(ir.contains("br i1"), "should branch on overflow");

    // Should request the intrinsic declaration
    assert!(
        result.required_declarations.iter().any(|d| d.contains("llvm.sadd.with.overflow.i64")),
        "should require sadd intrinsic declaration"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_comparison() {
    // Function: r0 = 5, r1 = 10, r2 = (r0 < r1), return r2
    let func = make_func(
        "cmp_test",
        2,
        vec![
            Opcode::LoadImm { rd: 0, value: 5 },
            Opcode::LoadImm { rd: 1, value: 10 },
            Opcode::LtInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_cmp")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    assert!(ir.contains("icmp slt i64"), "should use signed less-than comparison");
    assert!(ir.contains("zext i1"), "should zero-extend i1 to i64");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_boolean_ops() {
    // Function: r0 = true, r1 = false, r2 = r0 /\ r1, return r2
    let func = make_func(
        "bool_test",
        2,
        vec![
            Opcode::LoadBool { rd: 0, value: true },
            Opcode::LoadBool {
                rd: 1,
                value: false,
            },
            Opcode::And {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_bool")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    assert!(ir.contains("store i64 1"), "should store true as 1");
    assert!(ir.contains("store i64 0"), "should store false as 0");
    assert!(ir.contains("and i64"), "should use i64 and for conjunction");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_branch() {
    // Function with a branch:
    // r0 = 1
    // JumpFalse r0, +2  (skip next if false)
    // r1 = 42
    // Jump +1           (skip else)
    // r1 = 99
    // Ret r1
    let func = make_func(
        "branch_test",
        1,
        vec![
            Opcode::LoadBool { rd: 0, value: true },     // pc 0
            Opcode::JumpFalse { rs: 0, offset: 2 },      // pc 1 -> target pc 3
            Opcode::LoadImm { rd: 1, value: 42 },        // pc 2 (fallthrough)
            Opcode::Jump { offset: 2 },                  // pc 3 -> target pc 5
            Opcode::LoadImm { rd: 1, value: 99 },        // pc 4
            Opcode::Ret { rs: 1 },                       // pc 5
        ],
    );

    let result = lower::lower_invariant(&func, "test_branch")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    // Should have multiple basic blocks
    assert!(ir.contains("bb_"), "should have basic blocks for branch targets");
    assert!(ir.contains("br i1"), "should have conditional branch");
    assert!(ir.contains("br label"), "should have unconditional branch");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_division_by_zero_check() {
    // Function: r0 = 10, r1 = 0, r2 = r0 / r1, return r2
    let func = make_func(
        "div_zero_test",
        2,
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 0 },
            Opcode::IntDiv {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_div_zero")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    // Should check for zero divisor
    assert!(
        ir.contains("icmp eq i64"),
        "should compare divisor with zero"
    );
    // Should have error path writing DivisionByZero
    assert!(
        ir.contains(&format!("store i8 {}", JitRuntimeErrorKind::DivisionByZero as u8)),
        "should write DivisionByZero error kind"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_load_var() {
    // Function: r0 = state[0], r1 = state[1], r2 = r0 + r1, return r2
    let func = make_func(
        "state_load_test",
        2,
        vec![
            Opcode::LoadVar { rd: 0, var_idx: 0 },
            Opcode::LoadVar { rd: 1, var_idx: 1 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_load_var")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    // Should use GEP to access state array
    assert!(
        ir.contains("getelementptr i64, ptr %state"),
        "should use GEP to access state array elements"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_next_state() {
    // Function: state_out[0] = state_in[0] + 1
    let func = make_func(
        "next_state_test",
        1,
        vec![
            Opcode::LoadVar { rd: 0, var_idx: 0 },
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::AddInt {
                rd: 0,
                r1: 0,
                r2: 1,
            },
            Opcode::StoreVar { var_idx: 0, rs: 0 },
            Opcode::LoadBool { rd: 0, value: true },
            Opcode::Ret { rs: 0 },
        ],
    );

    let result = lower::lower_next_state(&func, "test_nxt")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    // Should have 4 parameters
    assert!(ir.contains("ptr %out"), "should have out param");
    assert!(ir.contains("ptr %state_in"), "should have state_in param");
    assert!(ir.contains("ptr %state_out"), "should have state_out param");
    assert!(ir.contains("i32 %state_len"), "should have state_len param");

    // Should write to state_out
    assert!(
        ir.contains("getelementptr i64, ptr %state_out"),
        "should use GEP to write to state_out"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_not_implies() {
    // Function: r0 = false, r1 = true, r2 = NOT r0, r3 = r0 => r1, return r2 AND r3
    let func = make_func(
        "not_implies_test",
        4,
        vec![
            Opcode::LoadBool {
                rd: 0,
                value: false,
            },
            Opcode::LoadBool { rd: 1, value: true },
            Opcode::Not { rd: 2, rs: 0 },
            Opcode::Implies {
                rd: 3,
                r1: 0,
                r2: 1,
            },
            Opcode::And {
                rd: 4,
                r1: 2,
                r2: 3,
            },
            Opcode::Ret { rs: 4 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_not_implies")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    // NOT should use icmp eq with 0
    assert!(ir.contains("icmp eq i64"), "NOT should compare with 0");
    // Implies should use or i1
    assert!(ir.contains("or i1"), "implies should use or i1 for !a || b");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_halt() {
    // Function: Halt immediately
    let func = make_func("halt_test", 0, vec![Opcode::Halt]);

    let result = lower::lower_invariant(&func, "test_halt")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    // Halt should emit a RuntimeError status and return
    assert!(
        ir.contains(&format!("store i8 {}", JitStatus::RuntimeError as u8)),
        "Halt should write RuntimeError status"
    );
    assert!(ir.contains("ret void"), "Halt should return void");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_real_division() {
    // Function: r0 = 10, r1 = 2, r2 = r0 / r1 (real div), return r2
    let func = make_func(
        "realdiv_test",
        2,
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::DivInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_realdiv")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    // Should check for zero divisor
    assert!(ir.contains("icmp eq i64"), "should check for zero divisor");
    // Should check for exactness (srem + icmp ne)
    assert!(ir.contains("srem i64"), "should compute remainder for exactness check");
    // Should have the actual division
    assert!(ir.contains("sdiv i64"), "should perform the division");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_move() {
    // Function: r0 = 42, r1 = Move r0, return r1
    let func = make_func(
        "move_test",
        1,
        vec![
            Opcode::LoadImm { rd: 0, value: 42 },
            Opcode::Move { rd: 1, rs: 0 },
            Opcode::Ret { rs: 1 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_move")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    // Should have load and store pairs for the move
    assert!(ir.contains("load i64, ptr %reg_0"), "should load from source register");
    assert!(ir.contains("store i64"), "should store to destination register");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_cond_move() {
    // Function: r0 = 1 (true), r1 = 42, r2 = 99
    // CondMove: r2 = cond(r0) ? r1 : r2
    // Return r2
    let func = make_func(
        "condmove_test",
        2,
        vec![
            Opcode::LoadBool { rd: 0, value: true },
            Opcode::LoadImm { rd: 1, value: 42 },
            Opcode::LoadImm { rd: 2, value: 99 },
            Opcode::CondMove {
                rd: 2,
                cond: 0,
                rs: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_condmove")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    assert!(ir.contains("select i1"), "should use LLVM select for CondMove");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_equiv() {
    // Function: r0 = 42, r1 = 42, r2 = r0 <=> r1, return r2
    let func = make_func(
        "equiv_test",
        2,
        vec![
            Opcode::LoadImm { rd: 0, value: 42 },
            Opcode::LoadImm { rd: 1, value: 42 },
            Opcode::Equiv {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_equiv")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    assert!(ir.contains("icmp eq i64"), "equiv should use eq comparison");
    assert!(ir.contains("zext i1"), "equiv should zero-extend i1 to i64");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_sub_mul_negint() {
    // Function: r0 = 10, r1 = 3, r2 = r0 - r1, r3 = r0 * r1, r4 = -r0, return r4
    let func = make_func(
        "arith_test",
        4,
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 3 },
            Opcode::SubInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::MulInt {
                rd: 3,
                r1: 0,
                r2: 1,
            },
            Opcode::NegInt { rd: 4, rs: 0 },
            Opcode::Ret { rs: 4 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_arith")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    assert!(ir.contains("llvm.ssub.with.overflow.i64"), "should use sub overflow intrinsic");
    assert!(ir.contains("llvm.smul.with.overflow.i64"), "should use mul overflow intrinsic");
    // NegInt uses ssub(0, x)
    assert!(
        ir.matches("llvm.ssub.with.overflow.i64").count() >= 2,
        "should use ssub for both SubInt and NegInt"
    );

    // Should require both intrinsic declarations
    assert!(
        result.required_declarations.iter().any(|d| d.contains("llvm.ssub.with.overflow.i64")),
        "should require ssub intrinsic"
    );
    assert!(
        result.required_declarations.iter().any(|d| d.contains("llvm.smul.with.overflow.i64")),
        "should require smul intrinsic"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_modint() {
    // Function: r0 = 10, r1 = 3, r2 = r0 % r1, return r2
    let func = make_func(
        "mod_test",
        2,
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 3 },
            Opcode::ModInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_mod")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    assert!(ir.contains("srem i64"), "should use srem for modulus");
    assert!(ir.contains("icmp eq i64"), "should check for zero divisor");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lower_or_neq_ge() {
    // Function: r0 = 5, r1 = 10, r2 = r0 != r1, r3 = r0 >= r1, r4 = r2 \/ r3, return r4
    let func = make_func(
        "logic_test",
        4,
        vec![
            Opcode::LoadImm { rd: 0, value: 5 },
            Opcode::LoadImm { rd: 1, value: 10 },
            Opcode::Neq {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::GeInt {
                rd: 3,
                r1: 0,
                r2: 1,
            },
            Opcode::Or {
                rd: 4,
                r1: 2,
                r2: 3,
            },
            Opcode::Ret { rs: 4 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_logic")
        .expect("lowering should succeed");
    let ir = result.function.to_ir();

    assert!(ir.contains("icmp ne i64"), "should use ne for Neq");
    assert!(ir.contains("icmp sge i64"), "should use sge for GeInt");
    assert!(ir.contains("or i64"), "should use or for disjunction");
}

// =========================================================================
// Compiler integration tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compiler_add_invariant() {
    let mut compiler = LlvmCompiler::new();

    let func = make_func(
        "inv_test",
        0,
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::Ret { rs: 0 },
        ],
    );

    let name = compiler
        .add_invariant(&func)
        .expect("should add invariant");
    assert!(name.starts_with("llvm_inv_"), "name should have llvm_inv_ prefix");

    let ir = compiler.to_ir();
    assert!(ir.contains("target triple"), "should have target triple");
    assert!(ir.contains(&name), "should contain the function");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compiler_multiple_functions() {
    let mut compiler = LlvmCompiler::new();

    let func1 = make_func(
        "f1",
        0,
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::Ret { rs: 0 },
        ],
    );
    let func2 = make_func(
        "f2",
        0,
        vec![
            Opcode::LoadBool { rd: 0, value: true },
            Opcode::Ret { rs: 0 },
        ],
    );

    let name1 = compiler.add_invariant(&func1).expect("should add f1");
    let name2 = compiler.add_invariant(&func2).expect("should add f2");

    let ir = compiler.to_ir();
    assert!(ir.contains(&name1), "should contain first function");
    assert!(ir.contains(&name2), "should contain second function");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compiler_unsupported_opcode() {
    let mut compiler = LlvmCompiler::new();

    // SetEnum is not supported in the minimal subset
    let func = make_func(
        "unsupported",
        2,
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::SetEnum {
                rd: 2,
                start: 0,
                count: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
    );

    let result = compiler.add_invariant(&func);
    assert!(result.is_err(), "SetEnum should not be supported");
    let err = result.unwrap_err();
    assert!(
        err.to_string().contains("unsupported"),
        "error should mention unsupported: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compiler_add_next_state() {
    let mut compiler = LlvmCompiler::new();

    let func = make_func(
        "nxt_test",
        1,
        vec![
            Opcode::LoadVar { rd: 0, var_idx: 0 },
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::AddInt {
                rd: 0,
                r1: 0,
                r2: 1,
            },
            Opcode::StoreVar { var_idx: 0, rs: 0 },
            Opcode::LoadBool { rd: 0, value: true },
            Opcode::Ret { rs: 0 },
        ],
    );

    let name = compiler
        .add_next_state(&func)
        .expect("should add next-state");
    assert!(name.starts_with("llvm_nxt_"), "name should have llvm_nxt_ prefix");

    let ir = compiler.to_ir();
    assert!(ir.contains(&name), "should contain the next-state function");
    assert!(ir.contains("ptr %state_out"), "should have state_out param");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compiler_opt_level() {
    let compiler = LlvmCompiler::new().with_opt_level(OptLevel::O3);
    assert_eq!(compiler.target_triple(), "aarch64-apple-darwin");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compiler_has_llvm_tools() {
    // Just verify the method doesn't panic
    let _ = LlvmCompiler::has_llvm_tools();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compiler_intrinsic_declarations() {
    let mut compiler = LlvmCompiler::new();

    // This function uses AddInt which requires llvm.sadd.with.overflow.i64
    let func = make_func(
        "decl_test",
        2,
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
    );

    compiler.add_invariant(&func).expect("should add function");
    let ir = compiler.to_ir();

    // Module IR should include the intrinsic declaration
    assert!(
        ir.contains("declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)"),
        "module should declare sadd intrinsic: {ir}"
    );
}

// =========================================================================
// IR module structure tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_module_ir_structure() {
    use crate::ir::{LlvmFunction, LlvmModule, LlvmType, LlvmValue};

    let mut module = LlvmModule::new("aarch64-apple-darwin");

    let mut func = LlvmFunction {
        name: "test_func".to_string(),
        params: vec![
            (LlvmValue("%a".to_string()), LlvmType::I64),
            (LlvmValue("%b".to_string()), LlvmType::I64),
        ],
        return_type: LlvmType::I64,
        blocks: Vec::new(),
        next_reg: 0,
    };

    let entry = func.new_block("entry");
    let result = func.emit_with_result(entry, "add i64 %a, %b");
    func.terminate(entry, format!("ret i64 {result}"));

    module.add_function(func);

    let ir = module.to_ir();
    assert!(ir.contains("target triple = \"aarch64-apple-darwin\""));
    assert!(ir.contains("define i64 @test_func(i64 %a, i64 %b)"));
    assert!(ir.contains("add i64 %a, %b"));
    assert!(ir.contains("ret i64"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_module_declarations() {
    use crate::ir::LlvmModule;

    let mut module = LlvmModule::new("aarch64-apple-darwin");
    module.add_declaration("declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)".to_string());
    // Adding the same declaration twice should not duplicate
    module.add_declaration("declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)".to_string());

    let ir = module.to_ir();
    let count = ir.matches("declare { i64, i1 } @llvm.sadd.with.overflow.i64").count();
    assert_eq!(count, 1, "should not duplicate declarations, got {count} in:\n{ir}");
}

// =========================================================================
// Error handling tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_empty_function_rejected() {
    let func = BytecodeFunction {
        name: "empty".to_string(),
        arity: 0,
        max_register: 0,
        instructions: vec![],
    };

    let result = lower::lower_invariant(&func, "test_empty");
    assert!(result.is_err(), "empty function should be rejected");
    let err = result.unwrap_err();
    assert!(
        err.to_string().contains("empty"),
        "should mention empty: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nonzero_arity_rejected() {
    let func = BytecodeFunction {
        name: "with_args".to_string(),
        arity: 2,
        max_register: 0,
        instructions: vec![Opcode::Ret { rs: 0 }],
    };

    let result = lower::lower_invariant(&func, "test_args");
    assert!(result.is_err(), "non-zero arity should be rejected");
    let err = result.unwrap_err();
    assert!(
        err.to_string().contains("arity"),
        "should mention arity: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_storevar_in_invariant_rejected() {
    let func = make_func(
        "bad_invariant",
        0,
        vec![
            Opcode::LoadImm { rd: 0, value: 42 },
            Opcode::StoreVar { var_idx: 0, rs: 0 },
            Opcode::Ret { rs: 0 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_storevar");
    assert!(result.is_err(), "StoreVar in invariant mode should fail");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_loadprime_in_invariant_rejected() {
    let func = make_func(
        "bad_invariant",
        0,
        vec![
            Opcode::LoadPrime { rd: 0, var_idx: 0 },
            Opcode::Ret { rs: 0 },
        ],
    );

    let result = lower::lower_invariant(&func, "test_loadprime");
    assert!(result.is_err(), "LoadPrime in invariant mode should fail");
}

// =========================================================================
// End-to-end compilation tests (require clang)
// =========================================================================

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_end_to_end_invariant_constant() {
    if !LlvmCompiler::has_llvm_tools() {
        // Skip if clang is not available
        return;
    }

    let mut compiler = LlvmCompiler::new().with_opt_level(OptLevel::O0);

    let func = make_func(
        "e2e_const",
        0,
        vec![
            Opcode::LoadImm { rd: 0, value: 42 },
            Opcode::Ret { rs: 0 },
        ],
    );

    let func_name = compiler.add_invariant(&func).expect("should add function");

    let tmp = tempfile::tempdir().expect("should create temp dir");
    let dylib_path = compiler
        .compile_to_dylib(tmp.path())
        .expect("should compile to dylib");

    // Load and execute the function
    unsafe {
        let lib = AotLibrary::load(&dylib_path).expect("should load library");
        let fn_ptr = lib
            .get_invariant_fn(&func_name)
            .expect("should get function");

        let mut out = JitCallOut::default();
        let state: [i64; 0] = [];
        fn_ptr(&mut out, state.as_ptr(), 0);

        assert_eq!(out.status, JitStatus::Ok, "should succeed");
        assert_eq!(out.value, 42, "should return 42");
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_end_to_end_invariant_arithmetic() {
    if !LlvmCompiler::has_llvm_tools() {
        return;
    }

    let mut compiler = LlvmCompiler::new().with_opt_level(OptLevel::O0);

    // r0 = 10, r1 = 3, r2 = r0 + r1 (13), r3 = r0 * r1 (30), r4 = r2 + r3 (43)
    let func = make_func(
        "e2e_arith",
        4,
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 3 },
            Opcode::AddInt { rd: 2, r1: 0, r2: 1 },
            Opcode::MulInt { rd: 3, r1: 0, r2: 1 },
            Opcode::AddInt { rd: 4, r1: 2, r2: 3 },
            Opcode::Ret { rs: 4 },
        ],
    );

    let func_name = compiler.add_invariant(&func).expect("should add function");

    let tmp = tempfile::tempdir().expect("should create temp dir");
    let dylib_path = compiler
        .compile_to_dylib(tmp.path())
        .expect("should compile to dylib");

    unsafe {
        let lib = AotLibrary::load(&dylib_path).expect("should load library");
        let fn_ptr = lib
            .get_invariant_fn(&func_name)
            .expect("should get function");

        let mut out = JitCallOut::default();
        let state: [i64; 0] = [];
        fn_ptr(&mut out, state.as_ptr(), 0);

        assert_eq!(out.status, JitStatus::Ok, "should succeed");
        assert_eq!(out.value, 43, "10+3=13, 10*3=30, 13+30=43");
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_end_to_end_invariant_state_read() {
    if !LlvmCompiler::has_llvm_tools() {
        return;
    }

    let mut compiler = LlvmCompiler::new().with_opt_level(OptLevel::O0);

    // r0 = state[0], r1 = state[1], r2 = r0 + r1, return r2
    let func = make_func(
        "e2e_state",
        2,
        vec![
            Opcode::LoadVar { rd: 0, var_idx: 0 },
            Opcode::LoadVar { rd: 1, var_idx: 1 },
            Opcode::AddInt { rd: 2, r1: 0, r2: 1 },
            Opcode::Ret { rs: 2 },
        ],
    );

    let func_name = compiler.add_invariant(&func).expect("should add function");

    let tmp = tempfile::tempdir().expect("should create temp dir");
    let dylib_path = compiler
        .compile_to_dylib(tmp.path())
        .expect("should compile to dylib");

    unsafe {
        let lib = AotLibrary::load(&dylib_path).expect("should load library");
        let fn_ptr = lib
            .get_invariant_fn(&func_name)
            .expect("should get function");

        let mut out = JitCallOut::default();
        let state: [i64; 2] = [100, 200];
        fn_ptr(&mut out, state.as_ptr(), 2);

        assert_eq!(out.status, JitStatus::Ok, "should succeed");
        assert_eq!(out.value, 300, "state[0]+state[1] = 100+200 = 300");
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_end_to_end_invariant_comparison() {
    if !LlvmCompiler::has_llvm_tools() {
        return;
    }

    let mut compiler = LlvmCompiler::new().with_opt_level(OptLevel::O0);

    // r0 = state[0], r1 = 100, r2 = (r0 < r1), return r2
    let func = make_func(
        "e2e_cmp",
        2,
        vec![
            Opcode::LoadVar { rd: 0, var_idx: 0 },
            Opcode::LoadImm { rd: 1, value: 100 },
            Opcode::LtInt { rd: 2, r1: 0, r2: 1 },
            Opcode::Ret { rs: 2 },
        ],
    );

    let func_name = compiler.add_invariant(&func).expect("should add function");

    let tmp = tempfile::tempdir().expect("should create temp dir");
    let dylib_path = compiler
        .compile_to_dylib(tmp.path())
        .expect("should compile to dylib");

    unsafe {
        let lib = AotLibrary::load(&dylib_path).expect("should load library");
        let fn_ptr = lib
            .get_invariant_fn(&func_name)
            .expect("should get function");

        // state[0] = 50 < 100, should return 1 (true)
        let mut out = JitCallOut::default();
        let state: [i64; 1] = [50];
        fn_ptr(&mut out, state.as_ptr(), 1);
        assert_eq!(out.status, JitStatus::Ok);
        assert_eq!(out.value, 1, "50 < 100 should be true");

        // state[0] = 200 < 100, should return 0 (false)
        let state: [i64; 1] = [200];
        fn_ptr(&mut out, state.as_ptr(), 1);
        assert_eq!(out.status, JitStatus::Ok);
        assert_eq!(out.value, 0, "200 < 100 should be false");
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_end_to_end_invariant_branch() {
    if !LlvmCompiler::has_llvm_tools() {
        return;
    }

    let mut compiler = LlvmCompiler::new().with_opt_level(OptLevel::O0);

    // IF state[0] > 0 THEN 1 ELSE 0
    let func = make_func(
        "e2e_branch",
        1,
        vec![
            Opcode::LoadVar { rd: 0, var_idx: 0 },           // pc 0
            Opcode::LoadImm { rd: 1, value: 0 },             // pc 1
            Opcode::GtInt { rd: 0, r1: 0, r2: 1 },           // pc 2: r0 = state[0] > 0
            Opcode::JumpFalse { rs: 0, offset: 2 },          // pc 3 -> pc 5
            Opcode::LoadImm { rd: 1, value: 1 },             // pc 4: then branch
            Opcode::Jump { offset: 2 },                      // pc 5 -> pc 7
            Opcode::LoadImm { rd: 1, value: 0 },             // pc 6: else branch
            Opcode::Ret { rs: 1 },                           // pc 7
        ],
    );

    let func_name = compiler.add_invariant(&func).expect("should add function");

    let tmp = tempfile::tempdir().expect("should create temp dir");
    let dylib_path = compiler
        .compile_to_dylib(tmp.path())
        .expect("should compile to dylib");

    unsafe {
        let lib = AotLibrary::load(&dylib_path).expect("should load library");
        let fn_ptr = lib
            .get_invariant_fn(&func_name)
            .expect("should get function");

        // state[0] = 5 > 0, should return 1
        let mut out = JitCallOut::default();
        let state: [i64; 1] = [5];
        fn_ptr(&mut out, state.as_ptr(), 1);
        assert_eq!(out.status, JitStatus::Ok);
        assert_eq!(out.value, 1, "5 > 0 should take then branch");

        // state[0] = -1, not > 0, should return 0
        let state: [i64; 1] = [-1];
        fn_ptr(&mut out, state.as_ptr(), 1);
        assert_eq!(out.status, JitStatus::Ok);
        assert_eq!(out.value, 0, "-1 > 0 should take else branch");
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_end_to_end_invariant_division_by_zero() {
    if !LlvmCompiler::has_llvm_tools() {
        return;
    }

    let mut compiler = LlvmCompiler::new().with_opt_level(OptLevel::O0);

    // r0 = 10, r1 = 0, r2 = r0 \div r1 (division by zero)
    let func = make_func(
        "e2e_divzero",
        2,
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 0 },
            Opcode::IntDiv { rd: 2, r1: 0, r2: 1 },
            Opcode::Ret { rs: 2 },
        ],
    );

    let func_name = compiler.add_invariant(&func).expect("should add function");

    let tmp = tempfile::tempdir().expect("should create temp dir");
    let dylib_path = compiler
        .compile_to_dylib(tmp.path())
        .expect("should compile to dylib");

    unsafe {
        let lib = AotLibrary::load(&dylib_path).expect("should load library");
        let fn_ptr = lib
            .get_invariant_fn(&func_name)
            .expect("should get function");

        let mut out = JitCallOut::default();
        let state: [i64; 0] = [];
        fn_ptr(&mut out, state.as_ptr(), 0);

        assert_eq!(out.status, JitStatus::RuntimeError, "should report error");
        assert_eq!(
            out.err_kind,
            JitRuntimeErrorKind::DivisionByZero,
            "should be division by zero"
        );
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_end_to_end_next_state() {
    if !LlvmCompiler::has_llvm_tools() {
        return;
    }

    let mut compiler = LlvmCompiler::new().with_opt_level(OptLevel::O0);

    // state_out[0] = state_in[0] + 1, return TRUE
    let func = make_func(
        "e2e_nxt",
        1,
        vec![
            Opcode::LoadVar { rd: 0, var_idx: 0 },
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::AddInt { rd: 0, r1: 0, r2: 1 },
            Opcode::StoreVar { var_idx: 0, rs: 0 },
            Opcode::LoadBool { rd: 0, value: true },
            Opcode::Ret { rs: 0 },
        ],
    );

    let func_name = compiler.add_next_state(&func).expect("should add function");

    let tmp = tempfile::tempdir().expect("should create temp dir");
    let dylib_path = compiler
        .compile_to_dylib(tmp.path())
        .expect("should compile to dylib");

    unsafe {
        let lib = AotLibrary::load(&dylib_path).expect("should load library");
        let fn_ptr = lib
            .get_next_state_fn(&func_name)
            .expect("should get function");

        let mut out = JitCallOut::default();
        let state_in: [i64; 1] = [42];
        let mut state_out: [i64; 1] = [0];
        fn_ptr(&mut out, state_in.as_ptr(), state_out.as_mut_ptr(), 1);

        assert_eq!(out.status, JitStatus::Ok, "should succeed");
        assert_eq!(out.value, 1, "should return TRUE");
        assert_eq!(state_out[0], 43, "state_out[0] should be state_in[0] + 1 = 43");
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_end_to_end_write_ir_file() {
    if !LlvmCompiler::has_llvm_tools() {
        return;
    }

    let mut compiler = LlvmCompiler::new();

    let func = make_func(
        "ir_file_test",
        0,
        vec![
            Opcode::LoadImm { rd: 0, value: 99 },
            Opcode::Ret { rs: 0 },
        ],
    );

    compiler.add_invariant(&func).expect("should add function");

    let tmp = tempfile::tempdir().expect("should create temp dir");
    let ll_path = tmp.path().join("test.ll");
    compiler.write_ir(&ll_path).expect("should write IR");

    let contents = std::fs::read_to_string(&ll_path).expect("should read file");
    assert!(contents.contains("target triple"), "written file should have target triple");
    assert!(contents.contains("store i64 99"), "written file should contain constant");
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_end_to_end_compile_to_object() {
    if !LlvmCompiler::has_llvm_tools() {
        return;
    }

    let mut compiler = LlvmCompiler::new().with_opt_level(OptLevel::O0);

    let func = make_func(
        "obj_test",
        0,
        vec![
            Opcode::LoadImm { rd: 0, value: 1 },
            Opcode::Ret { rs: 0 },
        ],
    );

    compiler.add_invariant(&func).expect("should add function");

    let tmp = tempfile::tempdir().expect("should create temp dir");
    let obj_path = compiler
        .compile_to_object(tmp.path())
        .expect("should compile to object");

    assert!(obj_path.exists(), "object file should exist");
    let metadata = std::fs::metadata(&obj_path).expect("should stat object file");
    assert!(metadata.len() > 0, "object file should not be empty");
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_end_to_end_real_division() {
    if !LlvmCompiler::has_llvm_tools() {
        return;
    }

    let mut compiler = LlvmCompiler::new().with_opt_level(OptLevel::O0);

    // Exact division: 10 / 2 = 5
    let func = make_func(
        "e2e_realdiv",
        2,
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 2 },
            Opcode::DivInt { rd: 2, r1: 0, r2: 1 },
            Opcode::Ret { rs: 2 },
        ],
    );

    let func_name = compiler.add_invariant(&func).expect("should add function");

    let tmp = tempfile::tempdir().expect("should create temp dir");
    let dylib_path = compiler
        .compile_to_dylib(tmp.path())
        .expect("should compile to dylib");

    unsafe {
        let lib = AotLibrary::load(&dylib_path).expect("should load library");
        let fn_ptr = lib
            .get_invariant_fn(&func_name)
            .expect("should get function");

        let mut out = JitCallOut::default();
        let state: [i64; 0] = [];
        fn_ptr(&mut out, state.as_ptr(), 0);

        assert_eq!(out.status, JitStatus::Ok, "exact division should succeed");
        assert_eq!(out.value, 5, "10 / 2 = 5");
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_end_to_end_real_division_inexact() {
    if !LlvmCompiler::has_llvm_tools() {
        return;
    }

    let mut compiler = LlvmCompiler::new().with_opt_level(OptLevel::O0);

    // Inexact division: 10 / 3 should produce a runtime error
    let func = make_func(
        "e2e_realdiv_inexact",
        2,
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 3 },
            Opcode::DivInt { rd: 2, r1: 0, r2: 1 },
            Opcode::Ret { rs: 2 },
        ],
    );

    let func_name = compiler.add_invariant(&func).expect("should add function");

    let tmp = tempfile::tempdir().expect("should create temp dir");
    let dylib_path = compiler
        .compile_to_dylib(tmp.path())
        .expect("should compile to dylib");

    unsafe {
        let lib = AotLibrary::load(&dylib_path).expect("should load library");
        let fn_ptr = lib
            .get_invariant_fn(&func_name)
            .expect("should get function");

        let mut out = JitCallOut::default();
        let state: [i64; 0] = [];
        fn_ptr(&mut out, state.as_ptr(), 0);

        assert_eq!(
            out.status,
            JitStatus::RuntimeError,
            "inexact real division should report error"
        );
        assert_eq!(
            out.err_kind,
            JitRuntimeErrorKind::TypeMismatch,
            "inexact division should be TypeMismatch"
        );
    }
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_end_to_end_multiple_functions_in_one_module() {
    if !LlvmCompiler::has_llvm_tools() {
        return;
    }

    let mut compiler = LlvmCompiler::new().with_opt_level(OptLevel::O0);

    // First function: return 10
    let func1 = make_func(
        "multi_f1",
        0,
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::Ret { rs: 0 },
        ],
    );

    // Second function: return 20
    let func2 = make_func(
        "multi_f2",
        0,
        vec![
            Opcode::LoadImm { rd: 0, value: 20 },
            Opcode::Ret { rs: 0 },
        ],
    );

    let name1 = compiler.add_invariant(&func1).expect("should add f1");
    let name2 = compiler.add_invariant(&func2).expect("should add f2");

    let tmp = tempfile::tempdir().expect("should create temp dir");
    let dylib_path = compiler
        .compile_to_dylib(tmp.path())
        .expect("should compile to dylib");

    unsafe {
        let lib = AotLibrary::load(&dylib_path).expect("should load library");

        let fn1 = lib.get_invariant_fn(&name1).expect("should get f1");
        let fn2 = lib.get_invariant_fn(&name2).expect("should get f2");

        let mut out = JitCallOut::default();
        let state: [i64; 0] = [];

        fn1(&mut out, state.as_ptr(), 0);
        assert_eq!(out.value, 10, "f1 should return 10");

        fn2(&mut out, state.as_ptr(), 0);
        assert_eq!(out.value, 20, "f2 should return 20");
    }
}
