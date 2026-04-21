// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end integration tests for the JIT compilation pipeline.
//!
//! These tests exercise the **full** path:
//!   TIR expression -> BytecodeCompiler -> BytecodeFunction
//!     -> BytecodeLowerer::compile_invariant -> JitInvariantFn -> execute
//!
//! Unlike the unit tests in `bytecode_lower/tests/` (which hand-build opcodes)
//! or the AST-level tests in `compiler/tests.rs` (which test the Expr -> Cranelift
//! path), these tests start from high-level TIR operator definitions and verify
//! the entire pipeline produces correct native results.
//!
//! Part of #3909.

use crate::abi::JitCallOut;
use crate::bytecode_lower::BytecodeLowerer;
use crate::tir_inlining::{inline_and_compile, JitInliningConfig};

use tla_core::intern_name;
use tla_core::span::{FileId, Span};
use tla_core::Spanned;
use tla_tir::bytecode::BytecodeCompiler;
use tla_tir::nodes::*;
use tla_tir::types::TirType;
use tla_tir::{TirModule, TirOperator};
use tla_value::Value;

// =========================================================================
// Test helpers
// =========================================================================

fn span() -> Span {
    Span::new(FileId(0), 0, 0)
}

fn spanned(expr: TirExpr) -> Spanned<TirExpr> {
    Spanned::new(expr, span())
}

fn int_const(n: i64) -> Spanned<TirExpr> {
    spanned(TirExpr::Const {
        value: Value::int(n),
        ty: TirType::Int,
    })
}

fn bool_const(b: bool) -> Spanned<TirExpr> {
    spanned(TirExpr::Const {
        value: Value::Bool(b),
        ty: TirType::Bool,
    })
}

fn state_var(name: &str, index: u16) -> Spanned<TirExpr> {
    spanned(TirExpr::Name(TirNameRef {
        name: name.to_string(),
        name_id: intern_name(name),
        kind: TirNameKind::StateVar { index },
        ty: TirType::Int,
    }))
}

fn name_ident(name: &str) -> Spanned<TirExpr> {
    spanned(TirExpr::Name(TirNameRef {
        name: name.to_string(),
        name_id: intern_name(name),
        kind: TirNameKind::Ident,
        ty: TirType::Dyn,
    }))
}

fn arith(left: Spanned<TirExpr>, op: TirArithOp, right: Spanned<TirExpr>) -> Spanned<TirExpr> {
    spanned(TirExpr::ArithBinOp {
        left: Box::new(left),
        op,
        right: Box::new(right),
    })
}

fn cmp(left: Spanned<TirExpr>, op: TirCmpOp, right: Spanned<TirExpr>) -> Spanned<TirExpr> {
    spanned(TirExpr::Cmp {
        left: Box::new(left),
        op,
        right: Box::new(right),
    })
}

fn bool_op(left: Spanned<TirExpr>, op: TirBoolOp, right: Spanned<TirExpr>) -> Spanned<TirExpr> {
    spanned(TirExpr::BoolBinOp {
        left: Box::new(left),
        op,
        right: Box::new(right),
    })
}

fn make_operator(name: &str, params: Vec<&str>, body: Spanned<TirExpr>) -> TirOperator {
    TirOperator {
        name: name.to_string(),
        name_id: intern_name(name),
        params: params.into_iter().map(String::from).collect(),
        is_recursive: false,
        body,
    }
}

/// Compile a zero-arity TIR operator to bytecode, JIT compile it,
/// and execute it on the given state array. Returns the JitCallOut.
fn compile_and_run_tir(op: &TirOperator, state: &[i64]) -> JitCallOut {
    let mut compiler = BytecodeCompiler::new();
    compiler
        .compile_operator(op)
        .expect("bytecode compilation failed");
    let chunk = compiler.finish();
    let func = chunk.get_function(0);

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let jit_fn = lowerer
        .compile_invariant(func)
        .expect("JIT compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }
    out
}

/// Compile a TIR module (with inlining) and JIT-compile + run a specific
/// zero-arity operator on the given state.
fn compile_module_and_run(module: &mut TirModule, op_name: &str, state: &[i64]) -> JitCallOut {
    let config = JitInliningConfig::default();
    let (chunk, _stats) = inline_and_compile(module, &config).expect("inline_and_compile failed");

    let target_func = {
        let mut found = None;
        for i in 0..chunk.function_count() {
            let f = chunk.get_function(i as u16);
            if f.name == op_name {
                found = Some(f);
                break;
            }
        }
        found.unwrap_or_else(|| panic!("operator '{op_name}' not found in chunk"))
    };

    let mut lowerer = BytecodeLowerer::new().expect("failed to create lowerer");
    let jit_fn = lowerer
        .compile_invariant(target_func)
        .expect("JIT compilation failed")
        .expect("function should be eligible");

    let mut out = JitCallOut::default();
    unsafe {
        jit_fn(&mut out, state.as_ptr(), state.len() as u32);
    }
    out
}

// =========================================================================
// Test 1: Compile and execute a simple invariant (x < 10)
//
// This tests the full TIR -> bytecode -> native path with a state-
// dependent expression. The expression reads a state variable and
// compares it against a constant.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_simple_invariant_x_lt_10_true() {
    // Invariant: x < 10, where x is state variable at index 0
    let op = make_operator(
        "Inv",
        vec![],
        cmp(state_var("x", 0), TirCmpOp::Lt, int_const(10)),
    );

    // State: x = 5 -> 5 < 10 = TRUE
    let out = compile_and_run_tir(&op, &[5]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "5 < 10 should be TRUE (1)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_simple_invariant_x_lt_10_false() {
    let op = make_operator(
        "Inv",
        vec![],
        cmp(state_var("x", 0), TirCmpOp::Lt, int_const(10)),
    );

    // State: x = 15 -> 15 < 10 = FALSE
    let out = compile_and_run_tir(&op, &[15]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 0, "15 < 10 should be FALSE (0)");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_simple_invariant_x_lt_10_boundary() {
    let op = make_operator(
        "Inv",
        vec![],
        cmp(state_var("x", 0), TirCmpOp::Lt, int_const(10)),
    );

    // State: x = 10 -> 10 < 10 = FALSE
    let out = compile_and_run_tir(&op, &[10]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 0, "10 < 10 should be FALSE (0)");
}

// =========================================================================
// Test 2: Compile and execute a comparison chain
//         (x > 0 /\ x < 10 /\ y >= x)
//
// This tests boolean connectives with multiple state variables and
// several comparison operators in a single expression.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_comparison_chain_all_true() {
    // x > 0 /\ x < 10 /\ y >= x
    // where x is state var 0, y is state var 1
    let x_gt_0 = cmp(state_var("x", 0), TirCmpOp::Gt, int_const(0));
    let x_lt_10 = cmp(state_var("x", 0), TirCmpOp::Lt, int_const(10));
    let y_geq_x = cmp(state_var("y", 1), TirCmpOp::Geq, state_var("x", 0));

    let and_left = bool_op(x_gt_0, TirBoolOp::And, x_lt_10);
    let body = bool_op(and_left, TirBoolOp::And, y_geq_x);

    let op = make_operator("Inv", vec![], body);

    // State: x = 5, y = 7 -> (5 > 0) /\ (5 < 10) /\ (7 >= 5) = TRUE
    let out = compile_and_run_tir(&op, &[5, 7]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "x=5, y=7 should satisfy all conditions");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_comparison_chain_first_fails() {
    let x_gt_0 = cmp(state_var("x", 0), TirCmpOp::Gt, int_const(0));
    let x_lt_10 = cmp(state_var("x", 0), TirCmpOp::Lt, int_const(10));
    let y_geq_x = cmp(state_var("y", 1), TirCmpOp::Geq, state_var("x", 0));

    let and_left = bool_op(x_gt_0, TirBoolOp::And, x_lt_10);
    let body = bool_op(and_left, TirBoolOp::And, y_geq_x);

    let op = make_operator("Inv", vec![], body);

    // State: x = 0, y = 7 -> (0 > 0) = FALSE, short-circuits
    let out = compile_and_run_tir(&op, &[0, 7]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 0, "x=0 fails x > 0");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_comparison_chain_last_fails() {
    let x_gt_0 = cmp(state_var("x", 0), TirCmpOp::Gt, int_const(0));
    let x_lt_10 = cmp(state_var("x", 0), TirCmpOp::Lt, int_const(10));
    let y_geq_x = cmp(state_var("y", 1), TirCmpOp::Geq, state_var("x", 0));

    let and_left = bool_op(x_gt_0, TirBoolOp::And, x_lt_10);
    let body = bool_op(and_left, TirBoolOp::And, y_geq_x);

    let op = make_operator("Inv", vec![], body);

    // State: x = 5, y = 3 -> (5 > 0) /\ (5 < 10) /\ (3 >= 5) = FALSE
    let out = compile_and_run_tir(&op, &[5, 3]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 0, "y=3 fails y >= x=5");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_comparison_chain_boundary_values() {
    let x_gt_0 = cmp(state_var("x", 0), TirCmpOp::Gt, int_const(0));
    let x_lt_10 = cmp(state_var("x", 0), TirCmpOp::Lt, int_const(10));
    let y_geq_x = cmp(state_var("y", 1), TirCmpOp::Geq, state_var("x", 0));

    let and_left = bool_op(x_gt_0, TirBoolOp::And, x_lt_10);
    let body = bool_op(and_left, TirBoolOp::And, y_geq_x);

    let op = make_operator("Inv", vec![], body);

    // State: x = 1, y = 1 -> (1 > 0) /\ (1 < 10) /\ (1 >= 1) = TRUE
    let out = compile_and_run_tir(&op, &[1, 1]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "x=1, y=1 is the boundary TRUE case");
}

// =========================================================================
// Test 3: JIT result matches interpreter result
//
// Verifies that the JIT-compiled native code produces the same result
// as direct evaluation of the expression for multiple state inputs.
// The "interpreter result" is computed as a plain Rust expression that
// mirrors the TLA+ semantics (since the JIT is a backend for the same
// TLA+ expression evaluator).
// =========================================================================

fn interpreter_eval_x_plus_y_eq_z(state: &[i64]) -> i64 {
    // x + y = z, where x=state[0], y=state[1], z=state[2]
    if state[0] + state[1] == state[2] {
        1
    } else {
        0
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_jit_matches_interpreter() {
    // Expression: x + y = z
    let x_plus_y = arith(state_var("x", 0), TirArithOp::Add, state_var("y", 1));
    let body = cmp(x_plus_y, TirCmpOp::Eq, state_var("z", 2));

    let op = make_operator("Check", vec![], body);

    let test_states: &[&[i64]] = &[
        &[1, 2, 3],   // 1 + 2 = 3 -> TRUE
        &[1, 2, 4],   // 1 + 2 != 4 -> FALSE
        &[0, 0, 0],   // 0 + 0 = 0 -> TRUE
        &[-5, 5, 0],  // -5 + 5 = 0 -> TRUE
        &[-5, 5, 1],  // -5 + 5 != 1 -> FALSE
        &[100, 200, 300], // 100 + 200 = 300 -> TRUE
        &[100, 200, 301], // 100 + 200 != 301 -> FALSE
    ];

    for state in test_states {
        let jit_out = compile_and_run_tir(&op, state);
        assert!(jit_out.is_ok(), "JIT error for state {state:?}: {jit_out:?}");

        let interp_result = interpreter_eval_x_plus_y_eq_z(state);
        assert_eq!(
            jit_out.value, interp_result,
            "JIT ({}) != interpreter ({interp_result}) for state {state:?}",
            jit_out.value
        );
    }
}

fn interpreter_eval_complex(state: &[i64]) -> i64 {
    // (x * 2 - y) > 0, where x=state[0], y=state[1]
    if state[0] * 2 - state[1] > 0 {
        1
    } else {
        0
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_jit_matches_interpreter_complex_arithmetic() {
    // Expression: (x * 2 - y) > 0
    let x_times_2 = arith(state_var("x", 0), TirArithOp::Mul, int_const(2));
    let diff = arith(x_times_2, TirArithOp::Sub, state_var("y", 1));
    let body = cmp(diff, TirCmpOp::Gt, int_const(0));

    let op = make_operator("Check", vec![], body);

    let test_states: &[&[i64]] = &[
        &[5, 3],   // 5*2 - 3 = 7 > 0 -> TRUE
        &[1, 3],   // 1*2 - 3 = -1 > 0 -> FALSE
        &[0, 0],   // 0*2 - 0 = 0 > 0 -> FALSE
        &[10, 19], // 10*2 - 19 = 1 > 0 -> TRUE
        &[10, 20], // 10*2 - 20 = 0 > 0 -> FALSE
        &[10, 21], // 10*2 - 21 = -1 > 0 -> FALSE
    ];

    for state in test_states {
        let jit_out = compile_and_run_tir(&op, state);
        assert!(jit_out.is_ok(), "JIT error for state {state:?}: {jit_out:?}");

        let interp_result = interpreter_eval_complex(state);
        assert_eq!(
            jit_out.value, interp_result,
            "JIT ({}) != interpreter ({interp_result}) for state {state:?}",
            jit_out.value
        );
    }
}

// =========================================================================
// Test 4: Inlining integration
//
// Function with a Call node gets inlined at TIR level, then compiled
// through the full pipeline: TIR module -> inline -> bytecode -> JIT
// -> execute. Verifies that inlined code produces correct results, not
// just that it passes the eligibility gate.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_inlining_produces_correct_result() {
    // Double(x) == x + x
    let double = make_operator(
        "Double",
        vec!["x"],
        arith(name_ident("x"), TirArithOp::Add, name_ident("x")),
    );

    // Inv == Double(5) = 10
    let apply = spanned(TirExpr::Apply {
        op: Box::new(name_ident("Double")),
        args: vec![int_const(5)],
    });
    let inv = make_operator(
        "Inv",
        vec![],
        cmp(apply, TirCmpOp::Eq, int_const(10)),
    );

    let mut module = TirModule {
        name: "Test".to_string(),
        operators: vec![double, inv],
    };

    // After inlining, Inv should compile to: (5 + 5) = 10 -> TRUE
    let out = compile_module_and_run(&mut module, "Inv", &[]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "Double(5) = 10 should be TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_inlining_multi_param_correct_result() {
    // AddMul(a, b) == a + b * 2
    let add_mul = make_operator(
        "AddMul",
        vec!["a", "b"],
        arith(
            name_ident("a"),
            TirArithOp::Add,
            arith(name_ident("b"), TirArithOp::Mul, int_const(2)),
        ),
    );

    // Inv == AddMul(3, 4) = 11
    // After inlining: 3 + 4 * 2 = 3 + 8 = 11
    let apply = spanned(TirExpr::Apply {
        op: Box::new(name_ident("AddMul")),
        args: vec![int_const(3), int_const(4)],
    });
    let inv = make_operator(
        "Inv",
        vec![],
        cmp(apply, TirCmpOp::Eq, int_const(11)),
    );

    let mut module = TirModule {
        name: "Test".to_string(),
        operators: vec![add_mul, inv],
    };

    let out = compile_module_and_run(&mut module, "Inv", &[]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "AddMul(3, 4) = 11 should be TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_inlining_with_state_vars() {
    // IsPositive(v) == v > 0
    let is_positive = make_operator(
        "IsPositive",
        vec!["v"],
        cmp(name_ident("v"), TirCmpOp::Gt, int_const(0)),
    );

    // Inv == IsPositive(x) where x is state var 0
    let apply = spanned(TirExpr::Apply {
        op: Box::new(name_ident("IsPositive")),
        args: vec![state_var("x", 0)],
    });
    let inv = make_operator("Inv", vec![], apply);

    let mut module = TirModule {
        name: "Test".to_string(),
        operators: vec![is_positive, inv],
    };

    // x = 5 -> IsPositive(5) -> 5 > 0 = TRUE
    let out = compile_module_and_run(&mut module, "Inv", &[5]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "IsPositive(5) should be TRUE");

    // Re-create module (inline_and_compile mutates it)
    let is_positive2 = make_operator(
        "IsPositive",
        vec!["v"],
        cmp(name_ident("v"), TirCmpOp::Gt, int_const(0)),
    );
    let apply2 = spanned(TirExpr::Apply {
        op: Box::new(name_ident("IsPositive")),
        args: vec![state_var("x", 0)],
    });
    let inv2 = make_operator("Inv", vec![], apply2);
    let mut module2 = TirModule {
        name: "Test".to_string(),
        operators: vec![is_positive2, inv2],
    };

    // x = -3 -> IsPositive(-3) -> -3 > 0 = FALSE
    let out = compile_module_and_run(&mut module2, "Inv", &[-3]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 0, "IsPositive(-3) should be FALSE");
}

// =========================================================================
// Test 5: Constant propagation / folding
//
// Expressions with constant sub-expressions should fold at compile time.
// The bytecode compiler emits LoadImm for constants, and the JIT compiles
// them into immediate operands in native code. This test verifies that
// the pipeline handles constant-only sub-trees correctly and produces
// the right final answer.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_const_propagation_pure_constants() {
    // Pure constant expression: (2 + 3) * 4 = 20
    // The bytecode compiler folds these into LoadImm instructions.
    // The JIT must produce 20 without any runtime state access.
    let add_expr = arith(int_const(2), TirArithOp::Add, int_const(3));
    let mul_expr = arith(add_expr, TirArithOp::Mul, int_const(4));
    let body = cmp(mul_expr, TirCmpOp::Eq, int_const(20));

    let op = make_operator("ConstCheck", vec![], body);
    let out = compile_and_run_tir(&op, &[]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "(2 + 3) * 4 = 20 should be TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_const_propagation_mixed_with_state() {
    // Mixed constant and state: x + (3 * 4) > 10
    // The sub-expression (3 * 4) = 12 is constant.
    // Full expression: x + 12 > 10
    let const_part = arith(int_const(3), TirArithOp::Mul, int_const(4));
    let sum = arith(state_var("x", 0), TirArithOp::Add, const_part);
    let body = cmp(sum, TirCmpOp::Gt, int_const(10));

    let op = make_operator("MixedCheck", vec![], body);

    // x = 0 -> 0 + 12 = 12 > 10 = TRUE
    let out = compile_and_run_tir(&op, &[0]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "0 + 12 > 10 should be TRUE");

    // x = -3 -> -3 + 12 = 9 > 10 = FALSE
    let out = compile_and_run_tir(&op, &[-3]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 0, "-3 + 12 = 9 > 10 should be FALSE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_const_propagation_boolean_chain() {
    // TRUE /\ (5 > 3) /\ (10 = 10) -> all constant, should be TRUE
    let five_gt_three = cmp(int_const(5), TirCmpOp::Gt, int_const(3));
    let ten_eq_ten = cmp(int_const(10), TirCmpOp::Eq, int_const(10));
    let left = bool_op(bool_const(true), TirBoolOp::And, five_gt_three);
    let body = bool_op(left, TirBoolOp::And, ten_eq_ten);

    let op = make_operator("BoolConst", vec![], body);
    let out = compile_and_run_tir(&op, &[]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "TRUE /\\ (5 > 3) /\\ (10 = 10) should be TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_const_propagation_nested_arithmetic() {
    // ((10 - 3) * (2 + 4)) = 42
    // All sub-expressions are constant. Bytecode compiler emits LoadImm
    // for each literal, then arithmetic ops. JIT folds or computes them.
    let diff = arith(int_const(10), TirArithOp::Sub, int_const(3));
    let sum = arith(int_const(2), TirArithOp::Add, int_const(4));
    let product = arith(diff, TirArithOp::Mul, sum);
    let body = cmp(product, TirCmpOp::Eq, int_const(42));

    let op = make_operator("NestedConst", vec![], body);
    let out = compile_and_run_tir(&op, &[]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "(10-3)*(2+4) = 42 should be TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_const_folded_in_inlined_operator() {
    // TripleAndAdd(x, c) == x * 3 + c
    // Inv == TripleAndAdd(2, 10) = 16
    //
    // After inlining: 2 * 3 + 10 = 16
    // Both the multiplication (2 * 3 = 6) and the addition (6 + 10 = 16)
    // operate on constants after inlining, testing that the combined
    // inlining + compilation pipeline handles constant propagation.
    let triple_and_add = make_operator(
        "TripleAndAdd",
        vec!["x", "c"],
        arith(
            arith(name_ident("x"), TirArithOp::Mul, int_const(3)),
            TirArithOp::Add,
            name_ident("c"),
        ),
    );

    let apply = spanned(TirExpr::Apply {
        op: Box::new(name_ident("TripleAndAdd")),
        args: vec![int_const(2), int_const(10)],
    });
    let inv = make_operator(
        "Inv",
        vec![],
        cmp(apply, TirCmpOp::Eq, int_const(16)),
    );

    let mut module = TirModule {
        name: "Test".to_string(),
        operators: vec![triple_and_add, inv],
    };

    let out = compile_module_and_run(&mut module, "Inv", &[]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "TripleAndAdd(2, 10) = 16 should be TRUE");
}

// =========================================================================
// Test 6: IF-THEN-ELSE through the full pipeline
//
// Verifies that the TIR IF node compiles correctly through bytecode
// and JIT, producing the right branch selection at runtime.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_if_then_else_with_state() {
    // IF x > 0 THEN x * 2 ELSE x * (-1)
    // Return value compared to expected
    let cond = cmp(state_var("x", 0), TirCmpOp::Gt, int_const(0));
    let then_ = arith(state_var("x", 0), TirArithOp::Mul, int_const(2));
    let else_ = arith(state_var("x", 0), TirArithOp::Mul, int_const(-1));
    let if_expr = spanned(TirExpr::If {
        cond: Box::new(cond),
        then_: Box::new(then_),
        else_: Box::new(else_),
    });

    // Wrap in a comparison: result = 10 (when x = 5, 5*2 = 10)
    let body = cmp(if_expr, TirCmpOp::Eq, int_const(10));
    let op = make_operator("IfCheck", vec![], body);

    // x = 5 -> IF TRUE THEN 10 ELSE -5 -> 10 = 10 -> TRUE
    let out = compile_and_run_tir(&op, &[5]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "IF 5>0 THEN 5*2=10 ELSE ... -> 10=10 TRUE");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_if_then_else_else_branch() {
    let cond = cmp(state_var("x", 0), TirCmpOp::Gt, int_const(0));
    let then_ = arith(state_var("x", 0), TirArithOp::Mul, int_const(2));
    let else_ = arith(state_var("x", 0), TirArithOp::Mul, int_const(-1));
    let if_expr = spanned(TirExpr::If {
        cond: Box::new(cond),
        then_: Box::new(then_),
        else_: Box::new(else_),
    });

    // result = 3 (when x = -3, -3 * -1 = 3)
    let body = cmp(if_expr, TirCmpOp::Eq, int_const(3));
    let op = make_operator("IfCheck", vec![], body);

    // x = -3 -> IF FALSE THEN -6 ELSE 3 -> 3 = 3 -> TRUE
    let out = compile_and_run_tir(&op, &[-3]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "IF -3>0 THEN ... ELSE -3*(-1)=3 -> 3=3 TRUE");
}

// =========================================================================
// Test 7: Multiple state variables with arithmetic
//
// Verifies that the pipeline correctly maps TIR state variable indices
// to the state array, even with more complex expressions.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_multi_state_var_arithmetic() {
    // (a + b) * c = result, where a=state[0], b=state[1], c=state[2]
    // Compare against state[3] (the expected result)
    let sum = arith(state_var("a", 0), TirArithOp::Add, state_var("b", 1));
    let product = arith(sum, TirArithOp::Mul, state_var("c", 2));
    let body = cmp(product, TirCmpOp::Eq, state_var("result", 3));

    let op = make_operator("ArithCheck", vec![], body);

    // (2 + 3) * 4 = 20
    let out = compile_and_run_tir(&op, &[2, 3, 4, 20]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "(2+3)*4 = 20 should be TRUE");

    // (2 + 3) * 4 != 21
    let out = compile_and_run_tir(&op, &[2, 3, 4, 21]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 0, "(2+3)*4 != 21 should be FALSE");
}

// =========================================================================
// Test 8: Boolean implies through the pipeline
//
// TLA+ => operator: FALSE => anything = TRUE, TRUE => FALSE = FALSE
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_implies_operator() {
    // (x > 0) => (x > -1)
    // This should be TRUE for all integers: if x > 0 then certainly x > -1
    let antecedent = cmp(state_var("x", 0), TirCmpOp::Gt, int_const(0));
    let consequent = cmp(state_var("x", 0), TirCmpOp::Gt, int_const(-1));
    let body = bool_op(antecedent, TirBoolOp::Implies, consequent);

    let op = make_operator("ImpliesCheck", vec![], body);

    for x in &[-10, -1, 0, 1, 5, 100] {
        let out = compile_and_run_tir(&op, &[*x]);
        assert!(out.is_ok(), "expected Ok for x={x}, got: {out:?}");
        assert_eq!(
            out.value, 1,
            "(x > 0) => (x > -1) should be TRUE for x={x}"
        );
    }
}

// =========================================================================
// Test 9: Negation through the pipeline
//
// Verifies TIR BoolNot and ArithNeg compile correctly end-to-end.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_bool_negation() {
    // ~(x = 0) -- TRUE when x != 0
    let eq_zero = cmp(state_var("x", 0), TirCmpOp::Eq, int_const(0));
    let body = spanned(TirExpr::BoolNot(Box::new(eq_zero)));

    let op = make_operator("NegCheck", vec![], body);

    let out = compile_and_run_tir(&op, &[0]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 0, "~(0 = 0) should be FALSE");

    let out = compile_and_run_tir(&op, &[5]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "~(5 = 0) should be TRUE");
}

// =========================================================================
// Test 10: Multiple independent callees inlined into one caller
//
// Verifies that the TIR inlining pass correctly handles a caller that
// invokes two different leaf operators. Both get inlined, and the
// resulting expression compiles and executes correctly through JIT.
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pipeline_multiple_callees_inlined() {
    // Square(n) == n * n
    let square = make_operator(
        "Square",
        vec!["n"],
        arith(name_ident("n"), TirArithOp::Mul, name_ident("n")),
    );

    // Inc(n) == n + 1
    let inc = make_operator(
        "Inc",
        vec!["n"],
        arith(name_ident("n"), TirArithOp::Add, int_const(1)),
    );

    // Inv == Square(3) + Inc(5) = 15
    // After inlining: (3 * 3) + (5 + 1) = 9 + 6 = 15
    let apply_sq = spanned(TirExpr::Apply {
        op: Box::new(name_ident("Square")),
        args: vec![int_const(3)],
    });
    let apply_inc = spanned(TirExpr::Apply {
        op: Box::new(name_ident("Inc")),
        args: vec![int_const(5)],
    });
    let sum = arith(apply_sq, TirArithOp::Add, apply_inc);
    let inv = make_operator(
        "Inv",
        vec![],
        cmp(sum, TirCmpOp::Eq, int_const(15)),
    );

    let mut module = TirModule {
        name: "Test".to_string(),
        operators: vec![square, inc, inv],
    };

    let out = compile_module_and_run(&mut module, "Inv", &[]);
    assert!(out.is_ok(), "expected Ok, got: {out:?}");
    assert_eq!(out.value, 1, "Square(3) + Inc(5) = 15 should be TRUE");
}
