// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for Lambda closure compilation and execution in the bytecode VM.
//!
//! Covers:
//! - Non-capturing Lambda (closure with `bytecode_func_idx`) via ValueApply
//! - Capturing Lambda via MakeClosure + ValueApply
//! - Nested Lambda expressions
//! - `[x \in S |-> body]` (FuncDef) pattern

use super::{make_func, BytecodeChunk, BytecodeVm, ConstantPool, Opcode, Value};
use std::sync::Arc;
use tla_value::ClosureValue;

/// Helper: build a non-capturing closure value with a bytecode_func_idx pointing
/// to a compiled sub-function in the chunk.
fn make_non_capturing_closure(params: Vec<String>, bc_idx: u16) -> Value {
    let dummy_body = tla_core::Spanned {
        node: tla_core::ast::Expr::Int(1.into()),
        span: tla_core::Span::default(),
    };
    let closure = ClosureValue::new(params, dummy_body, Arc::new(Default::default()), None)
        .with_bytecode_func_idx(bc_idx);
    Value::Closure(Arc::new(closure))
}

/// Non-capturing Lambda applied via ValueApply: `(LAMBDA x: x + 1)(5)` => 6
///
/// The Lambda compiles to a closure constant with bytecode_func_idx pointing
/// to a sub-function. ValueApply detects the bytecode_func_idx and executes
/// the sub-function natively instead of falling back to tree-walking.
#[test]
fn test_vm_non_capturing_lambda_via_value_apply() {
    let mut constants = ConstantPool::new();

    // Sub-function 0: lambda body (x) => x + 1
    let lambda_func = make_func(
        "<lambda@0>".to_string(),
        1, // arity: 1 param (x)
        vec![
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );

    // Closure constant pointing to sub-function 0
    let closure_val = make_non_capturing_closure(vec!["x".to_string()], 0);
    let closure_idx = constants.add_value(closure_val);

    // Main function 1: load closure, load 5, ValueApply
    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::LoadConst {
                rd: 0,
                idx: closure_idx,
            },
            Opcode::LoadImm { rd: 1, value: 5 },
            Opcode::ValueApply {
                rd: 2,
                func: 0,
                args_start: 1,
                argc: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );

    let mut chunk = BytecodeChunk::new();
    chunk.constants = constants;
    chunk.add_function(lambda_func);
    chunk.add_function(main_func);

    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let result = vm
        .execute_function(1)
        .expect("non-capturing lambda should execute");
    assert_eq!(result, Value::SmallInt(6));
}

/// Multi-param non-capturing Lambda: `(LAMBDA x, y: x * y + 1)(3, 4)` => 13
#[test]
fn test_vm_non_capturing_lambda_multi_param() {
    let mut constants = ConstantPool::new();

    // Sub-function 0: (x, y) => x * y + 1
    let lambda_func = make_func(
        "<lambda@0>".to_string(),
        2,
        vec![
            Opcode::MulInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::LoadImm { rd: 3, value: 1 },
            Opcode::AddInt {
                rd: 4,
                r1: 2,
                r2: 3,
            },
            Opcode::Ret { rs: 4 },
        ],
        4,
    );

    let closure_val = make_non_capturing_closure(vec!["x".to_string(), "y".to_string()], 0);
    let closure_idx = constants.add_value(closure_val);

    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::LoadConst {
                rd: 0,
                idx: closure_idx,
            },
            Opcode::LoadImm { rd: 1, value: 3 },
            Opcode::LoadImm { rd: 2, value: 4 },
            Opcode::ValueApply {
                rd: 3,
                func: 0,
                args_start: 1,
                argc: 2,
            },
            Opcode::Ret { rs: 3 },
        ],
        3,
    );

    let mut chunk = BytecodeChunk::new();
    chunk.constants = constants;
    chunk.add_function(lambda_func);
    chunk.add_function(main_func);

    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let result = vm
        .execute_function(1)
        .expect("multi-param lambda should execute");
    assert_eq!(result, Value::SmallInt(13));
}

/// Capturing Lambda via MakeClosure: `LET y == 10 IN (LAMBDA x: x + y)(5)` => 15
///
/// The compiler emits MakeClosure to build a closure with y captured from the
/// enclosing scope. The sub-function receives y as an extra parameter after x.
/// ValueApply extracts capture values from the closure env and passes them as
/// extra arguments in alphabetical order.
#[test]
fn test_vm_capturing_lambda_via_make_closure() {
    let mut constants = ConstantPool::new();

    // Sub-function 0: (x, y_capture) => x + y_capture
    // The capture "y" becomes the second parameter.
    let lambda_func = make_func(
        "<lambda@0>".to_string(),
        2, // arity: x + captured y
        vec![
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );

    // Template closure (empty env, bytecode_func_idx = 0, params = ["x"])
    let dummy_body = tla_core::Spanned {
        node: tla_core::ast::Expr::Int(1.into()),
        span: tla_core::Span::default(),
    };
    let template = ClosureValue::new(
        vec!["x".to_string()],
        dummy_body,
        Arc::new(Default::default()),
        None,
    )
    .with_bytecode_func_idx(0);
    let template_idx = constants.add_value(Value::Closure(Arc::new(template)));

    // Capture name "y" follows the template in the constant pool
    constants.add_value(Value::string("y".to_string()));

    // Main function 1:
    //   r0 = 10          (captured value for y)
    //   r1 = MakeClosure(template_idx, captures_start=0, capture_count=1)
    //   r2 = 5           (argument x)
    //   r3 = ValueApply(r1, r2, argc=1)
    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::LoadImm { rd: 0, value: 10 }, // captured y
            Opcode::MakeClosure {
                rd: 1,
                template_idx,
                captures_start: 0,
                capture_count: 1,
            },
            Opcode::LoadImm { rd: 2, value: 5 }, // argument x
            Opcode::ValueApply {
                rd: 3,
                func: 1,
                args_start: 2,
                argc: 1,
            },
            Opcode::Ret { rs: 3 },
        ],
        3,
    );

    let mut chunk = BytecodeChunk::new();
    chunk.constants = constants;
    chunk.add_function(lambda_func);
    chunk.add_function(main_func);

    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let result = vm
        .execute_function(1)
        .expect("capturing lambda should execute");
    assert_eq!(result, Value::SmallInt(15));
}

/// Capturing Lambda with multiple captures:
/// `LET a == 10, b == 20 IN (LAMBDA x: x + a + b)(5)` => 35
///
/// Captures are passed in alphabetical order: a, b.
#[test]
fn test_vm_capturing_lambda_multiple_captures() {
    let mut constants = ConstantPool::new();

    // Sub-function 0: (x, a_capture, b_capture) => x + a + b
    let lambda_func = make_func(
        "<lambda@0>".to_string(),
        3, // arity: x + captured a + captured b
        vec![
            Opcode::AddInt {
                rd: 3,
                r1: 0,
                r2: 1,
            }, // x + a
            Opcode::AddInt {
                rd: 4,
                r1: 3,
                r2: 2,
            }, // (x + a) + b
            Opcode::Ret { rs: 4 },
        ],
        4,
    );

    let dummy_body = tla_core::Spanned {
        node: tla_core::ast::Expr::Int(1.into()),
        span: tla_core::Span::default(),
    };
    let template = ClosureValue::new(
        vec!["x".to_string()],
        dummy_body,
        Arc::new(Default::default()),
        None,
    )
    .with_bytecode_func_idx(0);
    let template_idx = constants.add_value(Value::Closure(Arc::new(template)));

    // Capture names in order: a, b (alphabetical)
    constants.add_value(Value::string("a".to_string()));
    constants.add_value(Value::string("b".to_string()));

    // Main function 1:
    //   r0 = 10 (a), r1 = 20 (b)
    //   r2 = MakeClosure(template, captures=[r0, r1], count=2)
    //   r3 = 5 (argument x)
    //   r4 = ValueApply(r2, r3, argc=1)
    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::LoadImm { rd: 0, value: 10 },
            Opcode::LoadImm { rd: 1, value: 20 },
            Opcode::MakeClosure {
                rd: 2,
                template_idx,
                captures_start: 0,
                capture_count: 2,
            },
            Opcode::LoadImm { rd: 3, value: 5 },
            Opcode::ValueApply {
                rd: 4,
                func: 2,
                args_start: 3,
                argc: 1,
            },
            Opcode::Ret { rs: 4 },
        ],
        4,
    );

    let mut chunk = BytecodeChunk::new();
    chunk.constants = constants;
    chunk.add_function(lambda_func);
    chunk.add_function(main_func);

    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let result = vm
        .execute_function(1)
        .expect("multi-capture lambda should execute");
    assert_eq!(result, Value::SmallInt(35));
}

/// Non-capturing Lambda as a value (not immediately applied):
/// `(LAMBDA x: x + 1)` should produce a closure value.
#[test]
fn test_vm_lambda_as_value_returns_closure() {
    let mut constants = ConstantPool::new();

    // Sub-function 0: lambda body (unused in this test, but must exist)
    let lambda_func = make_func(
        "<lambda@0>".to_string(),
        1,
        vec![
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );

    let closure_val = make_non_capturing_closure(vec!["x".to_string()], 0);
    let closure_idx = constants.add_value(closure_val);

    // Main just loads and returns the closure.
    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::LoadConst {
                rd: 0,
                idx: closure_idx,
            },
            Opcode::Ret { rs: 0 },
        ],
        0,
    );

    let mut chunk = BytecodeChunk::new();
    chunk.constants = constants;
    chunk.add_function(lambda_func);
    chunk.add_function(main_func);

    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let result = vm
        .execute_function(1)
        .expect("lambda-as-value should execute");
    assert!(
        matches!(result, Value::Closure(_)),
        "lambda-as-value should return a closure, got {result:?}"
    );
}

/// MakeClosure produces a closure with captured environment that can
/// be inspected. Verify env keys and values are correct.
#[test]
fn test_vm_make_closure_builds_correct_env() {
    let mut constants = ConstantPool::new();

    // Sub-function 0 (not executed in this test)
    let lambda_func = make_func("<lambda@0>".to_string(), 2, vec![Opcode::Ret { rs: 0 }], 0);

    let dummy_body = tla_core::Spanned {
        node: tla_core::ast::Expr::Int(1.into()),
        span: tla_core::Span::default(),
    };
    let template = ClosureValue::new(
        vec!["x".to_string()],
        dummy_body,
        Arc::new(Default::default()),
        None,
    )
    .with_bytecode_func_idx(0);
    let template_idx = constants.add_value(Value::Closure(Arc::new(template)));
    constants.add_value(Value::string("captured_var".to_string()));

    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::LoadImm { rd: 0, value: 42 },
            Opcode::MakeClosure {
                rd: 1,
                template_idx,
                captures_start: 0,
                capture_count: 1,
            },
            Opcode::Ret { rs: 1 },
        ],
        1,
    );

    let mut chunk = BytecodeChunk::new();
    chunk.constants = constants;
    chunk.add_function(lambda_func);
    chunk.add_function(main_func);

    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let result = vm
        .execute_function(1)
        .expect("MakeClosure should produce a closure value");

    let Value::Closure(ref closure) = result else {
        panic!("MakeClosure result should be a closure, got {result:?}");
    };
    let env = closure.env();
    assert_eq!(env.len(), 1, "closure env should have 1 capture");
    let captured: Arc<str> = Arc::from("captured_var");
    assert_eq!(
        env.get(&captured),
        Some(&Value::SmallInt(42)),
        "captured variable should have value 42"
    );
    assert_eq!(
        closure.bytecode_func_idx(),
        Some(0),
        "closure should retain bytecode_func_idx from template"
    );
}

/// Nested Lambdas: `(LAMBDA f: f(10))((LAMBDA x: x + 1))` => 11
///
/// The outer lambda receives a closure as argument and applies it.
/// Tests that ValueApply can chain through multiple closure invocations.
#[test]
fn test_vm_nested_lambda_application() {
    let mut constants = ConstantPool::new();

    // Sub-function 0: inner lambda (x) => x + 1
    let inner_func = make_func(
        "<inner>".to_string(),
        1,
        vec![
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );

    // Sub-function 1: outer lambda (f) => f(10)
    // Uses ValueApply to call f (a closure) with argument 10.
    let outer_func = make_func(
        "<outer>".to_string(),
        1,
        vec![
            Opcode::LoadImm { rd: 1, value: 10 },
            Opcode::ValueApply {
                rd: 2,
                func: 0,
                args_start: 1,
                argc: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );

    // Closure constants
    let inner_closure = make_non_capturing_closure(vec!["x".to_string()], 0);
    let inner_idx = constants.add_value(inner_closure);

    let outer_closure = make_non_capturing_closure(vec!["f".to_string()], 1);
    let outer_idx = constants.add_value(outer_closure);

    // Main function 2: (outer)(inner) => outer applies inner to 10
    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::LoadConst {
                rd: 0,
                idx: outer_idx,
            },
            Opcode::LoadConst {
                rd: 1,
                idx: inner_idx,
            },
            Opcode::ValueApply {
                rd: 2,
                func: 0,
                args_start: 1,
                argc: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );

    let mut chunk = BytecodeChunk::new();
    chunk.constants = constants;
    chunk.add_function(inner_func);
    chunk.add_function(outer_func);
    chunk.add_function(main_func);

    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let result = vm
        .execute_function(2)
        .expect("nested lambda application should execute");
    assert_eq!(result, Value::SmallInt(11));
}

/// Lambda that calls a LET-scoped operator via Call opcode:
/// `LET F(a) == a + 1 IN (LAMBDA x: F(x))(5)` => 6
///
/// Part of #3776: Lambda bodies can reference LET-scoped operators via the
/// inherited local_op_indices. The sub-function emits a Call opcode targeting
/// the LET operator's function index.
#[test]
fn test_vm_lambda_calling_let_scoped_operator() {
    let mut constants = ConstantPool::new();

    // Sub-function 0: F(a) => a + 1 (the LET-scoped operator)
    let let_op_func = make_func(
        "F".to_string(),
        1,
        vec![
            Opcode::LoadImm { rd: 1, value: 1 },
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );

    // Sub-function 1: lambda body (x) => Call F(x)
    // The lambda body emits Call(op_idx=0, args_start=0, argc=1) targeting F.
    let lambda_func = make_func(
        "<lambda@1>".to_string(),
        1,
        vec![
            Opcode::Call {
                rd: 1,
                op_idx: 0,
                args_start: 0,
                argc: 1,
            },
            Opcode::Ret { rs: 1 },
        ],
        1,
    );

    // Closure constant pointing to sub-function 1 (the lambda)
    let closure_val = make_non_capturing_closure(vec!["x".to_string()], 1);
    let closure_idx = constants.add_value(closure_val);

    // Main function 2: load closure, load 5, ValueApply
    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::LoadConst {
                rd: 0,
                idx: closure_idx,
            },
            Opcode::LoadImm { rd: 1, value: 5 },
            Opcode::ValueApply {
                rd: 2,
                func: 0,
                args_start: 1,
                argc: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );

    let mut chunk = BytecodeChunk::new();
    chunk.constants = constants;
    chunk.add_function(let_op_func);
    chunk.add_function(lambda_func);
    chunk.add_function(main_func);

    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    let result = vm
        .execute_function(2)
        .expect("lambda calling LET-scoped operator should execute");
    assert_eq!(result, Value::SmallInt(6));
}

/// ValueApply arity mismatch: calling a bytecode-compiled closure with wrong
/// argc should fall through to the tree-walk path (which also fails without
/// EvalCtx), producing an unsupported error rather than a panic.
#[test]
fn test_vm_lambda_arity_mismatch_falls_back() {
    let mut constants = ConstantPool::new();

    // Sub-function 0: (x, y) => x + y, arity = 2
    let lambda_func = make_func(
        "<lambda@0>".to_string(),
        2,
        vec![
            Opcode::AddInt {
                rd: 2,
                r1: 0,
                r2: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );

    // Closure with params=["x", "y"], bc_idx=0
    let closure_val = make_non_capturing_closure(vec!["x".to_string(), "y".to_string()], 0);
    let closure_idx = constants.add_value(closure_val);

    // Main: call closure with only 1 arg (arity mismatch: closure needs 2)
    let main_func = make_func(
        "Main".to_string(),
        0,
        vec![
            Opcode::LoadConst {
                rd: 0,
                idx: closure_idx,
            },
            Opcode::LoadImm { rd: 1, value: 5 },
            Opcode::ValueApply {
                rd: 2,
                func: 0,
                args_start: 1,
                argc: 1,
            },
            Opcode::Ret { rs: 2 },
        ],
        2,
    );

    let mut chunk = BytecodeChunk::new();
    chunk.constants = constants;
    chunk.add_function(lambda_func);
    chunk.add_function(main_func);

    let state: Vec<Value> = vec![];
    let mut vm = BytecodeVm::new(&chunk, &state, None);
    // With no EvalCtx, the tree-walk fallback will fail with Unsupported.
    let err = vm
        .execute_function(1)
        .expect_err("arity-mismatched closure apply should error");
    assert!(
        matches!(err, super::VmError::Unsupported(_)),
        "arity mismatch should produce Unsupported error, got {err:?}"
    );
}
