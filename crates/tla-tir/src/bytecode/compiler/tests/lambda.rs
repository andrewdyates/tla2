// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for Lambda expression compilation to bytecode.
//!
//! Part of #3776: Bytecode VM Lambda expression compilation.
//!
//! Covers:
//! - Non-capturing (capture-free) Lambda → closure constant with bytecode_func_idx
//! - Capturing Lambda → MakeClosure opcode with template + capture names
//! - Multi-capture Lambda → correct capture ordering (alphabetical)
//! - Lambda referencing LET-scoped operators → Call opcode in sub-function
//! - Nested Lambda expressions
//! - Lambda with complex body expressions (IF/THEN/ELSE, quantifiers)

use super::*;
use std::sync::Arc;
use tla_core::ast::Expr;

// ---------------------------------------------------------------------------
// Helper: build a TirExpr::Lambda from params, TIR body, and AST body.
// ---------------------------------------------------------------------------
fn make_lambda(params: Vec<&str>, tir_body: TirExpr, ast_body: Expr) -> TirExpr {
    TirExpr::Lambda {
        params: params.into_iter().map(|s| s.to_string()).collect(),
        body: Box::new(spanned(tir_body)),
        ast_body: PreservedAstBody(Arc::new(Spanned {
            node: ast_body,
            span: Span::default(),
        })),
    }
}

fn ast_ident(name: &str) -> Spanned<Expr> {
    Spanned::dummy(Expr::Ident(name.to_string(), tla_core::NameId(0)))
}

fn ast_int(n: i64) -> Spanned<Expr> {
    Spanned::dummy(Expr::Int(n.into()))
}

// ===================================================================
// Non-capturing Lambda tests
// ===================================================================

#[test]
fn test_lambda_simple_add_compiles_to_closure_constant() {
    // LAMBDA x: x + 1
    // Non-capturing → should compile as a LoadConst with a closure value.
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(make_lambda(
        vec!["x"],
        TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirArithOp::Add,
            right: Box::new(spanned(TirExpr::Const {
                value: Value::SmallInt(1),
                ty: TirType::Int,
            })),
        },
        Expr::Add(Box::new(ast_ident("x")), Box::new(ast_int(1))),
    ));
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("capture-free Lambda should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    // Should be LoadConst (closure) + Move/Ret
    let const_idx = match func.instructions[0] {
        Opcode::LoadConst { idx, .. } => idx,
        ref other => panic!("expected LoadConst, got {other:?}"),
    };
    let Value::Closure(closure) = chunk.constants.get_value(const_idx) else {
        panic!("constant pool entry should be a Closure");
    };
    assert_eq!(closure.params(), &["x".to_string()]);
    // Non-capturing lambda should have bytecode_func_idx set (body compiled
    // as a sub-function).
    assert!(
        closure.bytecode_func_idx().is_some(),
        "non-capturing lambda should have bytecode_func_idx set"
    );
}

#[test]
fn test_lambda_identity_compiles() {
    // LAMBDA x: x
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(make_lambda(
        vec!["x"],
        TirExpr::Name(ident_name("x")),
        Expr::Ident("x".to_string(), tla_core::NameId(0)),
    ));
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("identity Lambda should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let const_idx = match func.instructions[0] {
        Opcode::LoadConst { idx, .. } => idx,
        ref other => panic!("expected LoadConst, got {other:?}"),
    };
    let Value::Closure(closure) = chunk.constants.get_value(const_idx) else {
        panic!("expected Closure in constant pool");
    };
    assert_eq!(closure.params(), &["x".to_string()]);
    assert!(closure.bytecode_func_idx().is_some());
}

#[test]
fn test_lambda_multi_param_compiles() {
    // LAMBDA x, y: x + y
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(make_lambda(
        vec!["x", "y"],
        TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirArithOp::Add,
            right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
        },
        Expr::Add(Box::new(ast_ident("x")), Box::new(ast_ident("y"))),
    ));
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("multi-param Lambda should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let const_idx = match func.instructions[0] {
        Opcode::LoadConst { idx, .. } => idx,
        ref other => panic!("expected LoadConst, got {other:?}"),
    };
    let Value::Closure(closure) = chunk.constants.get_value(const_idx) else {
        panic!("expected Closure");
    };
    assert_eq!(closure.params(), &["x".to_string(), "y".to_string()]);
    assert!(closure.bytecode_func_idx().is_some());
}

#[test]
fn test_lambda_retains_tir_body() {
    // Verify that compiled closures preserve the TIR body for fallback evaluation.
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(make_lambda(
        vec!["x"],
        TirExpr::ArithNeg(Box::new(spanned(TirExpr::Name(ident_name("x"))))),
        Expr::Neg(Box::new(ast_ident("x"))),
    ));
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("Lambda should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let const_idx = match func.instructions[0] {
        Opcode::LoadConst { idx, .. } => idx,
        ref other => panic!("expected LoadConst, got {other:?}"),
    };
    let Value::Closure(closure) = chunk.constants.get_value(const_idx) else {
        panic!("expected Closure");
    };
    assert!(
        closure.tir_body().is_some(),
        "compiled Lambda closure must retain its TIR body for tree-walker fallback"
    );
    let stored = closure
        .tir_body()
        .and_then(|body| body.as_any().downcast_ref::<crate::StoredTirBody>())
        .expect("TIR body should be a StoredTirBody");
    assert!(
        matches!(stored.expr().node, TirExpr::ArithNeg(_)),
        "stored TIR body should match the original Lambda body"
    );
}

// ===================================================================
// Capturing Lambda tests
// ===================================================================

#[test]
fn test_capturing_lambda_emits_make_closure() {
    // LAMBDA x: x + y  (y is captured from enclosing scope)
    // Part of #3776: capturing lambdas should compile to MakeClosure.
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(make_lambda(
        vec!["x"],
        TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirArithOp::Add,
            right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
        },
        Expr::Add(Box::new(ast_ident("x")), Box::new(ast_ident("y"))),
    ));
    let idx = compiler
        .compile_expression_with_callees("Make", &["y".to_string()], &expr, &Default::default())
        .expect("capturing lambda should compile via MakeClosure");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let has_make_closure = func.instructions.iter().any(|op| {
        matches!(
            op,
            Opcode::MakeClosure {
                capture_count: 1,
                ..
            }
        )
    });
    assert!(
        has_make_closure,
        "capturing lambda should emit MakeClosure with 1 capture: {:?}",
        func.instructions
    );
}

#[test]
fn test_capturing_lambda_stores_capture_names_in_constant_pool() {
    // Verify that capture names appear in the constant pool immediately after
    // the template closure.
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(make_lambda(
        vec!["x"],
        TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirArithOp::Add,
            right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
        },
        Expr::Add(Box::new(ast_ident("x")), Box::new(ast_ident("y"))),
    ));
    let idx = compiler
        .compile_expression_with_callees("Make", &["y".to_string()], &expr, &Default::default())
        .expect("should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let make_op = func
        .instructions
        .iter()
        .find(|op| matches!(op, Opcode::MakeClosure { .. }))
        .expect("should have MakeClosure");
    let template_idx = match make_op {
        Opcode::MakeClosure { template_idx, .. } => *template_idx,
        _ => unreachable!(),
    };

    assert!(
        matches!(chunk.constants.get_value(template_idx), Value::Closure(_)),
        "template_idx should point to a Closure"
    );
    assert_eq!(
        chunk.constants.get_value(template_idx + 1),
        &Value::string("y"),
        "capture name at template_idx+1 should be 'y'"
    );
}

#[test]
fn test_multi_capture_lambda_alphabetical_order() {
    // LAMBDA x: x + y + z  (captures y and z, sorted alphabetically)
    // Part of #3776: capture order must be alphabetical for deterministic
    // matching between compile-time parameter order and runtime extraction.
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(make_lambda(
        vec!["x"],
        TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Name(ident_name("z")))),
            })),
            op: TirArithOp::Add,
            right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
        },
        Expr::Add(
            Box::new(Spanned::dummy(Expr::Add(
                Box::new(ast_ident("x")),
                Box::new(ast_ident("z")),
            ))),
            Box::new(ast_ident("y")),
        ),
    ));
    // Enclosing scope has params z, y (reverse alphabetical) — the compiler
    // should sort captures to (y, z) regardless of source order.
    let idx = compiler
        .compile_expression_with_callees(
            "Make",
            &["z".to_string(), "y".to_string()],
            &expr,
            &Default::default(),
        )
        .expect("multi-capture lambda should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let make_op = func
        .instructions
        .iter()
        .find(|op| matches!(op, Opcode::MakeClosure { .. }))
        .expect("should have MakeClosure");
    let (template_idx, capture_count) = match make_op {
        Opcode::MakeClosure {
            template_idx,
            capture_count,
            ..
        } => (*template_idx, *capture_count),
        _ => unreachable!(),
    };

    assert_eq!(capture_count, 2, "should capture 2 variables");
    // Capture names in constant pool must be alphabetically sorted.
    assert_eq!(
        chunk.constants.get_value(template_idx + 1),
        &Value::string("y"),
        "first capture name should be 'y' (alphabetical)"
    );
    assert_eq!(
        chunk.constants.get_value(template_idx + 2),
        &Value::string("z"),
        "second capture name should be 'z' (alphabetical)"
    );
}

#[test]
fn test_capturing_lambda_template_has_bytecode_func_idx() {
    // Capturing lambdas should also compile the body as a sub-function.
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(make_lambda(
        vec!["x"],
        TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirArithOp::Mul,
            right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
        },
        Expr::Mul(Box::new(ast_ident("x")), Box::new(ast_ident("y"))),
    ));
    let idx = compiler
        .compile_expression_with_callees("Make", &["y".to_string()], &expr, &Default::default())
        .expect("should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let template_idx = func
        .instructions
        .iter()
        .find_map(|op| match op {
            Opcode::MakeClosure { template_idx, .. } => Some(*template_idx),
            _ => None,
        })
        .expect("should have MakeClosure");

    let Value::Closure(closure) = chunk.constants.get_value(template_idx) else {
        panic!("template should be a Closure");
    };
    assert!(
        closure.bytecode_func_idx().is_some(),
        "capturing lambda's template closure should have bytecode_func_idx \
         (body compiled as sub-function with captures as extra params)"
    );
}

// ===================================================================
// Lambda with LET-scoped operators
// ===================================================================

#[test]
fn test_lambda_calls_let_operator() {
    // LET F(a) == a + 1 IN LAMBDA x: F(x)
    // Part of #3776: Lambda bodies can reference LET-scoped operators via
    // the inherited local_op_indices map.
    let mut compiler = BytecodeCompiler::new();
    let body = spanned(TirExpr::Let {
        defs: vec![TirLetDef {
            name: "F".to_string(),
            name_id: tla_core::NameId(0),
            params: vec!["a".to_string()],
            body: spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Name(ident_name("a")))),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(1),
                    ty: TirType::Int,
                })),
            }),
        }],
        body: Box::new(spanned(make_lambda(
            vec!["x"],
            TirExpr::Apply {
                op: Box::new(spanned(TirExpr::Name(ident_name("F")))),
                args: vec![spanned(TirExpr::Name(ident_name("x")))],
            },
            Expr::Apply(
                Box::new(ast_ident("F")),
                vec![Spanned::dummy(Expr::Ident(
                    "x".to_string(),
                    tla_core::NameId(0),
                ))],
            ),
        ))),
    });
    let result = compiler.compile_expression_with_callees("Main", &[], &body, &Default::default());
    assert!(
        result.is_ok(),
        "lambda referencing LET-scoped operator should compile: {result:?}"
    );
    let chunk = compiler.finish();
    let func = chunk.get_function(result.unwrap());

    // The main function should emit LoadConst for the closure.
    let has_load_const = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::LoadConst { .. }));
    assert!(
        has_load_const,
        "lambda should emit LoadConst for closure value: {:?}",
        func.instructions
    );
}

// ===================================================================
// Lambda with complex body expressions
// ===================================================================

#[test]
fn test_lambda_with_if_then_else_body() {
    // LAMBDA x: IF x > 0 THEN x ELSE -x
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(make_lambda(
        vec!["x"],
        TirExpr::If {
            cond: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirCmpOp::Gt,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(0),
                    ty: TirType::Int,
                })),
            })),
            then_: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            else_: Box::new(spanned(TirExpr::ArithNeg(Box::new(spanned(
                TirExpr::Name(ident_name("x")),
            ))))),
        },
        Expr::If(
            Box::new(Spanned::dummy(Expr::Gt(
                Box::new(ast_ident("x")),
                Box::new(ast_int(0)),
            ))),
            Box::new(ast_ident("x")),
            Box::new(Spanned::dummy(Expr::Neg(Box::new(ast_ident("x"))))),
        ),
    ));
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("Lambda with IF body should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let const_idx = match func.instructions[0] {
        Opcode::LoadConst { idx, .. } => idx,
        ref other => panic!("expected LoadConst, got {other:?}"),
    };
    let Value::Closure(closure) = chunk.constants.get_value(const_idx) else {
        panic!("expected Closure");
    };
    assert!(
        closure.bytecode_func_idx().is_some(),
        "Lambda with IF body should compile to bytecode sub-function"
    );
}

#[test]
fn test_lambda_with_boolean_body() {
    // LAMBDA x, y: x /\ y
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(make_lambda(
        vec!["x", "y"],
        TirExpr::BoolBinOp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirBoolOp::And,
            right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
        },
        Expr::And(Box::new(ast_ident("x")), Box::new(ast_ident("y"))),
    ));
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("Lambda with boolean body should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let const_idx = match func.instructions[0] {
        Opcode::LoadConst { idx, .. } => idx,
        ref other => panic!("expected LoadConst, got {other:?}"),
    };
    let Value::Closure(closure) = chunk.constants.get_value(const_idx) else {
        panic!("expected Closure");
    };
    assert_eq!(closure.params(), &["x".to_string(), "y".to_string()]);
    assert!(closure.bytecode_func_idx().is_some());
}

#[test]
fn test_lambda_with_constant_body() {
    // LAMBDA x: 42  (body is a constant, trivial compilation)
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(make_lambda(
        vec!["x"],
        TirExpr::Const {
            value: Value::SmallInt(42),
            ty: TirType::Int,
        },
        Expr::Int(42.into()),
    ));
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("Lambda with constant body should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let const_idx = match func.instructions[0] {
        Opcode::LoadConst { idx, .. } => idx,
        ref other => panic!("expected LoadConst, got {other:?}"),
    };
    let Value::Closure(closure) = chunk.constants.get_value(const_idx) else {
        panic!("expected Closure");
    };
    assert!(closure.bytecode_func_idx().is_some());
}

// ===================================================================
// Sub-function verification
// ===================================================================

#[test]
fn test_lambda_sub_function_has_correct_arity() {
    // LAMBDA x, y: x - y
    // The compiled sub-function should have arity 2.
    // Use compile_expression_with_callees so sub-functions are added to chunk.
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(make_lambda(
        vec!["x", "y"],
        TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirArithOp::Sub,
            right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
        },
        Expr::Sub(Box::new(ast_ident("x")), Box::new(ast_ident("y"))),
    ));
    let idx = compiler
        .compile_expression_with_callees("test", &[], &expr, &Default::default())
        .expect("should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let const_idx = match func.instructions[0] {
        Opcode::LoadConst { idx, .. } => idx,
        ref other => panic!("expected LoadConst, got {other:?}"),
    };
    let Value::Closure(closure) = chunk.constants.get_value(const_idx) else {
        panic!("expected Closure");
    };
    let sub_func_idx = closure
        .bytecode_func_idx()
        .expect("should have bytecode_func_idx");
    let sub_func = chunk.get_function(sub_func_idx);
    assert_eq!(
        sub_func.arity, 2,
        "sub-function arity should match Lambda param count"
    );
}

#[test]
fn test_capturing_lambda_sub_function_includes_capture_params() {
    // LAMBDA x: x + y  (captures y)
    // Sub-function should have arity 2 (x + captured y).
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(make_lambda(
        vec!["x"],
        TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirArithOp::Add,
            right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
        },
        Expr::Add(Box::new(ast_ident("x")), Box::new(ast_ident("y"))),
    ));
    let idx = compiler
        .compile_expression_with_callees("Make", &["y".to_string()], &expr, &Default::default())
        .expect("should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let template_idx = func
        .instructions
        .iter()
        .find_map(|op| match op {
            Opcode::MakeClosure { template_idx, .. } => Some(*template_idx),
            _ => None,
        })
        .expect("should have MakeClosure");

    let Value::Closure(closure) = chunk.constants.get_value(template_idx) else {
        panic!("expected Closure");
    };
    let sub_func_idx = closure
        .bytecode_func_idx()
        .expect("should have bytecode_func_idx");
    let sub_func = chunk.get_function(sub_func_idx);
    assert_eq!(
        sub_func.arity, 2,
        "sub-function arity should be params(1) + captures(1) = 2"
    );
}

#[test]
fn test_lambda_sub_function_ends_with_ret() {
    // Every compiled sub-function must end with a Ret opcode.
    // Use compile_expression_with_callees so sub-functions are added to chunk.
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(make_lambda(
        vec!["x"],
        TirExpr::Name(ident_name("x")),
        Expr::Ident("x".to_string(), tla_core::NameId(0)),
    ));
    let idx = compiler
        .compile_expression_with_callees("test", &[], &expr, &Default::default())
        .expect("should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    let const_idx = match func.instructions[0] {
        Opcode::LoadConst { idx, .. } => idx,
        ref other => panic!("expected LoadConst, got {other:?}"),
    };
    let Value::Closure(closure) = chunk.constants.get_value(const_idx) else {
        panic!("expected Closure");
    };
    let sub_func = chunk.get_function(closure.bytecode_func_idx().unwrap());
    assert!(
        matches!(sub_func.instructions.last(), Some(Opcode::Ret { .. })),
        "sub-function must end with Ret: {:?}",
        sub_func.instructions
    );
}
