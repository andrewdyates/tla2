// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::Arc;
use tla_core::ast::Expr;

#[test]
fn test_compile_if_then_else() {
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::If {
        cond: Box::new(spanned(TirExpr::Const {
            value: Value::Bool(true),
            ty: TirType::Bool,
        })),
        then_: Box::new(spanned(TirExpr::Const {
            value: Value::SmallInt(1),
            ty: TirType::Int,
        })),
        else_: Box::new(spanned(TirExpr::Const {
            value: Value::SmallInt(0),
            ty: TirType::Int,
        })),
    });
    let idx = compiler.compile_expression("test", &expr).unwrap();
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    assert_eq!(
        func.instructions.len(),
        9,
        "IF lowering should emit the full branch skeleton: {:?}",
        func.instructions
    );
    assert!(matches!(
        func.instructions[0],
        Opcode::LoadBool { rd: 0, value: true }
    ));
    assert!(matches!(
        func.instructions[1],
        Opcode::JumpFalse { rs: 0, offset: 4 }
    ));
    assert!(matches!(
        func.instructions[2],
        Opcode::LoadImm { rd: 2, value: 1 }
    ));
    assert!(matches!(
        func.instructions[3],
        Opcode::Move { rd: 1, rs: 2 }
    ));
    assert!(matches!(func.instructions[4], Opcode::Jump { offset: 3 }));
    assert!(matches!(
        func.instructions[5],
        Opcode::LoadImm { rd: 3, value: 0 }
    ));
    assert!(matches!(
        func.instructions[6],
        Opcode::Move { rd: 1, rs: 3 }
    ));
    assert!(matches!(
        func.instructions[7],
        Opcode::Move { rd: 0, rs: 1 }
    ));
    assert!(matches!(func.instructions[8], Opcode::Ret { rs: 0 }));
}

#[test]
fn test_compile_short_circuit_and() {
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::BoolBinOp {
        left: Box::new(spanned(TirExpr::Const {
            value: Value::Bool(false),
            ty: TirType::Bool,
        })),
        op: TirBoolOp::And,
        right: Box::new(spanned(TirExpr::Const {
            value: Value::Bool(true),
            ty: TirType::Bool,
        })),
    });
    let idx = compiler.compile_expression("test", &expr).unwrap();
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // Should have short-circuit JumpFalse.
    let has_jump_false = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::JumpFalse { .. }));
    assert!(has_jump_false, "expected JumpFalse for short-circuit AND");
}

#[test]
fn test_compile_op_ref_as_closure_constant() {
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::OpRef("+".to_string()));
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("OpRef should compile as a closure constant");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let const_idx = match func.instructions[0] {
        Opcode::LoadConst { idx, .. } => idx,
        ref other => panic!("OpRef should load a closure constant, got {other:?}"),
    };
    assert!(
        matches!(chunk.constants.get_value(const_idx), Value::Closure(_)),
        "OpRef constant pool entry should be a closure"
    );
}

#[test]
fn test_compile_capture_free_lambda_as_closure_constant() {
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Lambda {
        params: vec!["x".to_string()],
        body: Box::new(spanned(TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirArithOp::Add,
            right: Box::new(spanned(TirExpr::Const {
                value: Value::SmallInt(1),
                ty: TirType::Int,
            })),
        })),
        ast_body: PreservedAstBody(Arc::new(Spanned {
            node: Expr::Add(
                Box::new(Spanned::dummy(Expr::Ident(
                    "x".to_string(),
                    tla_core::NameId(0),
                ))),
                Box::new(Spanned::dummy(Expr::Int(1.into()))),
            ),
            span: Span::default(),
        })),
    });
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("capture-free Lambda should compile as a closure constant");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let const_idx = match func.instructions[0] {
        Opcode::LoadConst { idx, .. } => idx,
        ref other => panic!("Lambda should load a closure constant, got {other:?}"),
    };
    let Value::Closure(closure) = chunk.constants.get_value(const_idx) else {
        panic!("Lambda constant pool entry should be a closure");
    };
    assert_eq!(closure.params(), ["x".to_string()]);
    assert!(
        closure.tir_body().is_some(),
        "compiled lambda closure should retain its lowered TIR body",
    );
    let stored = closure
        .tir_body()
        .and_then(|body| body.as_any().downcast_ref::<crate::StoredTirBody>())
        .expect("compiled lambda closure should store a tla-tir StoredTirBody");
    assert!(
        matches!(stored.expr().node, TirExpr::ArithBinOp { .. }),
        "expected stored TIR body to match the lowered lambda body",
    );
}

#[test]
fn test_capturing_lambda_compiles_via_make_closure() {
    // LAMBDA x: x + y  where y is a parameter of the enclosing operator.
    // Part of #3697: capturing lambdas should compile to MakeClosure.
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Lambda {
        params: vec!["x".to_string()],
        body: Box::new(spanned(TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirArithOp::Add,
            right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
        })),
        ast_body: PreservedAstBody(Arc::new(Spanned {
            node: Expr::Add(
                Box::new(Spanned::dummy(Expr::Ident(
                    "x".to_string(),
                    tla_core::NameId(0),
                ))),
                Box::new(Spanned::dummy(Expr::Ident(
                    "y".to_string(),
                    tla_core::NameId(0),
                ))),
            ),
            span: Span::default(),
        })),
    });
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
    // Verify the template closure and capture name are in the constant pool.
    let make_closure_op = func
        .instructions
        .iter()
        .find(|op| matches!(op, Opcode::MakeClosure { .. }))
        .unwrap();
    let (template_idx, _) = match make_closure_op {
        Opcode::MakeClosure {
            template_idx,
            capture_count,
            ..
        } => (*template_idx, *capture_count),
        _ => unreachable!(),
    };
    assert!(
        matches!(chunk.constants.get_value(template_idx), Value::Closure(_)),
        "template_idx should point to a closure constant"
    );
    assert_eq!(
        chunk.constants.get_value(template_idx + 1),
        &Value::string("y"),
        "capture name at template_idx+1 should be 'y'"
    );
}

#[test]
fn test_lambda_referencing_local_op_compiles_with_call() {
    // LET F(a) == a IN LAMBDA x: F(x)
    // Part of #3776: Lambda bodies can reference LET-scoped operators via
    // the inherited local_op_indices map. The sub-function compilation
    // context preserves the parent's local_op_indices, so Call opcodes
    // resolve normally.
    let mut compiler = BytecodeCompiler::new();
    let body = spanned(TirExpr::Let {
        defs: vec![TirLetDef {
            name: "F".to_string(),
            name_id: tla_core::NameId(0),
            params: vec!["a".to_string()],
            body: spanned(TirExpr::Name(ident_name("a"))),
        }],
        body: Box::new(spanned(TirExpr::Lambda {
            params: vec!["x".to_string()],
            body: Box::new(spanned(TirExpr::Apply {
                op: Box::new(spanned(TirExpr::Name(ident_name("F")))),
                args: vec![spanned(TirExpr::Name(ident_name("x")))],
            })),
            ast_body: PreservedAstBody(Arc::new(Spanned {
                node: Expr::Apply(
                    Box::new(Spanned::dummy(Expr::Ident(
                        "F".to_string(),
                        tla_core::NameId(0),
                    ))),
                    vec![Spanned::dummy(Expr::Ident(
                        "x".to_string(),
                        tla_core::NameId(0),
                    ))],
                ),
                span: Span::default(),
            })),
        })),
    });
    let result = compiler.compile_expression_with_callees("Main", &[], &body, &Default::default());
    assert!(
        result.is_ok(),
        "lambda referencing a LET-scoped operator should compile successfully: {result:?}"
    );
    let chunk = compiler.finish();
    let func = chunk.get_function(result.unwrap());
    // The lambda should produce a closure constant with a bytecode_func_idx
    // (the body was compiled as a sub-function that uses Call to invoke F).
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

#[test]
fn test_compile_zero_arg_call() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "N".to_string(),
        CalleeInfo {
            params: vec![],
            body: Arc::new(spanned(TirExpr::Const {
                value: Value::SmallInt(42),
                ty: TirType::Int,
            })),
            ast_body: None,
        },
    );
    let main_body = spanned(TirExpr::ArithBinOp {
        left: Box::new(spanned(TirExpr::Name(ident_name("N")))),
        op: TirArithOp::Add,
        right: Box::new(spanned(TirExpr::Const {
            value: Value::SmallInt(1),
            ty: TirType::Int,
        })),
    });
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &main_body, &callees)
        .expect("should compile Main with zero-arg call to N");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 0, .. }));
    assert!(has_call, "Main should contain Call(argc=0) for N");
}

#[test]
fn test_compile_parameterized_call() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "Add".to_string(),
        CalleeInfo {
            params: vec!["x".to_string(), "y".to_string()],
            body: Arc::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
            })),
            ast_body: None,
        },
    );
    let main_body = spanned(TirExpr::Apply {
        op: Box::new(spanned(TirExpr::Name(ident_name("Add")))),
        args: vec![
            spanned(TirExpr::Const {
                value: Value::SmallInt(3),
                ty: TirType::Int,
            }),
            spanned(TirExpr::Const {
                value: Value::SmallInt(4),
                ty: TirType::Int,
            }),
        ],
    });
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &main_body, &callees)
        .expect("should compile Main with parameterized call to Add");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 2, .. }));
    assert!(has_call, "Main should contain Call(argc=2) for Add");
}

#[test]
fn test_compile_parameterized_operator_reference_as_tir_backed_closure() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "Add".to_string(),
        CalleeInfo {
            params: vec!["x".to_string()],
            body: Arc::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(1),
                    ty: TirType::Int,
                })),
            })),
            ast_body: Some(PreservedAstBody(Arc::new(Spanned {
                node: Expr::Add(
                    Box::new(Spanned::dummy(Expr::Ident(
                        "x".to_string(),
                        tla_core::NameId(0),
                    ))),
                    Box::new(Spanned::dummy(Expr::Int(1.into()))),
                ),
                span: Span::default(),
            }))),
        },
    );

    let idx = compiler
        .compile_expression_with_callees(
            "Main",
            &[],
            &spanned(TirExpr::Name(ident_name("Add"))),
            &callees,
        )
        .expect("parameterized operator reference should compile as a closure value");

    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let const_idx = match func.instructions[0] {
        Opcode::LoadConst { idx, .. } => idx,
        ref other => panic!("operator reference should load a closure constant, got {other:?}"),
    };
    let Value::Closure(closure) = chunk.constants.get_value(const_idx) else {
        panic!("parameterized operator reference should lower to a closure constant");
    };
    assert_eq!(closure.params(), ["x".to_string()]);
    let stored = closure
        .tir_body()
        .and_then(|body| body.as_any().downcast_ref::<crate::StoredTirBody>())
        .expect("compiled operator reference should store a tla-tir StoredTirBody");
    assert!(
        matches!(stored.expr().node, TirExpr::ArithBinOp { .. }),
        "expected stored TIR body to match the lowered operator body",
    );
}

#[test]
fn test_compile_parameterized_call_with_complex_arg() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "Id".to_string(),
        CalleeInfo {
            params: vec!["x".to_string()],
            body: Arc::new(spanned(TirExpr::Const {
                value: Value::Bool(true),
                ty: TirType::Bool,
            })),
            ast_body: None,
        },
    );
    // Call Id(1 \div 0) — complex expression as argument should compile.
    let main_body = spanned(TirExpr::Apply {
        op: Box::new(spanned(TirExpr::Name(ident_name("Id")))),
        args: vec![spanned(TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Const {
                value: Value::SmallInt(1),
                ty: TirType::Int,
            })),
            op: TirArithOp::Div,
            right: Box::new(spanned(TirExpr::Const {
                value: Value::SmallInt(0),
                ty: TirType::Int,
            })),
        })],
    });
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &main_body, &callees)
        .expect("complex call args should compile to bytecode");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    assert_eq!(
        func.instructions.len(),
        7,
        "complex arg call should materialize the arg, pack it into the reserved slot, and Call: {:?}",
        func.instructions
    );
    assert!(matches!(
        func.instructions[0],
        Opcode::LoadImm { rd: 1, value: 1 }
    ));
    assert!(matches!(
        func.instructions[1],
        Opcode::LoadImm { rd: 2, value: 0 }
    ));
    assert!(matches!(
        func.instructions[2],
        Opcode::DivInt {
            rd: 3,
            r1: 1,
            r2: 2
        }
    ));
    assert!(matches!(
        func.instructions[3],
        Opcode::Move { rd: 0, rs: 3 }
    ));
    assert!(matches!(
        func.instructions[4],
        Opcode::Call {
            rd: 4,
            args_start: 0,
            argc: 1,
            ..
        }
    ));
    assert!(matches!(
        func.instructions[5],
        Opcode::Move { rd: 0, rs: 4 }
    ));
    assert!(matches!(func.instructions[6], Opcode::Ret { rs: 0 }));
}

#[test]
fn test_recursive_call_rejected() {
    let mut compiler = BytecodeCompiler::new();
    let callees = std::collections::HashMap::new();
    let fib_body = spanned(TirExpr::Apply {
        op: Box::new(spanned(TirExpr::Name(ident_name("Fib")))),
        args: vec![spanned(TirExpr::Const {
            value: Value::SmallInt(1),
            ty: TirType::Int,
        })],
    });
    let result =
        compiler.compile_expression_with_callees("Fib", &["n".to_string()], &fib_body, &callees);
    assert!(result.is_err(), "recursive operator should fail to compile");
}

#[test]
fn test_compile_bound_name_apply_uses_value_apply() {
    let mut compiler = BytecodeCompiler::new();
    let body = spanned(TirExpr::Apply {
        op: Box::new(spanned(TirExpr::Name(ident_name("f")))),
        args: vec![spanned(TirExpr::Const {
            value: Value::SmallInt(3),
            ty: TirType::Int,
        })],
    });
    let idx = compiler
        .compile_expression_with_callees("Use", &["f".to_string()], &body, &Default::default())
        .expect("bound callable apply should compile via ValueApply");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    assert!(
        func.instructions
            .iter()
            .any(|op| matches!(op, Opcode::ValueApply { argc: 1, .. })),
        "bound callable apply should emit ValueApply, got {:?}",
        func.instructions
    );
}

#[test]
fn test_compile_multi_arg_higher_order_apply_uses_value_apply() {
    let mut compiler = BytecodeCompiler::new();
    let body = spanned(TirExpr::Apply {
        op: Box::new(spanned(TirExpr::Name(ident_name("f")))),
        args: vec![
            spanned(TirExpr::Const {
                value: Value::SmallInt(1),
                ty: TirType::Int,
            }),
            spanned(TirExpr::Const {
                value: Value::SmallInt(2),
                ty: TirType::Int,
            }),
        ],
    });
    let idx = compiler
        .compile_expression_with_callees("Use", &["f".to_string()], &body, &Default::default())
        .expect("multi-arg higher-order apply should compile via ValueApply");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    assert!(
        func.instructions
            .iter()
            .any(|op| matches!(op, Opcode::ValueApply { argc: 2, .. })),
        "multi-arg higher-order apply should emit ValueApply, got {:?}",
        func.instructions
    );
}

#[test]
fn test_compile_parameterized_let() {
    // LET Greater(x, y) == x > y IN IF Greater(a, b) THEN a ELSE b
    // where a=3, b=5 are constants standing in for state vars.
    let mut compiler = BytecodeCompiler::new();
    let callees = std::collections::HashMap::new();

    let body = spanned(TirExpr::Let {
        defs: vec![TirLetDef {
            name: "Greater".to_string(),
            name_id: tla_core::NameId(0),
            params: vec!["x".to_string(), "y".to_string()],
            body: spanned(TirExpr::Cmp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirCmpOp::Gt,
                right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
            }),
        }],
        body: Box::new(spanned(TirExpr::If {
            cond: Box::new(spanned(TirExpr::Apply {
                op: Box::new(spanned(TirExpr::Name(ident_name("Greater")))),
                args: vec![
                    spanned(TirExpr::Const {
                        value: Value::SmallInt(3),
                        ty: TirType::Int,
                    }),
                    spanned(TirExpr::Const {
                        value: Value::SmallInt(5),
                        ty: TirType::Int,
                    }),
                ],
            })),
            then_: Box::new(spanned(TirExpr::Const {
                value: Value::SmallInt(3),
                ty: TirType::Int,
            })),
            else_: Box::new(spanned(TirExpr::Const {
                value: Value::SmallInt(5),
                ty: TirType::Int,
            })),
        })),
    });

    let idx = compiler
        .compile_expression_with_callees("Max", &[], &body, &callees)
        .expect("parameterized LET should compile as sub-function");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // The body should contain a Call to the LET-compiled "Greater" sub-function.
    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 2, .. }));
    assert!(has_call, "Max should contain Call(argc=2) for LET Greater");
    // The chunk should have at least 2 functions: Greater + Max.
    assert!(
        chunk.function_count() >= 2,
        "chunk should contain at least 2 functions (Greater + Max), got {}",
        chunk.function_count()
    );
}

#[test]
fn test_op_replacement_resolves_callee() {
    // Simulate CONSTANT Jug <- MCJug:
    // Callee is registered under "MCJug", but invariant body references "Jug".
    // With op_replacements, "Jug" should resolve to "MCJug" via Call.
    let mut compiler = BytecodeCompiler::new();
    let mut replacements = std::collections::HashMap::new();
    replacements.insert("Jug".to_string(), "MCJug".to_string());
    compiler.set_op_replacements(replacements);

    // Callee body: MCJug == 42
    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "MCJug".to_string(),
        CalleeInfo {
            params: vec![],
            body: Arc::new(spanned(TirExpr::Const {
                value: Value::SmallInt(42),
                ty: TirType::Int,
            })),
            ast_body: None,
        },
    );

    // Entry: Inv == Jug > 0  (references "Jug" which is replaced by "MCJug")
    let body = spanned(TirExpr::Cmp {
        left: Box::new(spanned(TirExpr::Name(ident_name("Jug")))),
        op: TirCmpOp::Gt,
        right: Box::new(spanned(TirExpr::Const {
            value: Value::SmallInt(0),
            ty: TirType::Int,
        })),
    });

    let idx = compiler
        .compile_expression_with_callees("Inv", &[], &body, &callees)
        .expect("operator replacement should resolve Jug -> MCJug");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // Should contain a Call to the MCJug operator.
    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 0, .. }));
    assert!(
        has_call,
        "Inv body should Call MCJug via operator replacement"
    );
}

#[test]
fn test_compile_apply_with_computed_op_uses_value_apply() {
    // Apply where op is a computed expression (FuncApply), not a Name.
    // Example: (f[x])(y) — the operator position is f[x], which is a FuncApply.
    // This exercises the `_ => self.compile_value_apply(op, args)` arm.
    let mut compiler = BytecodeCompiler::new();
    let body = spanned(TirExpr::Apply {
        op: Box::new(spanned(TirExpr::FuncApply {
            func: Box::new(spanned(TirExpr::Name(ident_name("f")))),
            arg: Box::new(spanned(TirExpr::Const {
                value: Value::SmallInt(1),
                ty: TirType::Dyn,
            })),
        })),
        args: vec![spanned(TirExpr::Const {
            value: Value::SmallInt(2),
            ty: TirType::Int,
        })],
    });
    let idx = compiler
        .compile_expression_with_callees("Use", &["f".to_string()], &body, &Default::default())
        .expect("Apply with computed op (FuncApply) should compile via ValueApply");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    assert!(
        func.instructions
            .iter()
            .any(|op| matches!(op, Opcode::ValueApply { argc: 1, .. })),
        "Apply with computed op should emit ValueApply, got {:?}",
        func.instructions
    );
    // Also verify that the FuncApply for f[x] appears before the ValueApply.
    let has_func_apply = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::FuncApply { .. }));
    assert!(
        has_func_apply,
        "the computed op (f[x]) should emit FuncApply: {:?}",
        func.instructions
    );
}

#[test]
fn test_compile_apply_with_if_op_uses_value_apply() {
    // Apply where op is an IF-THEN-ELSE expression.
    // Example: (IF b THEN f ELSE g)(x) — the operator position is a conditional.
    let mut compiler = BytecodeCompiler::new();
    let body = spanned(TirExpr::Apply {
        op: Box::new(spanned(TirExpr::If {
            cond: Box::new(spanned(TirExpr::Name(ident_name("b")))),
            then_: Box::new(spanned(TirExpr::Name(ident_name("f")))),
            else_: Box::new(spanned(TirExpr::Name(ident_name("g")))),
        })),
        args: vec![spanned(TirExpr::Const {
            value: Value::SmallInt(5),
            ty: TirType::Int,
        })],
    });
    let idx = compiler
        .compile_expression_with_callees(
            "Use",
            &["b".to_string(), "f".to_string(), "g".to_string()],
            &body,
            &Default::default(),
        )
        .expect("Apply with IF op should compile via ValueApply");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    assert!(
        func.instructions
            .iter()
            .any(|op| matches!(op, Opcode::ValueApply { argc: 1, .. })),
        "Apply with IF op should emit ValueApply, got {:?}",
        func.instructions
    );
}

fn state_var_name(name: &str, index: u16) -> TirNameRef {
    TirNameRef {
        name: name.to_string(),
        name_id: tla_core::NameId(0),
        kind: TirNameKind::StateVar { index },
        ty: TirType::Dyn,
    }
}

#[test]
fn test_compile_unchanged_single_var() {
    let mut compiler = BytecodeCompiler::new();
    let inner = spanned(TirExpr::Name(state_var_name("x", 0)));
    let expr = spanned(TirExpr::Unchanged(Box::new(inner)));
    let idx = compiler.compile_expression("test", &expr).unwrap();
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let has_unchanged = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Unchanged { count: 1, .. }));
    assert!(
        has_unchanged,
        "single-var UNCHANGED should emit Unchanged opcode: {:?}",
        func.instructions
    );
}

#[test]
fn test_compile_unchanged_tuple() {
    let mut compiler = BytecodeCompiler::new();
    let inner = spanned(TirExpr::Tuple(vec![
        spanned(TirExpr::Name(state_var_name("x", 0))),
        spanned(TirExpr::Name(state_var_name("y", 1))),
    ]));
    let expr = spanned(TirExpr::Unchanged(Box::new(inner)));
    let idx = compiler.compile_expression("test", &expr).unwrap();
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let has_unchanged = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Unchanged { count: 2, .. }));
    assert!(
        has_unchanged,
        "tuple UNCHANGED should emit Unchanged with count=2: {:?}",
        func.instructions
    );
}

#[test]
fn test_compile_unchanged_non_statevar_fails() {
    let mut compiler = BytecodeCompiler::new();
    let inner = spanned(TirExpr::Name(ident_name("z")));
    let expr = spanned(TirExpr::Unchanged(Box::new(inner)));
    let result = compiler.compile_expression("test", &expr);
    assert!(
        matches!(result, Err(CompileError::Unsupported(_))),
        "UNCHANGED on non-state-variable should be unsupported: {result:?}"
    );
}

#[test]
fn test_compile_operator_ref_zero_arg_emits_call() {
    // OperatorRef with empty path and no args should emit a Call opcode
    // when the operator is pre-compiled in callee_bodies.
    use crate::nodes::TirOperatorRef;
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "AllocInv".to_string(),
        CalleeInfo {
            params: vec![],
            body: Arc::new(spanned(TirExpr::Const {
                value: Value::Bool(true),
                ty: TirType::Bool,
            })),
            ast_body: None,
        },
    );
    let body = spanned(TirExpr::OperatorRef(TirOperatorRef {
        path: vec![],
        operator: "AllocInv".to_string(),
        operator_id: tla_core::NameId(0),
        args: vec![],
    }));
    let idx = compiler
        .compile_expression_with_callees("Inv", &[], &body, &callees)
        .expect("zero-arg OperatorRef should compile as Call");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 0, .. }));
    assert!(
        has_call,
        "zero-arg OperatorRef should emit Call(argc=0): {:?}",
        func.instructions
    );
}

#[test]
fn test_compile_operator_ref_with_args_emits_call() {
    // OperatorRef with empty path and args should compile to Call with argc > 0.
    use crate::nodes::TirOperatorRef;
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "Allocate".to_string(),
        CalleeInfo {
            params: vec!["c".to_string(), "s".to_string()],
            body: Arc::new(spanned(TirExpr::Const {
                value: Value::Bool(true),
                ty: TirType::Bool,
            })),
            ast_body: None,
        },
    );
    let body = spanned(TirExpr::OperatorRef(TirOperatorRef {
        path: vec![],
        operator: "Allocate".to_string(),
        operator_id: tla_core::NameId(0),
        args: vec![
            spanned(TirExpr::Const {
                value: Value::SmallInt(1),
                ty: TirType::Int,
            }),
            spanned(TirExpr::Const {
                value: Value::SmallInt(2),
                ty: TirType::Int,
            }),
        ],
    }));
    let idx = compiler
        .compile_expression_with_callees("DoAllocate", &[], &body, &callees)
        .expect("OperatorRef with args should compile as Call");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 2, .. }));
    assert!(
        has_call,
        "OperatorRef with 2 args should emit Call(argc=2): {:?}",
        func.instructions
    );
}

#[test]
fn test_compile_module_qualified_operator_ref_resolves_by_name() {
    // Part of #3693: module-qualified OperatorRef should resolve by the operator's
    // simple name when it has been pre-compiled as a callee.
    use crate::nodes::{TirModuleRefSegment, TirOperatorRef};
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "AllocInv".to_string(),
        CalleeInfo {
            params: vec![],
            body: Arc::new(spanned(TirExpr::Const {
                value: Value::Bool(true),
                ty: TirType::Bool,
            })),
            ast_body: None,
        },
    );
    let body = spanned(TirExpr::OperatorRef(TirOperatorRef {
        path: vec![TirModuleRefSegment {
            name: "Base".to_string(),
            name_id: tla_core::NameId(0),
            args: vec![],
        }],
        operator: "AllocInv".to_string(),
        operator_id: tla_core::NameId(0),
        args: vec![],
    }));
    let idx = compiler
        .compile_expression_with_callees("Inv", &[], &body, &callees)
        .expect("module-qualified OperatorRef should resolve by operator name");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 0, .. }));
    assert!(
        has_call,
        "module-qualified OperatorRef should emit Call: {:?}",
        func.instructions
    );
}

#[test]
fn test_compile_operator_ref_parameterized_as_value_emits_closure() {
    // Part of #3693: OperatorRef with zero args referencing a parameterized
    // operator should produce a closure constant (operator-as-value pattern).
    use crate::nodes::TirOperatorRef;
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "Add".to_string(),
        CalleeInfo {
            params: vec!["x".to_string(), "y".to_string()],
            body: Arc::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
            })),
            ast_body: Some(PreservedAstBody(Arc::new(Spanned {
                node: Expr::Add(
                    Box::new(Spanned::dummy(Expr::Ident(
                        "x".to_string(),
                        tla_core::NameId(0),
                    ))),
                    Box::new(Spanned::dummy(Expr::Ident(
                        "y".to_string(),
                        tla_core::NameId(0),
                    ))),
                ),
                span: Span::default(),
            }))),
        },
    );
    let body = spanned(TirExpr::OperatorRef(TirOperatorRef {
        path: vec![],
        operator: "Add".to_string(),
        operator_id: tla_core::NameId(0),
        args: vec![],
    }));
    let idx = compiler
        .compile_expression_with_callees("GetAdd", &[], &body, &callees)
        .expect("parameterized OperatorRef as value should compile as closure");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let const_idx = match func.instructions[0] {
        Opcode::LoadConst { idx, .. } => idx,
        ref other => {
            panic!("parameterized OperatorRef should load a closure constant, got {other:?}")
        }
    };
    let Value::Closure(closure) = chunk.constants.get_value(const_idx) else {
        panic!("parameterized OperatorRef constant pool entry should be a closure");
    };
    assert_eq!(
        closure.params(),
        ["x".to_string(), "y".to_string()],
        "closure should have the parameterized operator's params"
    );
}

#[test]
fn test_compile_module_qualified_operator_ref_parameterized_as_closure() {
    // Part of #3693: module-qualified OperatorRef with zero args referencing a
    // parameterized operator in callee_bodies should produce a closure.
    use crate::nodes::{TirModuleRefSegment, TirOperatorRef};
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "Before".to_string(),
        CalleeInfo {
            params: vec!["i".to_string(), "j".to_string()],
            body: Arc::new(spanned(TirExpr::Cmp {
                left: Box::new(spanned(TirExpr::Name(ident_name("i")))),
                op: TirCmpOp::Lt,
                right: Box::new(spanned(TirExpr::Name(ident_name("j")))),
            })),
            ast_body: Some(PreservedAstBody(Arc::new(Spanned {
                node: Expr::Lt(
                    Box::new(Spanned::dummy(Expr::Ident(
                        "i".to_string(),
                        tla_core::NameId(0),
                    ))),
                    Box::new(Spanned::dummy(Expr::Ident(
                        "j".to_string(),
                        tla_core::NameId(0),
                    ))),
                ),
                span: Span::default(),
            }))),
        },
    );
    let body = spanned(TirExpr::OperatorRef(TirOperatorRef {
        path: vec![TirModuleRefSegment {
            name: "Base".to_string(),
            name_id: tla_core::NameId(0),
            args: vec![],
        }],
        operator: "Before".to_string(),
        operator_id: tla_core::NameId(0),
        args: vec![],
    }));
    let idx = compiler
        .compile_expression_with_callees("GetBefore", &[], &body, &callees)
        .expect("module-qualified parameterized OperatorRef should compile as closure");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let const_idx = match func.instructions[0] {
        Opcode::LoadConst { idx, .. } => idx,
        ref other => {
            panic!("module-qualified parameterized OperatorRef should load closure, got {other:?}")
        }
    };
    assert!(
        matches!(chunk.constants.get_value(const_idx), Value::Closure(_)),
        "should be a closure constant"
    );
}

#[test]
fn test_compile_operator_ref_with_args_fallback_to_value_apply() {
    // Part of #3693: OperatorRef with args where callee is not pre-compiled
    // should fall through to ValueApply (the callee is available in callee_bodies
    // as a parameterized operator that emits a closure).
    use crate::nodes::TirOperatorRef;
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "Add".to_string(),
        CalleeInfo {
            params: vec!["x".to_string(), "y".to_string()],
            body: Arc::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
            })),
            ast_body: Some(PreservedAstBody(Arc::new(Spanned {
                node: Expr::Add(
                    Box::new(Spanned::dummy(Expr::Ident(
                        "x".to_string(),
                        tla_core::NameId(0),
                    ))),
                    Box::new(Spanned::dummy(Expr::Ident(
                        "y".to_string(),
                        tla_core::NameId(0),
                    ))),
                ),
                span: Span::default(),
            }))),
        },
    );
    // OperatorRef with args — the callee is in callee_bodies but the fixed-point
    // loop would have compiled it via Call. Here we test the case where the callee
    // isn't in op_indices — the new code should compile it as a closure + ValueApply.
    let body = spanned(TirExpr::OperatorRef(TirOperatorRef {
        path: vec![],
        operator: "Add".to_string(),
        operator_id: tla_core::NameId(0),
        args: vec![
            spanned(TirExpr::Const {
                value: Value::SmallInt(3),
                ty: TirType::Int,
            }),
            spanned(TirExpr::Const {
                value: Value::SmallInt(4),
                ty: TirType::Int,
            }),
        ],
    }));
    // Note: compile_expression_with_callees would normally compile "Add" via
    // the fixed-point loop, putting it in op_indices. To test the fallback path,
    // we would need Add to fail compilation in the loop but succeed as a closure.
    // Since the fixed-point loop will succeed here, this test verifies the normal
    // Call path still works for OperatorRef with args.
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("OperatorRef with args should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // The fixed-point loop should have compiled Add, so this should be a Call.
    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 2, .. }));
    assert!(
        has_call,
        "OperatorRef with args should emit Call(argc=2) when callee compiles: {:?}",
        func.instructions
    );
}

#[test]
fn test_compile_apply_with_lambda_op_uses_value_apply() {
    // Apply where op is a Lambda expression:  (LAMBDA x: x + 1)(5)
    // The Lambda compiles to a closure constant, then ValueApply applies it.
    let mut compiler = BytecodeCompiler::new();
    let body = spanned(TirExpr::Apply {
        op: Box::new(spanned(TirExpr::Lambda {
            params: vec!["x".to_string()],
            body: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(1),
                    ty: TirType::Int,
                })),
            })),
            ast_body: PreservedAstBody(Arc::new(Spanned {
                node: Expr::Add(
                    Box::new(Spanned::dummy(Expr::Ident(
                        "x".to_string(),
                        tla_core::NameId(0),
                    ))),
                    Box::new(Spanned::dummy(Expr::Int(1.into()))),
                ),
                span: Span::default(),
            })),
        })),
        args: vec![spanned(TirExpr::Const {
            value: Value::SmallInt(5),
            ty: TirType::Int,
        })],
    });
    let idx = compiler
        .compile_expression("test", &body)
        .expect("Apply with Lambda op should compile via ValueApply");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // Lambda compiles to a closure constant loaded via LoadConst.
    let has_load_const = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::LoadConst { .. }));
    assert!(
        has_load_const,
        "Lambda op should emit LoadConst for closure: {:?}",
        func.instructions
    );
    // The application should use ValueApply with argc=1.
    let has_value_apply = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::ValueApply { argc: 1, .. }));
    assert!(
        has_value_apply,
        "Apply with Lambda op should emit ValueApply(argc=1), got {:?}",
        func.instructions
    );
}

#[test]
fn test_compile_apply_with_choose_op_uses_value_apply() {
    // Apply where op is a CHOOSE expression:
    //   (CHOOSE f \in {1, 2} : f > 0)(arg)
    // The CHOOSE compiles to ChooseBegin/ChooseNext producing a value,
    // then ValueApply applies the chosen value to the argument.
    let mut compiler = BytecodeCompiler::new();
    let body = spanned(TirExpr::Apply {
        op: Box::new(spanned(TirExpr::Choose {
            var: TirBoundVar {
                name: "f".to_string(),
                name_id: tla_core::NameId(0),
                domain: Some(Box::new(spanned(TirExpr::SetEnum(vec![
                    spanned(TirExpr::Const {
                        value: Value::SmallInt(1),
                        ty: TirType::Int,
                    }),
                    spanned(TirExpr::Const {
                        value: Value::SmallInt(2),
                        ty: TirType::Int,
                    }),
                ])))),
                pattern: None,
            },
            body: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(spanned(TirExpr::Name(ident_name("f")))),
                op: TirCmpOp::Gt,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(0),
                    ty: TirType::Int,
                })),
            })),
        })),
        args: vec![spanned(TirExpr::Const {
            value: Value::SmallInt(99),
            ty: TirType::Int,
        })],
    });
    let idx = compiler
        .compile_expression("test", &body)
        .expect("Apply with CHOOSE op should compile via ValueApply");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // CHOOSE should emit ChooseBegin/ChooseNext for the op.
    let has_choose = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::ChooseBegin { .. }));
    assert!(
        has_choose,
        "CHOOSE op should emit ChooseBegin: {:?}",
        func.instructions
    );
    // The application should use ValueApply with argc=1.
    let has_value_apply = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::ValueApply { argc: 1, .. }));
    assert!(
        has_value_apply,
        "Apply with CHOOSE op should emit ValueApply(argc=1), got {:?}",
        func.instructions
    );
}

#[test]
fn test_compile_apply_with_let_bound_value_uses_value_apply() {
    // Apply where op comes from a LET-bound zero-arg def:
    //   LET fn == someExpr IN fn(arg)
    // The LET compiles someExpr and binds it to a register;
    // fn(arg) then uses ValueApply since fn is a bound variable.
    let mut compiler = BytecodeCompiler::new();
    let body = spanned(TirExpr::Let {
        defs: vec![TirLetDef {
            name: "fn".to_string(),
            name_id: tla_core::NameId(0),
            params: vec![],
            body: spanned(TirExpr::Const {
                value: Value::SmallInt(42),
                ty: TirType::Int,
            }),
        }],
        body: Box::new(spanned(TirExpr::Apply {
            op: Box::new(spanned(TirExpr::Name(ident_name("fn")))),
            args: vec![spanned(TirExpr::Const {
                value: Value::SmallInt(1),
                ty: TirType::Int,
            })],
        })),
    });
    let idx = compiler
        .compile_expression_with_callees("test", &[], &body, &Default::default())
        .expect("Apply with LET-bound value should compile via ValueApply");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // The LET-bound name resolves to a register binding, so Apply falls
    // through the Name guard (lookup_binding succeeds) to compile_value_apply.
    let has_value_apply = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::ValueApply { argc: 1, .. }));
    assert!(
        has_value_apply,
        "Apply with LET-bound fn should emit ValueApply(argc=1), got {:?}",
        func.instructions
    );
}

/// Part of #3789: cross-module zero-arg identifier compiles on-demand instead
/// of emitting CallExternal.
///
/// Simulates INSTANCE-imported operator "Helper" that is in callee_bodies
/// but not pre-compiled (e.g., the fixed-point loop skipped it). The compiler
/// should compile it on-demand and emit a Call opcode rather than CallExternal.
#[test]
fn test_cross_module_zero_arg_ident_compiles_on_demand() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    // Helper == 42 (zero-arg operator from an INSTANCE module)
    callees.insert(
        "Helper".to_string(),
        CalleeInfo {
            params: vec![],
            body: Arc::new(spanned(TirExpr::Const {
                value: Value::SmallInt(42),
                ty: TirType::Int,
            })),
            ast_body: None,
        },
    );
    // Main body references Helper as a zero-arg identifier: Helper + 1
    let body = spanned(TirExpr::ArithBinOp {
        left: Box::new(spanned(TirExpr::Name(ident_name("Helper")))),
        op: TirArithOp::Add,
        right: Box::new(spanned(TirExpr::Const {
            value: Value::SmallInt(1),
            ty: TirType::Int,
        })),
    });
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("cross-module zero-arg ident should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    // Should use Call, not CallExternal.
    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 0, .. }));
    let has_call_external = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::CallExternal { .. }));
    assert!(
        has_call,
        "cross-module zero-arg ident should emit Call(argc=0), got {:?}",
        func.instructions
    );
    assert!(
        !has_call_external,
        "cross-module zero-arg ident should NOT emit CallExternal: {:?}",
        func.instructions
    );
}

/// Part of #3789: cross-module transitive dependency chain compiles on-demand.
///
/// A -> B -> C chain where A is the entry, B depends on C, and C is a constant.
/// The on-demand compiler should follow the transitive dependency.
#[test]
fn test_cross_module_transitive_dependency_compiles() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    // C == 10
    callees.insert(
        "C".to_string(),
        CalleeInfo {
            params: vec![],
            body: Arc::new(spanned(TirExpr::Const {
                value: Value::SmallInt(10),
                ty: TirType::Int,
            })),
            ast_body: None,
        },
    );
    // B == C + 1  (references C)
    callees.insert(
        "B".to_string(),
        CalleeInfo {
            params: vec![],
            body: Arc::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Name(ident_name("C")))),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(1),
                    ty: TirType::Int,
                })),
            })),
            ast_body: None,
        },
    );
    // Main body: B + 2
    let body = spanned(TirExpr::ArithBinOp {
        left: Box::new(spanned(TirExpr::Name(ident_name("B")))),
        op: TirArithOp::Add,
        right: Box::new(spanned(TirExpr::Const {
            value: Value::SmallInt(2),
            ty: TirType::Int,
        })),
    });
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("transitive cross-module chain should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    // Verify the entry function uses Call (not CallExternal) for B.
    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 0, .. }));
    let has_call_external = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::CallExternal { .. }));
    assert!(
        has_call,
        "transitive chain should emit Call for B: {:?}",
        func.instructions
    );
    assert!(
        !has_call_external,
        "transitive chain should NOT emit CallExternal: {:?}",
        func.instructions
    );
    // Verify 3+ compiled functions exist: C, B, Main (+ possible sub-functions)
    assert!(
        chunk.functions.len() >= 3,
        "should have at least 3 functions (C, B, Main), got {}",
        chunk.functions.len()
    );
}

/// Part of #3789: Apply(Name(Ident), args) where callee is in callee_bodies
/// but not pre-compiled compiles on-demand with Call instead of CallExternal.
#[test]
fn test_cross_module_apply_compiles_on_demand() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    // Add(x, y) == x + y (parameterized operator from INSTANCE module)
    callees.insert(
        "Add".to_string(),
        CalleeInfo {
            params: vec!["x".to_string(), "y".to_string()],
            body: Arc::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
            })),
            ast_body: Some(PreservedAstBody(Arc::new(Spanned {
                node: Expr::Add(
                    Box::new(Spanned::dummy(Expr::Ident(
                        "x".to_string(),
                        tla_core::NameId(0),
                    ))),
                    Box::new(Spanned::dummy(Expr::Ident(
                        "y".to_string(),
                        tla_core::NameId(0),
                    ))),
                ),
                span: Span::default(),
            }))),
        },
    );
    // Main body: Add(3, 4)
    let body = spanned(TirExpr::Apply {
        op: Box::new(spanned(TirExpr::Name(ident_name("Add")))),
        args: vec![
            spanned(TirExpr::Const {
                value: Value::SmallInt(3),
                ty: TirType::Int,
            }),
            spanned(TirExpr::Const {
                value: Value::SmallInt(4),
                ty: TirType::Int,
            }),
        ],
    });
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("cross-module Apply should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    // Should use Call(argc=2), not CallExternal.
    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 2, .. }));
    let has_call_external = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::CallExternal { .. }));
    assert!(
        has_call,
        "cross-module Apply should emit Call(argc=2): {:?}",
        func.instructions
    );
    assert!(
        !has_call_external,
        "cross-module Apply should NOT emit CallExternal: {:?}",
        func.instructions
    );
}

/// Part of #3789: recursive callee (operator references itself) terminates
/// without infinite recursion. The recursion guard in `compile_callee_on_demand`
/// prevents infinite compilation loops.
#[test]
fn test_cross_module_recursive_callee_terminates() {
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    // Rec == Rec (self-referential — would cause infinite recursion without guard)
    callees.insert(
        "Rec".to_string(),
        CalleeInfo {
            params: vec![],
            body: Arc::new(spanned(TirExpr::Name(ident_name("Rec")))),
            ast_body: None,
        },
    );
    // Main body: Rec
    let body = spanned(TirExpr::Name(ident_name("Rec")));
    let idx = compiler.compile_expression_with_callees("Main", &[], &body, &callees);
    // The recursive reference should be caught by the recursion guard.
    // Either outcome is acceptable as long as no infinite loop occurs:
    // - Ok: compiled with some combination of Call and CallExternal
    // - Err: compilation failed (also acceptable)
    match idx {
        Ok(func_idx) => {
            // Compiled without infinite loop — verify it produced a valid chunk.
            let chunk = compiler.finish();
            let func = chunk.get_function(func_idx);
            // Main calls Rec via Call; inside Rec's sub-function, the
            // recursive self-reference hits the guard and falls back to
            // CallExternal. The overall compilation terminates.
            assert!(
                !func.instructions.is_empty(),
                "recursive callee should produce non-empty instructions"
            );
            // Must contain either Call or CallExternal for the recursive reference
            let has_call_or_external = func
                .instructions
                .iter()
                .any(|op| matches!(op, Opcode::Call { .. } | Opcode::CallExternal { .. }));
            assert!(
                has_call_or_external,
                "recursive callee should emit Call or CallExternal for self-reference: {:?}",
                func.instructions
            );
        }
        Err(e) => {
            // Failed compilation is also acceptable for self-referential operators.
            // Verify the error is meaningful (not empty).
            assert!(
                !format!("{e:?}").is_empty(),
                "compilation error should have a non-empty description"
            );
        }
    }
}

/// Part of #3693: module-qualified OperatorRef with args compiles to Call
/// via on-demand callee compilation from callee_bodies, not to CallExternal.
///
/// Simulates the pattern: `I == INSTANCE M WITH ...` then `I!Scale(arg)`.
/// The TIR lowerer produces OperatorRef with path=["I"], operator="Scale",
/// args=[arg]. The callee body for "Scale" is in callee_bodies.
#[test]
fn test_module_qualified_operator_ref_with_args_compiles_on_demand() {
    use crate::nodes::{TirModuleRefSegment, TirOperatorRef};
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "Scale".to_string(),
        CalleeInfo {
            params: vec!["x".to_string()],
            body: Arc::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirArithOp::Mul,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(3),
                    ty: TirType::Int,
                })),
            })),
            ast_body: None,
        },
    );
    // I!Scale(7) — module-qualified OperatorRef with one argument
    let body = spanned(TirExpr::OperatorRef(TirOperatorRef {
        path: vec![TirModuleRefSegment {
            name: "I".to_string(),
            name_id: tla_core::NameId(0),
            args: vec![],
        }],
        operator: "Scale".to_string(),
        operator_id: tla_core::NameId(0),
        args: vec![spanned(TirExpr::Const {
            value: Value::SmallInt(7),
            ty: TirType::Int,
        })],
    }));
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("module-qualified OperatorRef with args should compile via on-demand callee");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // Should emit Call(argc=1), not CallExternal.
    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 1, .. }));
    let has_call_external = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::CallExternal { .. }));
    assert!(
        has_call,
        "module-qualified OperatorRef with args should emit Call(argc=1): {:?}",
        func.instructions
    );
    assert!(
        !has_call_external,
        "module-qualified OperatorRef should NOT fallback to CallExternal: {:?}",
        func.instructions
    );
}

/// Part of #3693: module-qualified OperatorRef referencing a callee that
/// internally references another callee (transitive INSTANCE dependency).
///
/// Simulates: `I == INSTANCE M WITH K <- 5` where M has:
///   Base == K, Derived == Base + 10
/// Then `I!Derived` should compile with both Base and Derived in bytecode.
#[test]
fn test_module_qualified_operator_ref_transitive_dependency() {
    use crate::nodes::TirOperatorRef;
    let mut compiler = BytecodeCompiler::new();
    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "Base".to_string(),
        CalleeInfo {
            params: vec![],
            body: Arc::new(spanned(TirExpr::Const {
                value: Value::SmallInt(5),
                ty: TirType::Int,
            })),
            ast_body: None,
        },
    );
    callees.insert(
        "Derived".to_string(),
        CalleeInfo {
            params: vec![],
            body: Arc::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Name(ident_name("Base")))),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(10),
                    ty: TirType::Int,
                })),
            })),
            ast_body: None,
        },
    );
    // OperatorRef to Derived (no module path needed — it resolves by name)
    let body = spanned(TirExpr::OperatorRef(TirOperatorRef {
        path: vec![],
        operator: "Derived".to_string(),
        operator_id: tla_core::NameId(0),
        args: vec![],
    }));
    let idx = compiler
        .compile_expression_with_callees("Main", &[], &body, &callees)
        .expect("transitive OperatorRef dependency should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // Should emit Call(argc=0) for the Derived callee, not CallExternal.
    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 0, .. }));
    assert!(
        has_call,
        "transitive OperatorRef should emit Call: {:?}",
        func.instructions
    );
}

/// Regression test for #3802: on-demand compiled callees must not inherit the
/// caller's quantifier/LET bindings.
///
/// Without clearing parent bindings, the callee body's free identifier `v`
/// would resolve to the caller's deep register (`r11`) instead of the
/// zero-arg operator `v`, producing a function that references `r11` while
/// only allocating registers for its own body.
#[test]
fn test_on_demand_callee_clears_parent_bindings_before_compilation() {
    let mut constants = ConstantPool::new();
    let mut state = FnCompileState::new("Main".to_string(), 0, &mut constants);
    let op_indices = std::collections::HashMap::from([("v".to_string(), 7u16)]);
    state.op_indices = Some(&op_indices);

    // Simulate a parent quantifier/LET scope that has already allocated deep
    // registers before triggering on-demand compilation of a separate callee.
    state.bindings.push(("v".to_string(), 11));
    state.next_reg = 12;

    let info = CalleeInfo {
        params: vec![],
        body: Arc::new(spanned(TirExpr::Name(ident_name("v")))),
        ast_body: None,
    };

    let func_idx = state
        .compile_callee_on_demand("Inner", &info)
        .expect("on-demand callee should compile against op_indices, not parent bindings");

    assert_eq!(func_idx, 0, "first sub-function should take index 0");
    assert_eq!(
        state.sub_functions.len(),
        1,
        "callee should be emitted as exactly one sub-function"
    );
    assert_eq!(
        state.bindings,
        vec![("v".to_string(), 11)],
        "parent bindings must be restored after on-demand compilation"
    );
    assert_eq!(
        state.next_reg, 12,
        "parent next_reg must be restored after on-demand compilation"
    );

    let callee = &state.sub_functions[0];
    assert_eq!(
        callee.instructions,
        vec![
            Opcode::Call {
                rd: 0,
                op_idx: 7,
                args_start: 0,
                argc: 0,
            },
            Opcode::Ret { rs: 0 }
        ],
        "callee should resolve `v` via a zero-arg Call, not leak the parent's r11"
    );
    assert_eq!(
        callee.max_register, 0,
        "callee should size registers from its own body, not the parent's"
    );
}

// =============================================================================
// Part of #3824: CallBuiltin emission for stdlib operators
// =============================================================================

use crate::bytecode::BuiltinOp;

/// Helper: build an Apply(Name(name), args) TIR expression.
fn apply_builtin(name: &str, args: Vec<Spanned<TirExpr>>) -> TirExpr {
    TirExpr::Apply {
        op: Box::new(spanned(TirExpr::Name(ident_name(name)))),
        args,
    }
}

/// Helper: compile a standalone expression and return the emitted instructions.
fn compile_standalone_expr(expr: TirExpr) -> Vec<Opcode> {
    let mut compiler = BytecodeCompiler::new();
    let idx = compiler
        .compile_expression("test", &spanned(expr))
        .expect("compilation should succeed");
    let chunk = compiler.finish();
    chunk.get_function(idx).instructions.clone()
}

fn int_const(n: i64) -> Spanned<TirExpr> {
    spanned(TirExpr::Const {
        value: Value::SmallInt(n),
        ty: TirType::Int,
    })
}

#[test]
fn test_compile_builtin_len_emits_call_builtin() {
    let instrs = compile_standalone_expr(apply_builtin("Len", vec![int_const(0)]));
    let builtin_ops: Vec<_> = instrs
        .iter()
        .filter(|op| matches!(op, Opcode::CallBuiltin { .. }))
        .collect();
    assert_eq!(
        builtin_ops.len(),
        1,
        "Len should emit exactly one CallBuiltin: {:?}",
        instrs
    );
    assert!(
        matches!(
            builtin_ops[0],
            Opcode::CallBuiltin {
                builtin: BuiltinOp::Len,
                argc: 1,
                ..
            }
        ),
        "expected CallBuiltin(Len, argc=1), got {:?}",
        builtin_ops[0]
    );
}

#[test]
fn test_compile_builtin_head_emits_call_builtin() {
    let instrs = compile_standalone_expr(apply_builtin("Head", vec![int_const(0)]));
    let builtin_ops: Vec<_> = instrs
        .iter()
        .filter(|op| matches!(op, Opcode::CallBuiltin { .. }))
        .collect();
    assert_eq!(builtin_ops.len(), 1, "Head: {:?}", instrs);
    assert!(matches!(
        builtin_ops[0],
        Opcode::CallBuiltin {
            builtin: BuiltinOp::Head,
            argc: 1,
            ..
        }
    ));
}

#[test]
fn test_compile_builtin_tail_emits_call_builtin() {
    let instrs = compile_standalone_expr(apply_builtin("Tail", vec![int_const(0)]));
    let builtin_ops: Vec<_> = instrs
        .iter()
        .filter(|op| matches!(op, Opcode::CallBuiltin { .. }))
        .collect();
    assert_eq!(builtin_ops.len(), 1, "Tail: {:?}", instrs);
    assert!(matches!(
        builtin_ops[0],
        Opcode::CallBuiltin {
            builtin: BuiltinOp::Tail,
            argc: 1,
            ..
        }
    ));
}

#[test]
fn test_compile_builtin_append_emits_call_builtin() {
    let instrs = compile_standalone_expr(apply_builtin("Append", vec![int_const(0), int_const(1)]));
    let builtin_ops: Vec<_> = instrs
        .iter()
        .filter(|op| matches!(op, Opcode::CallBuiltin { .. }))
        .collect();
    assert_eq!(builtin_ops.len(), 1, "Append: {:?}", instrs);
    assert!(matches!(
        builtin_ops[0],
        Opcode::CallBuiltin {
            builtin: BuiltinOp::Append,
            argc: 2,
            ..
        }
    ));
}

#[test]
fn test_compile_builtin_subseq_emits_call_builtin() {
    let instrs = compile_standalone_expr(apply_builtin(
        "SubSeq",
        vec![int_const(0), int_const(1), int_const(2)],
    ));
    let builtin_ops: Vec<_> = instrs
        .iter()
        .filter(|op| matches!(op, Opcode::CallBuiltin { .. }))
        .collect();
    assert_eq!(builtin_ops.len(), 1, "SubSeq: {:?}", instrs);
    assert!(matches!(
        builtin_ops[0],
        Opcode::CallBuiltin {
            builtin: BuiltinOp::SubSeq,
            argc: 3,
            ..
        }
    ));
}

#[test]
fn test_compile_builtin_cardinality_emits_call_builtin() {
    let instrs = compile_standalone_expr(apply_builtin("Cardinality", vec![int_const(0)]));
    let builtin_ops: Vec<_> = instrs
        .iter()
        .filter(|op| matches!(op, Opcode::CallBuiltin { .. }))
        .collect();
    assert_eq!(builtin_ops.len(), 1, "Cardinality: {:?}", instrs);
    assert!(matches!(
        builtin_ops[0],
        Opcode::CallBuiltin {
            builtin: BuiltinOp::Cardinality,
            argc: 1,
            ..
        }
    ));
}

#[test]
fn test_compile_builtin_is_finite_set_emits_call_builtin() {
    let instrs = compile_standalone_expr(apply_builtin("IsFiniteSet", vec![int_const(0)]));
    let builtin_ops: Vec<_> = instrs
        .iter()
        .filter(|op| matches!(op, Opcode::CallBuiltin { .. }))
        .collect();
    assert_eq!(builtin_ops.len(), 1, "IsFiniteSet: {:?}", instrs);
    assert!(matches!(
        builtin_ops[0],
        Opcode::CallBuiltin {
            builtin: BuiltinOp::IsFiniteSet,
            argc: 1,
            ..
        }
    ));
}

#[test]
fn test_compile_builtin_to_string_emits_call_builtin() {
    let instrs = compile_standalone_expr(apply_builtin("ToString", vec![int_const(42)]));
    let builtin_ops: Vec<_> = instrs
        .iter()
        .filter(|op| matches!(op, Opcode::CallBuiltin { .. }))
        .collect();
    assert_eq!(builtin_ops.len(), 1, "ToString: {:?}", instrs);
    assert!(matches!(
        builtin_ops[0],
        Opcode::CallBuiltin {
            builtin: BuiltinOp::ToString,
            argc: 1,
            ..
        }
    ));
}

#[test]
fn test_compile_builtin_wrong_argc_falls_through() {
    // Len with 2 args should NOT emit CallBuiltin — try_compile_builtin_call
    // returns None, and the name falls through to Call/CallExternal resolution
    // which fails (no callee compiled). The compile error confirms we did NOT
    // emit CallBuiltin for the mismatched arity.
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(apply_builtin("Len", vec![int_const(0), int_const(1)]));
    let result = compiler.compile_expression("test", &expr);
    assert!(
        result.is_err(),
        "Len(x, y) with wrong arity should not emit CallBuiltin and should fail \
         to resolve as a user operator"
    );
}

#[test]
fn test_compile_non_builtin_name_does_not_emit_call_builtin() {
    // UserOp(x) should NOT emit CallBuiltin — try_compile_builtin_call returns
    // None, and the name falls through to Call/CallExternal resolution which
    // fails (no callee compiled). The compile error confirms we did NOT treat
    // an unknown name as a builtin.
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(apply_builtin("UserOp", vec![int_const(0)]));
    let result = compiler.compile_expression("test", &expr);
    assert!(
        result.is_err(),
        "non-builtin name should not emit CallBuiltin and should fail \
         to resolve as a user operator"
    );
}
