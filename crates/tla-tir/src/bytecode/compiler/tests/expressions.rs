// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_compile_constant_bool() {
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Const {
        value: Value::Bool(true),
        ty: TirType::Bool,
    });
    let idx = compiler.compile_expression("test", &expr).unwrap();
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // Should be: LoadBool r0 true, Ret r0
    assert_eq!(func.instructions.len(), 2);
    assert!(matches!(
        func.instructions[0],
        Opcode::LoadBool { rd: 0, value: true }
    ));
    assert!(matches!(func.instructions[1], Opcode::Ret { rs: 0 }));
}

#[test]
fn test_compile_constant_int() {
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Const {
        value: Value::SmallInt(42),
        ty: TirType::Int,
    });
    let idx = compiler.compile_expression("test", &expr).unwrap();
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    assert_eq!(func.instructions.len(), 2);
    assert!(matches!(
        func.instructions[0],
        Opcode::LoadImm { rd: 0, value: 42 }
    ));
}

#[test]
fn test_compile_arithmetic() {
    let mut compiler = BytecodeCompiler::new();
    // 1 + 2
    let expr = spanned(TirExpr::ArithBinOp {
        left: Box::new(spanned(TirExpr::Const {
            value: Value::SmallInt(1),
            ty: TirType::Int,
        })),
        op: TirArithOp::Add,
        right: Box::new(spanned(TirExpr::Const {
            value: Value::SmallInt(2),
            ty: TirType::Int,
        })),
    });
    let idx = compiler.compile_expression("test", &expr).unwrap();
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // LoadImm r0, 1
    // LoadImm r1, 2
    // AddInt r2, r0, r1
    // Ret r2 -> Move r0, r2; Ret r0
    assert!(func.instructions.len() >= 4);
    assert!(matches!(
        func.instructions[2],
        Opcode::AddInt {
            rd: 2,
            r1: 0,
            r2: 1
        }
    ));
}

#[test]
fn test_compile_state_variable() {
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Name(TirNameRef {
        name: "x".to_string(),
        name_id: tla_core::NameId(0),
        kind: TirNameKind::StateVar { index: 3 },
        ty: TirType::Int,
    }));
    let idx = compiler.compile_expression("test", &expr).unwrap();
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    assert!(matches!(
        func.instructions[0],
        Opcode::LoadVar { rd: 0, var_idx: 3 }
    ));
}

#[test]
fn test_compile_set_enum() {
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::SetEnum(vec![
        spanned(TirExpr::Const {
            value: Value::SmallInt(1),
            ty: TirType::Int,
        }),
        spanned(TirExpr::Const {
            value: Value::SmallInt(2),
            ty: TirType::Int,
        }),
    ]));
    let idx = compiler.compile_expression("test", &expr).unwrap();
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // LoadImm r0, 1; LoadImm r1, 2; SetEnum r2, start=0, count=2; Move; Ret
    let has_set_enum = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::SetEnum { count: 2, .. }));
    assert!(has_set_enum);
}

#[test]
fn test_compile_range() {
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Range {
        lo: Box::new(spanned(TirExpr::Const {
            value: Value::SmallInt(1),
            ty: TirType::Int,
        })),
        hi: Box::new(spanned(TirExpr::Const {
            value: Value::SmallInt(10),
            ty: TirType::Int,
        })),
    });
    let idx = compiler.compile_expression("test", &expr).unwrap();
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let has_range = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Range { .. }));
    assert!(has_range);
}

#[test]
fn test_compile_comparison() {
    let mut compiler = BytecodeCompiler::new();
    // x < y
    let expr = spanned(TirExpr::Cmp {
        left: Box::new(spanned(TirExpr::Const {
            value: Value::SmallInt(1),
            ty: TirType::Int,
        })),
        op: TirCmpOp::Lt,
        right: Box::new(spanned(TirExpr::Const {
            value: Value::SmallInt(2),
            ty: TirType::Int,
        })),
    });
    let idx = compiler.compile_expression("test", &expr).unwrap();
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let has_lt = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::LtInt { .. }));
    assert!(has_lt);
}

#[test]
fn test_compile_record_set_packs_field_results_into_reserved_slots() {
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::RecordSet(vec![
        (
            field_name("location"),
            spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(1),
                    ty: TirType::Int,
                })),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(2),
                    ty: TirType::Int,
                })),
            }),
        ),
        (
            field_name("waiting"),
            spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(3),
                    ty: TirType::Int,
                })),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(4),
                    ty: TirType::Int,
                })),
            }),
        ),
    ]));

    let idx = compiler.compile_expression("test", &expr).unwrap();
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    assert!(
        func.instructions
            .iter()
            .any(|op| matches!(op, Opcode::Move { rd: 0, rs } if *rs != 0)),
        "first field result should be moved into reserved slot r0: {:?}",
        func.instructions
    );
    assert!(
        func.instructions
            .iter()
            .any(|op| matches!(op, Opcode::Move { rd: 1, rs } if *rs != 1)),
        "second field result should be moved into reserved slot r1: {:?}",
        func.instructions
    );
    assert!(
        func.instructions.iter().any(|op| matches!(
            op,
            Opcode::RecordSet {
                values_start: 0,
                count: 2,
                ..
            }
        )),
        "record-set opcode should read from contiguous packed slots: {:?}",
        func.instructions
    );
}

#[test]
fn test_compile_multi_level_except_desugars_to_nested_func_except() {
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Except {
        base: Box::new(spanned(TirExpr::Record(vec![(
            field_name("a"),
            spanned(TirExpr::Record(vec![(
                field_name("b"),
                spanned(TirExpr::Const {
                    value: Value::SmallInt(2),
                    ty: TirType::Int,
                }),
            )])),
        )]))),
        specs: vec![TirExceptSpec {
            path: vec![
                TirExceptPathElement::Field(field_name("a")),
                TirExceptPathElement::Field(field_name("b")),
            ],
            value: spanned(TirExpr::Const {
                value: Value::SmallInt(99),
                ty: TirType::Int,
            }),
        }],
    });

    let idx = compiler
        .compile_expression("test", &expr)
        .expect("multi-level EXCEPT should compile via nested FuncExcept");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    assert_eq!(
        func.instructions
            .iter()
            .filter(|op| matches!(op, Opcode::FuncExcept { .. }))
            .count(),
        2,
        "multi-level EXCEPT should lower to two nested FuncExcept ops: {:?}",
        func.instructions
    );
}

#[test]
fn test_compile_three_level_except_desugars_recursively() {
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Except {
        base: Box::new(spanned(TirExpr::Record(vec![(
            field_name("a"),
            spanned(TirExpr::Record(vec![(
                field_name("b"),
                spanned(TirExpr::Record(vec![(
                    field_name("c"),
                    spanned(TirExpr::Const {
                        value: Value::SmallInt(2),
                        ty: TirType::Int,
                    }),
                )])),
            )])),
        )]))),
        specs: vec![TirExceptSpec {
            path: vec![
                TirExceptPathElement::Field(field_name("a")),
                TirExceptPathElement::Field(field_name("b")),
                TirExceptPathElement::Field(field_name("c")),
            ],
            value: spanned(TirExpr::Const {
                value: Value::SmallInt(99),
                ty: TirType::Int,
            }),
        }],
    });

    let idx = compiler
        .compile_expression("test", &expr)
        .expect("three-level EXCEPT should compile via recursive nested FuncExcept");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    assert_eq!(
        func.instructions
            .iter()
            .filter(|op| matches!(op, Opcode::FuncExcept { .. }))
            .count(),
        3,
        "three-level EXCEPT should lower to three nested FuncExcept ops: {:?}",
        func.instructions
    );
}

#[test]
fn test_compile_identifier_from_resolved_constants() {
    let mut resolved_constants = std::collections::HashMap::new();
    resolved_constants.insert(intern_name("N"), Value::SmallInt(3));

    let mut compiler = BytecodeCompiler::with_resolved_constants(resolved_constants);
    let expr = spanned(TirExpr::ArithBinOp {
        left: Box::new(spanned(TirExpr::Name(TirNameRef {
            name: "N".to_string(),
            name_id: intern_name("N"),
            kind: TirNameKind::Ident,
            ty: TirType::Int,
        }))),
        op: TirArithOp::Add,
        right: Box::new(spanned(TirExpr::Const {
            value: Value::SmallInt(1),
            ty: TirType::Int,
        })),
    });

    let idx = compiler
        .compile_expression("test", &expr)
        .expect("resolved constants should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);

    assert!(matches!(
        func.instructions[0],
        Opcode::LoadImm { rd: 0, value: 3 }
    ));
    assert!(
        !func
            .instructions
            .iter()
            .any(|opcode| matches!(opcode, Opcode::Call { .. })),
        "resolved constants should lower directly, not through Call",
    );
}

#[test]
fn test_ident_resolved_as_state_var_via_state_vars_map() {
    let mut compiler = BytecodeCompiler::new();
    let mut state_vars = std::collections::HashMap::new();
    state_vars.insert("x".to_string(), 0u16);
    compiler.set_state_vars(state_vars);

    let expr = spanned(TirExpr::Name(ident_name("x")));
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("Ident should resolve as state var via state_vars map");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    assert!(
        matches!(func.instructions[0], Opcode::LoadVar { rd: 0, var_idx: 0 }),
        "Ident 'x' should emit LoadVar{{var_idx:0}}: {:?}",
        func.instructions
    );
}

#[test]
fn test_prime_ident_resolved_as_state_var_via_state_vars_map() {
    let mut compiler = BytecodeCompiler::new();
    let mut state_vars = std::collections::HashMap::new();
    state_vars.insert("x".to_string(), 2u16);
    compiler.set_state_vars(state_vars);

    let expr = spanned(TirExpr::Prime(Box::new(spanned(TirExpr::Name(
        ident_name("x"),
    )))));
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("Prime(Ident) should resolve as state var via state_vars map");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    assert!(
        matches!(
            func.instructions[0],
            Opcode::LoadPrime { rd: 0, var_idx: 2 }
        ),
        "Prime(Ident 'x') should emit LoadPrime{{var_idx:2}}: {:?}",
        func.instructions
    );
}

#[test]
fn test_unchanged_single_ident_via_state_vars_map() {
    let mut compiler = BytecodeCompiler::new();
    let mut state_vars = std::collections::HashMap::new();
    state_vars.insert("x".to_string(), 0u16);
    compiler.set_state_vars(state_vars);

    let inner = spanned(TirExpr::Name(ident_name("x")));
    let expr = spanned(TirExpr::Unchanged(Box::new(inner)));
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("UNCHANGED(Ident) should resolve via state_vars map");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let has_unchanged = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Unchanged { count: 1, .. }));
    assert!(
        has_unchanged,
        "UNCHANGED on Ident state var should emit Unchanged opcode: {:?}",
        func.instructions
    );
}

#[test]
fn test_unchanged_tuple_ident_via_state_vars_map() {
    let mut compiler = BytecodeCompiler::new();
    let mut state_vars = std::collections::HashMap::new();
    state_vars.insert("x".to_string(), 0u16);
    state_vars.insert("y".to_string(), 1u16);
    compiler.set_state_vars(state_vars);

    let inner = spanned(TirExpr::Tuple(vec![
        spanned(TirExpr::Name(ident_name("x"))),
        spanned(TirExpr::Name(ident_name("y"))),
    ]));
    let expr = spanned(TirExpr::Unchanged(Box::new(inner)));
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("UNCHANGED(<<Ident, Ident>>) should resolve via state_vars map");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let has_unchanged = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Unchanged { count: 2, .. }));
    assert!(
        has_unchanged,
        "UNCHANGED on tuple of Ident state vars should emit Unchanged{{count:2}}: {:?}",
        func.instructions
    );
}

#[test]
fn test_ident_binding_shadows_state_var() {
    // When a name is bound (e.g., quantifier variable), it should take
    // precedence over the state_vars map — bindings are checked first.
    let mut compiler = BytecodeCompiler::new();
    let mut state_vars = std::collections::HashMap::new();
    state_vars.insert("x".to_string(), 0u16);
    compiler.set_state_vars(state_vars);

    // Use a quantifier to bind "x" — the body's reference to "x" should
    // resolve to the binding register, not emit LoadVar.
    let expr = spanned(TirExpr::Exists {
        vars: vec![TirBoundVar {
            name: "x".to_string(),
            name_id: tla_core::NameId(0),
            domain: Some(Box::new(spanned(TirExpr::SetEnum(vec![spanned(
                TirExpr::Const {
                    value: Value::SmallInt(1),
                    ty: TirType::Int,
                },
            )])))),
            pattern: None,
        }],
        body: Box::new(spanned(TirExpr::Cmp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirCmpOp::Eq,
            right: Box::new(spanned(TirExpr::Const {
                value: Value::SmallInt(1),
                ty: TirType::Int,
            })),
        })),
    });
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("quantifier-bound x should shadow state var x");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // The body should NOT contain LoadVar — "x" resolves to the quantifier binding.
    let has_load_var = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::LoadVar { .. }));
    assert!(
        !has_load_var,
        "bound variable 'x' should shadow state var 'x', no LoadVar expected: {:?}",
        func.instructions
    );
}

#[test]
fn test_op_replacement_zero_arg_ident() {
    // Same scenario but Jug appears as a standalone Name(Ident), not via Apply.
    // This covers the compile_expr.rs zero-arg path.
    let mut compiler = BytecodeCompiler::new();
    let mut replacements = std::collections::HashMap::new();
    replacements.insert("Jug".to_string(), "MCJug".to_string());
    compiler.set_op_replacements(replacements);

    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "MCJug".to_string(),
        CalleeInfo {
            params: vec![],
            body: std::sync::Arc::new(spanned(TirExpr::Const {
                value: Value::SmallInt(42),
                ty: TirType::Int,
            })),
            ast_body: None,
        },
    );

    // Entry: Check == Jug  (standalone ident, zero-arg)
    let body = spanned(TirExpr::Name(ident_name("Jug")));

    let idx = compiler
        .compile_expression_with_callees("Check", &[], &body, &callees)
        .expect("zero-arg ident should resolve via op_replacement");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let has_call = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Call { argc: 0, .. }));
    assert!(has_call, "Check should Call MCJug via operator replacement");
}
