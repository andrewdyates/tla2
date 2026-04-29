// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_compile_choose() {
    // CHOOSE x \in {1, 2, 3} : x > 1
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Choose {
        var: TirBoundVar {
            name: "x".to_string(),
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
                spanned(TirExpr::Const {
                    value: Value::SmallInt(3),
                    ty: TirType::Int,
                }),
            ])))),
            pattern: None,
        },
        body: Box::new(spanned(TirExpr::Cmp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirCmpOp::Gt,
            right: Box::new(spanned(TirExpr::Const {
                value: Value::SmallInt(1),
                ty: TirType::Int,
            })),
        })),
    });
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("CHOOSE should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let has_choose_begin = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::ChooseBegin { .. }));
    let has_choose_next = func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::ChooseNext { .. }));
    assert!(has_choose_begin, "should emit ChooseBegin");
    assert!(has_choose_next, "should emit ChooseNext");
}

#[test]
fn test_compile_choose_true_predicate() {
    // CHOOSE x \in {1, 2} : TRUE
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Choose {
        var: TirBoundVar {
            name: "x".to_string(),
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
        body: Box::new(spanned(TirExpr::Const {
            value: Value::Bool(true),
            ty: TirType::Bool,
        })),
    });
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("CHOOSE with TRUE predicate should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    assert!(func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::ChooseBegin { .. })));
    assert!(func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::ChooseNext { .. })));
}

#[test]
fn test_compile_choose_with_and_predicate() {
    // CHOOSE x \in {1, 2, 3} : x > 0 /\ x < 3
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Choose {
        var: TirBoundVar {
            name: "x".to_string(),
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
                spanned(TirExpr::Const {
                    value: Value::SmallInt(3),
                    ty: TirType::Int,
                }),
            ])))),
            pattern: None,
        },
        body: Box::new(spanned(TirExpr::BoolBinOp {
            left: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirCmpOp::Gt,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(0),
                    ty: TirType::Int,
                })),
            })),
            op: TirBoolOp::And,
            right: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirCmpOp::Lt,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(3),
                    ty: TirType::Int,
                })),
            })),
        })),
    });
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("CHOOSE with AND predicate should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    assert!(func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::ChooseBegin { .. })));
    // AND should use short-circuit JumpFalse
    assert!(func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::JumpFalse { .. })));
}

#[test]
fn test_compile_choose_with_or_predicate() {
    // CHOOSE x \in {1, 2, 3} : x = 1 \/ x = 3
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Choose {
        var: TirBoundVar {
            name: "x".to_string(),
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
                spanned(TirExpr::Const {
                    value: Value::SmallInt(3),
                    ty: TirType::Int,
                }),
            ])))),
            pattern: None,
        },
        body: Box::new(spanned(TirExpr::BoolBinOp {
            left: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirCmpOp::Eq,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(1),
                    ty: TirType::Int,
                })),
            })),
            op: TirBoolOp::Or,
            right: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirCmpOp::Eq,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(3),
                    ty: TirType::Int,
                })),
            })),
        })),
    });
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("CHOOSE with OR predicate should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    assert!(func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::ChooseBegin { .. })));
    // OR should use short-circuit JumpTrue
    assert!(func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::JumpTrue { .. })));
}

#[test]
fn test_compile_choose_with_if_then_else_predicate() {
    // CHOOSE x \in {1, 2, 3} : IF x > 1 THEN x < 3 ELSE FALSE
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Choose {
        var: TirBoundVar {
            name: "x".to_string(),
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
                spanned(TirExpr::Const {
                    value: Value::SmallInt(3),
                    ty: TirType::Int,
                }),
            ])))),
            pattern: None,
        },
        body: Box::new(spanned(TirExpr::If {
            cond: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirCmpOp::Gt,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(1),
                    ty: TirType::Int,
                })),
            })),
            then_: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirCmpOp::Lt,
                right: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(3),
                    ty: TirType::Int,
                })),
            })),
            else_: Box::new(spanned(TirExpr::Const {
                value: Value::Bool(false),
                ty: TirType::Bool,
            })),
        })),
    });
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("CHOOSE with IF-THEN-ELSE predicate should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    assert!(func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::ChooseBegin { .. })));
    // IF-THEN-ELSE should produce Jump and JumpFalse
    assert!(func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Jump { .. })));
}

#[test]
fn test_compile_nested_choose() {
    // CHOOSE x \in {1, 2} : x = CHOOSE y \in {1, 2} : y > 1
    let mut compiler = BytecodeCompiler::new();
    let inner_choose = spanned(TirExpr::Choose {
        var: TirBoundVar {
            name: "y".to_string(),
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
            left: Box::new(spanned(TirExpr::Name(ident_name("y")))),
            op: TirCmpOp::Gt,
            right: Box::new(spanned(TirExpr::Const {
                value: Value::SmallInt(1),
                ty: TirType::Int,
            })),
        })),
    });
    let expr = spanned(TirExpr::Choose {
        var: TirBoundVar {
            name: "x".to_string(),
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
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirCmpOp::Eq,
            right: Box::new(inner_choose),
        })),
    });
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("nested CHOOSE should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // Should have 2 ChooseBegin and 2 ChooseNext (nested).
    let choose_begins = func
        .instructions
        .iter()
        .filter(|op| matches!(op, Opcode::ChooseBegin { .. }))
        .count();
    let choose_nexts = func
        .instructions
        .iter()
        .filter(|op| matches!(op, Opcode::ChooseNext { .. }))
        .count();
    assert_eq!(choose_begins, 2, "nested CHOOSE should have 2 ChooseBegin");
    assert_eq!(choose_nexts, 2, "nested CHOOSE should have 2 ChooseNext");
}

#[test]
fn test_compile_choose_without_domain_returns_error() {
    // CHOOSE x : x > 0  (no domain — unbounded CHOOSE)
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Choose {
        var: TirBoundVar {
            name: "x".to_string(),
            name_id: tla_core::NameId(0),
            domain: None,
            pattern: None,
        },
        body: Box::new(spanned(TirExpr::Cmp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirCmpOp::Gt,
            right: Box::new(spanned(TirExpr::Const {
                value: Value::SmallInt(0),
                ty: TirType::Int,
            })),
        })),
    });
    let result = compiler.compile_expression("test", &expr);
    assert!(
        result.is_err(),
        "CHOOSE without domain should return CompileError"
    );
}

#[test]
fn test_compile_choose_with_range_domain() {
    // CHOOSE x \in 1..5 : x > 3
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Choose {
        var: TirBoundVar {
            name: "x".to_string(),
            name_id: tla_core::NameId(0),
            domain: Some(Box::new(spanned(TirExpr::Range {
                lo: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(1),
                    ty: TirType::Int,
                })),
                hi: Box::new(spanned(TirExpr::Const {
                    value: Value::SmallInt(5),
                    ty: TirType::Int,
                })),
            }))),
            pattern: None,
        },
        body: Box::new(spanned(TirExpr::Cmp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirCmpOp::Gt,
            right: Box::new(spanned(TirExpr::Const {
                value: Value::SmallInt(3),
                ty: TirType::Int,
            })),
        })),
    });
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("CHOOSE with range domain should compile");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // Should have Range opcode for the domain
    assert!(func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::Range { .. })));
    assert!(func
        .instructions
        .iter()
        .any(|op| matches!(op, Opcode::ChooseBegin { .. })));
}

#[test]
fn test_compile_multi_var_forall() {
    // \A x \in {1, 2}, y \in {3, 4} : x + y > 0
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Forall {
        vars: vec![
            TirBoundVar {
                name: "x".to_string(),
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
            TirBoundVar {
                name: "y".to_string(),
                name_id: tla_core::NameId(0),
                domain: Some(Box::new(spanned(TirExpr::SetEnum(vec![
                    spanned(TirExpr::Const {
                        value: Value::SmallInt(3),
                        ty: TirType::Int,
                    }),
                    spanned(TirExpr::Const {
                        value: Value::SmallInt(4),
                        ty: TirType::Int,
                    }),
                ])))),
                pattern: None,
            },
        ],
        body: Box::new(spanned(TirExpr::Cmp {
            left: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
            })),
            op: TirCmpOp::Gt,
            right: Box::new(spanned(TirExpr::Const {
                value: Value::SmallInt(0),
                ty: TirType::Int,
            })),
        })),
    });
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("multi-variable FORALL should compile via nesting");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // Should have two nested ForallBegin/ForallNext pairs.
    let forall_begins = func
        .instructions
        .iter()
        .filter(|op| matches!(op, Opcode::ForallBegin { .. }))
        .count();
    let forall_nexts = func
        .instructions
        .iter()
        .filter(|op| matches!(op, Opcode::ForallNext { .. }))
        .count();
    assert_eq!(forall_begins, 2, "should have 2 nested ForallBegin");
    assert_eq!(forall_nexts, 2, "should have 2 nested ForallNext");
}

#[test]
fn test_compile_multi_var_exists() {
    // \E x \in {1, 2}, y \in {3, 4} : x + y = 5
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::Exists {
        vars: vec![
            TirBoundVar {
                name: "x".to_string(),
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
            TirBoundVar {
                name: "y".to_string(),
                name_id: tla_core::NameId(0),
                domain: Some(Box::new(spanned(TirExpr::SetEnum(vec![
                    spanned(TirExpr::Const {
                        value: Value::SmallInt(3),
                        ty: TirType::Int,
                    }),
                    spanned(TirExpr::Const {
                        value: Value::SmallInt(4),
                        ty: TirType::Int,
                    }),
                ])))),
                pattern: None,
            },
        ],
        body: Box::new(spanned(TirExpr::Cmp {
            left: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
            })),
            op: TirCmpOp::Eq,
            right: Box::new(spanned(TirExpr::Const {
                value: Value::SmallInt(5),
                ty: TirType::Int,
            })),
        })),
    });
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("multi-variable EXISTS should compile via nesting");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    let exists_begins = func
        .instructions
        .iter()
        .filter(|op| matches!(op, Opcode::ExistsBegin { .. }))
        .count();
    assert_eq!(exists_begins, 2, "should have 2 nested ExistsBegin");
}

#[test]
fn test_compile_multi_var_set_builder_flattens_with_big_union() {
    // {x + y : x \in {1, 2}, y \in {3, 4}}
    // Multi-variable SetBuilder desugars via BigUnion:
    // UNION {{x + y : y \in {3,4}} : x \in {1,2}}
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::SetBuilder {
        body: Box::new(spanned(TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirArithOp::Add,
            right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
        })),
        vars: vec![
            TirBoundVar {
                name: "x".to_string(),
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
            TirBoundVar {
                name: "y".to_string(),
                name_id: tla_core::NameId(0),
                domain: Some(Box::new(spanned(TirExpr::SetEnum(vec![
                    spanned(TirExpr::Const {
                        value: Value::SmallInt(3),
                        ty: TirType::Int,
                    }),
                    spanned(TirExpr::Const {
                        value: Value::SmallInt(4),
                        ty: TirType::Int,
                    }),
                ])))),
                pattern: None,
            },
        ],
    });
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("multi-variable SetBuilder should compile via BigUnion flattening");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // Should have 2 nested SetBuilderBegin loops and 1 BigUnion.
    let set_builder_begins = func
        .instructions
        .iter()
        .filter(|op| matches!(op, Opcode::SetBuilderBegin { .. }))
        .count();
    assert_eq!(
        set_builder_begins, 2,
        "should have 2 nested SetBuilderBegin"
    );
    let big_unions = func
        .instructions
        .iter()
        .filter(|op| matches!(op, Opcode::BigUnion { .. }))
        .count();
    assert_eq!(big_unions, 1, "should have 1 BigUnion to flatten");
}

#[test]
fn test_compile_multi_var_func_def_tuple_domain() {
    // [x \in {1, 2}, y \in {3, 4} |-> x + y]
    // Multi-variable FuncDef desugars to tuple-domain:
    // [t \in {1,2} \X {3,4} |-> LET x == t[1], y == t[2] IN x + y]
    let mut compiler = BytecodeCompiler::new();
    let expr = spanned(TirExpr::FuncDef {
        vars: vec![
            TirBoundVar {
                name: "x".to_string(),
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
            TirBoundVar {
                name: "y".to_string(),
                name_id: tla_core::NameId(0),
                domain: Some(Box::new(spanned(TirExpr::SetEnum(vec![
                    spanned(TirExpr::Const {
                        value: Value::SmallInt(3),
                        ty: TirType::Int,
                    }),
                    spanned(TirExpr::Const {
                        value: Value::SmallInt(4),
                        ty: TirType::Int,
                    }),
                ])))),
                pattern: None,
            },
        ],
        body: Box::new(spanned(TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Name(ident_name("x")))),
            op: TirArithOp::Add,
            right: Box::new(spanned(TirExpr::Name(ident_name("y")))),
        })),
    });
    let idx = compiler
        .compile_expression("test", &expr)
        .expect("multi-variable FuncDef should compile via tuple-domain desugaring");
    let chunk = compiler.finish();
    let func = chunk.get_function(idx);
    // Should have 1 Times (cross product) and 1 FuncDefBegin.
    let times_count = func
        .instructions
        .iter()
        .filter(|op| matches!(op, Opcode::Times { .. }))
        .count();
    assert_eq!(times_count, 1, "should have 1 Times for cross product");
    let func_def_begins = func
        .instructions
        .iter()
        .filter(|op| matches!(op, Opcode::FuncDefBegin { .. }))
        .count();
    assert_eq!(func_def_begins, 1, "should have 1 FuncDefBegin");
    // Should have 2 FuncApply for destructuring t[1] and t[2].
    let func_applies = func
        .instructions
        .iter()
        .filter(|op| matches!(op, Opcode::FuncApply { .. }))
        .count();
    assert_eq!(
        func_applies, 2,
        "should have 2 FuncApply for tuple destructuring"
    );
}
