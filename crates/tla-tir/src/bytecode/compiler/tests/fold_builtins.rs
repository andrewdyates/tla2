// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::bytecode::BuiltinOp;
use std::sync::Arc;

fn int_const(n: i64) -> Spanned<TirExpr> {
    spanned(TirExpr::Const {
        value: Value::SmallInt(n),
        ty: TirType::Int,
    })
}

fn name_expr(name: &str) -> Spanned<TirExpr> {
    spanned(TirExpr::Name(ident_name(name)))
}

fn fold_function_on_set_expr(op: Spanned<TirExpr>, base: Spanned<TirExpr>) -> Spanned<TirExpr> {
    spanned(TirExpr::Apply {
        op: Box::new(name_expr("FoldFunctionOnSet")),
        args: vec![op, base, name_expr("f"), name_expr("S")],
    })
}

fn compile_fold_entry(
    body: Spanned<TirExpr>,
    callees: &std::collections::HashMap<String, CalleeInfo>,
) -> Vec<Opcode> {
    let mut compiler = BytecodeCompiler::new();
    let idx = compiler
        .compile_expression_with_callees(
            "Main",
            &["f".to_string(), "S".to_string()],
            &body,
            callees,
        )
        .expect("fold entry should compile");
    let chunk = compiler.finish();
    chunk.get_function(idx).instructions.clone()
}

fn fold_function_on_set_callee() -> CalleeInfo {
    let body = name_expr("base");
    CalleeInfo {
        params: vec![
            "op".to_string(),
            "base".to_string(),
            "f".to_string(),
            "S".to_string(),
        ],
        body: Arc::new(body),
        ast_body: None,
    }
}

fn generic_fold_callees() -> std::collections::HashMap<String, CalleeInfo> {
    let mut callees = std::collections::HashMap::new();
    callees.insert(
        "FoldFunctionOnSet".to_string(),
        fold_function_on_set_callee(),
    );
    callees
}

#[test]
fn test_fold_function_on_set_plus_zero_emits_sum_builtin() {
    let body = fold_function_on_set_expr(spanned(TirExpr::OpRef("+".to_string())), int_const(0));
    let instrs = compile_fold_entry(body, &Default::default());

    let fold_builtins: Vec<_> = instrs
        .iter()
        .filter(|op| {
            matches!(
                op,
                Opcode::CallBuiltin {
                    builtin: BuiltinOp::FoldFunctionOnSetSum,
                    ..
                }
            )
        })
        .collect();
    assert_eq!(
        fold_builtins.len(),
        1,
        "FoldFunctionOnSet(+, 0, f, S) should emit one recognizable sum builtin: {:?}",
        instrs
    );
    assert!(
        matches!(
            fold_builtins[0],
            Opcode::CallBuiltin {
                builtin: BuiltinOp::FoldFunctionOnSetSum,
                argc: 2,
                ..
            }
        ),
        "sum fold builtin should carry only f and S operands, got {:?}",
        fold_builtins[0]
    );
    assert!(
        !instrs.iter().any(|op| matches!(
            op,
            Opcode::MakeClosure { .. } | Opcode::CallExternal { .. } | Opcode::ValueApply { .. }
        )),
        "recognized sum fold should avoid closure/external/value-apply fallback: {:?}",
        instrs
    );
}

#[test]
fn test_fold_function_on_set_plus_nonzero_base_falls_back() {
    let body = fold_function_on_set_expr(spanned(TirExpr::OpRef("+".to_string())), int_const(1));
    let instrs = compile_fold_entry(body, &generic_fold_callees());

    assert!(
        !instrs.iter().any(|op| matches!(
            op,
            Opcode::CallBuiltin {
                builtin: BuiltinOp::FoldFunctionOnSetSum,
                ..
            }
        )),
        "nonzero base should not be marked as the plus-zero sum builtin: {:?}",
        instrs
    );
    assert!(
        instrs
            .iter()
            .any(|op| matches!(op, Opcode::Call { argc: 4, .. })),
        "nonzero base should remain available to the generic fold callee: {:?}",
        instrs
    );
}

#[test]
fn test_fold_function_on_set_non_plus_op_falls_back() {
    let body = fold_function_on_set_expr(spanned(TirExpr::OpRef("-".to_string())), int_const(0));
    let instrs = compile_fold_entry(body, &generic_fold_callees());

    assert!(
        !instrs.iter().any(|op| matches!(
            op,
            Opcode::CallBuiltin {
                builtin: BuiltinOp::FoldFunctionOnSetSum,
                ..
            }
        )),
        "non-plus fold operator should not be marked as a sum builtin: {:?}",
        instrs
    );
    assert!(
        instrs
            .iter()
            .any(|op| matches!(op, Opcode::Call { argc: 4, .. })),
        "non-plus fold should remain available to the generic fold callee: {:?}",
        instrs
    );
}
