// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    apply_builtin_binary_op, apply_closure_with_values, apply_named_binary_op, check_arity,
    create_closure_from_arg, eval, eval_iter_set, values_equal, EvalCtx, EvalError, EvalResult,
    Expr, FuncValue, Span, Spanned, Value,
};
use std::sync::Arc;
use tla_value::ClosureValue;

enum BinaryRelationArg {
    Eq,
    Neq,
    BuiltIn(String),
    Named(String),
    Closure(Arc<ClosureValue>),
}

impl BinaryRelationArg {
    fn from_expr(
        ctx: &EvalCtx,
        arg: &Spanned<Expr>,
        span: Option<Span>,
    ) -> EvalResult<BinaryRelationArg> {
        match &arg.node {
            Expr::OpRef(op) if op == "=" => Ok(BinaryRelationArg::Eq),
            Expr::OpRef(op) if op == "#" || op == "/=" => Ok(BinaryRelationArg::Neq),
            Expr::OpRef(op) => Ok(BinaryRelationArg::BuiltIn(op.clone())),
            Expr::Ident(name, _) if name == "=" => Ok(BinaryRelationArg::Eq),
            Expr::Ident(name, _) if name == "#" || name == "/=" => Ok(BinaryRelationArg::Neq),
            Expr::Ident(name, _) if ctx.get_op(name).is_some() => {
                Ok(BinaryRelationArg::Named(name.clone()))
            }
            _ => match create_closure_from_arg(ctx, arg, "RelationUnder", 2, span)? {
                Value::Closure(ref closure) => Ok(BinaryRelationArg::Closure(Arc::clone(closure))),
                other => Err(EvalError::Internal {
                    message: format!(
                        "Relation higher-order argument must evaluate to a closure, got {other:?}"
                    ),
                    span,
                }),
            },
        }
    }

    fn eval_bool(
        &self,
        ctx: &EvalCtx,
        left: &Value,
        right: &Value,
        span: Option<Span>,
    ) -> EvalResult<bool> {
        match self {
            BinaryRelationArg::Eq => values_equal(ctx, left, right, span),
            BinaryRelationArg::Neq => values_equal(ctx, left, right, span).map(|eq| !eq),
            BinaryRelationArg::BuiltIn(op) => {
                let result = apply_builtin_binary_op(op, left.clone(), right.clone(), span)?;
                result
                    .as_bool()
                    .ok_or_else(|| EvalError::type_error("BOOLEAN", &result, span))
            }
            BinaryRelationArg::Named(name) => {
                let result = apply_named_binary_op(ctx, name, left.clone(), right.clone(), span)?;
                result
                    .as_bool()
                    .ok_or_else(|| EvalError::type_error("BOOLEAN", &result, span))
            }
            BinaryRelationArg::Closure(closure) => {
                let result =
                    apply_closure_with_values(ctx, closure, &[left.clone(), right.clone()], span)?;
                result
                    .as_bool()
                    .ok_or_else(|| EvalError::type_error("BOOLEAN", &result, span))
            }
        }
    }
}

fn eval_relation_nodes(ctx: &EvalCtx, set_expr: &Spanned<Expr>) -> EvalResult<Vec<Value>> {
    let sv = eval(ctx, set_expr)?;
    let mut nodes: Vec<Value> = eval_iter_set(ctx, &sv, Some(set_expr.span))?.collect();
    nodes.sort();
    Ok(nodes)
}

fn eval_relation_function(
    ctx: &EvalCtx,
    relation_expr: &Spanned<Expr>,
) -> EvalResult<(FuncValue, String)> {
    let relation = eval(ctx, relation_expr)?;
    let display = relation.to_string();
    let func = relation
        .to_func_coerced()
        .ok_or_else(|| EvalError::type_error("Function", &relation, Some(relation_expr.span)))?;
    Ok((func, display))
}

fn relation_matrix_from_function(
    nodes: &[Value],
    func: &FuncValue,
    relation_display: &str,
    span: Option<Span>,
) -> EvalResult<Vec<Vec<bool>>> {
    let mut matrix = vec![vec![false; nodes.len()]; nodes.len()];
    for (i, left) in nodes.iter().enumerate() {
        for (j, right) in nodes.iter().enumerate() {
            let key = Value::tuple([left.clone(), right.clone()]);
            let cell = func
                .mapping_get(&key)
                .ok_or_else(|| EvalError::NotInDomain {
                    arg: key.to_string(),
                    func_display: Some(relation_display.to_string()),
                    span,
                })?;
            matrix[i][j] = cell
                .as_bool()
                .ok_or_else(|| EvalError::type_error("BOOLEAN", cell, span))?;
        }
    }
    Ok(matrix)
}

fn relation_matrix_from_operator(
    ctx: &EvalCtx,
    op_arg: &Spanned<Expr>,
    nodes: &[Value],
    span: Option<Span>,
) -> EvalResult<Vec<Vec<bool>>> {
    let op = BinaryRelationArg::from_expr(ctx, op_arg, span)?;
    let mut matrix = vec![vec![false; nodes.len()]; nodes.len()];
    for (i, left) in nodes.iter().enumerate() {
        for (j, right) in nodes.iter().enumerate() {
            matrix[i][j] = op.eval_bool(ctx, left, right, span)?;
        }
    }
    Ok(matrix)
}

fn transitive_closure_matrix(matrix: &[Vec<bool>]) -> Vec<Vec<bool>> {
    let mut closure = matrix.to_vec();
    let n = closure.len();
    #[allow(clippy::needless_range_loop)]
    for k in 0..n {
        for i in 0..n {
            if closure[i][k] {
                for j in 0..n {
                    if closure[k][j] {
                        closure[i][j] = true;
                    }
                }
            }
        }
    }
    closure
}

fn relation_function_from_matrix(nodes: &[Value], matrix: &[Vec<bool>]) -> Value {
    let mut entries = Vec::with_capacity(nodes.len() * nodes.len());
    for (i, left) in nodes.iter().enumerate() {
        for (j, right) in nodes.iter().enumerate() {
            entries.push((
                Value::tuple([left.clone(), right.clone()]),
                Value::Bool(matrix[i][j]),
            ));
        }
    }
    Value::Func(Arc::new(FuncValue::from_sorted_entries(entries)))
}

fn is_reflexive(matrix: &[Vec<bool>]) -> bool {
    matrix.iter().enumerate().all(|(i, row)| row[i])
}

fn is_irreflexive(matrix: &[Vec<bool>]) -> bool {
    matrix.iter().enumerate().all(|(i, row)| !row[i])
}

fn is_symmetric(matrix: &[Vec<bool>]) -> bool {
    matrix.iter().enumerate().all(|(i, row)| {
        row.iter()
            .enumerate()
            .all(|(j, value)| *value == matrix[j][i])
    })
}

fn is_antisymmetric(nodes: &[Value], matrix: &[Vec<bool>]) -> bool {
    matrix.iter().enumerate().all(|(i, row)| {
        row.iter()
            .enumerate()
            .all(|(j, value)| !(*value && matrix[j][i]) || nodes[i] == nodes[j])
    })
}

fn is_asymmetric(matrix: &[Vec<bool>]) -> bool {
    matrix.iter().enumerate().all(|(i, row)| {
        row.iter()
            .enumerate()
            .all(|(j, value)| !(*value && matrix[j][i]))
    })
}

fn is_transitive(matrix: &[Vec<bool>]) -> bool {
    let closure = transitive_closure_matrix(matrix);
    closure == matrix
}

fn is_strictly_totally_ordered(nodes: &[Value], matrix: &[Vec<bool>]) -> bool {
    is_irreflexive(matrix)
        && is_antisymmetric(nodes, matrix)
        && is_transitive(matrix)
        && matrix.iter().enumerate().all(|(i, row)| {
            row.iter()
                .enumerate()
                .all(|(j, value)| i == j || *value || matrix[j][i])
        })
}

fn is_totally_ordered(nodes: &[Value], matrix: &[Vec<bool>]) -> bool {
    is_reflexive(matrix)
        && is_antisymmetric(nodes, matrix)
        && is_transitive(matrix)
        && matrix.iter().enumerate().all(|(i, row)| {
            row.iter()
                .enumerate()
                .all(|(j, value)| *value || matrix[j][i])
        })
}

fn is_connected(matrix: &[Vec<bool>]) -> bool {
    let mut closure = transitive_closure_matrix(matrix);
    for (i, row) in closure.iter_mut().enumerate() {
        row[i] = true;
    }
    closure.iter().all(|row| row.iter().all(|value| *value))
}

pub(super) fn eval_builtin_relation(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    let bool_result = |value: bool| Ok(Some(Value::Bool(value)));

    match name {
        "IsReflexive" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let (func, display) = eval_relation_function(ctx, &args[0])?;
            let matrix = relation_matrix_from_function(&nodes, &func, &display, span)?;
            bool_result(is_reflexive(&matrix))
        }
        "IsReflexiveUnder" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let matrix = relation_matrix_from_operator(ctx, &args[0], &nodes, span)?;
            bool_result(is_reflexive(&matrix))
        }
        "IsIrreflexive" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let (func, display) = eval_relation_function(ctx, &args[0])?;
            let matrix = relation_matrix_from_function(&nodes, &func, &display, span)?;
            bool_result(is_irreflexive(&matrix))
        }
        "IsIrreflexiveUnder" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let matrix = relation_matrix_from_operator(ctx, &args[0], &nodes, span)?;
            bool_result(is_irreflexive(&matrix))
        }
        "IsSymmetric" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let (func, display) = eval_relation_function(ctx, &args[0])?;
            let matrix = relation_matrix_from_function(&nodes, &func, &display, span)?;
            bool_result(is_symmetric(&matrix))
        }
        "IsSymmetricUnder" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let matrix = relation_matrix_from_operator(ctx, &args[0], &nodes, span)?;
            bool_result(is_symmetric(&matrix))
        }
        "IsAntiSymmetric" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let (func, display) = eval_relation_function(ctx, &args[0])?;
            let matrix = relation_matrix_from_function(&nodes, &func, &display, span)?;
            bool_result(is_antisymmetric(&nodes, &matrix))
        }
        "IsAntiSymmetricUnder" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let matrix = relation_matrix_from_operator(ctx, &args[0], &nodes, span)?;
            bool_result(is_antisymmetric(&nodes, &matrix))
        }
        "IsAsymmetric" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let (func, display) = eval_relation_function(ctx, &args[0])?;
            let matrix = relation_matrix_from_function(&nodes, &func, &display, span)?;
            bool_result(is_asymmetric(&matrix))
        }
        "IsAsymmetricUnder" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let matrix = relation_matrix_from_operator(ctx, &args[0], &nodes, span)?;
            bool_result(is_asymmetric(&matrix))
        }
        "IsTransitive" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let (func, display) = eval_relation_function(ctx, &args[0])?;
            let matrix = relation_matrix_from_function(&nodes, &func, &display, span)?;
            bool_result(is_transitive(&matrix))
        }
        "IsTransitiveUnder" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let matrix = relation_matrix_from_operator(ctx, &args[0], &nodes, span)?;
            bool_result(is_transitive(&matrix))
        }
        "IsStrictlyPartiallyOrdered" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let (func, display) = eval_relation_function(ctx, &args[0])?;
            let matrix = relation_matrix_from_function(&nodes, &func, &display, span)?;
            bool_result(
                is_irreflexive(&matrix)
                    && is_antisymmetric(&nodes, &matrix)
                    && is_transitive(&matrix),
            )
        }
        "IsStrictlyPartiallyOrderedUnder" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let matrix = relation_matrix_from_operator(ctx, &args[0], &nodes, span)?;
            bool_result(
                is_irreflexive(&matrix)
                    && is_antisymmetric(&nodes, &matrix)
                    && is_transitive(&matrix),
            )
        }
        "IsPartiallyOrdered" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let (func, display) = eval_relation_function(ctx, &args[0])?;
            let matrix = relation_matrix_from_function(&nodes, &func, &display, span)?;
            bool_result(
                is_reflexive(&matrix)
                    && is_antisymmetric(&nodes, &matrix)
                    && is_transitive(&matrix),
            )
        }
        "IsPartiallyOrderedUnder" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let matrix = relation_matrix_from_operator(ctx, &args[0], &nodes, span)?;
            bool_result(
                is_reflexive(&matrix)
                    && is_antisymmetric(&nodes, &matrix)
                    && is_transitive(&matrix),
            )
        }
        "IsStrictlyTotallyOrdered" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let (func, display) = eval_relation_function(ctx, &args[0])?;
            let matrix = relation_matrix_from_function(&nodes, &func, &display, span)?;
            bool_result(is_strictly_totally_ordered(&nodes, &matrix))
        }
        "IsStrictlyTotallyOrderedUnder" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let matrix = relation_matrix_from_operator(ctx, &args[0], &nodes, span)?;
            bool_result(is_strictly_totally_ordered(&nodes, &matrix))
        }
        "IsTotallyOrdered" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let (func, display) = eval_relation_function(ctx, &args[0])?;
            let matrix = relation_matrix_from_function(&nodes, &func, &display, span)?;
            bool_result(is_totally_ordered(&nodes, &matrix))
        }
        "IsTotallyOrderedUnder" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let matrix = relation_matrix_from_operator(ctx, &args[0], &nodes, span)?;
            bool_result(is_totally_ordered(&nodes, &matrix))
        }
        "TransitiveClosure" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let (func, display) = eval_relation_function(ctx, &args[0])?;
            let matrix = relation_matrix_from_function(&nodes, &func, &display, span)?;
            Ok(Some(relation_function_from_matrix(
                &nodes,
                &transitive_closure_matrix(&matrix),
            )))
        }
        "ReflexiveTransitiveClosure" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let (func, display) = eval_relation_function(ctx, &args[0])?;
            let mut matrix = transitive_closure_matrix(&relation_matrix_from_function(
                &nodes, &func, &display, span,
            )?);
            for (i, row) in matrix.iter_mut().enumerate() {
                row[i] = true;
            }
            Ok(Some(relation_function_from_matrix(&nodes, &matrix)))
        }
        "IsConnected" => {
            check_arity(name, args, 2, span)?;
            let nodes = eval_relation_nodes(ctx, &args[1])?;
            let (func, display) = eval_relation_function(ctx, &args[0])?;
            let matrix = relation_matrix_from_function(&nodes, &func, &display, span)?;
            bool_result(is_connected(&matrix))
        }
        _ => Ok(None),
    }
}
