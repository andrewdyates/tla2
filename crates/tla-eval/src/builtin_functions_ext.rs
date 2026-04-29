// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    check_arity, eval, values_equal, EvalCtx, EvalError, EvalResult, Expr, FuncValue, Span,
    Spanned, Value,
};
use rustc_hash::FxHashSet;
use std::sync::Arc;
// FunctionsExt module operators — RestrictDomain, RestrictValues, IsRestriction, Pointwise, AntiFunction

pub(super) fn eval_builtin_functions_ext(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // RestrictDomain(f, P) - restrict function to domain elements satisfying predicate P
        // RestrictDomain(f, P) == [x \in DOMAIN f |-> f[x] : P(x)]
        "RestrictDomain" => {
            check_arity(name, args, 2, span)?;
            let fv = eval(ctx, &args[0])?;
            let func = fv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Func", &fv, Some(args[0].span)))?;

            // Get the predicate (should be a lambda with one parameter)
            let (param, pred_body) = match &args[1].node {
                Expr::Lambda(params, body) if params.len() == 1 => {
                    (params[0].node.clone(), body.as_ref())
                }
                _ => {
                    return Err(EvalError::Internal {
                        message: "RestrictDomain requires a lambda predicate as second argument"
                            .into(),
                        span,
                    });
                }
            };

            let mut new_entries: Vec<(Value, Value)> = Vec::new();
            for (key, val) in func.mapping_iter() {
                let pred_ctx = ctx.bind(param.as_str(), key.clone());
                let pred_result = eval(&pred_ctx, pred_body)?;
                if pred_result
                    .as_bool()
                    .ok_or_else(|| EvalError::type_error("BOOLEAN", &pred_result, span))?
                {
                    new_entries.push((key.clone(), val.clone()));
                }
            }

            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                new_entries,
            )))))
        }

        // RestrictValues(f, P) - restrict function to domain elements whose range values satisfy P
        // RestrictValues(f, P) == [x \in DOMAIN f |-> f[x] : P(f[x])]
        "RestrictValues" => {
            check_arity(name, args, 2, span)?;
            let fv = eval(ctx, &args[0])?;
            let func = fv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Func", &fv, Some(args[0].span)))?;

            // Get the predicate (should be a lambda with one parameter)
            let (param, pred_body) = match &args[1].node {
                Expr::Lambda(params, body) if params.len() == 1 => {
                    (params[0].node.clone(), body.as_ref())
                }
                _ => {
                    return Err(EvalError::Internal {
                        message: "RestrictValues requires a lambda predicate as second argument"
                            .into(),
                        span,
                    });
                }
            };

            let mut new_entries: Vec<(Value, Value)> = Vec::new();
            for (key, val) in func.mapping_iter() {
                let pred_ctx = ctx.bind(param.as_str(), val.clone());
                let pred_result = eval(&pred_ctx, pred_body)?;
                if pred_result
                    .as_bool()
                    .ok_or_else(|| EvalError::type_error("BOOLEAN", &pred_result, span))?
                {
                    new_entries.push((key.clone(), val.clone()));
                }
            }

            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                new_entries,
            )))))
        }

        // IsRestriction(f, g) - TRUE if f is a restriction of g
        // IsRestriction(f, g) == DOMAIN f \subseteq DOMAIN g /\ \A x \in DOMAIN f: f[x] = g[x]
        "IsRestriction" => {
            check_arity(name, args, 2, span)?;
            let fv = eval(ctx, &args[0])?;
            let func_f = fv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Func", &fv, Some(args[0].span)))?;
            let gv = eval(ctx, &args[1])?;
            let func_g = gv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Func", &gv, Some(args[1].span)))?;

            // Check: DOMAIN f \subseteq DOMAIN g
            for key in func_f.domain_iter() {
                if !func_g.domain_contains(key) {
                    return Ok(Some(Value::Bool(false)));
                }
            }

            // Check: \A x \in DOMAIN f: f[x] = g[x]
            // Must use values_equal for extensional set equality (#2894).
            for key in func_f.domain_iter() {
                match (func_f.mapping_get(key), func_g.mapping_get(key)) {
                    (Some(fv), Some(gv)) => {
                        if !values_equal(ctx, fv, gv, span)? {
                            return Ok(Some(Value::Bool(false)));
                        }
                    }
                    _ => return Ok(Some(Value::Bool(false))),
                }
            }

            Ok(Some(Value::Bool(true)))
        }

        // Pointwise(Op, f, g) - pointwise combination of two functions
        // Pointwise(Op, f, g) == [x \in DOMAIN f \cap DOMAIN g |-> Op(f[x], g[x])]
        "Pointwise" => {
            check_arity(name, args, 3, span)?;

            // Get the operator name from the first argument
            let op_name = match &args[0].node {
                Expr::Ident(name, _) => name.clone(),
                _ => {
                    return Err(EvalError::Internal {
                        message: "Pointwise requires operator name as first argument".into(),
                        span,
                    });
                }
            };

            let fv = eval(ctx, &args[1])?;
            let func_f = fv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Func", &fv, Some(args[1].span)))?;
            let gv = eval(ctx, &args[2])?;
            let func_g = gv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Func", &gv, Some(args[2].span)))?;

            // Get the operator definition
            let op_def = ctx.get_op(&op_name).ok_or_else(|| EvalError::UndefinedOp {
                name: op_name.clone(),
                span,
            })?;

            if op_def.params.len() != 2 {
                return Err(EvalError::ArityMismatch {
                    op: op_name,
                    expected: 2,
                    got: op_def.params.len(),
                    span,
                });
            }

            // Compute intersection of domains
            let mut new_entries: Vec<(Value, Value)> = Vec::new();

            for key in func_f.domain_iter() {
                if func_g.domain_contains(key) {
                    if let (Some(f_val), Some(g_val)) =
                        (func_f.mapping_get(key), func_g.mapping_get(key))
                    {
                        let new_ctx = ctx.bind2(
                            op_def.params[0].name.node.as_str(),
                            f_val.clone(),
                            op_def.params[1].name.node.as_str(),
                            g_val.clone(),
                        );
                        let result_val = eval(&new_ctx, &op_def.body)?;
                        new_entries.push((key.clone(), result_val));
                    }
                }
            }

            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                new_entries,
            )))))
        }

        // AntiFunction(f) - reverses key-value pairs (only valid for injective functions)
        // AntiFunction(f) == [y \in Range(f) |-> CHOOSE x \in DOMAIN f : f[x] = y]
        "AntiFunction" => {
            check_arity(name, args, 1, span)?;
            let fv = eval(ctx, &args[0])?;
            let func = fv
                .to_func_coerced()
                .ok_or_else(|| EvalError::type_error("Func", &fv, Some(args[0].span)))?;

            // Phase 1A (#3073): FxHashSet for O(1) membership vs OrdSet O(log n)
            #[allow(clippy::mutable_key_type)]
            let mut seen_values: FxHashSet<Value> = FxHashSet::default();
            let mut new_entries: Vec<(Value, Value)> = Vec::new();

            for (key, val) in func.mapping_iter() {
                if seen_values.contains(val) {
                    return Err(EvalError::Internal {
                        message: "AntiFunction requires an injective function".into(),
                        span,
                    });
                }
                seen_values.insert(val.clone());
                new_entries.push((val.clone(), key.clone()));
            }

            // Sort entries by new key (the original values)
            new_entries.sort_by(|a, b| a.0.cmp(&b.0));
            Ok(Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                new_entries,
            )))))
        }

        _ => Ok(None),
    }
}
