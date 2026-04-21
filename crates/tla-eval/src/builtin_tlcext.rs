// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    apply_closure_with_values, check_arity, create_closure_from_arg, eval, tlc_register_get,
    tlc_register_set, values_equal, EvalCtx, EvalError, EvalResult, Expr, Span, Spanned, Value,
};
use num_traits::ToPrimitive;
use tla_value::value_fingerprint;
// TLCExt operators — AssertError, AssertEq, Trace, CounterExample, ToTrace, etc.

fn empty_counterexample_value() -> Value {
    Value::record([
        ("action", Value::empty_set()),
        ("state", Value::empty_set()),
    ])
}

fn placeholder_action_value() -> Value {
    Value::record([("name", Value::string("<Action>"))])
}

fn counterexample_from_trace_value(trace_value: &Value) -> Value {
    let Some(states) = trace_value.as_seq_or_tuple_elements() else {
        return empty_counterexample_value();
    };

    let state_nodes: Vec<Value> = states
        .iter()
        .enumerate()
        .map(|(idx, state)| Value::tuple([Value::int((idx + 1) as i64), state.clone()]))
        .collect();

    let action_edges: Vec<Value> = state_nodes
        .windows(2)
        .map(|window| {
            Value::tuple([
                window[0].clone(),
                placeholder_action_value(),
                window[1].clone(),
            ])
        })
        .collect();

    Value::record([
        ("action", Value::set(action_edges)),
        ("state", Value::set(state_nodes)),
    ])
}

fn trace_from_counterexample_value(
    counterexample: &Value,
    span: Option<Span>,
) -> EvalResult<Value> {
    let Value::Record(record) = counterexample else {
        return Err(EvalError::argument_error(
            "first",
            "ToTrace",
            "CounterExample",
            counterexample,
            span,
        ));
    };

    let Some(state_field) = record.get("state") else {
        return Err(EvalError::argument_error(
            "first",
            "ToTrace",
            "CounterExample",
            counterexample,
            span,
        ));
    };

    let Value::Set(states) = state_field else {
        return Err(EvalError::argument_error(
            "first",
            "ToTrace",
            "CounterExample",
            counterexample,
            span,
        ));
    };

    let mut ordered_states: Vec<(i64, Value)> = Vec::with_capacity(states.len());
    for state in states.as_ref() {
        let Value::Tuple(parts) = state else {
            return Err(EvalError::argument_error(
                "first",
                "ToTrace",
                "CounterExample",
                counterexample,
                span,
            ));
        };
        if parts.len() != 2 {
            return Err(EvalError::argument_error(
                "first",
                "ToTrace",
                "CounterExample",
                counterexample,
                span,
            ));
        }

        let Some(idx) = parts[0].to_bigint().and_then(|n| n.to_i64()) else {
            return Err(EvalError::argument_error(
                "first",
                "ToTrace",
                "CounterExample",
                counterexample,
                span,
            ));
        };
        ordered_states.push((idx, parts[1].clone()));
    }

    ordered_states.sort_by_key(|(idx, _)| *idx);
    for (expected, (idx, _)) in ordered_states.iter().enumerate() {
        if *idx != (expected + 1) as i64 {
            return Err(EvalError::argument_error(
                "first",
                "ToTrace",
                "CounterExample",
                counterexample,
                span,
            ));
        }
    }

    Ok(Value::tuple(
        ordered_states.into_iter().map(|(_, state)| state),
    ))
}

pub(super) fn eval_builtin_tlcext(
    ctx: &EvalCtx,
    name: &str,
    args: &[Spanned<Expr>],
    span: Option<Span>,
) -> EvalResult<Option<Value>> {
    match name {
        // AssertError(expectedMsg, expr) - returns TRUE if expr throws an error
        // whose message matches expectedMsg exactly. TLC semantics: the second
        // argument is expected to THROW, not return a boolean.
        // Ref: TLCExt.java assertError()
        "AssertError" => {
            check_arity(name, args, 2, span)?;
            let msg_val = eval(ctx, &args[0])?;
            let expected_msg = msg_val
                .as_string()
                .ok_or_else(|| EvalError::type_error("String", &msg_val, Some(args[0].span)))?;
            // Evaluate expr - if it throws an error, check the message
            match eval(ctx, &args[1]) {
                Ok(_) => {
                    // No error thrown - return FALSE
                    Ok(Some(Value::Bool(false)))
                }
                Err(EvalError::ExitRequested { .. }) => {
                    // ExitRequested is a control-flow signal, not a catchable error
                    Err(EvalError::ExitRequested { span })
                }
                Err(e) => {
                    // Error thrown - check if message matches exactly (TLC semantics)
                    let actual_msg = e.to_string();
                    Ok(Some(Value::Bool(actual_msg == expected_msg)))
                }
            }
        }

        // AssertEq(a, b) - like = but prints values if not equal
        // Must use values_equal for extensional set equality (#2894).
        "AssertEq" => {
            check_arity(name, args, 2, span)?;
            let a = eval(ctx, &args[0])?;
            let b = eval(ctx, &args[1])?;
            let eq = values_equal(ctx, &a, &b, span)?;
            if !eq {
                eprintln!("AssertEq failed:");
                eprintln!("  Left:  {a}");
                eprintln!("  Right: {b}");
            }
            Ok(Some(Value::Bool(eq)))
        }

        // TLCDefer(expr) - defer evaluation (stub: just evaluate)
        "TLCDefer" => {
            check_arity(name, args, 1, span)?;
            // In TLC, this defers evaluation to when the successor state is chosen.
            // For model checking, we just evaluate immediately.
            Ok(Some(eval(ctx, &args[0])?))
        }

        // PickSuccessor(expr) - interactive successor selection (stub: TRUE)
        "PickSuccessor" => {
            check_arity(name, args, 1, span)?;
            // Evaluate condition for any side effects, but TLA2 doesn't do interactive
            // selection, so always return TRUE (non-interactive mode behavior)
            let _cond = eval(ctx, &args[0])?;
            Ok(Some(Value::Bool(true)))
        }

        // TLCNoOp(val) - returns val unchanged (debugging hook)
        "TLCNoOp" => {
            check_arity(name, args, 1, span)?;
            Ok(Some(eval(ctx, &args[0])?))
        }

        // TLCModelValue(str) - create a model value from string
        "TLCModelValue" => {
            check_arity(name, args, 1, span)?;
            let sv = eval(ctx, &args[0])?;
            let s = sv
                .as_string()
                .ok_or_else(|| EvalError::type_error("String", &sv, Some(args[0].span)))?;
            // Use interning to enable pointer-based equality
            Ok(Some(Value::try_model_value(s)?))
        }

        // TLCCache(expr, closure) - caching (stub: just evaluate expr)
        "TLCCache" => {
            check_arity(name, args, 2, span)?;
            // In TLC, this caches based on closure.
            // For model checking, we just evaluate the expression.
            Ok(Some(eval(ctx, &args[0])?))
        }

        // TLCGetOrDefault(key, defaultVal) - like TLCGet but returns default if not set
        // Part of #814: Now uses actual register storage.
        "TLCGetOrDefault" => {
            check_arity(name, args, 2, span)?;
            let key = eval(ctx, &args[0])?;
            let default_val = eval(ctx, &args[1])?;

            // Handle integer register access
            if let Some(i) = key.to_bigint().and_then(|n| n.to_i64()) {
                if i < 0 {
                    return Err(EvalError::Internal {
                        message: format!(
                            "TLCGetOrDefault: register index must be non-negative, got {i}"
                        ),
                        span,
                    });
                }
                match tlc_register_get(i) {
                    Some(val) => return Ok(Some(val)),
                    None => return Ok(Some(default_val)),
                }
            }

            Err(EvalError::type_error("Int", &key, Some(args[0].span)))
        }

        // TLCGetAndSet(key, Op, val, defaultVal) - atomic get-and-set
        // Part of #814: Now uses actual register storage.
        // Semantics: oldVal = TLCGetOrDefault(key, defaultVal), then TLCSet(key, Op(oldVal, val))
        // Returns oldVal (the value before the set)
        "TLCGetAndSet" => {
            check_arity(name, args, 4, span)?;
            let key = eval(ctx, &args[0])?;
            let val = eval(ctx, &args[2])?;
            let default_val = eval(ctx, &args[3])?;

            // Handle integer register access
            if let Some(i) = key.to_bigint().and_then(|n| n.to_i64()) {
                if i < 0 {
                    return Err(EvalError::Internal {
                        message: format!(
                            "TLCGetAndSet: register index must be non-negative, got {i}"
                        ),
                        span,
                    });
                }

                // Get old value (or default)
                let old_val = tlc_register_get(i).unwrap_or_else(|| default_val.clone());

                // Apply binary operator: Op(oldVal, val)
                // Create closure from the operator argument and apply it
                let op_value = create_closure_from_arg(ctx, &args[1], "TLCGetAndSet", 2, span)?;
                let Value::Closure(ref op_closure) = op_value else {
                    return Err(EvalError::Internal {
                        message: "TLCGetAndSet: second argument must be an operator".into(),
                        span,
                    });
                };
                let new_val =
                    apply_closure_with_values(ctx, &op_closure, &[old_val.clone(), val], span)?;

                // Set the new value
                tlc_register_set(i, new_val);

                // Return old value
                return Ok(Some(old_val));
            }

            Err(EvalError::type_error("Int", &key, Some(args[0].span)))
        }

        // TLCFP(val) - returns the fingerprint of a value as an integer
        "TLCFP" => {
            check_arity(name, args, 1, span)?;
            let val = eval(ctx, &args[0])?;
            // Compute fingerprint and return lower 32 bits as integer
            // TLC returns lower 32 bits because TLA+ integers can't represent 64-bit values easily
            let fp = value_fingerprint(&val).map_err(|e| EvalError::Internal {
                message: e.to_string(),
                span,
            })?;
            // Return as signed 32-bit integer (TLC behavior)
            let fp32 = (fp & 0xFFFFFFFF) as i32;
            Ok(Some(Value::int(fp32 as i64)))
        }

        // TLCEvalDefinition(defName) - evaluate a definition by name
        // Useful for dynamically accessing definitions
        "TLCEvalDefinition" => {
            check_arity(name, args, 1, span)?;
            let name_val = eval(ctx, &args[0])?;
            let def_name = name_val
                .as_string()
                .ok_or_else(|| EvalError::type_error("String", &name_val, Some(args[0].span)))?;

            // Look up the definition
            let op_def = ctx.get_op(def_name).ok_or_else(|| EvalError::UndefinedOp {
                name: def_name.to_string(),
                span,
            })?;

            // Must be zero-arity
            if !op_def.params.is_empty() {
                return Err(EvalError::ArityMismatch {
                    op: def_name.to_string(),
                    expected: 0,
                    got: op_def.params.len(),
                    span,
                });
            }

            // Evaluate the body
            Ok(Some(eval(ctx, &op_def.body)?))
        }

        // Trace - returns the current trace as a sequence of records
        // Part of #1117: Returns the trace (initial state -> current state) as a tuple of records
        "Trace" => {
            check_arity(name, args, 0, span)?;
            // TLCExt!Trace requires trace context to be populated by the model checker.
            // When trace context is set (during invariant/action evaluation), return it.
            // When not set (e.g., constant evaluation), return error per TLC semantics.
            if let Some(trace_value) = &ctx.tlc_trace_value {
                Ok(Some(Value::clone(trace_value)))
            } else {
                // Per TLC semantics: Trace fails when evaluated outside model checking context
                Err(EvalError::Internal {
                    message: "TLCExt!Trace: trace context not available. Trace can only be \
                              evaluated during model checking when the trace has been reconstructed."
                        .to_string(),
                    span,
                })
            }
        }

        // CounterExample - returns counterexample graph when trace context is available.
        // TLC returns an empty graph when no counterexample has been installed.
        "CounterExample" => {
            check_arity(name, args, 0, span)?;
            if let Some(trace_value) = ctx.tlc_trace_value() {
                Ok(Some(counterexample_from_trace_value(trace_value)))
            } else {
                Ok(Some(empty_counterexample_value()))
            }
        }

        // ToTrace(ce) - convert CounterExample graph back to an ordered trace sequence.
        "ToTrace" => {
            check_arity(name, args, 1, span)?;
            let ce = eval(ctx, &args[0])?;
            Ok(Some(trace_from_counterexample_value(&ce, span)?))
        }

        // Not handled by this domain
        _ => Ok(None),
    }
}
