// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Value conversion and operation helpers for the bytecode VM executor.

use num_bigint::BigInt;
use num_traits::ToPrimitive;
use smallvec::SmallVec;
use std::cell::Cell;
use std::sync::Arc;
use tla_value::error::EvalError;
use tla_value::{SortedSet, Value};

use crate::{apply_closure_with_values, core::EvalCtx, StateEnvRef};

use super::execute::VmError;

const MAX_VM_CALL_DEPTH: u16 = 16;

thread_local! {
    static VM_CALL_DEPTH: Cell<u16> = const { Cell::new(0) };
}

pub(super) fn as_bool(v: &Value) -> Result<bool, VmError> {
    match v {
        Value::Bool(b) => Ok(*b),
        _ => Err(VmError::TypeError {
            expected: "boolean",
            actual: format!("{v:?}"),
        }),
    }
}

pub(super) fn to_bigint(v: &Value) -> Result<BigInt, VmError> {
    match v {
        Value::SmallInt(n) => Ok(BigInt::from(*n)),
        Value::Int(n) => Ok(n.as_ref().clone()),
        _ => Err(VmError::TypeError {
            expected: "integer",
            actual: format!("{v:?}"),
        }),
    }
}

pub(super) fn to_sorted_set(v: &Value) -> Result<SortedSet, VmError> {
    v.to_sorted_set().ok_or_else(|| VmError::TypeError {
        expected: "set",
        actual: format!("{v:?}"),
    })
}

pub(super) fn int_arith(
    left: &Value,
    right: &Value,
    small_op: impl Fn(i64, i64) -> Option<i64>,
    big_op: impl Fn(BigInt, BigInt) -> BigInt,
) -> Result<Value, VmError> {
    if let (Value::SmallInt(a), Value::SmallInt(b)) = (left, right) {
        if let Some(result) = small_op(*a, *b) {
            return Ok(Value::SmallInt(result));
        }
    }
    let a = to_bigint(left)?;
    let b = to_bigint(right)?;
    Ok(Value::big_int(big_op(a, b)))
}

pub(super) fn int_div(
    left: &Value,
    right: &Value,
    small_op: impl Fn(i64, i64) -> Option<i64>,
    big_op: impl Fn(BigInt, BigInt) -> BigInt,
) -> Result<Value, VmError> {
    match right {
        Value::SmallInt(0) => {
            return Err(VmError::Eval(EvalError::DivisionByZero { span: None }));
        }
        Value::Int(n) if n.as_ref() == &BigInt::from(0) => {
            return Err(VmError::Eval(EvalError::DivisionByZero { span: None }));
        }
        _ => {}
    }
    int_arith(left, right, small_op, big_op)
}

pub(super) fn int_cmp(
    left: &Value,
    right: &Value,
    small_cmp: impl Fn(i64, i64) -> bool,
    big_cmp: impl Fn(&BigInt, &BigInt) -> bool,
) -> Result<Value, VmError> {
    if let (Value::SmallInt(a), Value::SmallInt(b)) = (left, right) {
        return Ok(Value::Bool(small_cmp(*a, *b)));
    }
    let a = to_bigint(left)?;
    let b = to_bigint(right)?;
    Ok(Value::Bool(big_cmp(&a, &b)))
}

pub(super) fn int_pow(base: &Value, exp: &Value) -> Result<Value, VmError> {
    let b = to_bigint(base)?;
    let e = to_bigint(exp)?;
    let e_u32 = e.to_u32().ok_or_else(|| VmError::TypeError {
        expected: "non-negative exponent fitting in u32",
        actual: format!("{e}"),
    })?;
    Ok(Value::big_int(b.pow(e_u32)))
}

pub(super) fn func_apply(f: &Value, a: &Value) -> Result<Value, VmError> {
    match f {
        Value::Func(fv) => fv.apply(a).cloned().ok_or_else(|| {
            VmError::Eval(EvalError::NotInDomain {
                arg: format!("{a}"),
                func_display: Some(format!("{f}")),
                span: None,
            })
        }),
        Value::IntFunc(ifv) => ifv.apply(a).cloned().ok_or_else(|| {
            VmError::Eval(EvalError::NotInDomain {
                arg: format!("{a}"),
                func_display: Some(format!("{f}")),
                span: None,
            })
        }),
        Value::Tuple(t) => {
            if let Value::SmallInt(idx) = a {
                let i = *idx as usize;
                if i >= 1 && i <= t.len() {
                    Ok(t[i - 1].clone())
                } else {
                    Err(VmError::Eval(EvalError::NotInDomain {
                        arg: format!("{a}"),
                        func_display: Some(format!("{f}")),
                        span: None,
                    }))
                }
            } else {
                Err(VmError::Eval(EvalError::NotInDomain {
                    arg: format!("{a}"),
                    func_display: Some(format!("{f}")),
                    span: None,
                }))
            }
        }
        Value::Seq(s) => {
            if let Value::SmallInt(idx) = a {
                let i = *idx as usize;
                if i >= 1 && i <= s.len() {
                    Ok(s.get(i - 1).cloned().unwrap_or(Value::Bool(false)))
                } else {
                    Err(VmError::Eval(EvalError::NotInDomain {
                        arg: format!("{a}"),
                        func_display: Some(format!("{f}")),
                        span: None,
                    }))
                }
            } else {
                Err(VmError::Eval(EvalError::NotInDomain {
                    arg: format!("{a}"),
                    func_display: Some(format!("{f}")),
                    span: None,
                }))
            }
        }
        Value::Record(rec) => {
            if let Value::String(s) = a {
                rec.get(s).cloned().ok_or_else(|| {
                    VmError::Eval(EvalError::NotInDomain {
                        arg: format!("{a}"),
                        func_display: Some(format!("{f}")),
                        span: None,
                    })
                })
            } else {
                Err(VmError::Eval(EvalError::NotInDomain {
                    arg: format!("{a}"),
                    func_display: Some(format!("{f}")),
                    span: None,
                }))
            }
        }
        _ => Err(VmError::Eval(EvalError::NotInDomain {
            arg: format!("{a}"),
            func_display: Some(format!("{f}")),
            span: None,
        })),
    }
}

pub(super) fn value_apply(
    ctx: Option<&EvalCtx>,
    callable: &Value,
    args: &[Value],
) -> Result<Value, VmError> {
    match callable {
        Value::Closure(closure) => {
            let Some(ctx) = ctx else {
                return Err(VmError::Unsupported(
                    "closure apply requires EvalCtx".to_string(),
                ));
            };
            apply_closure_with_values(ctx, closure.as_ref(), args, None).map_err(VmError::Eval)
        }
        _ if args.len() == 1 => func_apply(callable, &args[0]),
        _ => Err(VmError::Unsupported(format!(
            "value apply expects closure or single-arg function, got argc={}",
            args.len()
        ))),
    }
}

/// Call an external (non-compiled) operator by name via the TIR tree-walker.
///
/// Used by the `CallExternal` opcode for INSTANCE-imported operators that
/// weren't pre-compiled into bytecode. Delegates to `EvalCtx::eval_op` for
/// zero-arg operators, or `apply_user_op_with_values` for parameterized ones.
pub(super) fn call_external(
    ctx: Option<&EvalCtx>,
    name: &str,
    args: &[Value],
) -> Result<Value, VmError> {
    let ctx =
        ctx.ok_or_else(|| VmError::Unsupported("CallExternal requires EvalCtx".to_string()))?;
    if args.is_empty() {
        ctx.eval_op(name).map_err(VmError::Eval)
    } else {
        let def = ctx.get_op(name).ok_or_else(|| {
            VmError::Eval(tla_value::error::EvalError::UndefinedOp {
                name: name.to_string(),
                span: None,
            })
        })?;
        let def = Arc::clone(def);
        crate::apply_user_op_with_values(ctx, name, &def, args, None).map_err(VmError::Eval)
    }
}

#[inline]
pub(super) fn enter_vm_call() -> Result<(), VmError> {
    let depth = VM_CALL_DEPTH.with(|d| {
        let cur = d.get();
        d.set(cur + 1);
        cur + 1
    });
    if depth > MAX_VM_CALL_DEPTH {
        exit_vm_call();
        return Err(VmError::Unsupported(format!(
            "VM call depth exceeded ({MAX_VM_CALL_DEPTH})"
        )));
    }
    Ok(())
}

#[inline]
pub(super) fn exit_vm_call() {
    VM_CALL_DEPTH.with(|d| d.set(d.get() - 1));
}

#[inline]
pub(super) fn load_cached_value(
    env: StateEnvRef,
    cache: &mut SmallVec<[Option<Value>; 8]>,
    idx: usize,
) -> Value {
    if idx >= cache.len() {
        cache.resize(idx + 1, None);
    }
    if let Some(value) = &cache[idx] {
        return value.clone();
    }
    // SAFETY: callers bounds-check `idx` against the environment length first.
    let value = unsafe { env.get_value(idx) };
    cache[idx] = Some(value.clone());
    value
}

pub(super) fn load_state_var(
    env: StateEnvRef,
    cache: &mut SmallVec<[Option<Value>; 8]>,
    var_idx: u16,
) -> Result<Value, VmError> {
    load_state_slot(
        env,
        cache,
        var_idx as usize,
        "valid state variable index",
        "state",
    )
}

#[inline]
pub(super) fn load_prime_var(
    next_state: Option<StateEnvRef>,
    next_state_cache: Option<&mut SmallVec<[Option<Value>; 8]>>,
    var_idx: u16,
) -> Result<Value, VmError> {
    let env = next_state.ok_or_else(|| VmError::TypeError {
        expected: "next state available for primed variable",
        actual: "no next state bound".to_string(),
    })?;
    let cache = next_state_cache.expect("next_state_cache must exist when next_state is present");
    load_state_slot(
        env,
        cache,
        var_idx as usize,
        "valid primed variable index",
        "next_state",
    )
}

#[inline]
fn load_state_slot(
    env: StateEnvRef,
    cache: &mut SmallVec<[Option<Value>; 8]>,
    idx: usize,
    expected: &'static str,
    label: &'static str,
) -> Result<Value, VmError> {
    if idx < env.env_len() {
        Ok(load_cached_value(env, cache, idx))
    } else {
        Err(VmError::TypeError {
            expected,
            actual: format!("index {idx} >= {label} len {}", env.env_len()),
        })
    }
}

pub(super) fn value_domain(v: &Value) -> Result<Value, VmError> {
    match v {
        Value::Func(f) => Ok(Value::Set(Arc::new(SortedSet::from_iter(
            f.domain_iter().cloned(),
        )))),
        Value::IntFunc(f) => {
            let lo = BigInt::from(tla_value::IntIntervalFunc::min(f));
            let hi = BigInt::from(tla_value::IntIntervalFunc::max(f));
            Ok(tla_value::range_set(&lo, &hi))
        }
        Value::Tuple(t) => {
            let lo = BigInt::from(1);
            let hi = BigInt::from(t.len() as i64);
            Ok(tla_value::range_set(&lo, &hi))
        }
        Value::Seq(s) => {
            let lo = BigInt::from(1);
            let hi = BigInt::from(s.len() as i64);
            Ok(tla_value::range_set(&lo, &hi))
        }
        Value::Record(rec) => {
            let keys: Vec<Value> = rec.key_strings().map(Value::String).collect();
            Ok(Value::Set(Arc::new(SortedSet::from_iter(keys))))
        }
        _ => Err(VmError::TypeError {
            expected: "function-like value for DOMAIN",
            actual: format!("{v:?}"),
        }),
    }
}

pub(super) fn value_except(f: Value, arg: Value, val: Value) -> Result<Value, VmError> {
    match &f {
        Value::Func(fv) => Ok(Value::Func(Arc::new(fv.as_ref().clone().except(arg, val)))),
        Value::IntFunc(ifv) => Ok(Value::IntFunc(Arc::new(
            ifv.as_ref().clone().except(arg, val),
        ))),
        Value::Tuple(t) => {
            if let Value::SmallInt(idx) = &arg {
                let i = (*idx as usize).wrapping_sub(1);
                if i < t.len() {
                    let mut new_t: Vec<Value> = t.as_ref().to_vec();
                    new_t[i] = val;
                    return Ok(Value::Tuple(new_t.into()));
                }
            }
            Err(VmError::TypeError {
                expected: "valid tuple index for EXCEPT",
                actual: format!("{arg:?}"),
            })
        }
        Value::Seq(s) => {
            if let Value::SmallInt(idx) = &arg {
                let i = (*idx as usize).wrapping_sub(1);
                if i < s.len() {
                    return Ok(Value::Seq(Arc::new(s.except(i, val))));
                }
            }
            Err(VmError::TypeError {
                expected: "valid sequence index for EXCEPT",
                actual: format!("{arg:?}"),
            })
        }
        Value::Record(rec) => {
            if let Value::String(field_name) = &arg {
                let name_id = tla_core::intern_name(field_name);
                return Ok(Value::Record(rec.insert(name_id, val)));
            }
            Err(VmError::TypeError {
                expected: "string field name for record EXCEPT",
                actual: format!("{arg:?}"),
            })
        }
        _ => Err(VmError::TypeError {
            expected: "function-like value for EXCEPT",
            actual: format!("{f:?}"),
        }),
    }
}
