// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Preflight constant evaluator for JIT compilation.
//!
//! Evaluates TLA+ expressions at compile time to detect overflow, division by
//! zero, and type errors *before* emitting Cranelift IR.  Cranelift integer
//! ops wrap on overflow, so the preflight pass ensures every executed integer
//! operation is in-range for i64.

use crate::error::JitError;
use num_traits::ToPrimitive;
use tla_core::ast::{ExceptPathElement, ExceptSpec, Expr};

use super::lower::expr_type_name;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum PreflightValue {
    Bool(bool),
    Int(i64),
    /// A finite set of integer values (for set membership and quantifier domains).
    Set(Vec<i64>),
    /// A compile-time function: mapping from i64 keys to i64 values, plus
    /// the domain as an ordered set of keys.
    /// Used for constant-folding `FuncApply`, `Domain`, and `RecordAccess`.
    Function(Vec<(i64, i64)>),
    /// A compile-time record: mapping from field name strings to i64 values.
    /// Used for constant-folding `RecordAccess`.
    Record(Vec<(String, i64)>),
    /// A compile-time function that maps i64 keys to record values.
    /// Used for compiling `f[x].field` where `f` maps integers to records
    /// and `x` is a runtime value. Each entry is `(key, record_fields)`.
    /// Part of #3798.
    RecordFunction(Vec<(i64, Vec<(String, i64)>)>),
}

impl PreflightValue {
    pub(crate) fn ty_name(&self) -> &'static str {
        match self {
            PreflightValue::Bool(_) => "boolean",
            PreflightValue::Int(_) => "integer",
            PreflightValue::Set(_) => "set",
            PreflightValue::Function(_) => "function",
            PreflightValue::Record(_) => "record",
            PreflightValue::RecordFunction(_) => "record-function",
        }
    }

    pub(crate) fn as_i64(self) -> Result<i64, JitError> {
        match self {
            PreflightValue::Bool(false) => Ok(0),
            PreflightValue::Bool(true) => Ok(1),
            PreflightValue::Int(v) => Ok(v),
            other => Err(JitError::TypeMismatch {
                expected: "scalar (boolean or integer)".to_string(),
                actual: other.ty_name().to_string(),
            }),
        }
    }
}

pub(crate) fn preflight_const_value(expr: &Expr) -> Result<PreflightValue, JitError> {
    fn overflow(op: &str) -> JitError {
        JitError::CompileError(format!("i64 {op} overflow in JIT (fallback required)"))
    }

    fn type_mismatch(expected: &str, actual: PreflightValue) -> JitError {
        JitError::TypeMismatch {
            expected: expected.to_string(),
            actual: actual.ty_name().to_string(),
        }
    }

    fn expect_int(v: PreflightValue) -> Result<i64, JitError> {
        match v {
            PreflightValue::Int(n) => Ok(n),
            other => Err(type_mismatch("integer", other)),
        }
    }

    fn expect_bool(v: PreflightValue) -> Result<bool, JitError> {
        match v {
            PreflightValue::Bool(b) => Ok(b),
            other => Err(type_mismatch("boolean", other)),
        }
    }

    match expr {
        Expr::Int(n) => n
            .to_i64()
            .ok_or_else(|| JitError::CompileError("Integer too large for i64".to_string()))
            .map(PreflightValue::Int),

        Expr::Bool(true) => Ok(PreflightValue::Bool(true)),
        Expr::Bool(false) => Ok(PreflightValue::Bool(false)),

        Expr::Add(left, right) => {
            let lhs = expect_int(preflight_const_value(&left.node)?)?;
            let rhs = expect_int(preflight_const_value(&right.node)?)?;
            lhs.checked_add(rhs)
                .ok_or_else(|| overflow("add"))
                .map(PreflightValue::Int)
        }
        Expr::Sub(left, right) => {
            let lhs = expect_int(preflight_const_value(&left.node)?)?;
            let rhs = expect_int(preflight_const_value(&right.node)?)?;
            lhs.checked_sub(rhs)
                .ok_or_else(|| overflow("sub"))
                .map(PreflightValue::Int)
        }
        Expr::Mul(left, right) => {
            let lhs = expect_int(preflight_const_value(&left.node)?)?;
            let rhs = expect_int(preflight_const_value(&right.node)?)?;
            lhs.checked_mul(rhs)
                .ok_or_else(|| overflow("mul"))
                .map(PreflightValue::Int)
        }
        Expr::Div(left, right) => {
            // Regular division (/) - truncates toward zero
            let lhs = expect_int(preflight_const_value(&left.node)?)?;
            let rhs = expect_int(preflight_const_value(&right.node)?)?;
            if rhs == 0 {
                return Err(JitError::CompileError(
                    "division by zero in JIT (fallback required)".to_string(),
                ));
            }
            lhs.checked_div(rhs)
                .ok_or_else(|| overflow("div"))
                .map(PreflightValue::Int)
        }
        Expr::IntDiv(left, right) => {
            // TLA+ \div - floor division, matches TLC semantics
            // See ~/tlaplus/tlatools/org.lamport.tlatools/src/tlc2/module/Integers.java:154
            let lhs = expect_int(preflight_const_value(&left.node)?)?;
            let rhs = expect_int(preflight_const_value(&right.node)?)?;
            if rhs == 0 {
                return Err(JitError::CompileError(
                    "division by zero in JIT (fallback required)".to_string(),
                ));
            }
            // Floor division: MIN / -1 overflows i64
            if lhs == i64::MIN && rhs == -1 {
                return Err(overflow("div"));
            }
            let q = lhs / rhs;
            let result = if (lhs ^ rhs) < 0 && lhs % rhs != 0 {
                q - 1
            } else {
                q
            };
            Ok(PreflightValue::Int(result))
        }
        Expr::Mod(left, right) => {
            // TLA+ % - Euclidean modulo with positive divisor requirement (TLC semantics)
            // See ~/tlaplus/tlatools/org.lamport.tlatools/src/tlc2/module/Integers.java:174
            let lhs = expect_int(preflight_const_value(&left.node)?)?;
            let rhs = expect_int(preflight_const_value(&right.node)?)?;
            if rhs <= 0 {
                return Err(JitError::CompileError(
                    "modulus divisor not positive in JIT (TLC requires y > 0)".to_string(),
                ));
            }
            // rem_euclid always returns non-negative for positive divisor
            Ok(PreflightValue::Int(lhs.rem_euclid(rhs)))
        }
        Expr::Neg(inner) => {
            let v = expect_int(preflight_const_value(&inner.node)?)?;
            v.checked_neg()
                .ok_or_else(|| overflow("neg"))
                .map(PreflightValue::Int)
        }
        Expr::Pow(base, exp) => {
            let base = expect_int(preflight_const_value(&base.node)?)?;
            let exp = expect_int(preflight_const_value(&exp.node)?)?;
            if exp < 0 {
                return Err(JitError::CompileError(
                    "negative exponent in JIT (fallback required)".to_string(),
                ));
            }

            let mut exp = u64::try_from(exp)
                .map_err(|_| JitError::CompileError("invalid exponent in JIT".to_string()))?;
            let mut acc = 1i64;
            let mut factor = base;
            while exp > 0 {
                if (exp & 1) != 0 {
                    acc = acc.checked_mul(factor).ok_or_else(|| overflow("pow mul"))?;
                }
                exp >>= 1;
                if exp > 0 {
                    factor = factor
                        .checked_mul(factor)
                        .ok_or_else(|| overflow("pow mul"))?;
                }
            }
            Ok(PreflightValue::Int(acc))
        }

        Expr::Eq(left, right) => {
            let lhs = preflight_const_value(&left.node)?;
            let rhs = preflight_const_value(&right.node)?;
            match (lhs, rhs) {
                (PreflightValue::Int(a), PreflightValue::Int(b)) => {
                    Ok(PreflightValue::Bool(a == b))
                }
                (PreflightValue::Bool(a), PreflightValue::Bool(b)) => {
                    Ok(PreflightValue::Bool(a == b))
                }
                (a, b) => {
                    if a.as_i64()? == b.as_i64()? {
                        Err(JitError::CompileError(
                            "cannot distinguish bool from int in equality (fallback required)"
                                .to_string(),
                        ))
                    } else {
                        Ok(PreflightValue::Bool(false))
                    }
                }
            }
        }
        Expr::Neq(left, right) => {
            let lhs = preflight_const_value(&left.node)?;
            let rhs = preflight_const_value(&right.node)?;
            match (lhs, rhs) {
                (PreflightValue::Int(a), PreflightValue::Int(b)) => {
                    Ok(PreflightValue::Bool(a != b))
                }
                (PreflightValue::Bool(a), PreflightValue::Bool(b)) => {
                    Ok(PreflightValue::Bool(a != b))
                }
                (a, b) => {
                    if a.as_i64()? == b.as_i64()? {
                        Err(JitError::CompileError(
                            "cannot distinguish bool from int in inequality (fallback required)"
                                .to_string(),
                        ))
                    } else {
                        Ok(PreflightValue::Bool(true))
                    }
                }
            }
        }
        Expr::Lt(left, right) => {
            let lhs = expect_int(preflight_const_value(&left.node)?)?;
            let rhs = expect_int(preflight_const_value(&right.node)?)?;
            Ok(PreflightValue::Bool(lhs < rhs))
        }
        Expr::Leq(left, right) => {
            let lhs = expect_int(preflight_const_value(&left.node)?)?;
            let rhs = expect_int(preflight_const_value(&right.node)?)?;
            Ok(PreflightValue::Bool(lhs <= rhs))
        }
        Expr::Gt(left, right) => {
            let lhs = expect_int(preflight_const_value(&left.node)?)?;
            let rhs = expect_int(preflight_const_value(&right.node)?)?;
            Ok(PreflightValue::Bool(lhs > rhs))
        }
        Expr::Geq(left, right) => {
            let lhs = expect_int(preflight_const_value(&left.node)?)?;
            let rhs = expect_int(preflight_const_value(&right.node)?)?;
            Ok(PreflightValue::Bool(lhs >= rhs))
        }

        Expr::And(left, right) => {
            let lhs = expect_bool(preflight_const_value(&left.node)?)?;
            if !lhs {
                Ok(PreflightValue::Bool(false))
            } else {
                Ok(PreflightValue::Bool(expect_bool(preflight_const_value(
                    &right.node,
                )?)?))
            }
        }
        Expr::Or(left, right) => {
            let lhs = expect_bool(preflight_const_value(&left.node)?)?;
            if lhs {
                Ok(PreflightValue::Bool(true))
            } else {
                Ok(PreflightValue::Bool(expect_bool(preflight_const_value(
                    &right.node,
                )?)?))
            }
        }
        Expr::Not(inner) => {
            let v = expect_bool(preflight_const_value(&inner.node)?)?;
            Ok(PreflightValue::Bool(!v))
        }
        Expr::Implies(left, right) => {
            let lhs = expect_bool(preflight_const_value(&left.node)?)?;
            if !lhs {
                Ok(PreflightValue::Bool(true))
            } else {
                Ok(PreflightValue::Bool(expect_bool(preflight_const_value(
                    &right.node,
                )?)?))
            }
        }
        Expr::Equiv(left, right) => {
            // TLC evaluates both sides first, then checks both are booleans.
            let lhs = preflight_const_value(&left.node)?;
            let rhs = preflight_const_value(&right.node)?;
            let lhs = expect_bool(lhs)?;
            let rhs = expect_bool(rhs)?;
            Ok(PreflightValue::Bool(lhs == rhs))
        }

        Expr::If(cond, then_expr, else_expr) => {
            let cond_val = expect_bool(preflight_const_value(&cond.node)?)?;
            if cond_val {
                preflight_const_value(&then_expr.node)
            } else {
                preflight_const_value(&else_expr.node)
            }
        }

        // === Set enumeration ===
        Expr::SetEnum(elements) => {
            let mut vals = Vec::with_capacity(elements.len());
            for elem in elements {
                vals.push(expect_int(preflight_const_value(&elem.node)?)?);
            }
            Ok(PreflightValue::Set(vals))
        }

        // === Integer range (a..b) ===
        Expr::Range(lo, hi) => {
            let lo_val = expect_int(preflight_const_value(&lo.node)?)?;
            let hi_val = expect_int(preflight_const_value(&hi.node)?)?;
            if hi_val < lo_val {
                // Empty range
                Ok(PreflightValue::Set(vec![]))
            } else {
                let count = (hi_val - lo_val + 1) as usize;
                // Cap at 1024 elements to prevent huge expansion
                if count > 1024 {
                    return Err(JitError::CompileError(
                        "range too large for JIT expansion (>1024 elements, fallback required)"
                            .to_string(),
                    ));
                }
                let vals: Vec<i64> = (lo_val..=hi_val).collect();
                Ok(PreflightValue::Set(vals))
            }
        }

        // === Set membership: x \in S ===
        Expr::In(elem, set) => {
            let elem_val = expect_int(preflight_const_value(&elem.node)?)?;
            let set_val = expect_set(preflight_const_value(&set.node)?)?;
            Ok(PreflightValue::Bool(set_val.contains(&elem_val)))
        }

        // === Set non-membership: x \notin S ===
        Expr::NotIn(elem, set) => {
            let elem_val = expect_int(preflight_const_value(&elem.node)?)?;
            let set_val = expect_set(preflight_const_value(&set.node)?)?;
            Ok(PreflightValue::Bool(!set_val.contains(&elem_val)))
        }

        // === Universal quantifier: \A x \in S : P(x) ===
        Expr::Forall(bounds, body) => preflight_quantifier(bounds, body, true),

        // === Existential quantifier: \E x \in S : P(x) ===
        Expr::Exists(bounds, body) => preflight_quantifier(bounds, body, false),

        // === Function definition: [x \in S |-> body] ===
        //
        // Evaluates the function by iterating over the domain, substituting each
        // value for the bound variable in the body, and collecting key-value pairs.
        // Only supports single-variable functions with integer domain and integer
        // body (since all JIT values are i64). The body must be constant for each
        // domain element (i.e., it can reference the bound variable via inline
        // constant substitution done by preflight_funcdef_body).
        Expr::FuncDef(bounds, body) => super::preflight_funcdef::preflight_funcdef(bounds, body),

        // === Function application: f[x] ===
        //
        // Evaluates both the function and the argument at compile time.
        // The function must be a compile-time-known Function (FuncDef) and the
        // argument must be an integer key present in the function's domain.
        Expr::FuncApply(func, arg) => {
            let func_val = preflight_const_value(&func.node)?;
            let arg_val = expect_int(preflight_const_value(&arg.node)?)?;
            match func_val {
                PreflightValue::Function(pairs) => {
                    for (k, v) in &pairs {
                        if *k == arg_val {
                            return Ok(PreflightValue::Int(*v));
                        }
                    }
                    Err(JitError::CompileError(
                        "function application: argument not in domain".to_string(),
                    ))
                }
                PreflightValue::RecordFunction(pairs) => {
                    for (k, fields) in &pairs {
                        if *k == arg_val {
                            return Ok(PreflightValue::Record(fields.clone()));
                        }
                    }
                    Err(JitError::CompileError(
                        "function application: argument not in domain".to_string(),
                    ))
                }
                other => Err(JitError::TypeMismatch {
                    expected: "function".to_string(),
                    actual: other.ty_name().to_string(),
                }),
            }
        }

        // === Record constructor: [a |-> 1, b |-> 2] ===
        Expr::Record(fields) => {
            let mut pairs = Vec::with_capacity(fields.len());
            for (name, val_expr) in fields {
                let val = expect_int(preflight_const_value(&val_expr.node)?)?;
                pairs.push((name.node.clone(), val));
            }
            Ok(PreflightValue::Record(pairs))
        }

        // === Record field access: r.field ===
        Expr::RecordAccess(record, field_name) => {
            let rec_val = preflight_const_value(&record.node)?;
            match rec_val {
                PreflightValue::Record(pairs) => {
                    let target = &field_name.name.node;
                    for (k, v) in &pairs {
                        if k == target {
                            return Ok(PreflightValue::Int(*v));
                        }
                    }
                    Err(JitError::CompileError(format!(
                        "record field access: field '{}' not found",
                        target
                    )))
                }
                other => Err(JitError::TypeMismatch {
                    expected: "record".to_string(),
                    actual: other.ty_name().to_string(),
                }),
            }
        }

        // === EXCEPT: [f EXCEPT ![a] = b] or [r EXCEPT !.field = v] ===
        //
        // Evaluates the base expression, then applies each ExceptSpec to modify
        // the resulting function or record. Only single-level paths are supported:
        //   - ![index] = value  for functions (key-value update)
        //   - !.field = value   for records (field update)
        Expr::Except(base, specs) => {
            let base_val = preflight_const_value(&base.node)?;
            preflight_except(base_val, specs)
        }

        // === Domain: DOMAIN f ===
        //
        // Extracts the domain of a function as a set of integer keys.
        Expr::Domain(func) => {
            let func_val = preflight_const_value(&func.node)?;
            match func_val {
                PreflightValue::Function(pairs) => {
                    let domain: Vec<i64> = pairs.iter().map(|(k, _)| *k).collect();
                    Ok(PreflightValue::Set(domain))
                }
                PreflightValue::RecordFunction(pairs) => {
                    let domain: Vec<i64> = pairs.iter().map(|(k, _)| *k).collect();
                    Ok(PreflightValue::Set(domain))
                }
                PreflightValue::Record(pairs) => {
                    // DOMAIN of a record is a set of strings — not representable
                    // as i64 values. Reject for JIT (string sets are not supported).
                    let _ = pairs;
                    Err(JitError::UnsupportedExpr(
                        "DOMAIN of record produces string set, not supported in JIT".to_string(),
                    ))
                }
                other => Err(JitError::TypeMismatch {
                    expected: "function".to_string(),
                    actual: other.ty_name().to_string(),
                }),
            }
        }

        _ => Err(JitError::UnsupportedExpr(format!(
            "{} expression type not yet supported",
            expr_type_name(expr)
        ))),
    }
}

pub(crate) fn preflight_const_i64(expr: &Expr) -> Result<i64, JitError> {
    preflight_const_value(expr)?.as_i64()
}

/// Extract a set of i64 values from a preflight value.
pub(crate) fn expect_set(v: PreflightValue) -> Result<Vec<i64>, JitError> {
    match v {
        PreflightValue::Set(vals) => Ok(vals),
        other => Err(JitError::TypeMismatch {
            expected: "set".to_string(),
            actual: other.ty_name().to_string(),
        }),
    }
}

/// Preflight evaluate an EXCEPT expression.
///
/// Supports two forms:
/// - `[f EXCEPT ![key] = val]` — updates a function's value at `key`
/// - `[r EXCEPT !.field = val]` — updates a record's field value
///
/// Only single-level paths are supported. Multi-level paths like
/// `![a][b]` or `![a].field` are rejected.
fn preflight_except(
    mut base_val: PreflightValue,
    specs: &[ExceptSpec],
) -> Result<PreflightValue, JitError> {
    for spec in specs {
        if spec.path.len() != 1 {
            return Err(JitError::UnsupportedExpr(
                "multi-level EXCEPT path not yet supported in JIT".to_string(),
            ));
        }

        match (&mut base_val, &spec.path[0]) {
            // [f EXCEPT ![key] = val] — function key update
            (PreflightValue::Function(ref mut pairs), ExceptPathElement::Index(idx_expr)) => {
                let key = preflight_const_value(&idx_expr.node)?;
                let key_i64 = match key {
                    PreflightValue::Int(n) => n,
                    other => {
                        return Err(JitError::TypeMismatch {
                            expected: "integer (EXCEPT function key)".to_string(),
                            actual: other.ty_name().to_string(),
                        })
                    }
                };
                let new_val = preflight_const_value(&spec.value.node)?;
                let new_val_i64 = match new_val {
                    PreflightValue::Int(n) => n,
                    PreflightValue::Bool(b) => i64::from(b),
                    other => {
                        return Err(JitError::TypeMismatch {
                            expected: "integer or boolean (EXCEPT function value)".to_string(),
                            actual: other.ty_name().to_string(),
                        })
                    }
                };
                // Update existing key or append
                let mut found = false;
                for (k, v) in pairs.iter_mut() {
                    if *k == key_i64 {
                        *v = new_val_i64;
                        found = true;
                        break;
                    }
                }
                if !found {
                    // TLA+ EXCEPT on a missing key extends the function
                    pairs.push((key_i64, new_val_i64));
                }
            }
            // [r EXCEPT !.field = val] — record field update
            (PreflightValue::Record(ref mut pairs), ExceptPathElement::Field(field_name)) => {
                let target = &field_name.name.node;
                let new_val = preflight_const_value(&spec.value.node)?;
                let new_val_i64 = match new_val {
                    PreflightValue::Int(n) => n,
                    PreflightValue::Bool(b) => i64::from(b),
                    other => {
                        return Err(JitError::TypeMismatch {
                            expected: "integer or boolean (EXCEPT record value)".to_string(),
                            actual: other.ty_name().to_string(),
                        })
                    }
                };
                let mut found = false;
                for (k, v) in pairs.iter_mut() {
                    if k == target {
                        *v = new_val_i64;
                        found = true;
                        break;
                    }
                }
                if !found {
                    pairs.push((target.clone(), new_val_i64));
                }
            }
            // RecordFunction with index path — [rf EXCEPT ![key] = record_val]
            (PreflightValue::RecordFunction(ref mut pairs), ExceptPathElement::Index(idx_expr)) => {
                let key = preflight_const_value(&idx_expr.node)?;
                let key_i64 = match key {
                    PreflightValue::Int(n) => n,
                    other => {
                        return Err(JitError::TypeMismatch {
                            expected: "integer (EXCEPT record-function key)".to_string(),
                            actual: other.ty_name().to_string(),
                        })
                    }
                };
                let new_val = preflight_const_value(&spec.value.node)?;
                match new_val {
                    PreflightValue::Record(fields) => {
                        let mut found = false;
                        for (k, v) in pairs.iter_mut() {
                            if *k == key_i64 {
                                *v = fields.clone();
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            pairs.push((key_i64, fields));
                        }
                    }
                    other => {
                        return Err(JitError::TypeMismatch {
                            expected: "record (EXCEPT record-function value)".to_string(),
                            actual: other.ty_name().to_string(),
                        })
                    }
                }
            }
            // Type mismatches
            (PreflightValue::Function(_), ExceptPathElement::Field(_)) => {
                return Err(JitError::TypeMismatch {
                    expected: "index path (![key]) for function EXCEPT".to_string(),
                    actual: "field path (.field)".to_string(),
                })
            }
            (PreflightValue::Record(_), ExceptPathElement::Index(_)) => {
                return Err(JitError::TypeMismatch {
                    expected: "field path (.field) for record EXCEPT".to_string(),
                    actual: "index path (![key])".to_string(),
                })
            }
            (other, _) => {
                return Err(JitError::TypeMismatch {
                    expected: "function or record".to_string(),
                    actual: other.ty_name().to_string(),
                })
            }
        }
    }
    Ok(base_val)
}

/// Preflight evaluate a quantifier (\A or \E) over a finite domain.
///
/// For `is_forall=true` (universal): all body evaluations must be true.
/// For `is_forall=false` (existential): at least one body evaluation must be true.
///
/// Currently supports only single-variable quantifiers with a domain that
/// evaluates to a finite integer set. Multi-variable quantifiers and
/// unbounded quantifiers are rejected.
fn preflight_quantifier(
    bounds: &[tla_core::ast::BoundVar],
    body: &tla_core::span::Spanned<Expr>,
    is_forall: bool,
) -> Result<PreflightValue, JitError> {
    use tla_core::ast::BoundVar;

    // Only support single-variable quantifiers for now
    if bounds.len() != 1 {
        return Err(JitError::UnsupportedExpr(
            "multi-variable quantifier not yet supported in JIT".to_string(),
        ));
    }

    let BoundVar {
        domain, pattern, ..
    } = &bounds[0];

    // Pattern destructuring not supported
    if pattern.is_some() {
        return Err(JitError::UnsupportedExpr(
            "pattern destructuring in quantifier not supported in JIT".to_string(),
        ));
    }

    // Domain must be present
    let domain_expr = domain.as_ref().ok_or_else(|| {
        JitError::UnsupportedExpr(
            "unbounded quantifier not supported in JIT (no domain)".to_string(),
        )
    })?;

    // Evaluate the domain to get the set of values
    let domain_val = preflight_const_value(&domain_expr.node)?;
    let set = expect_set(domain_val)?;

    // For the preflight, we don't substitute — the body must also be constant.
    // This is only correct when the body doesn't reference the bound variable,
    // which is unusual but valid. The real evaluation happens in compile_expr_inner.
    //
    // For now, just validate that the domain is a finite set and the body is
    // evaluable. Return the quantifier result based on the body being constant.
    // If the body references the bound variable, it will fail with "Ident not supported".
    //
    // This is a conservative approach: we verify the domain is finite and small,
    // then defer actual evaluation to the Cranelift lowerer which does proper
    // substitution-free expansion.

    // Validate each element is in i64 range (already guaranteed by expect_set)
    // and the set is reasonably sized
    if set.len() > 1024 {
        return Err(JitError::CompileError(
            "quantifier domain too large for JIT expansion (>1024 elements)".to_string(),
        ));
    }

    // Try to evaluate body as constant (works when body doesn't use bound var)
    match preflight_const_value(&body.node) {
        Ok(body_val) => {
            let body_bool = match body_val {
                PreflightValue::Bool(b) => b,
                other => {
                    return Err(JitError::TypeMismatch {
                        expected: "boolean".to_string(),
                        actual: other.ty_name().to_string(),
                    })
                }
            };
            if is_forall {
                // \A x \in S : TRUE = TRUE (for non-empty S), \A x \in {} : P = TRUE
                Ok(PreflightValue::Bool(body_bool || set.is_empty()))
            } else {
                // \E x \in S : TRUE = TRUE (for non-empty S), \E x \in {} : P = FALSE
                Ok(PreflightValue::Bool(body_bool && !set.is_empty()))
            }
        }
        Err(_) => {
            // Body is not constant (it references the bound variable).
            // Use substitution-based evaluation: substitute each domain element
            // for the bound variable and evaluate the predicate.
            let var_name = &bounds[0].name.node;
            super::preflight_funcdef::preflight_quantifier_with_subst(
                var_name, &set, body, is_forall,
            )
        }
    }
}
