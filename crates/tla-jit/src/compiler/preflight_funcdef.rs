// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Preflight evaluation of TLA+ function definitions (`FuncDef`).
//!
//! A TLA+ function definition `[x \in S |-> body(x)]` defines a mapping from
//! each element of `S` to the value of `body` with `x` substituted. This
//! module evaluates such definitions at compile time by iterating the domain
//! and performing inline constant substitution of the bound variable.
//!
//! Limitations:
//! - Single bound variable only (no multi-variable functions).
//! - Domain must be a finite integer set (evaluated via preflight).
//! - Body must reduce to an integer for each domain element after substitution.

use crate::error::JitError;
use num_bigint::BigInt;
use tla_core::ast::{BoundVar, Expr};
use tla_core::span::Spanned;

use super::preflight::{expect_set, preflight_const_value, PreflightValue};

/// Evaluate a FuncDef at compile time, producing a `PreflightValue::Function`.
///
/// For `[x \in S |-> body]`, this:
/// 1. Evaluates `S` to get a finite set of i64 values.
/// 2. For each element `v` in `S`, substitutes `v` for `x` in `body` and
///    evaluates the result.
/// 3. Returns a `Function` containing `(key, value)` pairs.
pub(crate) fn preflight_funcdef(
    bounds: &[BoundVar],
    body: &Spanned<Expr>,
) -> Result<PreflightValue, JitError> {
    // Only support single-variable functions
    if bounds.len() != 1 {
        return Err(JitError::UnsupportedExpr(
            "multi-variable function definition not yet supported in JIT".to_string(),
        ));
    }

    let BoundVar {
        name,
        domain,
        pattern,
    } = &bounds[0];

    // Pattern destructuring not supported
    if pattern.is_some() {
        return Err(JitError::UnsupportedExpr(
            "pattern destructuring in function definition not supported in JIT".to_string(),
        ));
    }

    // Domain must be present
    let domain_expr = domain.as_ref().ok_or_else(|| {
        JitError::UnsupportedExpr(
            "function definition without domain not supported in JIT".to_string(),
        )
    })?;

    // Evaluate the domain to get the set of values
    let domain_val = preflight_const_value(&domain_expr.node)?;
    let set = expect_set(domain_val)?;

    // Cap domain size
    if set.len() > 1024 {
        return Err(JitError::CompileError(
            "function domain too large for JIT expansion (>1024 elements)".to_string(),
        ));
    }

    let var_name = &name.node;

    // Evaluate body for each domain element by substituting the bound variable.
    // First pass: evaluate all bodies to determine the value type (scalar or record).
    let mut body_values = Vec::with_capacity(set.len());
    for &key in &set {
        let substituted_body = substitute_ident(&body.node, var_name, key);
        let val = preflight_const_value(&substituted_body)?;
        body_values.push((key, val));
    }

    // Determine whether this is a scalar-valued or record-valued function.
    // All bodies must have the same type (either all scalar or all record).
    let all_scalar = body_values
        .iter()
        .all(|(_, v)| matches!(v, PreflightValue::Int(_) | PreflightValue::Bool(_)));
    let all_record = body_values
        .iter()
        .all(|(_, v)| matches!(v, PreflightValue::Record(_)));

    if all_scalar {
        let mut pairs = Vec::with_capacity(body_values.len());
        for (key, val) in body_values {
            let val_i64 = match val {
                PreflightValue::Int(n) => n,
                PreflightValue::Bool(b) => i64::from(b),
                _ => unreachable!(),
            };
            pairs.push((key, val_i64));
        }
        Ok(PreflightValue::Function(pairs))
    } else if all_record {
        // Record-valued function: [x \in S |-> [field |-> expr(x)]]
        // Part of #3798: enables f[x].field compilation.
        let mut pairs = Vec::with_capacity(body_values.len());
        for (key, val) in body_values {
            match val {
                PreflightValue::Record(fields) => pairs.push((key, fields)),
                _ => unreachable!(),
            }
        }
        Ok(PreflightValue::RecordFunction(pairs))
    } else if body_values.is_empty() {
        // Empty domain produces an empty scalar function
        Ok(PreflightValue::Function(vec![]))
    } else {
        // Mixed types — not supported
        Err(JitError::TypeMismatch {
            expected: "integer, boolean, or record (uniform)".to_string(),
            actual: "mixed types in function body".to_string(),
        })
    }
}

/// Substitute all occurrences of `Ident(var_name, _)` with `Int(value)` in
/// an expression tree.
///
/// This is a simple structural substitution: it replaces every `Ident` whose
/// name matches `var_name` with the integer literal `value`. It handles
/// shadowing for quantifier and function definition bounds: if a nested
/// binder rebinds the same name, substitution stops in that scope.
pub(crate) fn substitute_ident(expr: &Expr, var_name: &str, value: i64) -> Expr {
    match expr {
        Expr::Ident(name, _) if name == var_name => Expr::Int(BigInt::from(value)),

        // Recursively substitute in subexpressions
        Expr::Add(l, r) => Expr::Add(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::Sub(l, r) => Expr::Sub(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::Mul(l, r) => Expr::Mul(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::Div(l, r) => Expr::Div(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::IntDiv(l, r) => Expr::IntDiv(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::Mod(l, r) => Expr::Mod(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::Pow(l, r) => Expr::Pow(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::Neg(inner) => Expr::Neg(Box::new(subst_spanned(inner, var_name, value))),

        // Comparisons
        Expr::Eq(l, r) => Expr::Eq(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::Neq(l, r) => Expr::Neq(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::Lt(l, r) => Expr::Lt(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::Leq(l, r) => Expr::Leq(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::Gt(l, r) => Expr::Gt(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::Geq(l, r) => Expr::Geq(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),

        // Boolean
        Expr::And(l, r) => Expr::And(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::Or(l, r) => Expr::Or(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::Not(inner) => Expr::Not(Box::new(subst_spanned(inner, var_name, value))),
        Expr::Implies(l, r) => Expr::Implies(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::Equiv(l, r) => Expr::Equiv(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),

        // Control flow
        Expr::If(cond, then_e, else_e) => Expr::If(
            Box::new(subst_spanned(cond, var_name, value)),
            Box::new(subst_spanned(then_e, var_name, value)),
            Box::new(subst_spanned(else_e, var_name, value)),
        ),

        // Set operations
        Expr::In(l, r) => Expr::In(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::NotIn(l, r) => Expr::NotIn(
            Box::new(subst_spanned(l, var_name, value)),
            Box::new(subst_spanned(r, var_name, value)),
        ),
        Expr::SetEnum(elems) => {
            let new_elems: Vec<_> = elems
                .iter()
                .map(|e| subst_spanned(e, var_name, value))
                .collect();
            Expr::SetEnum(new_elems)
        }
        Expr::Range(lo, hi) => Expr::Range(
            Box::new(subst_spanned(lo, var_name, value)),
            Box::new(subst_spanned(hi, var_name, value)),
        ),

        // Function application
        Expr::FuncApply(func, arg) => Expr::FuncApply(
            Box::new(subst_spanned(func, var_name, value)),
            Box::new(subst_spanned(arg, var_name, value)),
        ),

        // Record access (field name is static, substitute the record expr)
        Expr::RecordAccess(rec, field) => {
            Expr::RecordAccess(Box::new(subst_spanned(rec, var_name, value)), field.clone())
        }

        // Record constructor
        Expr::Record(fields) => {
            let new_fields: Vec<_> = fields
                .iter()
                .map(|(name, val)| (name.clone(), subst_spanned(val, var_name, value)))
                .collect();
            Expr::Record(new_fields)
        }

        // FuncDef — substitute in domain, but respect shadowing in body
        Expr::FuncDef(bounds, body) => {
            if bounds.iter().any(|b| b.name.node == var_name) {
                let new_bounds = subst_bounds_until_shadow(bounds, var_name, value);
                Expr::FuncDef(new_bounds, body.clone())
            } else {
                let new_bounds = subst_bounds(bounds, var_name, value);
                Expr::FuncDef(new_bounds, Box::new(subst_spanned(body, var_name, value)))
            }
        }

        // Quantifiers — substitute in domains and bodies, respecting shadowing
        Expr::Forall(bounds, body) => {
            if bounds.iter().any(|b| b.name.node == var_name) {
                let new_bounds = subst_bounds_until_shadow(bounds, var_name, value);
                Expr::Forall(new_bounds, body.clone())
            } else {
                let new_bounds = subst_bounds(bounds, var_name, value);
                Expr::Forall(new_bounds, Box::new(subst_spanned(body, var_name, value)))
            }
        }
        Expr::Exists(bounds, body) => {
            if bounds.iter().any(|b| b.name.node == var_name) {
                let new_bounds = subst_bounds_until_shadow(bounds, var_name, value);
                Expr::Exists(new_bounds, body.clone())
            } else {
                let new_bounds = subst_bounds(bounds, var_name, value);
                Expr::Exists(new_bounds, Box::new(subst_spanned(body, var_name, value)))
            }
        }

        // Domain
        Expr::Domain(inner) => Expr::Domain(Box::new(subst_spanned(inner, var_name, value))),

        // EXCEPT: [f EXCEPT ![a] = b, !.field = v, ...]
        Expr::Except(base, specs) => {
            let new_base = Box::new(subst_spanned(base, var_name, value));
            let new_specs: Vec<_> = specs
                .iter()
                .map(|spec| {
                    use tla_core::ast::{ExceptPathElement, ExceptSpec};
                    let new_path: Vec<_> = spec
                        .path
                        .iter()
                        .map(|elem| match elem {
                            ExceptPathElement::Index(idx) => {
                                ExceptPathElement::Index(subst_spanned(idx, var_name, value))
                            }
                            ExceptPathElement::Field(f) => ExceptPathElement::Field(f.clone()),
                        })
                        .collect();
                    ExceptSpec {
                        path: new_path,
                        value: subst_spanned(&spec.value, var_name, value),
                    }
                })
                .collect();
            Expr::Except(new_base, new_specs)
        }

        // Leaf nodes and non-matching idents — return as-is
        _ => expr.clone(),
    }
}

/// Substitute in a `Spanned<Expr>`, preserving the span.
fn subst_spanned(spanned: &Spanned<Expr>, var_name: &str, value: i64) -> Spanned<Expr> {
    Spanned::new(
        substitute_ident(&spanned.node, var_name, value),
        spanned.span,
    )
}

/// Substitute in bound variable domains (but not the bound names themselves).
fn subst_bounds(bounds: &[BoundVar], var_name: &str, value: i64) -> Vec<BoundVar> {
    bounds
        .iter()
        .map(|b| BoundVar {
            name: b.name.clone(),
            domain: b
                .domain
                .as_ref()
                .map(|d| Box::new(subst_spanned(d, var_name, value))),
            pattern: b.pattern.clone(),
        })
        .collect()
}

/// Substitute in bound variable domains up to (but not past) a bound that
/// shadows `var_name`. Once we hit the shadowing bound, we still substitute
/// in its domain (the domain is evaluated in the outer scope) but not beyond.
fn subst_bounds_until_shadow(bounds: &[BoundVar], var_name: &str, value: i64) -> Vec<BoundVar> {
    let mut result = Vec::with_capacity(bounds.len());
    for (i, b) in bounds.iter().enumerate() {
        let new_domain = b
            .domain
            .as_ref()
            .map(|d| Box::new(subst_spanned(d, var_name, value)));
        result.push(BoundVar {
            name: b.name.clone(),
            domain: new_domain,
            pattern: b.pattern.clone(),
        });
        if b.name.node == var_name {
            // Shadow found: copy remaining bounds unchanged
            for b2 in &bounds[i + 1..] {
                result.push(b2.clone());
            }
            break;
        }
    }
    result
}

/// Evaluate a quantifier body by substituting each domain element for the
/// bound variable and evaluating the predicate.
///
/// This is used by the preflight quantifier evaluator when the body references
/// the bound variable. Returns the quantifier result:
/// - For `\A`: true iff all substituted bodies evaluate to true.
/// - For `\E`: true iff at least one substituted body evaluates to true.
pub(crate) fn preflight_quantifier_with_subst(
    var_name: &str,
    domain_set: &[i64],
    body: &Spanned<Expr>,
    is_forall: bool,
) -> Result<PreflightValue, JitError> {
    if domain_set.is_empty() {
        // \A x \in {} : P = TRUE (vacuously), \E x \in {} : P = FALSE
        return Ok(PreflightValue::Bool(is_forall));
    }

    for &elem in domain_set {
        let substituted = substitute_ident(&body.node, var_name, elem);
        let val = preflight_const_value(&substituted)?;
        let b = match val {
            PreflightValue::Bool(b) => b,
            other => {
                return Err(JitError::TypeMismatch {
                    expected: "boolean".to_string(),
                    actual: other.ty_name().to_string(),
                })
            }
        };

        if is_forall && !b {
            return Ok(PreflightValue::Bool(false));
        }
        if !is_forall && b {
            return Ok(PreflightValue::Bool(true));
        }
    }

    Ok(PreflightValue::Bool(is_forall))
}
