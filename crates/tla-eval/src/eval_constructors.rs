// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Set, record, tuple, function set construction, literals, and DOMAIN.
//!
//! Part of #3214: Split from eval_expr_helpers.rs.

use super::core::EvalCtx;
use super::{eval, try_borrow_materialized_read, EvalError, EvalResult};
use crate::value::{
    intern_string, range_set, ComponentDomain, FuncSetValue, LazyDomain, RecordBuilder, SetBuilder,
    SetCupValue, SortedSet, SubsetValue, Value,
};
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};
use smallvec::SmallVec;
use std::sync::Arc;
use tla_core::{Span, Spanned};

/// Evaluate a lambda expression by creating a closure that captures the current environment.
/// Fixes #174: Must capture local_stack bindings AND local_ops.
pub(super) fn eval_lambda(
    ctx: &EvalCtx,
    params: &[Spanned<String>],
    body: &Spanned<tla_core::ast::Expr>,
) -> EvalResult<Value> {
    let param_names: Vec<String> = params.iter().map(|p| p.node.clone()).collect();
    // Part of #2895: Use create_closure for O(1) chain capture.
    let closure = ctx.create_closure(param_names, (*body).clone(), ctx.local_ops.clone());
    Ok(Value::Closure(Arc::new(closure)))
}

/// Evaluate set union, trying eager evaluation if both operands are enumerable.
pub(super) fn eval_union(
    ctx: &EvalCtx,
    a: &Spanned<tla_core::ast::Expr>,
    b: &Spanned<tla_core::ast::Expr>,
) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    let bv = eval(ctx, b)?;
    union_values(av, bv, Some(a.span), Some(b.span))
}

pub(crate) fn union_values(
    av: Value,
    bv: Value,
    left_span: Option<Span>,
    right_span: Option<Span>,
) -> EvalResult<Value> {
    if !av.is_set() {
        return Err(EvalError::type_error("Set", &av, left_span));
    }
    if !bv.is_set() {
        return Err(EvalError::type_error("Set", &bv, right_span));
    }
    // Part of #3063: `msgs \\cup {msg}` is lowered to Expr::Union, which previously
    // missed the singleton fast path that named `\\cup` dispatch already had.
    // Use SortedSet::insert() for concrete singleton unions to avoid a full merge.
    // #3073: Use as_singleton() to detect singletons without forcing normalization.
    if let (Value::Set(big), Value::Set(singleton)) = (&av, &bv) {
        if let Some(elem) = singleton.as_singleton() {
            return Ok(Value::from_sorted_set(big.insert(elem.clone())));
        }
    }
    if let (Value::Set(singleton), Value::Set(big)) = (&av, &bv) {
        if let Some(elem) = singleton.as_singleton() {
            return Ok(Value::from_sorted_set(big.insert(elem.clone())));
        }
    }
    // Preserve identity for empty-set unions to avoid wrapping finite compound
    // sets in structural SetCup shells (for example {} \cup [a : {1,2}]).
    if av.set_len().is_some_and(|n| n.is_zero()) {
        return Ok(bv);
    }
    if bv.set_len().is_some_and(|n| n.is_zero()) {
        return Ok(av);
    }
    // Part of #3063: only materialize when both operands are already concrete
    // (Set or Interval). Preserve lazy structure for compound sets (RecordSet,
    // FuncSet, TupleSet, etc.) which support O(fields) membership checking.
    // Previously, eval_union eagerly materialized unions of RecordSets into
    // giant SortedSets, causing 24% of runtime in Value::eq during invariant
    // checking (binary search on 530-element materialized set vs O(5) lazy
    // branch checks with field-by-field RecordSet membership).
    let both_concrete = matches!(
        (&av, &bv),
        (
            Value::Set(_) | Value::Interval(_),
            Value::Set(_) | Value::Interval(_)
        )
    );
    if both_concrete {
        if let (Some(sa), Some(sb)) = (av.to_sorted_set(), bv.to_sorted_set()) {
            return Ok(Value::from_sorted_set(sa.union(&sb)));
        }
    }
    Ok(Value::SetCup(SetCupValue::new(av, bv)))
}

/// Evaluate SUBSET (powerset) expression.
pub(super) fn eval_powerset(ctx: &EvalCtx, a: &Spanned<tla_core::ast::Expr>) -> EvalResult<Value> {
    let av = eval(ctx, a)?;
    if !av.is_set() {
        return Err(EvalError::type_error("Set", &av, Some(a.span)));
    }
    Ok(Value::Subset(SubsetValue::new(av)))
}

/// Evaluate set enumeration `{a, b, c}`.
pub(super) fn eval_set_enum(
    ctx: &EvalCtx,
    elems: &[Spanned<tla_core::ast::Expr>],
) -> EvalResult<Value> {
    let mut set = SetBuilder::new();
    for elem in elems {
        set.insert(eval(ctx, elem)?);
    }
    Ok(set.build_value())
}

/// Evaluate a function set `[D -> R]`.
pub(super) fn eval_func_set(
    ctx: &EvalCtx,
    domain: &Spanned<tla_core::ast::Expr>,
    range: &Spanned<tla_core::ast::Expr>,
) -> EvalResult<Value> {
    let dv = eval(ctx, domain)?;
    let rv = eval(ctx, range)?;
    if !dv.is_set() {
        return Err(EvalError::type_error("Set", &dv, Some(domain.span)));
    }
    if !rv.is_set() {
        return Err(EvalError::type_error("Set", &rv, Some(range.span)));
    }
    Ok(Value::FuncSet(FuncSetValue::new(dv, rv)))
}

/// Evaluate a record literal `[a |-> 1, b |-> 2]`.
pub(super) fn eval_record(
    ctx: &EvalCtx,
    fields: &[(Spanned<String>, Spanned<tla_core::ast::Expr>)],
) -> EvalResult<Value> {
    let mut builder = RecordBuilder::with_capacity(fields.len());
    for (name, val_expr) in fields {
        builder.insert(
            tla_core::intern_name(name.node.as_str()),
            eval(ctx, val_expr)?,
        );
    }
    Ok(Value::Record(builder.build()))
}

/// Evaluate record field access `r.field`.
pub(super) fn eval_record_access(
    ctx: &EvalCtx,
    rec_expr: &Spanned<tla_core::ast::Expr>,
    field: &tla_core::ast::RecordFieldName,
    span: Option<Span>,
) -> EvalResult<Value> {
    if let Some(record_value) = try_borrow_materialized_read(ctx, rec_expr) {
        let record_value = record_value?;
        let record = record_value
            .as_record()
            .ok_or_else(|| EvalError::type_error("Record", &record_value, Some(rec_expr.span)))?;
        return record
            .get_by_id(field.field_id)
            .cloned()
            .ok_or_else(|| EvalError::NoSuchField {
                field: field.name.node.clone(),
                record_display: Some(format!("{record_value}")),
                span,
            });
    }

    let rv = eval(ctx, rec_expr)?;
    let rec = rv
        .as_record()
        .ok_or_else(|| EvalError::type_error("Record", &rv, Some(rec_expr.span)))?;
    // Part of #3168: use pre-interned field_id instead of runtime intern_name()
    rec.get_by_id(field.field_id)
        .cloned()
        .ok_or_else(|| EvalError::NoSuchField {
            field: field.name.node.clone(),
            record_display: Some(format!("{rv}")),
            span,
        })
}

/// Evaluate a record set `[a : S1, b : S2]`.
///
/// Part of #3805: SmallVec avoids heap allocation for record sets with <= 4 fields
/// (most TLA+ records have 2-5 fields).
pub(super) fn eval_record_set(
    ctx: &EvalCtx,
    fields: &[(Spanned<String>, Spanned<tla_core::ast::Expr>)],
) -> EvalResult<Value> {
    let mut field_sets: SmallVec<[(Arc<str>, Value); 4]> = SmallVec::with_capacity(fields.len());
    for (name, set_expr) in fields {
        let sv = eval(ctx, set_expr)?;
        if !sv.is_set() {
            return Err(EvalError::type_error("Set", &sv, Some(set_expr.span)));
        }
        field_sets.push((intern_string(name.node.as_str()), sv));
    }
    Ok(Value::record_set(field_sets))
}

/// Evaluate a tuple literal `<<a, b, c>>`.
///
/// Part of #3805: SmallVec avoids heap allocation for tuples with <= 4 elements
/// (the vast majority -- TLA+ tuples are typically 2-3 elements like `<<pc, i>>`).
/// The intermediate Vec alloc is eliminated; only the final Arc<[Value]> allocates.
pub(super) fn eval_tuple(
    ctx: &EvalCtx,
    elems: &[Spanned<tla_core::ast::Expr>],
) -> EvalResult<Value> {
    let mut vals: SmallVec<[Value; 4]> = SmallVec::with_capacity(elems.len());
    for elem in elems {
        vals.push(eval(ctx, elem)?);
    }
    Ok(Value::Tuple(Arc::from(vals.as_slice())))
}

/// Evaluate a Cartesian product `S1 \X S2 \X ...`.
///
/// Part of #3805: SmallVec avoids heap allocation for products with <= 4 factors
/// (most TLA+ Cartesian products have 2-3 factors).
pub(super) fn eval_times(
    ctx: &EvalCtx,
    factors: &[Spanned<tla_core::ast::Expr>],
) -> EvalResult<Value> {
    let mut components: SmallVec<[Value; 4]> = SmallVec::with_capacity(factors.len());
    for factor in factors {
        let fv = eval(ctx, factor)?;
        if !fv.is_set() {
            return Err(EvalError::type_error("Set", &fv, Some(factor.span)));
        }
        components.push(fv);
    }
    Ok(Value::tuple_set(components))
}

/// Evaluate a BigInt literal with span-keyed caching.
/// SmallInt values are returned directly; BigInt values are cached by span
/// to avoid repeated cloning (matching TLC's parse-time literal storage).
pub(super) fn eval_int_literal(n: &BigInt, span: Option<Span>) -> EvalResult<Value> {
    use super::SMALL_CACHES;

    // SmallInt: trivially cheap, no caching needed
    if let Some(small) = n.to_i64() {
        return Ok(Value::SmallInt(small));
    }
    // BigInt: clone is expensive, check cache
    if let Some(sp) = span {
        if sp != Span::dummy() {
            // Part of #3962: Access literal_cache via consolidated SMALL_CACHES.
            return SMALL_CACHES.with(|sc| {
                {
                    let c = sc.borrow();
                    if let Some(v) = c.literal_cache.get(&sp) {
                        return Ok(v.clone());
                    }
                }
                let v = Value::Int(Arc::new(n.clone()));
                sc.borrow_mut().literal_cache.insert(sp, v.clone());
                Ok(v)
            });
        }
    }
    Ok(Value::Int(Arc::new(n.clone())))
}

/// Evaluate a string literal with span-keyed caching and interning.
/// FIX #575: Validates cached value matches expression content after AST substitution.
pub(super) fn eval_string_literal(s: &str, span: Option<Span>) -> EvalResult<Value> {
    use super::SMALL_CACHES;

    if let Some(sp) = span {
        if sp != Span::dummy() {
            // Part of #3962: Access literal_cache via consolidated SMALL_CACHES.
            return SMALL_CACHES.with(|sc| {
                {
                    let c = sc.borrow();
                    if let Some(v) = c.literal_cache.get(&sp) {
                        // Validate cache hit matches the expression
                        if let Value::String(cached_str) = v {
                            if &**cached_str == s {
                                return Ok(v.clone());
                            }
                            // Cache mismatch - fall through to recalculate
                        }
                        // Wrong type cached - fall through to recalculate
                    }
                }
                let v = Value::String(intern_string(s));
                sc.borrow_mut().literal_cache.insert(sp, v.clone());
                Ok(v)
            });
        }
    }
    Ok(Value::String(intern_string(s)))
}

/// Evaluate DOMAIN(f) — returns the domain of a function, sequence, tuple, or record.
pub(super) fn eval_domain(
    ctx: &EvalCtx,
    func_expr: &Spanned<tla_core::ast::Expr>,
    _span: Option<Span>,
) -> EvalResult<Value> {
    let fv = eval(ctx, func_expr)?;
    eval_domain_value(&fv).map_err(|err| match err {
        EvalError::TypeError { .. } => {
            EvalError::type_error("Function/Seq/Tuple/Record", &fv, Some(func_expr.span))
        }
        other => other,
    })
}

pub(crate) fn eval_domain_value(fv: &Value) -> EvalResult<Value> {
    match fv {
        Value::Func(f) => {
            let domain: Vec<Value> = f.domain_iter().cloned().collect();
            Ok(Value::from_sorted_set(SortedSet::from_sorted_vec(domain)))
        }
        Value::IntFunc(f) => {
            // DOMAIN of IntFunc is the integer interval min..max
            Ok(range_set(
                &BigInt::from(tla_value::IntIntervalFunc::min(f)),
                &BigInt::from(tla_value::IntIntervalFunc::max(f)),
            ))
        }
        Value::Seq(s) => {
            // DOMAIN of sequence is 1..Len(s)
            if s.is_empty() {
                Ok(Value::empty_set())
            } else {
                Ok(range_set(&BigInt::one(), &BigInt::from(s.len())))
            }
        }
        Value::Tuple(s) => {
            // DOMAIN of tuple is 1..Len(s)
            if s.is_empty() {
                Ok(Value::empty_set())
            } else {
                Ok(range_set(&BigInt::one(), &BigInt::from(s.len())))
            }
        }
        Value::Record(r) => {
            // DOMAIN of record is set of field names
            let names: SortedSet = r.key_strings().map(Value::String).collect();
            Ok(Value::from_sorted_set(names))
        }
        Value::LazyFunc(f) => {
            // DOMAIN of LazyFunc is the set representation of its domain type
            match f.domain() {
                LazyDomain::Nat => Ok(Value::ModelValue(Arc::from("Nat"))),
                LazyDomain::Int => Ok(Value::ModelValue(Arc::from("Int"))),
                LazyDomain::Real => Ok(Value::ModelValue(Arc::from("Real"))),
                LazyDomain::String => Ok(Value::StringSet),
                LazyDomain::Product(components) => {
                    // For multi-argument functions, domain is a cartesian product
                    let sets: Vec<Value> = components
                        .iter()
                        .map(|c| match c {
                            ComponentDomain::Nat => Value::ModelValue(Arc::from("Nat")),
                            ComponentDomain::Int => Value::ModelValue(Arc::from("Int")),
                            ComponentDomain::Real => Value::ModelValue(Arc::from("Real")),
                            ComponentDomain::String => Value::StringSet,
                            ComponentDomain::Finite(s) => Value::from_sorted_set(s.clone()),
                        })
                        .collect();
                    Ok(Value::tuple_set(sets))
                }
                LazyDomain::General(v) => {
                    // For general domains, return the stored domain value directly
                    Ok(v.as_ref().clone())
                }
            }
        }
        _ => Err(EvalError::type_error("Function/Seq/Tuple/Record", fv, None)),
    }
}

#[cfg(test)]
mod tests {
    use super::union_values;
    use crate::value::Value;
    use std::sync::Arc;

    #[test]
    fn test_union_values_record_set_matches_combined_record_set() {
        let left = Value::record_set([(Arc::from("a"), Value::set([Value::int(1)]))]);
        let right = Value::record_set([(Arc::from("a"), Value::set([Value::int(2)]))]);
        let expected =
            Value::record_set([(Arc::from("a"), Value::set([Value::int(1), Value::int(2)]))]);

        let union = union_values(left, right, None, None).expect("record-set union should succeed");
        assert_eq!(union, expected);
    }

    #[test]
    fn test_union_values_empty_identity_preserves_compound_set_shape() {
        let record_set =
            Value::record_set([(Arc::from("a"), Value::set([Value::int(1), Value::int(2)]))]);

        assert!(matches!(
            union_values(Value::empty_set(), record_set.clone(), None, None)
                .expect("empty union should succeed"),
            Value::RecordSet(_)
        ));
        assert!(matches!(
            union_values(record_set, Value::empty_set(), None, None)
                .expect("empty union should succeed"),
            Value::RecordSet(_)
        ));
    }
}
