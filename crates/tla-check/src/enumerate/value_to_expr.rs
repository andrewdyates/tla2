// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conversion from Value to Expr AST nodes.
//!
//! Extracted from enumerate.rs as part of #637 parent file decomposition.

use num_bigint::BigInt;

use crate::value::IntIntervalFunc;
use crate::Value;
use tla_core::ast::Expr;
use tla_core::name_intern::NameId;
use tla_core::Spanned;

/// Try to convert a Value back to an Expr for embedding in expressions.
///
/// Returns `None` for truly non-reifiable values (Closure, SetPred, LazyFunc,
/// StringSet, AnySet, SeqSet, KSubset) that should not be substituted back
/// into AST form.
pub(crate) fn try_value_to_expr(value: &Value) -> Option<Expr> {
    match value {
        Value::Bool(b) => Some(Expr::Bool(*b)),
        Value::SmallInt(n) => Some(Expr::Int(BigInt::from(*n))),
        Value::Int(n) => Some(Expr::Int((**n).clone())),
        Value::String(s) => Some(Expr::String(s.to_string())),
        Value::ModelValue(name) => Some(Expr::Ident(name.to_string(), NameId::INVALID)),
        Value::Tuple(elems) => Some(Expr::Tuple(
            elems
                .iter()
                .map(|e| Some(Spanned::dummy(try_value_to_expr(e)?)))
                .collect::<Option<Vec<_>>>()?,
        )),
        Value::Set(set) => Some(Expr::SetEnum(
            set.iter()
                .map(|e| Some(Spanned::dummy(try_value_to_expr(e)?)))
                .collect::<Option<Vec<_>>>()?,
        )),
        Value::Seq(elems) => Some(Expr::Tuple(
            elems
                .iter()
                .map(|e| Some(Spanned::dummy(try_value_to_expr(e)?)))
                .collect::<Option<Vec<_>>>()?,
        )),
        Value::Record(fields) => Some(Expr::Record(
            fields
                .iter_str()
                .map(|(k, v)| {
                    Some((
                        Spanned::dummy(k.to_string()),
                        Spanned::dummy(try_value_to_expr(v)?),
                    ))
                })
                .collect::<Option<Vec<_>>>()?,
        )),
        Value::Interval(iv) => Some(Expr::Range(
            Box::new(Spanned::dummy(Expr::Int(iv.low().clone()))),
            Box::new(Spanned::dummy(Expr::Int(iv.high().clone()))),
        )),
        Value::Func(func) => Some(func_to_expr(func.mapping_iter(), func.domain_is_empty())),
        Value::IntFunc(f) => {
            let iter = f.values().iter().enumerate().map(|(i, v)| {
                let k = Value::SmallInt(IntIntervalFunc::min(f) + i as i64);
                (k, v.clone())
            });
            Some(func_to_expr(
                iter.collect::<Vec<_>>().iter().map(|(k, v)| (k, v)),
                f.values().is_empty(),
            ))
        }
        Value::Subset(subset) => Some(Expr::Powerset(Box::new(Spanned::dummy(try_value_to_expr(
            subset.base(),
        )?)))),
        Value::FuncSet(fs) => Some(Expr::FuncSet(
            Box::new(Spanned::dummy(try_value_to_expr(fs.domain())?)),
            Box::new(Spanned::dummy(try_value_to_expr(fs.codomain())?)),
        )),
        Value::RecordSet(rs) => Some(Expr::RecordSet(
            rs.fields_iter()
                .map(|(k, v)| {
                    Some((
                        Spanned::dummy(k.as_ref().to_string()),
                        Spanned::dummy(try_value_to_expr(v)?),
                    ))
                })
                .collect::<Option<Vec<_>>>()?,
        )),
        Value::TupleSet(ts) => Some(Expr::Times(
            ts.components_iter()
                .map(|c| Some(Spanned::dummy(try_value_to_expr(c)?)))
                .collect::<Option<Vec<_>>>()?,
        )),
        Value::SetCup(sc) => Some(Expr::Union(
            Box::new(Spanned::dummy(try_value_to_expr(sc.set1())?)),
            Box::new(Spanned::dummy(try_value_to_expr(sc.set2())?)),
        )),
        Value::SetCap(sc) => Some(Expr::Intersect(
            Box::new(Spanned::dummy(try_value_to_expr(sc.set1())?)),
            Box::new(Spanned::dummy(try_value_to_expr(sc.set2())?)),
        )),
        Value::SetDiff(sd) => Some(Expr::SetMinus(
            Box::new(Spanned::dummy(try_value_to_expr(sd.set1())?)),
            Box::new(Spanned::dummy(try_value_to_expr(sd.set2())?)),
        )),
        Value::BigUnion(u) => Some(Expr::BigUnion(Box::new(Spanned::dummy(try_value_to_expr(
            u.set(),
        )?)))),
        _ => None,
    }
}

/// Convert a Value back to an Expr for embedding in expressions
///
/// This is used when we've evaluated values and need to create expressions from them,
/// e.g., when converting existential assignments to InSet expressions.
///
/// Part of #251: Made pub(crate) for z4_enumerate constant pre-evaluation.
///
/// # Panics
/// Panics on truly non-reifiable values (Closure, SetPred, LazyFunc, StringSet,
/// AnySet, SeqSet, KSubset) that should never appear in enumeration contexts.
pub(crate) fn value_to_expr(value: &Value) -> Expr {
    try_value_to_expr(value).unwrap_or_else(|| {
        panic!(
            "value_to_expr: cannot convert value to Expr — \
             this value type should not appear in enumeration contexts: {:?}",
            std::mem::discriminant(value),
        )
    })
}

/// Build a function expression as a chain of `:>` and `@@` operators.
/// Shared by `Func` and `IntFunc` arms.
fn func_to_expr<'a>(entries: impl Iterator<Item = (&'a Value, &'a Value)>, is_empty: bool) -> Expr {
    if is_empty {
        Expr::FuncDef(
            vec![tla_core::ast::BoundVar {
                name: Spanned::dummy("_".to_string()),
                pattern: None,
                domain: Some(Box::new(Spanned::dummy(Expr::SetEnum(vec![])))),
            }],
            Box::new(Spanned::dummy(Expr::Ident(
                "_".to_string(),
                NameId::INVALID,
            ))),
        )
    } else {
        let mut result: Option<Expr> = None;
        for (k, v) in entries {
            let single = Expr::Apply(
                Box::new(Spanned::dummy(Expr::Ident(
                    ":>".to_string(),
                    NameId::INVALID,
                ))),
                vec![
                    Spanned::dummy(value_to_expr(k)),
                    Spanned::dummy(value_to_expr(v)),
                ],
            );
            result = Some(match result {
                None => single,
                Some(acc) => Expr::Apply(
                    Box::new(Spanned::dummy(Expr::Ident(
                        "@@".to_string(),
                        NameId::INVALID,
                    ))),
                    vec![Spanned::dummy(acc), Spanned::dummy(single)],
                ),
            });
        }
        result.expect("entries non-empty when is_empty is false")
    }
}
