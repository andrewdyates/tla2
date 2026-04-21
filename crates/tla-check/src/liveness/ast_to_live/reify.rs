// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::value::IntIntervalFunc;
use crate::Value;
use num_bigint::BigInt;
use tla_core::ast::Expr;
use tla_core::name_intern::NameId;
use tla_core::Spanned;

/// Error returned when a `Value` cannot be reified as an AST `Expr`.
#[derive(Debug, Clone)]
pub(super) enum ReifyError {
    /// The Value variant is not representable as a pure AST expression.
    UnsupportedValue(&'static str),
}

impl std::fmt::Display for ReifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReifyError::UnsupportedValue(variant) => {
                write!(f, "liveness substitution cannot reify {} as Expr", variant)
            }
        }
    }
}

impl std::error::Error for ReifyError {}

pub(super) fn value_variant_name(value: &Value) -> &'static str {
    match value {
        Value::Bool(_) => "Bool",
        Value::SmallInt(_) => "SmallInt",
        Value::Int(_) => "Int",
        Value::String(_) => "String",
        Value::Set(_) => "Set",
        Value::Interval(_) => "Interval",
        Value::Subset(_) => "Subset",
        Value::FuncSet(_) => "FuncSet",
        Value::RecordSet(_) => "RecordSet",
        Value::TupleSet(_) => "TupleSet",
        Value::SetCup(_) => "SetCup",
        Value::SetCap(_) => "SetCap",
        Value::SetDiff(_) => "SetDiff",
        Value::SetPred(_) => "SetPred",
        Value::KSubset(_) => "KSubset",
        Value::BigUnion(_) => "BigUnion",
        Value::Func(_) => "Func",
        Value::IntFunc(_) => "IntFunc",
        Value::LazyFunc(_) => "LazyFunc",
        Value::Seq(_) => "Seq",
        Value::Record(_) => "Record",
        Value::Tuple(_) => "Tuple",
        Value::ModelValue(_) => "ModelValue",
        Value::Closure(_) => "Closure",
        Value::StringSet => "StringSet",
        Value::AnySet => "AnySet",
        Value::SeqSet(_) => "SeqSet",
        _ => "Unknown",
    }
}

pub(super) fn value_is_reifiable_for_substitution(value: &Value) -> bool {
    match value {
        Value::Bool(_)
        | Value::SmallInt(_)
        | Value::Int(_)
        | Value::String(_)
        | Value::ModelValue(_)
        | Value::Interval(_) => true,
        Value::Tuple(elems) => elems.iter().all(value_is_reifiable_for_substitution),
        Value::Seq(elems) => elems.iter().all(value_is_reifiable_for_substitution),
        Value::Set(set) => set.iter().all(value_is_reifiable_for_substitution),
        Value::Record(fields) => fields
            .iter()
            .all(|(_, v)| value_is_reifiable_for_substitution(v)),
        Value::Func(func) => func.mapping_iter().all(|(k, v)| {
            value_is_reifiable_for_substitution(k) && value_is_reifiable_for_substitution(v)
        }),
        Value::Subset(subset) => value_is_reifiable_for_substitution(subset.base()),
        Value::FuncSet(fs) => {
            value_is_reifiable_for_substitution(fs.domain())
                && value_is_reifiable_for_substitution(fs.codomain())
        }
        Value::RecordSet(rs) => rs
            .fields_iter()
            .all(|(_, v)| value_is_reifiable_for_substitution(v)),
        Value::TupleSet(ts) => ts
            .components_iter()
            .all(value_is_reifiable_for_substitution),
        Value::SetCup(sc) => {
            value_is_reifiable_for_substitution(sc.set1())
                && value_is_reifiable_for_substitution(sc.set2())
        }
        Value::SetCap(sc) => {
            value_is_reifiable_for_substitution(sc.set1())
                && value_is_reifiable_for_substitution(sc.set2())
        }
        Value::SetDiff(sd) => {
            value_is_reifiable_for_substitution(sd.set1())
                && value_is_reifiable_for_substitution(sd.set2())
        }
        Value::BigUnion(u) => value_is_reifiable_for_substitution(u.set()),
        Value::IntFunc(f) => f.values().iter().all(value_is_reifiable_for_substitution),
        _ => false,
    }
}

pub(super) fn value_to_expr(value: &Value) -> Result<Expr, ReifyError> {
    match value {
        Value::Bool(b) => Ok(Expr::Bool(*b)),
        Value::SmallInt(n) => Ok(Expr::Int(BigInt::from(*n))),
        Value::Int(n) => Ok(Expr::Int((**n).clone())),
        Value::String(s) => Ok(Expr::String(s.to_string())),
        Value::ModelValue(name) => {
            // Model values are represented as identifiers
            Ok(Expr::Ident(name.to_string(), NameId::INVALID))
        }
        Value::Interval(iv) => Ok(Expr::Range(
            Box::new(Spanned::dummy(Expr::Int(iv.low().clone()))),
            Box::new(Spanned::dummy(Expr::Int(iv.high().clone()))),
        )),
        Value::Subset(subset) => Ok(Expr::Powerset(Box::new(Spanned::dummy(value_to_expr(
            subset.base(),
        )?)))),
        Value::FuncSet(fs) => Ok(Expr::FuncSet(
            Box::new(Spanned::dummy(value_to_expr(fs.domain())?)),
            Box::new(Spanned::dummy(value_to_expr(fs.codomain())?)),
        )),
        Value::RecordSet(rs) => {
            let field_exprs: Result<Vec<_>, _> = rs
                .fields_iter()
                .map(|(k, v)| {
                    Ok((
                        Spanned::dummy(k.as_ref().to_string()),
                        Spanned::dummy(value_to_expr(v)?),
                    ))
                })
                .collect();
            Ok(Expr::RecordSet(field_exprs?))
        }
        Value::TupleSet(ts) => {
            let component_exprs: Result<Vec<_>, _> = ts
                .components_iter()
                .map(|c| Ok(Spanned::dummy(value_to_expr(c)?)))
                .collect();
            Ok(Expr::Times(component_exprs?))
        }
        Value::SetCup(sc) => Ok(Expr::Union(
            Box::new(Spanned::dummy(value_to_expr(sc.set1())?)),
            Box::new(Spanned::dummy(value_to_expr(sc.set2())?)),
        )),
        Value::SetCap(sc) => Ok(Expr::Intersect(
            Box::new(Spanned::dummy(value_to_expr(sc.set1())?)),
            Box::new(Spanned::dummy(value_to_expr(sc.set2())?)),
        )),
        Value::SetDiff(sd) => Ok(Expr::SetMinus(
            Box::new(Spanned::dummy(value_to_expr(sd.set1())?)),
            Box::new(Spanned::dummy(value_to_expr(sd.set2())?)),
        )),
        Value::BigUnion(u) => Ok(Expr::BigUnion(Box::new(Spanned::dummy(value_to_expr(
            u.set(),
        )?)))),
        Value::Tuple(elems) => {
            let exprs: Result<Vec<_>, _> = elems
                .iter()
                .map(|e| Ok(Spanned::dummy(value_to_expr(e)?)))
                .collect();
            Ok(Expr::Tuple(exprs?))
        }
        Value::Set(set) => {
            let exprs: Result<Vec<_>, _> = set
                .iter()
                .map(|e| Ok(Spanned::dummy(value_to_expr(e)?)))
                .collect();
            Ok(Expr::SetEnum(exprs?))
        }
        Value::Seq(elems) => {
            // Sequences are tuples in TLA+
            let exprs: Result<Vec<_>, _> = elems
                .iter()
                .map(|e| Ok(Spanned::dummy(value_to_expr(e)?)))
                .collect();
            Ok(Expr::Tuple(exprs?))
        }
        Value::Record(fields) => {
            let field_exprs: Result<Vec<_>, _> = fields
                .iter_str()
                .map(|(k, v)| {
                    Ok((
                        Spanned::dummy(k.to_string()),
                        Spanned::dummy(value_to_expr(v)?),
                    ))
                })
                .collect();
            Ok(Expr::Record(field_exprs?))
        }
        Value::Func(func) => {
            // Convert a finite function value to a chain of :> and @@ operators.
            // For {a |-> va, b |-> vb}: (a :> va) @@ (b :> vb)
            //
            // This evaluates back to Value::Func, unlike SetEnum of pairs.
            if func.domain_is_empty() {
                // Empty function: [x \\in {} |-> x]
                Ok(Expr::FuncDef(
                    vec![tla_core::ast::BoundVar {
                        name: Spanned::dummy("_".to_string()),
                        pattern: None,
                        domain: Some(Box::new(Spanned::dummy(Expr::SetEnum(vec![])))),
                    }],
                    Box::new(Spanned::dummy(Expr::Ident(
                        "_".to_string(),
                        NameId::INVALID,
                    ))),
                ))
            } else {
                let mapped: Result<Vec<_>, _> = func
                    .mapping_iter()
                    .map(|(k, v)| {
                        Ok(Expr::Apply(
                            Box::new(Spanned::dummy(Expr::Ident(
                                ":>".to_string(),
                                NameId::INVALID,
                            ))),
                            vec![
                                Spanned::dummy(value_to_expr(k)?),
                                Spanned::dummy(value_to_expr(v)?),
                            ],
                        ))
                    })
                    .collect();
                Ok(mapped?
                    .into_iter()
                    .reduce(|acc, single| {
                        Expr::Apply(
                            Box::new(Spanned::dummy(Expr::Ident(
                                "@@".to_string(),
                                NameId::INVALID,
                            ))),
                            vec![Spanned::dummy(acc), Spanned::dummy(single)],
                        )
                    })
                    // SAFETY: entries.is_empty() returned false above
                    .unwrap_or_else(|| unreachable!("guarded by is_empty check")))
            }
        }
        Value::IntFunc(f) => {
            if f.values().is_empty() {
                Ok(Expr::FuncDef(
                    vec![tla_core::ast::BoundVar {
                        name: Spanned::dummy("_".to_string()),
                        pattern: None,
                        domain: Some(Box::new(Spanned::dummy(Expr::SetEnum(vec![])))),
                    }],
                    Box::new(Spanned::dummy(Expr::Ident(
                        "_".to_string(),
                        NameId::INVALID,
                    ))),
                ))
            } else {
                let mapped: Result<Vec<_>, _> = f
                    .values()
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let k = Value::SmallInt(IntIntervalFunc::min(f) + i as i64);
                        Ok(Expr::Apply(
                            Box::new(Spanned::dummy(Expr::Ident(
                                ":>".to_string(),
                                NameId::INVALID,
                            ))),
                            vec![
                                Spanned::dummy(value_to_expr(&k)?),
                                Spanned::dummy(value_to_expr(v)?),
                            ],
                        ))
                    })
                    .collect();
                Ok(mapped?
                    .into_iter()
                    .reduce(|acc, single| {
                        Expr::Apply(
                            Box::new(Spanned::dummy(Expr::Ident(
                                "@@".to_string(),
                                NameId::INVALID,
                            ))),
                            vec![Spanned::dummy(acc), Spanned::dummy(single)],
                        )
                    })
                    // SAFETY: f.values().is_empty() returned false above
                    .unwrap_or_else(|| unreachable!("guarded by is_empty check")))
            }
        }
        other => Err(ReifyError::UnsupportedValue(value_variant_name(other))),
    }
}
