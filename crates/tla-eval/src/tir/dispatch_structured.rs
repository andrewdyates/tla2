// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TIR dispatch helpers for structured values and diagnostics.

use super::dispatch::eval_tir;
use crate::core::EvalCtx;
use crate::eval_constructors::union_values;
use tla_core::Spanned;
use tla_tir::nodes::{TirExpr, TirSetOp};
use tla_value::error::{EvalError, EvalResult};
use tla_value::{range_set, RecordBuilder, SetBuilder, SetCapValue, SetDiffValue, Value};

pub(super) fn eval_tir_record(
    ctx: &EvalCtx,
    fields: &[(tla_tir::nodes::TirFieldName, Spanned<TirExpr>)],
) -> EvalResult<Value> {
    let mut builder = RecordBuilder::with_capacity(fields.len());
    for (field, value_expr) in fields {
        builder.insert(field.field_id, eval_tir(ctx, value_expr)?);
    }
    Ok(Value::Record(builder.build()))
}

pub(super) fn eval_tir_record_access(
    ctx: &EvalCtx,
    record: &Spanned<TirExpr>,
    field: &tla_tir::nodes::TirFieldName,
    span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let record_value = eval_tir(ctx, record)?;
    let rec = record_value
        .as_record()
        .ok_or_else(|| EvalError::type_error("Record", &record_value, Some(record.span)))?;
    rec.get_by_id(field.field_id)
        .cloned()
        .ok_or_else(|| EvalError::NoSuchField {
            field: field.name.clone(),
            record_display: Some(format!("{record_value}")),
            span,
        })
}

pub(super) fn eval_tir_set_enum(ctx: &EvalCtx, elems: &[Spanned<TirExpr>]) -> EvalResult<Value> {
    let mut builder = SetBuilder::new();
    for elem in elems {
        builder.insert(eval_tir(ctx, elem)?);
    }
    Ok(builder.build_value())
}

pub(super) fn eval_tir_set_bin(
    ctx: &EvalCtx,
    left: &Spanned<TirExpr>,
    op: TirSetOp,
    right: &Spanned<TirExpr>,
    _span: Option<tla_core::Span>,
) -> EvalResult<Value> {
    let left_value = eval_tir(ctx, left)?;
    let right_value = eval_tir(ctx, right)?;
    match op {
        TirSetOp::Union => union_values(left_value, right_value, Some(left.span), Some(right.span)),
        TirSetOp::Intersect => {
            if !left_value.is_set() {
                return Err(EvalError::type_error("Set", &left_value, Some(left.span)));
            }
            if !right_value.is_set() {
                return Err(EvalError::type_error("Set", &right_value, Some(right.span)));
            }
            match (left_value.to_sorted_set(), right_value.to_sorted_set()) {
                (Some(sa), Some(sb)) => Ok(Value::from_sorted_set(sa.intersection(&sb))),
                _ => Ok(Value::SetCap(SetCapValue::new(left_value, right_value))),
            }
        }
        TirSetOp::Minus => {
            if !left_value.is_set() {
                return Err(EvalError::type_error("Set", &left_value, Some(left.span)));
            }
            if !right_value.is_set() {
                return Err(EvalError::type_error("Set", &right_value, Some(right.span)));
            }
            match (left_value.to_sorted_set(), right_value.to_sorted_set()) {
                (Some(sa), Some(sb)) => Ok(Value::from_sorted_set(sa.difference(&sb))),
                _ => Ok(Value::SetDiff(SetDiffValue::new(left_value, right_value))),
            }
        }
    }
}

pub(super) fn eval_tir_range(
    ctx: &EvalCtx,
    lo: &Spanned<TirExpr>,
    hi: &Spanned<TirExpr>,
) -> EvalResult<Value> {
    let lo_value = eval_tir(ctx, lo)?;
    let hi_value = eval_tir(ctx, hi)?;
    let lo_big = lo_value
        .to_bigint()
        .ok_or_else(|| EvalError::type_error("Int", &lo_value, Some(lo.span)))?;
    let hi_big = hi_value
        .to_bigint()
        .ok_or_else(|| EvalError::type_error("Int", &hi_value, Some(hi.span)))?;
    Ok(range_set(&lo_big, &hi_big))
}

pub(super) fn eval_tir_tuple(ctx: &EvalCtx, elems: &[Spanned<TirExpr>]) -> EvalResult<Value> {
    let mut values = Vec::with_capacity(elems.len());
    for elem in elems {
        values.push(eval_tir(ctx, elem)?);
    }
    Ok(Value::Tuple(values.into()))
}

pub(super) fn eval_tir_times(ctx: &EvalCtx, factors: &[Spanned<TirExpr>]) -> EvalResult<Value> {
    let mut components = Vec::with_capacity(factors.len());
    for factor in factors {
        let factor_value = eval_tir(ctx, factor)?;
        if !factor_value.is_set() {
            return Err(EvalError::type_error(
                "Set",
                &factor_value,
                Some(factor.span),
            ));
        }
        components.push(factor_value);
    }
    Ok(Value::tuple_set(components))
}

pub(crate) fn tir_expr_kind(expr: &TirExpr) -> &'static str {
    match expr {
        TirExpr::Const { .. } => "Const",
        TirExpr::Name(_) => "Name",
        TirExpr::OperatorRef(_) => "OperatorRef",
        TirExpr::ArithBinOp { .. } => "ArithBinOp",
        TirExpr::ArithNeg(_) => "ArithNeg",
        TirExpr::BoolBinOp { .. } => "BoolBinOp",
        TirExpr::BoolNot(_) => "BoolNot",
        TirExpr::Cmp { .. } => "Cmp",
        TirExpr::In { .. } => "In",
        TirExpr::Subseteq { .. } => "Subseteq",
        TirExpr::Unchanged(_) => "Unchanged",
        TirExpr::ActionSubscript { .. } => "ActionSubscript",
        TirExpr::Always(_) => "Always",
        TirExpr::Eventually(_) => "Eventually",
        TirExpr::RecordAccess { .. } => "RecordAccess",
        TirExpr::Except { .. } => "Except",
        TirExpr::ExceptAt => "ExceptAt",
        TirExpr::Range { .. } => "Range",
        TirExpr::If { .. } => "If",
        TirExpr::Forall { .. } => "Forall",
        TirExpr::Exists { .. } => "Exists",
        TirExpr::Choose { .. } => "Choose",
        TirExpr::SetEnum(_) => "SetEnum",
        TirExpr::SetFilter { .. } => "SetFilter",
        TirExpr::SetBuilder { .. } => "SetBuilder",
        TirExpr::SetBinOp { .. } => "SetBinOp",
        TirExpr::Powerset(_) => "Powerset",
        TirExpr::BigUnion(_) => "BigUnion",
        TirExpr::KSubset { .. } => "KSubset",
        TirExpr::FuncDef { .. } => "FuncDef",
        TirExpr::FuncApply { .. } => "FuncApply",
        TirExpr::FuncSet { .. } => "FuncSet",
        TirExpr::Domain(_) => "Domain",
        TirExpr::Record(_) => "Record",
        TirExpr::RecordSet(_) => "RecordSet",
        TirExpr::Tuple(_) => "Tuple",
        TirExpr::Times(_) => "Times",
        TirExpr::Let { .. } => "Let",
        TirExpr::Case { .. } => "Case",
        TirExpr::Prime(_) => "Prime",
        TirExpr::Apply { .. } => "Apply",
        TirExpr::Lambda { .. } => "Lambda",
        TirExpr::OpRef(_) => "OpRef",
        TirExpr::Label { .. } => "Label",
        TirExpr::LeadsTo { .. } => "LeadsTo",
        TirExpr::WeakFair { .. } => "WeakFair",
        TirExpr::StrongFair { .. } => "StrongFair",
        TirExpr::Enabled(_) => "Enabled",
    }
}
