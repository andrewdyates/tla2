// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-cutting CHC helpers shared by builder and translation modules

use std::str::FromStr;

use num_bigint::BigInt;
use tla_core::ast::Expr;
use tla_core::name_intern::NameId;
use tla_core::Spanned;
use z4_chc::{ChcExpr, ChcSort};

use crate::error::{Z4Error, Z4Result};
use crate::TlaSort;

const DOMAIN_KEY_BOOL_PREFIX: &str = "bool:";
const DOMAIN_KEY_INT_PREFIX: &str = "int:";
const DOMAIN_KEY_STRING_PREFIX: &str = "str:";
const DOMAIN_KEY_IDENT_PREFIX: &str = "id:";

/// Convert TlaSort to ChcSort
pub(super) fn tla_sort_to_chc(sort: &TlaSort) -> Z4Result<ChcSort> {
    match sort {
        TlaSort::Bool => Ok(ChcSort::Bool),
        TlaSort::Int => Ok(ChcSort::Int),
        TlaSort::String => Ok(ChcSort::Int),
        TlaSort::Function { .. } => Err(Z4Error::UnsupportedOp(
            "function sorts must be expanded into scalar predicate arguments before CHC lowering"
                .to_string(),
        )),
        TlaSort::Tuple { .. } => Err(Z4Error::UnsupportedOp(
            "tuple sorts must be decomposed before CHC lowering".to_string(),
        )),
        TlaSort::Record { .. } => Err(Z4Error::UnsupportedOp(
            "record sorts must be decomposed before CHC lowering".to_string(),
        )),
        TlaSort::Set { .. } => Err(Z4Error::UnsupportedOp(
            "set sorts must be decomposed before CHC lowering".to_string(),
        )),
        TlaSort::Sequence { .. } => Err(Z4Error::UnsupportedOp(
            "sequence sorts must be decomposed before CHC lowering".to_string(),
        )),
    }
}

/// Build conjunction of expressions, returning true if empty
pub(super) fn and_all(exprs: Vec<ChcExpr>) -> ChcExpr {
    if exprs.is_empty() {
        ChcExpr::Bool(true)
    } else {
        let mut result = exprs.into_iter();
        let first = result.next().expect("checked non-empty above");
        result.fold(first, ChcExpr::and)
    }
}

/// Build disjunction of expressions, returning false if empty
pub(super) fn or_all(exprs: Vec<ChcExpr>) -> ChcExpr {
    if exprs.is_empty() {
        ChcExpr::Bool(false)
    } else {
        let mut result = exprs.into_iter();
        let first = result.next().expect("checked non-empty above");
        result.fold(first, ChcExpr::or)
    }
}

fn encode_domain_key(tag: &str, value: &str) -> String {
    format!("{tag}:{value}")
}

/// Normalize legacy raw domain-key strings to the canonical tagged form used by CHC.
pub(super) fn normalize_domain_key(key: &str) -> String {
    if key.starts_with(DOMAIN_KEY_BOOL_PREFIX)
        || key.starts_with(DOMAIN_KEY_INT_PREFIX)
        || key.starts_with(DOMAIN_KEY_STRING_PREFIX)
        || key.starts_with(DOMAIN_KEY_IDENT_PREFIX)
    {
        return key.to_string();
    }

    if key == "true" || key == "false" {
        return encode_domain_key("bool", key);
    }
    if BigInt::from_str(key).is_ok() {
        return encode_domain_key("int", key);
    }
    encode_domain_key("id", key)
}

/// Convert a domain key into a CHC-variable-safe suffix.
pub(super) fn domain_key_to_var_suffix(key: &str) -> String {
    let mut suffix = String::new();
    for byte in normalize_domain_key(key).bytes() {
        let ch = byte as char;
        if ch.is_ascii_alphanumeric() {
            suffix.push(ch);
        } else {
            suffix.push('_');
            suffix.push_str(&format!("{byte:02x}"));
        }
    }
    suffix
}

/// Convert a scalar AST expression to the canonical finite-domain key form.
pub(super) fn expr_to_domain_key(expr: &Spanned<Expr>) -> Option<String> {
    match &expr.node {
        Expr::Int(n) => Some(encode_domain_key("int", &n.to_string())),
        Expr::Bool(b) => Some(encode_domain_key("bool", &b.to_string())),
        Expr::String(s) => Some(encode_domain_key("str", s)),
        Expr::Ident(name, _) => Some(encode_domain_key("id", name)),
        _ => None,
    }
}

/// Extract finite-domain keys from a TLA+ set expression.
pub(super) fn extract_finite_domain_keys(domain: &Spanned<Expr>) -> Z4Result<Vec<String>> {
    match &domain.node {
        Expr::SetEnum(elements) => elements
            .iter()
            .map(|elem| {
                expr_to_domain_key(elem).ok_or_else(|| {
                    Z4Error::UnsupportedOp(format!(
                        "unsupported finite-domain element: {:?}",
                        elem.node
                    ))
                })
            })
            .collect(),
        Expr::Range(lo, hi) => {
            let lo_val: i64 = match &lo.node {
                Expr::Int(n) => n.try_into().map_err(|_| {
                    Z4Error::IntegerOverflow("range lower bound too large".to_string())
                })?,
                _ => {
                    return Err(Z4Error::UnsupportedOp(
                        "range bounds must be integer literals".to_string(),
                    ))
                }
            };
            let hi_val: i64 = match &hi.node {
                Expr::Int(n) => n.try_into().map_err(|_| {
                    Z4Error::IntegerOverflow("range upper bound too large".to_string())
                })?,
                _ => {
                    return Err(Z4Error::UnsupportedOp(
                        "range bounds must be integer literals".to_string(),
                    ))
                }
            };

            if hi_val < lo_val {
                return Ok(Vec::new());
            }
            if hi_val - lo_val > 1_000 {
                return Err(Z4Error::UnsupportedOp(
                    "finite domain too large for CHC expansion (>1000 elements)".to_string(),
                ));
            }

            Ok((lo_val..=hi_val)
                .map(|i| encode_domain_key("int", &i.to_string()))
                .collect())
        }
        Expr::Ident(name, _) if name == "BOOLEAN" => Ok(vec![
            encode_domain_key("bool", "false"),
            encode_domain_key("bool", "true"),
        ]),
        _ => Err(Z4Error::UnsupportedOp(format!(
            "cannot extract finite domain from {:?}",
            std::mem::discriminant(&domain.node)
        ))),
    }
}

/// Reconstruct a scalar AST expression from a finite-domain key.
pub(super) fn key_to_ast_expr(key: &str) -> Spanned<Expr> {
    if let Some(value) = key.strip_prefix(DOMAIN_KEY_BOOL_PREFIX) {
        return Spanned::dummy(Expr::Bool(value == "true"));
    }
    if let Some(value) = key.strip_prefix(DOMAIN_KEY_INT_PREFIX) {
        if let Ok(n) = BigInt::from_str(value) {
            return Spanned::dummy(Expr::Int(n));
        }
    }
    if let Some(value) = key.strip_prefix(DOMAIN_KEY_STRING_PREFIX) {
        return Spanned::dummy(Expr::String(value.to_string()));
    }
    if let Some(value) = key.strip_prefix(DOMAIN_KEY_IDENT_PREFIX) {
        return Spanned::dummy(Expr::Ident(value.to_string(), NameId::INVALID));
    }

    // Legacy fallback for older raw domain-key strings.
    if key == "true" {
        return Spanned::dummy(Expr::Bool(true));
    }
    if key == "false" {
        return Spanned::dummy(Expr::Bool(false));
    }
    if let Ok(n) = key.parse::<i64>() {
        return Spanned::dummy(Expr::Int(BigInt::from(n)));
    }
    Spanned::dummy(Expr::Ident(key.to_string(), NameId::INVALID))
}
