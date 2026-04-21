// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Expression and value resolution for FlatZinc-to-SMT translation

use z4_flatzinc_parser::ast::Expr;

use crate::error::TranslateError;
use crate::translate::{smt_int, Context, ScalarValue};

/// Expression resolution methods for the translation context.
impl Context {
    /// Convert a scalar FlatZinc expression to an SMT-LIB term string.
    pub(crate) fn expr_to_smt(&self, expr: &Expr) -> Result<String, TranslateError> {
        match expr {
            Expr::Bool(true) => Ok("true".into()),
            Expr::Bool(false) => Ok("false".into()),
            Expr::Int(n) => Ok(smt_int(*n)),
            Expr::Float(f) => Ok(format!("{f}")),
            Expr::Ident(name) => self.resolve_ident(name),
            Expr::ArrayAccess(name, idx_expr) => {
                let idx = self.resolve_int(idx_expr)?;
                self.resolve_array_access(name, idx)
            }
            _ => Err(TranslateError::UnsupportedType(format!("{expr:?}"))),
        }
    }

    /// Convert an array expression to a vector of SMT term strings.
    pub(crate) fn expr_to_smt_array(&self, expr: &Expr) -> Result<Vec<String>, TranslateError> {
        match expr {
            Expr::ArrayLit(elems) => elems.iter().map(|e| self.expr_to_smt(e)).collect(),
            Expr::Ident(name) => {
                if let Some((_, _, values)) = self.array_params.get(name) {
                    return Ok(values.iter().map(ScalarValue::to_smt).collect());
                }
                if let Some((lo, hi, _)) = self.array_vars.get(name) {
                    return Ok((*lo..=*hi).map(|i| format!("{name}_{i}")).collect());
                }
                Err(TranslateError::UnknownIdentifier(name.clone()))
            }
            _ => Err(TranslateError::ExpectedArray),
        }
    }

    /// Resolve an integer array expression to concrete i64 values.
    pub(crate) fn resolve_int_array(&self, expr: &Expr) -> Result<Vec<i64>, TranslateError> {
        match expr {
            Expr::ArrayLit(elems) => elems.iter().map(|e| self.resolve_int(e)).collect(),
            Expr::Ident(name) => {
                if let Some((_, _, values)) = self.array_params.get(name) {
                    values
                        .iter()
                        .map(|v| match v {
                            ScalarValue::Int(n) => Ok(*n),
                            _ => Err(TranslateError::ExpectedIntLiteral(format!("{v:?}"))),
                        })
                        .collect()
                } else {
                    Err(TranslateError::UnknownIdentifier(name.clone()))
                }
            }
            _ => Err(TranslateError::ExpectedArray),
        }
    }

    /// Resolve a set expression to a vector of integers.
    pub(crate) fn resolve_set(&self, expr: &Expr) -> Result<Vec<i64>, TranslateError> {
        match expr {
            Expr::SetLit(elems) => elems.iter().map(|e| self.resolve_int(e)).collect(),
            Expr::IntRange(lo, hi) => Ok((*lo..=*hi).collect()),
            Expr::EmptySet => Ok(vec![]),
            Expr::Ident(name) => {
                if let Some(values) = self.set_params.get(name) {
                    Ok(values.clone())
                } else {
                    Err(TranslateError::UnknownIdentifier(name.clone()))
                }
            }
            _ => Err(TranslateError::UnsupportedType(format!("{expr:?}"))),
        }
    }

    pub(crate) fn resolve_int(&self, expr: &Expr) -> Result<i64, TranslateError> {
        match expr {
            Expr::Int(n) => Ok(*n),
            Expr::Ident(name) => {
                if let Some(ScalarValue::Int(n)) = self.scalar_params.get(name) {
                    Ok(*n)
                } else {
                    Err(TranslateError::ExpectedIntLiteral(name.clone()))
                }
            }
            _ => Err(TranslateError::ExpectedIntLiteral(format!("{expr:?}"))),
        }
    }

    fn resolve_ident(&self, name: &str) -> Result<String, TranslateError> {
        if let Some(val) = self.scalar_params.get(name) {
            return Ok(val.to_smt());
        }
        if let Some((smt_name, _)) = self.scalar_vars.get(name) {
            return Ok(smt_name.clone());
        }
        // Set variables are used directly by name in SMT-LIB
        if self.set_vars.contains_key(name) {
            return Ok(name.to_string());
        }
        Err(TranslateError::UnknownIdentifier(name.into()))
    }

    fn resolve_array_access(&self, name: &str, idx: i64) -> Result<String, TranslateError> {
        if let Some((lo, _, values)) = self.array_params.get(name) {
            let offset = (idx - lo) as usize;
            if offset < values.len() {
                return Ok(values[offset].to_smt());
            }
            return Err(TranslateError::ArrayIndexOutOfBounds {
                name: name.into(),
                index: idx,
            });
        }
        if self.array_vars.contains_key(name) {
            return Ok(format!("{name}_{idx}"));
        }
        Err(TranslateError::UnknownIdentifier(name.into()))
    }

    pub(crate) fn resolve_scalar_value(&self, expr: &Expr) -> Result<ScalarValue, TranslateError> {
        match expr {
            Expr::Bool(b) => Ok(ScalarValue::Bool(*b)),
            Expr::Int(n) => Ok(ScalarValue::Int(*n)),
            Expr::Float(f) => Ok(ScalarValue::Float(*f)),
            Expr::Ident(name) => self
                .scalar_params
                .get(name)
                .cloned()
                .ok_or_else(|| TranslateError::UnknownIdentifier(name.clone())),
            _ => Err(TranslateError::ExpectedIntLiteral(format!("{expr:?}"))),
        }
    }

    pub(crate) fn resolve_array_values(
        &self,
        expr: &Expr,
    ) -> Result<Vec<ScalarValue>, TranslateError> {
        match expr {
            Expr::ArrayLit(elems) => elems.iter().map(|e| self.resolve_scalar_value(e)).collect(),
            Expr::Ident(name) => self
                .array_params
                .get(name)
                .map(|(_, _, v)| v.clone())
                .ok_or_else(|| TranslateError::UnknownIdentifier(name.clone())),
            _ => Err(TranslateError::ExpectedArray),
        }
    }

    /// Resolve an array of set literals (for array-of-set parameters).
    pub(crate) fn resolve_array_of_sets(
        &self,
        expr: &Expr,
    ) -> Result<Vec<Vec<i64>>, TranslateError> {
        match expr {
            Expr::ArrayLit(elems) => elems.iter().map(|e| self.resolve_set_literal(e)).collect(),
            _ => Err(TranslateError::ExpectedArray),
        }
    }

    pub(crate) fn resolve_set_literal(&self, expr: &Expr) -> Result<Vec<i64>, TranslateError> {
        match expr {
            Expr::SetLit(elems) => elems.iter().map(|e| self.resolve_int(e)).collect(),
            Expr::IntRange(lo, hi) => Ok((*lo..=*hi).collect()),
            Expr::EmptySet => Ok(vec![]),
            _ => Err(TranslateError::UnsupportedType(format!("{expr:?}"))),
        }
    }
}
