// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Record and tuple encoding dispatch for z4 translator via [`RecordEncoder`].
//!
//! Part of #3749: record encoding as product types.
//! Part of #3778: wire compound type encoders into BMC dispatch.
//! Part of #3787: record/tuple equality, DOMAIN, and literal encoding.

use std::collections::HashMap;

use tla_core::ast::Expr;
use tla_core::Spanned;
use z4_dpll::api::Term;

use super::record_encoder::RecordEncoder;
use super::{TlaSort, Z4Translator};
use crate::error::{Z4Error, Z4Result};

impl Z4Translator {
    /// Try to translate record equality as field-wise conjunction.
    ///
    /// Handles three cases:
    /// - `record_var = record_var` (pointwise field comparison)
    /// - `record_var = [f1 |-> e1, ...]` (variable vs literal)
    /// - `[f1 |-> e1, ...] = [g1 |-> e1', ...]` (literal vs literal)
    ///
    /// Returns `None` if neither operand is a known record variable or literal.
    /// Part of #3787.
    pub(super) fn try_translate_record_equality(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Z4Result<Option<Term>> {
        let left_is_record_var = matches!(
            &left.node,
            Expr::Ident(name, _) if self.record_vars.contains_key(name)
        );
        let right_is_record_var = matches!(
            &right.node,
            Expr::Ident(name, _) if self.record_vars.contains_key(name)
        );
        let left_is_record_lit = matches!(&left.node, Expr::Record(_));
        let right_is_record_lit = matches!(&right.node, Expr::Record(_));

        // Case 1: var = var
        if left_is_record_var && right_is_record_var {
            let l = match &left.node {
                Expr::Ident(name, _) => name.clone(),
                _ => unreachable!(),
            };
            let r = match &right.node {
                Expr::Ident(name, _) => name.clone(),
                _ => unreachable!(),
            };
            let enc = RecordEncoder::new();
            let result = enc.encode_record_equality(self, &l, &r)?;
            return Ok(Some(result));
        }

        // Case 2: var = literal
        if left_is_record_var && right_is_record_lit {
            let var_name = match &left.node {
                Expr::Ident(name, _) => name.clone(),
                _ => unreachable!(),
            };
            if let Expr::Record(fields) = &right.node {
                return Ok(Some(
                    self.translate_record_var_eq_literal(&var_name, fields)?,
                ));
            }
        }

        // Case 3: literal = var (symmetric)
        if left_is_record_lit && right_is_record_var {
            let var_name = match &right.node {
                Expr::Ident(name, _) => name.clone(),
                _ => unreachable!(),
            };
            if let Expr::Record(fields) = &left.node {
                return Ok(Some(
                    self.translate_record_var_eq_literal(&var_name, fields)?,
                ));
            }
        }

        // Case 4: literal = literal
        if left_is_record_lit && right_is_record_lit {
            if let (Expr::Record(l_fields), Expr::Record(r_fields)) = (&left.node, &right.node) {
                return Ok(Some(
                    self.translate_record_literal_eq_literal(l_fields, r_fields)?,
                ));
            }
        }

        Ok(None)
    }

    /// Translate `record_var = [f1 |-> e1, ..., fn |-> en]`.
    ///
    /// Translates each field value and builds pointwise equality with the
    /// record variable's SMT variables.
    fn translate_record_var_eq_literal(
        &mut self,
        var_name: &str,
        fields: &[(Spanned<String>, Spanned<Expr>)],
    ) -> Z4Result<Term> {
        let mut field_terms = HashMap::with_capacity(fields.len());
        for (name_spanned, value_expr) in fields {
            let field_name = &name_spanned.node;
            let term = self
                .translate_int(value_expr)
                .or_else(|_| self.translate_bool(value_expr))
                .or_else(|_| self.translate_string(value_expr))?;
            field_terms.insert(field_name.clone(), term);
        }

        let enc = RecordEncoder::new();
        enc.encode_record_var_eq_literal(self, var_name, &field_terms)
    }

    /// Translate `[f1 |-> e1, ...] = [g1 |-> e1', ...]` (literal = literal).
    ///
    /// Creates fresh record variables for each literal, constructs them,
    /// then compares pointwise.
    fn translate_record_literal_eq_literal(
        &mut self,
        left_fields: &[(Spanned<String>, Spanned<Expr>)],
        right_fields: &[(Spanned<String>, Spanned<Expr>)],
    ) -> Z4Result<Term> {
        // Different number of fields => not equal
        if left_fields.len() != right_fields.len() {
            return Ok(self.solver.bool_const(false));
        }

        // Build sorted field name sets to check domain equality
        let mut left_names: Vec<&str> = left_fields.iter().map(|(n, _)| n.node.as_str()).collect();
        let mut right_names: Vec<&str> =
            right_fields.iter().map(|(n, _)| n.node.as_str()).collect();
        left_names.sort();
        right_names.sort();

        if left_names != right_names {
            return Ok(self.solver.bool_const(false));
        }

        // Build per-field equality: for each shared field, compare values
        let mut conjuncts = Vec::with_capacity(left_fields.len());
        for (l_name, l_val) in left_fields {
            // Find matching field in right
            let r_val = right_fields
                .iter()
                .find(|(rn, _)| rn.node == l_name.node)
                .map(|(_, rv)| rv);

            let r_val = match r_val {
                Some(v) => v,
                None => return Ok(self.solver.bool_const(false)),
            };

            // Build equality expression and translate it
            let eq_expr = Expr::Eq(Box::new(l_val.clone()), Box::new(r_val.clone()));
            let eq_term = self.translate_bool(&Spanned::new(eq_expr, l_val.span))?;
            conjuncts.push(eq_term);
        }

        if conjuncts.is_empty() {
            return Ok(self.solver.bool_const(true));
        }
        let mut result = conjuncts[0];
        for &c in &conjuncts[1..] {
            result = self.solver.try_and(result, c)?;
        }
        Ok(result)
    }

    /// Translate record field access `r.field` returning Bool.
    pub(super) fn translate_record_access_bool(
        &mut self,
        base: &Spanned<Expr>,
        field: &str,
    ) -> Z4Result<Term> {
        let record_name = self.extract_record_name(base)?;
        let enc = RecordEncoder::new();

        // Verify field exists and has Bool sort
        let sort = enc.field_sort(self, &record_name, field)?;
        if sort != TlaSort::Bool {
            return Err(Z4Error::TypeMismatch {
                name: format!("{record_name}.{field}"),
                expected: "Bool".to_string(),
                actual: format!("{sort}"),
            });
        }

        enc.translate_field_access(self, &record_name, field)
    }

    /// Translate record field access `r.field` returning Int.
    pub(super) fn translate_record_access_int(
        &mut self,
        base: &Spanned<Expr>,
        field: &str,
    ) -> Z4Result<Term> {
        let record_name = self.extract_record_name(base)?;
        let enc = RecordEncoder::new();

        // Verify field exists and has Int sort
        let sort = enc.field_sort(self, &record_name, field)?;
        if sort != TlaSort::Int {
            return Err(Z4Error::TypeMismatch {
                name: format!("{record_name}.{field}"),
                expected: "Int".to_string(),
                actual: format!("{sort}"),
            });
        }

        enc.translate_field_access(self, &record_name, field)
    }

    /// Translate `DOMAIN expr` where expr is a record or tuple variable.
    ///
    /// For records, DOMAIN returns the set of field name strings (interned).
    /// For tuples, DOMAIN returns the set {1, ..., n}.
    ///
    /// This is used in membership context (`x \in DOMAIN r`). Returns the
    /// domain element terms for use in membership disjunctions.
    ///
    /// Part of #3787.
    pub(crate) fn translate_record_or_tuple_domain(
        &mut self,
        func_expr: &Spanned<Expr>,
    ) -> Z4Result<Option<Vec<Term>>> {
        let name = match &func_expr.node {
            Expr::Ident(name, _) => name,
            _ => return Ok(None),
        };

        let enc = RecordEncoder::new();

        // Check record vars first
        if self.record_vars.contains_key(name) {
            let ids = enc.encode_record_domain_ids(self, name)?;
            return Ok(Some(ids));
        }

        // Check tuple vars
        if self.tuple_vars.contains_key(name) {
            let ids = enc.encode_tuple_domain_ids(self, name)?;
            return Ok(Some(ids));
        }

        Ok(None)
    }

    /// Extract a record variable name from a base expression.
    ///
    /// Currently only supports simple `Ident` references to declared record variables.
    fn extract_record_name(&self, base: &Spanned<Expr>) -> Z4Result<String> {
        match &base.node {
            Expr::Ident(name, _) => {
                if self.record_vars.contains_key(name) {
                    Ok(name.clone())
                } else {
                    Err(Z4Error::UnknownVariable(format!(
                        "'{name}' is not a declared record variable"
                    )))
                }
            }
            _ => Err(Z4Error::UnsupportedOp(
                "record field access on non-variable expression not supported in z4".to_string(),
            )),
        }
    }
}
