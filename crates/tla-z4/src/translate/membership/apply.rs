// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Finite-domain function application helpers.
//!
//! Builds ITE chains for `f[x]` over finite domains: given domain `{a, b, c}`,
//! translates to `IF x = a THEN f__a ELSE IF x = b THEN f__b ELSE f__c`.

use tla_core::ast::Expr;
use tla_core::Spanned;
use z4_dpll::api::Term;

use crate::error::{Z4Error, Z4Result};

use super::{FunctionVarInfo, Z4Translator};

impl Z4Translator {
    /// Build an ITE chain for function application over finite domain
    pub(super) fn build_func_apply_ite(
        &mut self,
        info: &FunctionVarInfo,
        arg: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        if info.domain_keys.is_empty() {
            return Err(Z4Error::UnsupportedOp(
                "function with empty domain".to_string(),
            ));
        }

        // Try to evaluate the argument to a constant key
        if let Some(key) = self.try_expr_to_key(arg) {
            // Direct lookup
            return info
                .element_terms
                .get(&key)
                .copied()
                .ok_or_else(|| Z4Error::UnknownVariable(format!("f[{key}]")));
        }

        // Build ITE chain: IF arg = key1 THEN f__key1 ELSE IF arg = key2 THEN ...
        let arg_term = self
            .translate_int(arg)
            .or_else(|_| self.translate_bool(arg))?;

        let mut keys_iter = info.domain_keys.iter().rev();

        // Start with the last element (else case)
        let last_key = keys_iter
            .next()
            .expect("domain_keys is non-empty per check above");
        let mut result = info
            .element_terms
            .get(last_key)
            .copied()
            .ok_or_else(|| Z4Error::UnknownVariable(format!("f[{last_key}]")))?;

        // Build ITE chain from back to front
        for key in keys_iter {
            let key_term = self.key_to_term(key)?;
            let elem_term = info
                .element_terms
                .get(key)
                .copied()
                .ok_or_else(|| Z4Error::UnknownVariable(format!("f[{key}]")))?;
            let cond = self.solver.try_eq(arg_term, key_term)?;
            result = self.solver.try_ite(cond, elem_term, result)?;
        }

        Ok(result)
    }

    /// Try to convert an expression to a string key
    fn try_expr_to_key(&self, expr: &Spanned<Expr>) -> Option<String> {
        match &expr.node {
            Expr::Int(n) => Some(n.to_string()),
            Expr::Bool(b) => Some(b.to_string()),
            Expr::String(s) => Some(s.clone()),
            Expr::Ident(name, _) => Some(name.clone()),
            _ => None,
        }
    }

    /// Convert a string key back to a z4 term
    fn key_to_term(&mut self, key: &str) -> Z4Result<Term> {
        // Try parsing as integer
        if let Ok(n) = key.parse::<i64>() {
            return Ok(self.solver.int_const(n));
        }
        // Try as boolean
        if key == "true" {
            return Ok(self.solver.bool_const(true));
        }
        if key == "false" {
            return Ok(self.solver.bool_const(false));
        }
        // Otherwise treat as identifier - look up in vars
        if let Ok((_, term)) = self.get_var(key) {
            return Ok(term);
        }
        Err(Z4Error::UnsupportedOp(format!(
            "cannot convert key '{key}' to z4 term"
        )))
    }
}
