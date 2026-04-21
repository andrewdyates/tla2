// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Function-set membership, finite domain extraction, and range sort inference.
//!
//! Handles `f \in [D -> R]` for finite domain D by asserting each element
//! variable is in the range R.

use tla_core::ast::Expr;
use tla_core::Spanned;
use z4_dpll::api::Term;

use crate::error::{Z4Error, Z4Result};

use super::{TlaSort, Z4Translator};

impl Z4Translator {
    /// Translate function set membership: f \in [D -> R]
    ///
    /// For finite domain D = {a, b, c} and range R:
    /// f__a \in R /\ f__b \in R /\ f__c \in R
    pub(super) fn translate_func_set_membership(
        &mut self,
        elem: &Spanned<Expr>,
        domain: &Spanned<Expr>,
        range: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        // Get the function variable name
        let func_name = match &elem.node {
            Expr::Ident(name, _) => name.clone(),
            _ => {
                return Err(Z4Error::UnsupportedOp(
                    "only simple function variable membership is supported".to_string(),
                ))
            }
        };

        // Extract domain elements
        let domain_keys = self.extract_finite_domain(domain)?;

        // Check if function already declared
        if !self.func_vars.contains_key(&func_name) {
            // Infer range sort from the range set expression
            let range_sort = self.infer_range_sort(range)?;

            // Declare the function variable
            self.declare_func_var(&func_name, domain_keys.clone(), range_sort)?;
        }

        let info = self
            .func_vars
            .get(&func_name)
            .cloned()
            .ok_or_else(|| Z4Error::UnknownVariable(format!("function {func_name}")))?;

        // Build conjunction: each element is in range
        let mut conjuncts = Vec::new();
        for key in &info.domain_keys {
            let elem_term = info
                .element_terms
                .get(key)
                .copied()
                .ok_or_else(|| Z4Error::UnknownVariable(format!("{func_name}[{key}]")))?;
            let constraint = self.translate_range_membership(elem_term, &info.range_sort, range)?;
            conjuncts.push(constraint);
        }

        if conjuncts.is_empty() {
            return Ok(self.solver.bool_const(true));
        }

        let mut result = conjuncts[0];
        for c in &conjuncts[1..] {
            result = self.solver.try_and(result, *c)?;
        }
        Ok(result)
    }

    /// Extract finite domain elements from a set expression
    fn extract_finite_domain(&self, domain: &Spanned<Expr>) -> Z4Result<Vec<String>> {
        match &domain.node {
            Expr::SetEnum(elements) => {
                let mut keys = Vec::new();
                for e in elements {
                    match &e.node {
                        Expr::Int(n) => keys.push(n.to_string()),
                        Expr::Bool(b) => keys.push(b.to_string()),
                        Expr::String(s) => keys.push(s.clone()),
                        Expr::Ident(name, _) => keys.push(name.clone()),
                        _ => {
                            return Err(Z4Error::UnsupportedOp(format!(
                                "unsupported domain element: {:?}",
                                e.node
                            )))
                        }
                    }
                }
                Ok(keys)
            }
            Expr::Range(lo, hi) => {
                // Extract integer range
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

                if hi_val - lo_val > 1000 {
                    return Err(Z4Error::UnsupportedOp(
                        "domain too large for finite expansion (>1000 elements)".to_string(),
                    ));
                }

                let keys: Vec<String> = (lo_val..=hi_val).map(|i| i.to_string()).collect();
                Ok(keys)
            }
            Expr::Ident(name, _) if name == "BOOLEAN" => {
                Ok(vec!["false".to_string(), "true".to_string()])
            }
            _ => Err(Z4Error::UnsupportedOp(format!(
                "cannot extract finite domain from {:?}",
                std::mem::discriminant(&domain.node)
            ))),
        }
    }

    /// Infer the range sort from a range set expression
    fn infer_range_sort(&self, range: &Spanned<Expr>) -> Z4Result<TlaSort> {
        match &range.node {
            Expr::Ident(name, _) if name == "BOOLEAN" => Ok(TlaSort::Bool),
            Expr::Ident(name, _) if name == "Int" || name == "Nat" => Ok(TlaSort::Int),
            Expr::SetEnum(elements) if !elements.is_empty() => {
                // Infer from first element
                match &elements[0].node {
                    Expr::Int(_) => Ok(TlaSort::Int),
                    Expr::Bool(_) => Ok(TlaSort::Bool),
                    Expr::String(_) => Ok(TlaSort::String),
                    _ => Ok(TlaSort::Int), // Default to Int
                }
            }
            Expr::Range(_, _) => Ok(TlaSort::Int),
            _ => Ok(TlaSort::Int), // Default to Int for unknown ranges
        }
    }

    /// Translate membership constraint for a single element in a range
    fn translate_range_membership(
        &mut self,
        elem_term: Term,
        elem_sort: &TlaSort,
        range: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        match &range.node {
            Expr::Ident(name, _) if name == "BOOLEAN" => {
                if *elem_sort != TlaSort::Bool {
                    return Ok(self.solver.bool_const(false));
                }

                // Any bool is in BOOLEAN, but reference the element so it gets assigned.
                let t = self.solver.bool_const(true);
                let f = self.solver.bool_const(false);
                let is_true = self.solver.try_eq(elem_term, t)?;
                let is_false = self.solver.try_eq(elem_term, f)?;
                Ok(self.solver.try_or(is_true, is_false)?)
            }
            Expr::Ident(name, _) if name == "Int" => {
                // Any int is in Int
                Ok(self.solver.try_eq(elem_term, elem_term)?)
            }
            Expr::Ident(name, _) if name == "Nat" => {
                // elem >= 0
                let zero = self.solver.int_const(0);
                Ok(self.solver.try_ge(elem_term, zero)?)
            }
            Expr::SetEnum(elements) => {
                // elem \in {a, b, c}
                if elements.is_empty() {
                    return Ok(self.solver.bool_const(false));
                }

                // Optimization: if all elements are integer literals forming a
                // contiguous range, use bounds (min <= x /\ x <= max) instead of
                // disjunctions. This avoids z4 QF_LIA incompleteness on
                // disjunctions of integer equalities (Part of #1622).
                if let Some((min_val, max_val)) = Self::try_extract_contiguous_int_range(elements) {
                    let lo = self.solver.int_const(min_val);
                    let hi = self.solver.int_const(max_val);
                    let ge_lo = self.solver.try_ge(elem_term, lo)?;
                    let le_hi = self.solver.try_le(elem_term, hi)?;
                    return Ok(self.solver.try_and(ge_lo, le_hi)?);
                }

                let mut disjuncts = Vec::new();
                for e in elements {
                    let e_term = self
                        .translate_int(e)
                        .or_else(|_| self.translate_string(e))
                        .or_else(|_| self.translate_bool(e))?;
                    disjuncts.push(self.solver.try_eq(elem_term, e_term)?);
                }
                let mut result = disjuncts[0];
                for d in &disjuncts[1..] {
                    result = self.solver.try_or(result, *d)?;
                }
                Ok(result)
            }
            Expr::Range(lo, hi) => {
                // elem \in lo..hi
                let lo_term = self.translate_int(lo)?;
                let hi_term = self.translate_int(hi)?;
                let ge_lo = self.solver.try_ge(elem_term, lo_term)?;
                let le_hi = self.solver.try_le(elem_term, hi_term)?;
                Ok(self.solver.try_and(ge_lo, le_hi)?)
            }
            _ => Err(Z4Error::UnsupportedOp(format!(
                "unsupported range in function set: {:?}",
                std::mem::discriminant(&range.node)
            ))),
        }
    }

    /// Check if a set enum contains only integer literals forming a contiguous range.
    ///
    /// Returns `Some((min, max))` if the elements are a contiguous integer range,
    /// `None` otherwise. Used to convert `x \in {0, 1, 2}` into `0 <= x /\ x <= 2`
    /// which avoids disjunctions that trigger z4 QF_LIA incompleteness.
    pub(super) fn try_extract_contiguous_int_range(
        elements: &[Spanned<Expr>],
    ) -> Option<(i64, i64)> {
        if elements.is_empty() {
            return None;
        }

        let mut values = Vec::with_capacity(elements.len());
        for e in elements {
            match &e.node {
                Expr::Int(n) => {
                    let v: i64 = n.try_into().ok()?;
                    values.push(v);
                }
                _ => return None, // Non-integer element
            }
        }

        let min_val = *values.iter().min()?;
        let max_val = *values.iter().max()?;

        // Check contiguity: max - min + 1 == count, and all values are distinct
        if (max_val - min_val + 1) as usize == values.len() {
            // Verify all values are distinct (sort and check for duplicates)
            values.sort_unstable();
            values.dedup();
            if values.len() == elements.len() {
                return Some((min_val, max_val));
            }
        }

        None
    }
}
