// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tuple operations for Z4 translation.
//!
//! Handles tuple indexing (t[i]), tuple equality (t = <<e1, e2, ...>>),
//! ITE chain construction for dynamic tuple access, and scalar type inference.

use tla_core::ast::Expr;
use tla_core::Spanned;
use z4_dpll::api::Term;

use crate::error::{Z4Error, Z4Result};

use super::{TlaSort, TupleVarInfo, Z4Translator};

impl Z4Translator {
    /// Translate tuple indexing t[i] where the expected result is Bool
    pub(super) fn translate_tuple_apply_bool(
        &mut self,
        tuple_name: &str,
        info: &TupleVarInfo,
        index: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        // Try constant index first
        if let Some(idx) = self.try_expr_to_int(index) {
            if idx < 1 || idx as usize > info.element_sorts.len() {
                return Err(Z4Error::UnsupportedOp(format!(
                    "tuple index {} out of bounds (tuple has {} elements)",
                    idx,
                    info.element_sorts.len()
                )));
            }
            let elem_sort = &info.element_sorts[idx as usize - 1];
            if *elem_sort != TlaSort::Bool {
                return Err(Z4Error::TypeMismatch {
                    name: format!("{tuple_name}[{idx}]"),
                    expected: "Bool".to_string(),
                    actual: format!("{elem_sort}"),
                });
            }
            return info
                .element_terms
                .get(&(idx as usize))
                .copied()
                .ok_or_else(|| Z4Error::UnsupportedOp(format!("{tuple_name}[{idx}] not found")));
        }

        // Dynamic index: build ITE chain
        self.build_tuple_ite_chain_bool(tuple_name, info, index)
    }

    /// Translate tuple indexing t[i] where the expected result is Int
    pub(super) fn translate_tuple_apply_int(
        &mut self,
        tuple_name: &str,
        info: &TupleVarInfo,
        index: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        // Try constant index first
        if let Some(idx) = self.try_expr_to_int(index) {
            if idx < 1 || idx as usize > info.element_sorts.len() {
                return Err(Z4Error::UnsupportedOp(format!(
                    "tuple index {} out of bounds (tuple has {} elements)",
                    idx,
                    info.element_sorts.len()
                )));
            }
            let elem_sort = &info.element_sorts[idx as usize - 1];
            if *elem_sort != TlaSort::Int {
                return Err(Z4Error::TypeMismatch {
                    name: format!("{tuple_name}[{idx}]"),
                    expected: "Int".to_string(),
                    actual: format!("{elem_sort}"),
                });
            }
            return info
                .element_terms
                .get(&(idx as usize))
                .copied()
                .ok_or_else(|| Z4Error::UnsupportedOp(format!("{tuple_name}[{idx}] not found")));
        }

        // Dynamic index: build ITE chain
        self.build_tuple_ite_chain_int(tuple_name, info, index)
    }

    /// Try to extract a constant integer from an expression
    pub(super) fn try_expr_to_int(&self, expr: &Spanned<Expr>) -> Option<i64> {
        match &expr.node {
            Expr::Int(n) => n.try_into().ok(),
            _ => None,
        }
    }

    /// Infer the scalar type of an expression for type-mismatch detection.
    ///
    /// Returns Some(TlaSort) if the expression has a recognizable scalar type,
    /// None if the type cannot be inferred.
    ///
    /// Used for cross-type equality semantics: `1 = "a"` is FALSE, not an error.
    pub(super) fn infer_scalar_type(&self, expr: &Spanned<Expr>) -> Option<TlaSort> {
        match &expr.node {
            // Literals
            Expr::Int(_) => Some(TlaSort::Int),
            Expr::Bool(_) => Some(TlaSort::Bool),
            Expr::String(_) => Some(TlaSort::String),

            // Variables - look up declared type in scalar vars or tuple vars
            Expr::Ident(name, _) => {
                // Check scalar variables first
                if let Some((sort, _)) = self.vars.get(name) {
                    if sort.is_scalar() {
                        return Some(sort.clone());
                    }
                }
                // Check tuple variables
                if let Some(info) = self.tuple_vars.get(name) {
                    return Some(TlaSort::Tuple {
                        element_sorts: info.element_sorts.clone(),
                    });
                }
                None
            }

            // Tuple literals have a tuple type (for tuple vs scalar mismatch)
            Expr::Tuple(_) => Some(TlaSort::Tuple {
                element_sorts: vec![], // Placeholder - we just need to know it's a tuple
            }),

            // For other expressions, we can't easily infer without side effects
            // Return None - the comparison will error as before
            _ => None,
        }
    }

    /// Build an ITE chain for tuple indexing with Int elements
    fn build_tuple_ite_chain_int(
        &mut self,
        tuple_name: &str,
        info: &TupleVarInfo,
        index: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let index_term = self.translate_int(index)?;
        let len = info.element_sorts.len();

        // Find Int elements for the ITE chain
        let int_indices: Vec<usize> = (1..=len)
            .filter(|&i| info.element_sorts[i - 1] == TlaSort::Int)
            .collect();

        if int_indices.is_empty() {
            return Err(Z4Error::TypeMismatch {
                name: tuple_name.to_string(),
                expected: "tuple with Int elements".to_string(),
                actual: "tuple with no Int elements".to_string(),
            });
        }

        // Build ITE chain from last to first
        let last_idx = *int_indices
            .last()
            .expect("int_indices is non-empty per check above");
        let mut result =
            info.element_terms.get(&last_idx).copied().ok_or_else(|| {
                Z4Error::UnsupportedOp(format!("{tuple_name}[{last_idx}] not found"))
            })?;
        for &idx in int_indices.iter().rev().skip(1) {
            let idx_const = self.solver.int_const(idx as i64);
            let cond = self.solver.try_eq(index_term, idx_const)?;
            let elem_term =
                info.element_terms.get(&idx).copied().ok_or_else(|| {
                    Z4Error::UnsupportedOp(format!("{tuple_name}[{idx}] not found"))
                })?;
            result = self.solver.try_ite(cond, elem_term, result)?;
        }

        Ok(result)
    }

    /// Build an ITE chain for tuple indexing with Bool elements
    fn build_tuple_ite_chain_bool(
        &mut self,
        tuple_name: &str,
        info: &TupleVarInfo,
        index: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let index_term = self.translate_int(index)?;
        let len = info.element_sorts.len();

        // Find Bool elements for the ITE chain
        let bool_indices: Vec<usize> = (1..=len)
            .filter(|&i| info.element_sorts[i - 1] == TlaSort::Bool)
            .collect();

        if bool_indices.is_empty() {
            return Err(Z4Error::TypeMismatch {
                name: tuple_name.to_string(),
                expected: "tuple with Bool elements".to_string(),
                actual: "tuple with no Bool elements".to_string(),
            });
        }

        // Build ITE chain from last to first
        let last_idx = *bool_indices
            .last()
            .expect("bool_indices is non-empty per check above");
        let mut result =
            info.element_terms.get(&last_idx).copied().ok_or_else(|| {
                Z4Error::UnsupportedOp(format!("{tuple_name}[{last_idx}] not found"))
            })?;
        for &idx in bool_indices.iter().rev().skip(1) {
            let idx_const = self.solver.int_const(idx as i64);
            let cond = self.solver.try_eq(index_term, idx_const)?;
            let elem_term =
                info.element_terms.get(&idx).copied().ok_or_else(|| {
                    Z4Error::UnsupportedOp(format!("{tuple_name}[{idx}] not found"))
                })?;
            result = self.solver.try_ite(cond, elem_term, result)?;
        }

        Ok(result)
    }

    /// Translate tuple indexing for String result
    pub(super) fn translate_tuple_apply_string(
        &mut self,
        func: &Spanned<Expr>,
        arg: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let var_name = match &func.node {
            Expr::Ident(name, _) => name.clone(),
            _ => {
                return Err(Z4Error::UnsupportedOp(
                    "only simple variable tuple indexing supported".to_string(),
                ))
            }
        };

        if let Some(info) = self.tuple_vars.get(&var_name).cloned() {
            if let Some(idx) = self.try_expr_to_int(arg) {
                if idx < 1 || idx as usize > info.element_sorts.len() {
                    return Err(Z4Error::UnsupportedOp(format!(
                        "tuple index {idx} out of bounds"
                    )));
                }
                if info.element_sorts[idx as usize - 1] != TlaSort::String {
                    return Err(Z4Error::TypeMismatch {
                        name: format!("{var_name}[{idx}]"),
                        expected: "String".to_string(),
                        actual: format!("{}", info.element_sorts[idx as usize - 1]),
                    });
                }
                return info
                    .element_terms
                    .get(&(idx as usize))
                    .copied()
                    .ok_or_else(|| Z4Error::UnsupportedOp(format!("{var_name}[{idx}] not found")));
            }
            return self.build_tuple_ite_chain_string(&var_name, &info, arg);
        }
        Err(Z4Error::UnknownVariable(format!("{var_name} not a tuple")))
    }

    /// Build ITE chain for tuple indexing with String elements
    fn build_tuple_ite_chain_string(
        &mut self,
        tuple_name: &str,
        info: &TupleVarInfo,
        index: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let idx_term = self.translate_int(index)?;
        let indices: Vec<usize> = (1..=info.element_sorts.len())
            .filter(|&i| info.element_sorts[i - 1] == TlaSort::String)
            .collect();
        if indices.is_empty() {
            return Err(Z4Error::TypeMismatch {
                name: tuple_name.to_string(),
                expected: "tuple with String elements".to_string(),
                actual: "no String elements".to_string(),
            });
        }
        let last_idx = *indices
            .last()
            .expect("indices is non-empty per check above");
        let mut result =
            info.element_terms.get(&last_idx).copied().ok_or_else(|| {
                Z4Error::UnsupportedOp(format!("{tuple_name}[{last_idx}] not found"))
            })?;
        for &idx in indices.iter().rev().skip(1) {
            let idx_const = self.solver.int_const(idx as i64);
            let cond = self.solver.try_eq(idx_term, idx_const)?;
            let elem_term =
                info.element_terms.get(&idx).copied().ok_or_else(|| {
                    Z4Error::UnsupportedOp(format!("{tuple_name}[{idx}] not found"))
                })?;
            result = self.solver.try_ite(cond, elem_term, result)?;
        }
        Ok(result)
    }

    /// Try to translate tuple equality: t = <<e1, e2, ...>>
    ///
    /// Returns Some(term) if both sides can be interpreted as tuples of the same arity,
    /// None if neither side is a tuple, or an error if there's a type/arity mismatch.
    ///
    /// Handles:
    /// - tuple_var = <<e1, e2, ...>> (variable equals literal)
    /// - <<e1, e2, ...>> = tuple_var (literal equals variable)
    /// - <<a1, a2, ...>> = <<b1, b2, ...>> (literal equals literal)
    pub(super) fn try_translate_tuple_equality(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Z4Result<Option<Term>> {
        // Check if left is a tuple var and right is a tuple literal
        if let Expr::Ident(name, _) = &left.node {
            if let Ok(info) = self.get_tuple_var(name).cloned() {
                if let Expr::Tuple(elements) = &right.node {
                    return Ok(Some(
                        self.translate_tuple_var_eq_literal(name, &info, elements)?,
                    ));
                }
            }
        }

        // Check if right is a tuple var and left is a tuple literal
        if let Expr::Ident(name, _) = &right.node {
            if let Ok(info) = self.get_tuple_var(name).cloned() {
                if let Expr::Tuple(elements) = &left.node {
                    return Ok(Some(
                        self.translate_tuple_var_eq_literal(name, &info, elements)?,
                    ));
                }
            }
        }

        // Check if both are tuple literals
        if let (Expr::Tuple(left_elems), Expr::Tuple(right_elems)) = (&left.node, &right.node) {
            return Ok(Some(
                self.translate_tuple_literal_eq_literal(left_elems, right_elems)?,
            ));
        }

        // Neither side is a tuple
        Ok(None)
    }

    /// Translate equality between a tuple variable and a tuple literal
    /// t = <<e1, e2, ..., en>> => (t__1 = e1) /\ (t__2 = e2) /\ ... /\ (t__n = en)
    fn translate_tuple_var_eq_literal(
        &mut self,
        tuple_name: &str,
        info: &TupleVarInfo,
        elements: &[Spanned<Expr>],
    ) -> Z4Result<Term> {
        // Part of #538: Arity mismatch should return FALSE, not an error.
        // Per TLA+ semantics: <<1,2>> = <<1>> is FALSE (different arity means not equal)
        if info.element_sorts.len() != elements.len() {
            return Ok(self.solver.bool_const(false));
        }

        let mut conjuncts = Vec::new();
        for (i, elem) in elements.iter().enumerate() {
            let idx = i + 1; // 1-based indexing
            let var_term =
                info.element_terms.get(&idx).copied().ok_or_else(|| {
                    Z4Error::UnsupportedOp(format!("{tuple_name}[{idx}] not found"))
                })?;
            let elem_sort = &info.element_sorts[i];

            let eq = match elem_sort {
                TlaSort::Int => {
                    let elem_term = self.translate_int(elem)?;
                    self.solver.try_eq(var_term, elem_term)?
                }
                TlaSort::Bool => {
                    let elem_term = self.translate_bool(elem)?;
                    // Bool equality: (a /\ b) \/ (~a /\ ~b)
                    let a_and_b = self.solver.try_and(var_term, elem_term)?;
                    let not_a = self.solver.try_not(var_term)?;
                    let not_b = self.solver.try_not(elem_term)?;
                    let not_a_and_not_b = self.solver.try_and(not_a, not_b)?;
                    self.solver.try_or(a_and_b, not_a_and_not_b)?
                }
                TlaSort::String => {
                    let elem_term = self.translate_string(elem)?;
                    self.solver.try_eq(var_term, elem_term)?
                }
                _ => {
                    return Err(Z4Error::UnsupportedOp(
                        "nested tuple/function elements in equality not supported".to_string(),
                    ))
                }
            };
            conjuncts.push(eq);
        }

        // Build conjunction of all element equalities
        if conjuncts.is_empty() {
            return Ok(self.solver.bool_const(true)); // Empty tuple equality
        }
        let mut result = conjuncts[0];
        for c in &conjuncts[1..] {
            result = self.solver.try_and(result, *c)?;
        }
        Ok(result)
    }

    /// Translate equality between two tuple literals
    /// <<a1, a2, ...>> = <<b1, b2, ...>> => (a1 = b1) /\ (a2 = b2) /\ ...
    fn translate_tuple_literal_eq_literal(
        &mut self,
        left: &[Spanned<Expr>],
        right: &[Spanned<Expr>],
    ) -> Z4Result<Term> {
        if left.len() != right.len() {
            // Different arities => FALSE
            return Ok(self.solver.bool_const(false));
        }

        if left.is_empty() {
            // Empty tuples are equal
            return Ok(self.solver.bool_const(true));
        }

        let mut conjuncts = Vec::new();
        for (l, r) in left.iter().zip(right.iter()) {
            // Create equality expression and translate it
            let eq_expr = Expr::Eq(Box::new(l.clone()), Box::new(r.clone()));
            let eq_term = self.translate_bool(&Spanned::new(eq_expr, l.span))?;
            conjuncts.push(eq_term);
        }

        let mut result = conjuncts[0];
        for c in &conjuncts[1..] {
            result = self.solver.try_and(result, *c)?;
        }
        Ok(result)
    }
}
