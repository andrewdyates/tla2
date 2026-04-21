// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Record and tuple encoding for BMC translator.
//!
//! Records are encoded as per-field SMT variables:
//! - `[a |-> 1, b |-> TRUE]` → `r__f_a: Int, r__f_b: Bool`
//! - `r.a` → direct field variable lookup (`r__f_a`)
//! - `[r EXCEPT !.a = 2]` → copy all fields, override `r__f_a`
//!
//! Tuples are encoded as per-element SMT variables:
//! - `<<1, TRUE, "x">>` → `t__e_1: Int, t__e_2: Bool, t__e_3: Int`
//! - `t[2]` → direct element variable lookup (`t__e_2`)
//!
//! Part of #3787: z4 symbolic engine record and tuple encoding for BMC.

use tla_core::ast::{ExceptPathElement, ExceptSpec, Expr};
use tla_core::{dispatch_translate_bool, dispatch_translate_int, Spanned};
use z4_dpll::api::Term;

use crate::error::{Z4Error, Z4Result};
use crate::TlaSort;

use super::BmcTranslator;

/// Information about a record variable across all BMC steps.
///
/// Each record is encoded as a set of per-field SMT variables per step.
/// The field sorts are stored in canonical name order.
///
/// Part of #3787: Record encoding in BMC translator.
#[derive(Debug)]
pub(super) struct BmcRecordVarInfo {
    /// Field sorts in canonical (alphabetical) name order.
    pub(super) field_sorts: Vec<(String, TlaSort)>,
    /// Per-field terms per step: field_terms[field_idx][step] = Term.
    pub(super) field_terms: Vec<Vec<Term>>,
}

/// Information about a tuple variable across all BMC steps.
///
/// Each tuple is encoded as a set of per-element SMT variables per step.
/// Element indices are 1-based (matching TLA+ tuple indexing).
///
/// Part of #3787: Tuple encoding in BMC translator.
#[derive(Debug)]
pub(super) struct BmcTupleVarInfo {
    /// Element sorts (0-indexed internally, but 1-indexed in TLA+).
    pub(super) element_sorts: Vec<TlaSort>,
    /// Per-element terms per step: element_terms[elem_idx][step] = Term.
    pub(super) element_terms: Vec<Vec<Term>>,
}

impl BmcTranslator {
    // === Record variable declaration ===

    /// Declare a record state variable for all k+1 steps.
    ///
    /// Each record field becomes an independent SMT variable per step:
    /// - `{name}__f_{field}__{step}`: field-sort variable
    ///
    /// The field sorts must be scalar (Bool, Int, or String).
    ///
    /// Part of #3787: Record encoding in BMC translator.
    pub fn declare_record_var(
        &mut self,
        name: &str,
        field_sorts: Vec<(String, TlaSort)>,
    ) -> Z4Result<()> {
        if self.record_vars.contains_key(name) {
            return Ok(()); // Already declared
        }

        for (field_name, sort) in &field_sorts {
            if !sort.is_scalar()
                && !matches!(sort, TlaSort::Set { .. })
                && !matches!(sort, TlaSort::Record { .. })
            {
                return Err(Z4Error::UnsupportedOp(format!(
                    "BMC record field must be scalar or Set, got {sort} for field \
                     '{field_name}' of record '{name}'"
                )));
            }
        }

        let mut all_field_terms = Vec::with_capacity(field_sorts.len());

        for (field_name, sort) in &field_sorts {
            match sort {
                TlaSort::Record { field_sorts: sub_fields } => {
                    // Recursively declare sub-record for all k+1 steps.
                    // The sub-record is registered as "{name}__f_{field_name}" in
                    // record_vars with its own per-step field terms.
                    let sub_name = format!("{name}__f_{field_name}");
                    self.declare_record_var(&sub_name, sub_fields.clone())?;
                    // Store empty step_terms as placeholder — nested record access
                    // goes through the sub-record's own entry in record_vars.
                    let sentinel_terms = (0..=self.bound_k)
                        .map(|_| self.solver.bool_const(true))
                        .collect();
                    all_field_terms.push(sentinel_terms);
                }
                _ => {
                    // Scalar or Set: declare directly (Set maps to (Array Int Bool))
                    let z4_sort = sort.to_z4()?;
                    let mut step_terms = Vec::with_capacity(self.bound_k + 1);
                    for step in 0..=self.bound_k {
                        let var_name = format!("{name}__f_{field_name}__{step}");
                        let term = self.solver.declare_const(&var_name, z4_sort.clone());
                        step_terms.push(term);
                    }
                    all_field_terms.push(step_terms);
                }
            }
        }

        self.record_vars.insert(
            name.to_string(),
            BmcRecordVarInfo {
                field_sorts,
                field_terms: all_field_terms,
            },
        );
        Ok(())
    }

    // === Tuple variable declaration ===

    /// Declare a tuple state variable for all k+1 steps.
    ///
    /// Each tuple element becomes an independent SMT variable per step:
    /// - `{name}__e_{index}__{step}`: element-sort variable (1-indexed)
    ///
    /// The element sorts must be scalar (Bool, Int, or String).
    ///
    /// Part of #3787: Tuple encoding in BMC translator.
    pub fn declare_tuple_var(&mut self, name: &str, element_sorts: Vec<TlaSort>) -> Z4Result<()> {
        if self.tuple_vars.contains_key(name) {
            return Ok(()); // Already declared
        }

        for (i, sort) in element_sorts.iter().enumerate() {
            if !sort.is_scalar() {
                return Err(Z4Error::UnsupportedOp(format!(
                    "BMC tuple element must be scalar, got {sort} for element {} \
                     of tuple '{name}'",
                    i + 1
                )));
            }
        }

        let mut all_element_terms = Vec::with_capacity(element_sorts.len());

        for (i, sort) in element_sorts.iter().enumerate() {
            let z4_sort = sort.to_z4()?;
            let mut step_terms = Vec::with_capacity(self.bound_k + 1);
            for step in 0..=self.bound_k {
                let var_name = format!("{name}__e_{}__{step}", i + 1);
                let term = self.solver.declare_const(&var_name, z4_sort.clone());
                step_terms.push(term);
            }
            all_element_terms.push(step_terms);
        }

        self.tuple_vars.insert(
            name.to_string(),
            BmcTupleVarInfo {
                element_sorts,
                element_terms: all_element_terms,
            },
        );
        Ok(())
    }

    // === Record field access ===

    /// Get the term for a specific record field at a given step.
    ///
    /// Part of #3787.
    pub(crate) fn get_record_field_at_step(
        &self,
        name: &str,
        field: &str,
        step: usize,
    ) -> Z4Result<Term> {
        let info = self.record_vars.get(name).ok_or_else(|| {
            Z4Error::UnknownVariable(format!("record {name} (field {field}, step {step})"))
        })?;
        if step > self.bound_k {
            return Err(Z4Error::UntranslatableExpr(format!(
                "step {step} exceeds bound {}",
                self.bound_k
            )));
        }
        let field_idx = info
            .field_sorts
            .iter()
            .position(|(f, _)| f == field)
            .ok_or_else(|| {
                Z4Error::UntranslatableExpr(format!("record '{name}' has no field '{field}'"))
            })?;
        Ok(info.field_terms[field_idx][step])
    }

    // === Tuple element access ===

    /// Get the term for a specific tuple element at a given step.
    ///
    /// `index` is 1-based (TLA+ convention).
    ///
    /// Part of #3787.
    pub(crate) fn get_tuple_element_at_step(
        &self,
        name: &str,
        index: usize,
        step: usize,
    ) -> Z4Result<Term> {
        let info = self.tuple_vars.get(name).ok_or_else(|| {
            Z4Error::UnknownVariable(format!("tuple {name} (element {index}, step {step})"))
        })?;
        if step > self.bound_k {
            return Err(Z4Error::UntranslatableExpr(format!(
                "step {step} exceeds bound {}",
                self.bound_k
            )));
        }
        if index == 0 || index > info.element_sorts.len() {
            return Err(Z4Error::UntranslatableExpr(format!(
                "tuple '{name}' index {index} out of bounds (1..={})",
                info.element_sorts.len()
            )));
        }
        Ok(info.element_terms[index - 1][step])
    }

    // === Record/tuple variable detection ===

    /// Check whether an expression refers to a declared record variable.
    pub(super) fn is_record_var_expr(&self, expr: &Spanned<Expr>) -> bool {
        match &expr.node {
            Expr::Ident(name, _) | Expr::StateVar(name, ..) => self.record_vars.contains_key(name),
            Expr::Prime(inner) => match &inner.node {
                Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
                    self.record_vars.contains_key(name)
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// Check whether an expression refers to a declared tuple variable.
    pub(super) fn is_tuple_var_expr(&self, expr: &Spanned<Expr>) -> bool {
        match &expr.node {
            Expr::Ident(name, _) | Expr::StateVar(name, ..) => self.tuple_vars.contains_key(name),
            Expr::Prime(inner) => match &inner.node {
                Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
                    self.tuple_vars.contains_key(name)
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// Resolve a record variable expression to `(variable_name, step)`.
    pub(super) fn resolve_record_var(&self, expr: &Spanned<Expr>) -> Z4Result<(String, usize)> {
        match &expr.node {
            Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
                if self.record_vars.contains_key(name) {
                    Ok((name.clone(), self.current_step))
                } else {
                    Err(Z4Error::UnknownVariable(format!("record {name}")))
                }
            }
            Expr::Prime(inner) => match &inner.node {
                Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
                    if self.record_vars.contains_key(name) {
                        Ok((name.clone(), self.current_step + 1))
                    } else {
                        Err(Z4Error::UnknownVariable(format!("record {name}")))
                    }
                }
                _ => Err(Z4Error::UntranslatableExpr(
                    "BMC record operation requires variable reference".to_string(),
                )),
            },
            _ => Err(Z4Error::UntranslatableExpr(
                "BMC record operation requires variable reference".to_string(),
            )),
        }
    }

    /// Resolve a tuple variable expression to `(variable_name, step)`.
    pub(super) fn resolve_tuple_var(&self, expr: &Spanned<Expr>) -> Z4Result<(String, usize)> {
        match &expr.node {
            Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
                if self.tuple_vars.contains_key(name) {
                    Ok((name.clone(), self.current_step))
                } else {
                    Err(Z4Error::UnknownVariable(format!("tuple {name}")))
                }
            }
            Expr::Prime(inner) => match &inner.node {
                Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
                    if self.tuple_vars.contains_key(name) {
                        Ok((name.clone(), self.current_step + 1))
                    } else {
                        Err(Z4Error::UnknownVariable(format!("tuple {name}")))
                    }
                }
                _ => Err(Z4Error::UntranslatableExpr(
                    "BMC tuple operation requires variable reference".to_string(),
                )),
            },
            _ => Err(Z4Error::UntranslatableExpr(
                "BMC tuple operation requires variable reference".to_string(),
            )),
        }
    }

    // === Record construction ===

    /// Translate a record construction `[a |-> e1, b |-> e2]` into per-field
    /// constraints on a fresh set of variables.
    ///
    /// Returns a conjunction of equalities: `fresh_a = e1 /\ fresh_b = e2`.
    /// The fresh variables are stored for later access.
    ///
    /// Part of #3787.
    pub(super) fn translate_record_construct(
        &mut self,
        fields: &[(Spanned<String>, Spanned<Expr>)],
    ) -> Z4Result<Term> {
        if fields.is_empty() {
            return Ok(self.solver.bool_const(true));
        }

        let mut conjuncts = Vec::with_capacity(fields.len());

        for (field_name, value) in fields {
            let id = self.aux_var_counter;
            self.aux_var_counter += 1;
            let var_name = format!("__rec_f_{}_{id}", field_name.node);

            // Try translating as Int first, fall back to Bool
            if let Ok(val_term) = dispatch_translate_int(self, value) {
                let fresh = self
                    .solver
                    .declare_const(&var_name, z4_dpll::api::Sort::Int);
                let eq = self.solver.try_eq(fresh, val_term)?;
                conjuncts.push(eq);
            } else {
                let val_term = dispatch_translate_bool(self, value)?;
                let fresh = self
                    .solver
                    .declare_const(&var_name, z4_dpll::api::Sort::Bool);
                // Bool equality: (fresh => val) /\ (val => fresh)
                let fwd = self.solver.try_implies(fresh, val_term)?;
                let bwd = self.solver.try_implies(val_term, fresh)?;
                let eq_both = self.solver.try_and(fwd, bwd)?;
                conjuncts.push(eq_both);
            }
        }

        self.build_conjunction(conjuncts)
    }

    /// Translate record field access `r.field` into the appropriate field term.
    ///
    /// Resolves the record variable and step, then looks up the field term.
    ///
    /// Part of #3787.
    pub(super) fn translate_record_access(
        &mut self,
        record_expr: &Spanned<Expr>,
        field_name: &str,
    ) -> Z4Result<Term> {
        let (name, step) = self.resolve_record_var(record_expr)?;
        self.get_record_field_at_step(&name, field_name, step)
    }

    /// Translate record EXCEPT `[r EXCEPT !.a = v]` as equality constraints.
    ///
    /// For a record with fields {a, b, c}:
    /// - `target.a = v`  (the overridden field)
    /// - `target.b = source.b`  (copied)
    /// - `target.c = source.c`  (copied)
    ///
    /// Returns a conjunction of per-field equalities between target and
    /// source (with overrides applied).
    ///
    /// Part of #3787.
    pub(super) fn translate_record_except_eq(
        &mut self,
        target: &(String, usize),
        source: &(String, usize),
        specs: &[ExceptSpec],
    ) -> Z4Result<Term> {
        let info = self
            .record_vars
            .get(&source.0)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("record {}", source.0)))?;

        let field_names: Vec<String> = info.field_sorts.iter().map(|(n, _)| n.clone()).collect();
        let num_fields = field_names.len();

        // Collect all field overrides from EXCEPT specs
        let mut overrides: std::collections::HashMap<String, &Spanned<Expr>> =
            std::collections::HashMap::new();
        for spec in specs {
            if spec.path.len() == 1 {
                if let ExceptPathElement::Field(ref rfn) = spec.path[0] {
                    overrides.insert(rfn.name.node.clone(), &spec.value);
                }
            }
        }

        let mut conjuncts = Vec::with_capacity(num_fields);

        for field_name in &field_names {
            let target_term = self.get_record_field_at_step(&target.0, field_name, target.1)?;

            if let Some(value_expr) = overrides.get(field_name) {
                // Overridden field: target.field = value
                let field_sort = self
                    .record_vars
                    .get(&source.0)
                    .and_then(|info| {
                        info.field_sorts
                            .iter()
                            .find(|(n, _)| n == field_name)
                            .map(|(_, s)| s.clone())
                    })
                    .unwrap_or(TlaSort::Int);

                let val_term = if field_sort == TlaSort::Bool {
                    dispatch_translate_bool(self, value_expr)?
                } else {
                    dispatch_translate_int(self, value_expr)?
                };

                let eq = self.solver.try_eq(target_term, val_term)?;
                conjuncts.push(eq);
            } else {
                // Copied field: target.field = source.field
                let source_term = self.get_record_field_at_step(&source.0, field_name, source.1)?;
                let eq = self.solver.try_eq(target_term, source_term)?;
                conjuncts.push(eq);
            }
        }

        self.build_conjunction(conjuncts)
    }

    // === Tuple construction ===

    /// Translate a tuple construction `<<e1, e2, e3>>` as per-element
    /// constraints on fresh variables.
    ///
    /// Returns a conjunction: `fresh_1 = e1 /\ fresh_2 = e2 /\ ...`
    ///
    /// Part of #3787.
    #[allow(dead_code)]
    pub(super) fn translate_tuple_construct(
        &mut self,
        elements: &[Spanned<Expr>],
    ) -> Z4Result<Term> {
        if elements.is_empty() {
            return Ok(self.solver.bool_const(true));
        }

        let mut conjuncts = Vec::with_capacity(elements.len());

        for (i, elem) in elements.iter().enumerate() {
            let id = self.aux_var_counter;
            self.aux_var_counter += 1;
            let var_name = format!("__tup_e_{}_{id}", i + 1);

            // Try translating as Int first, fall back to Bool
            if let Ok(val_term) = dispatch_translate_int(self, elem) {
                let fresh = self
                    .solver
                    .declare_const(&var_name, z4_dpll::api::Sort::Int);
                let eq = self.solver.try_eq(fresh, val_term)?;
                conjuncts.push(eq);
            } else {
                let val_term = dispatch_translate_bool(self, elem)?;
                let fresh = self
                    .solver
                    .declare_const(&var_name, z4_dpll::api::Sort::Bool);
                // Bool equality: (fresh => val) /\ (val => fresh)
                let fwd = self.solver.try_implies(fresh, val_term)?;
                let bwd = self.solver.try_implies(val_term, fresh)?;
                let eq_both = self.solver.try_and(fwd, bwd)?;
                conjuncts.push(eq_both);
            }
        }

        self.build_conjunction(conjuncts)
    }

    /// Translate tuple indexing `t[i]` into the appropriate element term.
    ///
    /// Resolves the tuple variable and step, then looks up the element term.
    /// The index must be a constant integer literal.
    ///
    /// Part of #3787.
    pub(super) fn translate_tuple_index(
        &mut self,
        tuple_expr: &Spanned<Expr>,
        index_expr: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let (name, step) = self.resolve_tuple_var(tuple_expr)?;

        // Index must be a constant integer
        let index = match &index_expr.node {
            Expr::Int(n) => {
                let i: i64 = n.try_into().map_err(|_| {
                    Z4Error::IntegerOverflow(format!("tuple index {n} too large for i64"))
                })?;
                i as usize
            }
            _ => {
                return Err(Z4Error::UntranslatableExpr(
                    "BMC tuple indexing requires constant integer index".to_string(),
                ));
            }
        };

        self.get_tuple_element_at_step(&name, index, step)
    }

    // === UNCHANGED for record/tuple ===

    /// Translate UNCHANGED for a record variable.
    ///
    /// Produces: `r.a' = r.a /\ r.b' = r.b /\ ...` for all fields.
    ///
    /// Part of #3787.
    pub(super) fn translate_unchanged_record(&mut self, name: &str) -> Z4Result<Term> {
        let info = self
            .record_vars
            .get(name)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("record {name}")))?;

        let num_fields = info.field_sorts.len();
        let mut conjuncts = Vec::with_capacity(num_fields);

        for field_idx in 0..num_fields {
            let current = info.field_terms[field_idx][self.current_step];
            let next = info.field_terms[field_idx][self.current_step + 1];
            let eq = self.solver.try_eq(next, current)?;
            conjuncts.push(eq);
        }

        self.build_conjunction(conjuncts)
    }

    /// Translate UNCHANGED for a tuple variable.
    ///
    /// Produces: `t[1]' = t[1] /\ t[2]' = t[2] /\ ...` for all elements.
    ///
    /// Part of #3787.
    pub(super) fn translate_unchanged_tuple(&mut self, name: &str) -> Z4Result<Term> {
        let info = self
            .tuple_vars
            .get(name)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("tuple {name}")))?;

        let num_elements = info.element_sorts.len();
        let mut conjuncts = Vec::with_capacity(num_elements);

        for elem_idx in 0..num_elements {
            let current = info.element_terms[elem_idx][self.current_step];
            let next = info.element_terms[elem_idx][self.current_step + 1];
            let eq = self.solver.try_eq(next, current)?;
            conjuncts.push(eq);
        }

        self.build_conjunction(conjuncts)
    }

    // === Try-translate helpers for equality dispatch ===

    /// Try to translate record EXCEPT equality: `r' = [r EXCEPT !.a = v]`.
    ///
    /// Returns `None` if neither side involves a record EXCEPT.
    /// Returns `Some(result)` if record EXCEPT equality is detected.
    ///
    /// Part of #3787.
    pub(super) fn try_translate_record_except_eq(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Option<Z4Result<Term>> {
        if let Some(result) = self.try_translate_record_except_eq_directed(left, right) {
            return Some(result);
        }
        self.try_translate_record_except_eq_directed(right, left)
    }

    /// Try record EXCEPT equality in one direction:
    /// lhs is a (possibly primed) record variable, rhs is an EXCEPT expression.
    fn try_translate_record_except_eq_directed(
        &mut self,
        lhs: &Spanned<Expr>,
        rhs: &Spanned<Expr>,
    ) -> Option<Z4Result<Term>> {
        // rhs must be Except(base, specs) with a record variable base
        let (base, specs) = match &rhs.node {
            Expr::Except(base, specs) if self.is_record_var_expr(base) => {
                (base.as_ref(), specs.as_slice())
            }
            _ => return None,
        };

        // lhs must be a (possibly primed) record variable
        if !self.is_record_var_expr(lhs) {
            return None;
        }

        let target = match self.resolve_record_var(lhs) {
            Ok(r) => r,
            Err(e) => return Some(Err(e)),
        };
        let source = match self.resolve_record_var(base) {
            Ok(r) => r,
            Err(e) => return Some(Err(e)),
        };

        Some(self.translate_record_except_eq(&target, &source, specs))
    }

    /// Try to translate record field equality: `r' = [a |-> e1, b |-> e2]`
    /// or `r.field = expr` patterns.
    ///
    /// Returns `None` if neither side is record-related.
    ///
    /// Part of #3787.
    pub(super) fn try_translate_record_eq(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Option<Z4Result<Term>> {
        // Try: record_var = [a |-> e1, b |-> e2]
        if let Some(result) = self.try_translate_record_construct_eq(left, right) {
            return Some(result);
        }
        if let Some(result) = self.try_translate_record_construct_eq(right, left) {
            return Some(result);
        }

        // Try: record_var1 = record_var2
        if self.is_record_var_expr(left) && self.is_record_var_expr(right) {
            let l = match self.resolve_record_var(left) {
                Ok(r) => r,
                Err(e) => return Some(Err(e)),
            };
            let r = match self.resolve_record_var(right) {
                Ok(r) => r,
                Err(e) => return Some(Err(e)),
            };
            return Some(self.translate_record_var_eq(&l, &r));
        }

        None
    }

    /// Try record construction equality: lhs is a record var, rhs is Record literal.
    fn try_translate_record_construct_eq(
        &mut self,
        lhs: &Spanned<Expr>,
        rhs: &Spanned<Expr>,
    ) -> Option<Z4Result<Term>> {
        if !self.is_record_var_expr(lhs) {
            return None;
        }

        let fields = match &rhs.node {
            Expr::Record(fields) => fields,
            _ => return None,
        };

        let target = match self.resolve_record_var(lhs) {
            Ok(r) => r,
            Err(e) => return Some(Err(e)),
        };

        Some(self.translate_record_literal_eq(&target, fields))
    }

    /// Translate `target = [a |-> e1, b |-> e2]` as per-field equalities.
    fn translate_record_literal_eq(
        &mut self,
        target: &(String, usize),
        fields: &[(Spanned<String>, Spanned<Expr>)],
    ) -> Z4Result<Term> {
        let mut conjuncts = Vec::with_capacity(fields.len());

        for (field_name, value_expr) in fields {
            let target_term =
                self.get_record_field_at_step(&target.0, &field_name.node, target.1)?;

            // Determine field sort to choose Int or Bool translation
            let field_sort = self
                .record_vars
                .get(&target.0)
                .and_then(|info| {
                    info.field_sorts
                        .iter()
                        .find(|(n, _)| n == &field_name.node)
                        .map(|(_, s)| s.clone())
                })
                .unwrap_or(TlaSort::Int);

            let val_term = if field_sort == TlaSort::Bool {
                dispatch_translate_bool(self, value_expr)?
            } else {
                dispatch_translate_int(self, value_expr)?
            };

            let eq = self.solver.try_eq(target_term, val_term)?;
            conjuncts.push(eq);
        }

        self.build_conjunction(conjuncts)
    }

    /// Translate equality between two record variables: all fields must match.
    fn translate_record_var_eq(
        &mut self,
        lhs: &(String, usize),
        rhs: &(String, usize),
    ) -> Z4Result<Term> {
        let info = self
            .record_vars
            .get(&lhs.0)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("record {}", lhs.0)))?;

        let field_names: Vec<String> = info.field_sorts.iter().map(|(n, _)| n.clone()).collect();
        let mut conjuncts = Vec::with_capacity(field_names.len());

        for field_name in &field_names {
            let l_term = self.get_record_field_at_step(&lhs.0, field_name, lhs.1)?;
            let r_term = self.get_record_field_at_step(&rhs.0, field_name, rhs.1)?;
            let eq = self.solver.try_eq(l_term, r_term)?;
            conjuncts.push(eq);
        }

        self.build_conjunction(conjuncts)
    }

    // === Tuple equality dispatch ===

    /// Try to translate tuple equality: `t' = <<e1, e2>>` or `t = t'`.
    ///
    /// Part of #3787.
    pub(super) fn try_translate_tuple_eq(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Option<Z4Result<Term>> {
        // Try: tuple_var = <<e1, e2>>
        if let Some(result) = self.try_translate_tuple_literal_eq(left, right) {
            return Some(result);
        }
        if let Some(result) = self.try_translate_tuple_literal_eq(right, left) {
            return Some(result);
        }

        // Try: tuple_var1 = tuple_var2
        if self.is_tuple_var_expr(left) && self.is_tuple_var_expr(right) {
            let l = match self.resolve_tuple_var(left) {
                Ok(r) => r,
                Err(e) => return Some(Err(e)),
            };
            let r = match self.resolve_tuple_var(right) {
                Ok(r) => r,
                Err(e) => return Some(Err(e)),
            };
            return Some(self.translate_tuple_var_eq(&l, &r));
        }

        None
    }

    /// Try tuple literal equality: lhs is tuple var, rhs is Tuple literal.
    fn try_translate_tuple_literal_eq(
        &mut self,
        lhs: &Spanned<Expr>,
        rhs: &Spanned<Expr>,
    ) -> Option<Z4Result<Term>> {
        if !self.is_tuple_var_expr(lhs) {
            return None;
        }

        let elements = match &rhs.node {
            Expr::Tuple(elems) => elems,
            _ => return None,
        };

        let target = match self.resolve_tuple_var(lhs) {
            Ok(r) => r,
            Err(e) => return Some(Err(e)),
        };

        Some(self.translate_tuple_literal_eq(&target, elements))
    }

    /// Translate `target = <<e1, e2, e3>>` as per-element equalities.
    fn translate_tuple_literal_eq(
        &mut self,
        target: &(String, usize),
        elements: &[Spanned<Expr>],
    ) -> Z4Result<Term> {
        let mut conjuncts = Vec::with_capacity(elements.len());

        for (i, elem) in elements.iter().enumerate() {
            let index_1based = i + 1;
            let target_term = self.get_tuple_element_at_step(&target.0, index_1based, target.1)?;

            // Determine element sort
            let elem_sort = self
                .tuple_vars
                .get(&target.0)
                .and_then(|info| info.element_sorts.get(i).cloned())
                .unwrap_or(TlaSort::Int);

            let val_term = if elem_sort == TlaSort::Bool {
                dispatch_translate_bool(self, elem)?
            } else {
                dispatch_translate_int(self, elem)?
            };

            let eq = self.solver.try_eq(target_term, val_term)?;
            conjuncts.push(eq);
        }

        self.build_conjunction(conjuncts)
    }

    /// Translate equality between two tuple variables: all elements must match.
    fn translate_tuple_var_eq(
        &mut self,
        lhs: &(String, usize),
        rhs: &(String, usize),
    ) -> Z4Result<Term> {
        let info = self
            .tuple_vars
            .get(&lhs.0)
            .ok_or_else(|| Z4Error::UnknownVariable(format!("tuple {}", lhs.0)))?;

        let num_elems = info.element_sorts.len();
        let mut conjuncts = Vec::with_capacity(num_elems);

        for i in 0..num_elems {
            let l_term = self.get_tuple_element_at_step(&lhs.0, i + 1, lhs.1)?;
            let r_term = self.get_tuple_element_at_step(&rhs.0, i + 1, rhs.1)?;
            let eq = self.solver.try_eq(l_term, r_term)?;
            conjuncts.push(eq);
        }

        self.build_conjunction(conjuncts)
    }

    // === Shared helpers ===

    /// Build a conjunction from a list of terms.
    fn build_conjunction(&mut self, mut conjuncts: Vec<Term>) -> Z4Result<Term> {
        if conjuncts.is_empty() {
            return Ok(self.solver.bool_const(true));
        }
        if conjuncts.len() == 1 {
            return Ok(conjuncts.pop().expect("invariant: len checked == 1"));
        }
        let mut result = conjuncts.pop().expect("invariant: len checked > 1");
        for c in conjuncts.into_iter().rev() {
            result = self.solver.try_and(c, result)?;
        }
        Ok(result)
    }
}
