// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compound type expression dispatch for the z4 translator.
//!
//! Wires `FunctionEncoder`, `RecordEncoder`, and `FiniteSetEncoder` into the
//! main `translate_bool`/`translate_int` dispatch so that the translator can
//! handle expressions involving functions, records, and finite sets end-to-end.
//!
//! Part of #3778: wire compound type encoders into BMC expression translator.

use std::collections::HashMap;

use tla_core::ast::{ExceptPathElement, Expr};
use tla_core::Spanned;
use z4_dpll::api::{Sort, Term};

use crate::error::{Z4Error, Z4Result};

use super::finite_set::FiniteSetEncoder;
#[allow(unused_imports)]
use super::function_encoder::{FuncTerm, FunctionEncoder};
use super::record_encoder::RecordEncoder;
use super::{TlaSort, Z4Translator};

impl Z4Translator {
    // =========================================================================
    // Record construction: [a |-> 1, b |-> 2]
    // =========================================================================

    /// Translate record construction `[f1 |-> e1, ..., fn |-> en]` as a Bool
    /// constraint.
    ///
    /// Declares a fresh record variable, translates each field value, and
    /// returns the conjunction of field equalities. This is useful in
    /// BMC/CHC contexts where record construction appears in `Init` or
    /// `Next` constraints.
    pub(crate) fn translate_record_construct_bool(
        &mut self,
        fields: &[(Spanned<String>, Spanned<Expr>)],
    ) -> Z4Result<Term> {
        if fields.is_empty() {
            return Err(Z4Error::UnsupportedOp(
                "empty record construction not supported".to_string(),
            ));
        }

        // Infer field sorts from expressions
        let mut field_sorts = Vec::with_capacity(fields.len());
        let mut field_terms_map = HashMap::with_capacity(fields.len());

        for (name_spanned, value_expr) in fields {
            let field_name = &name_spanned.node;

            // Try Int first, then Bool, then String
            if let Ok(term) = self.translate_int(value_expr) {
                field_sorts.push((field_name.clone(), TlaSort::Int));
                field_terms_map.insert(field_name.clone(), term);
            } else if let Ok(term) = self.translate_bool(value_expr) {
                field_sorts.push((field_name.clone(), TlaSort::Bool));
                field_terms_map.insert(field_name.clone(), term);
            } else if let Ok(term) = self.translate_string(value_expr) {
                field_sorts.push((field_name.clone(), TlaSort::String));
                field_terms_map.insert(field_name.clone(), term);
            } else {
                return Err(Z4Error::UntranslatableExpr(format!(
                    "cannot translate record field '{field_name}' value"
                )));
            }
        }

        // Declare a fresh record variable
        let fresh_name = self.fresh_name("rec");
        self.declare_record_var(&fresh_name, field_sorts)?;

        let enc = RecordEncoder::new();
        enc.encode_record_construction(self, &fresh_name, &field_terms_map)
    }

    // =========================================================================
    // Tuple construction: <<e1, ..., en>>
    // =========================================================================

    /// Translate tuple construction `<<e1, ..., en>>` as a Bool constraint.
    ///
    /// Declares a fresh tuple variable, translates each element value, and
    /// returns the conjunction of element equalities via `RecordEncoder`.
    pub(crate) fn translate_tuple_construct_bool(
        &mut self,
        elements: &[Spanned<Expr>],
    ) -> Z4Result<Term> {
        if elements.is_empty() {
            return Err(Z4Error::UnsupportedOp(
                "empty tuple construction not supported".to_string(),
            ));
        }

        // Infer element sorts from expressions
        let mut element_sorts = Vec::with_capacity(elements.len());
        let mut element_terms = Vec::with_capacity(elements.len());

        for (i, value_expr) in elements.iter().enumerate() {
            // Try Int first, then Bool, then String
            if let Ok(term) = self.translate_int(value_expr) {
                element_sorts.push(TlaSort::Int);
                element_terms.push(term);
            } else if let Ok(term) = self.translate_bool(value_expr) {
                element_sorts.push(TlaSort::Bool);
                element_terms.push(term);
            } else if let Ok(term) = self.translate_string(value_expr) {
                element_sorts.push(TlaSort::String);
                element_terms.push(term);
            } else {
                return Err(Z4Error::UntranslatableExpr(format!(
                    "cannot translate tuple element {} value",
                    i + 1
                )));
            }
        }

        // Declare a fresh tuple variable
        let fresh_name = self.fresh_name("tup");
        self.declare_tuple_var(&fresh_name, element_sorts)?;

        let enc = RecordEncoder::new();
        enc.encode_tuple_construction(self, &fresh_name, &element_terms)
    }

    // =========================================================================
    // Function definition: [x \in S |-> expr]
    // =========================================================================

    /// Translate function definition `[x \in S |-> e(x)]` as a Bool constraint.
    ///
    /// For finite domain S, evaluates e(x) for each concrete domain element
    /// and builds an `FunctionEncoder::encode_func_def`. Returns `TRUE` after
    /// asserting the function constraints (the function is stored internally).
    ///
    /// This currently only supports single-variable bindings with finite
    /// enumerable domains.
    pub(crate) fn translate_func_def_bool(
        &mut self,
        bounds: &[tla_core::ast::BoundVar],
        body: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        if bounds.len() != 1 {
            return Err(Z4Error::UnsupportedOp(
                "multi-variable function definitions not yet supported in z4".to_string(),
            ));
        }

        let bound = &bounds[0];
        let domain = bound.domain.as_ref().ok_or_else(|| {
            Z4Error::UnsupportedOp(
                "function definition without domain not supported in z4".to_string(),
            )
        })?;

        // Extract finite domain elements
        let domain_elements = self.extract_set_enum_ints(domain)?;
        if domain_elements.is_empty() {
            // Empty domain function: return TRUE (trivially satisfied)
            return Ok(self.solver_mut().bool_const(true));
        }

        // For each domain element, substitute into body and translate.
        // Track whether body is Int-sorted or Bool-sorted from the first
        // successfully translated element, then enforce consistency.
        let bound_name = &bound.name.node;
        let mut dom_terms = Vec::with_capacity(domain_elements.len());
        let mut ran_terms = Vec::with_capacity(domain_elements.len());
        let mut range_sort: Option<Sort> = None;

        for &dom_val in &domain_elements {
            let dom_term = self.solver_mut().int_const(dom_val);
            dom_terms.push(dom_term);

            // Substitute bound variable with concrete value in body
            let subst_body = substitute_int_literal(body, bound_name, dom_val);
            // Try translating as Int first, then Bool, tracking the sort
            if let Ok(ran_term) = self.translate_int(&subst_body) {
                ran_terms.push(ran_term);
                if range_sort.is_none() {
                    range_sort = Some(Sort::Int);
                }
            } else if let Ok(ran_term) = self.translate_bool(&subst_body) {
                ran_terms.push(ran_term);
                if range_sort.is_none() {
                    range_sort = Some(Sort::Bool);
                }
            } else {
                return Err(Z4Error::UntranslatableExpr(format!(
                    "cannot translate function body at {bound_name}={dom_val}"
                )));
            }
        }

        // Use the inferred range sort, defaulting to Int for empty domains
        let range_sort = range_sort.unwrap_or(Sort::Int);

        let enc = FunctionEncoder::new(Sort::Int, range_sort);
        let func_term = enc.encode_func_def(self, &dom_terms, &ran_terms)?;

        // Store the array-encoded function for later retrieval by
        // function application, DOMAIN, EXCEPT, and equality operations.
        let func_name = self.fresh_name("funcdef");
        self.store_array_func(&func_name, func_term);

        Ok(self.solver_mut().bool_const(true))
    }

    // =========================================================================
    // Domain: DOMAIN f
    // =========================================================================

    /// Translate `DOMAIN f` as a Bool-context expression.
    ///
    /// DOMAIN is set-valued, so in Bool context we return an error with
    /// guidance to use membership tests (`x \in DOMAIN f`). However, for
    /// records and tuples, `translate_record_or_tuple_domain` provides the
    /// domain elements for membership dispatch.
    ///
    /// Part of #3787: record/tuple DOMAIN support.
    pub(crate) fn translate_domain_bool(&mut self, func_expr: &Spanned<Expr>) -> Z4Result<Term> {
        // DOMAIN is typically used in set membership context (x \in DOMAIN f)
        // which is handled by the membership dispatch. When used standalone
        // as a Bool expression, return an error with a helpful message.
        let name = match &func_expr.node {
            Expr::Ident(name, _) => name.clone(),
            _ => {
                return Err(Z4Error::UnsupportedOp(
                    "DOMAIN on non-variable expression not supported in z4".to_string(),
                ))
            }
        };

        if self.func_vars.contains_key(&name)
            || self.record_vars.contains_key(&name)
            || self.tuple_vars.contains_key(&name)
        {
            // DOMAIN is a set, not a Bool. Guide users to membership context.
            Err(Z4Error::UntranslatableExpr(
                "DOMAIN f is a set, not a Bool expression; \
                 use `x \\in DOMAIN f` for membership tests"
                    .to_string(),
            ))
        } else {
            Err(Z4Error::UnknownVariable(format!(
                "DOMAIN {name}: not a declared function, record, or tuple variable"
            )))
        }
    }

    // =========================================================================
    // EXCEPT: [f EXCEPT ![a] = b, ![c] = d]
    // =========================================================================

    /// Translate `[f EXCEPT ![a] = b]` as a Bool constraint.
    ///
    /// For per-variable functions, creates a fresh function variable with
    /// the updated value. For record EXCEPT (`.field`), delegates to
    /// `RecordEncoder`.
    pub(crate) fn translate_except_bool(
        &mut self,
        base: &Spanned<Expr>,
        specs: &[tla_core::ast::ExceptSpec],
    ) -> Z4Result<Term> {
        if specs.is_empty() {
            // No-op EXCEPT: [f EXCEPT ] = f — trivially true
            return Ok(self.solver_mut().bool_const(true));
        }

        let base_name = match &base.node {
            Expr::Ident(name, _) => name.clone(),
            _ => {
                return Err(Z4Error::UnsupportedOp(
                    "EXCEPT on non-variable base not supported in z4".to_string(),
                ))
            }
        };

        // Determine whether this is a record EXCEPT or function EXCEPT
        let first_path = &specs[0].path;
        if first_path.is_empty() {
            return Err(Z4Error::UnsupportedOp(
                "EXCEPT with empty path not supported".to_string(),
            ));
        }

        match &first_path[0] {
            ExceptPathElement::Field(field_name) => {
                // Record EXCEPT: [r EXCEPT !.field = e]
                self.translate_record_except_bool(&base_name, specs, field_name)
            }
            ExceptPathElement::Index(_) => {
                // Function EXCEPT: [f EXCEPT ![a] = b]
                self.translate_func_except_bool(&base_name, specs)
            }
        }
    }

    /// Translate record EXCEPT `[r EXCEPT !.field = e]`.
    fn translate_record_except_bool(
        &mut self,
        base_name: &str,
        specs: &[tla_core::ast::ExceptSpec],
        _first_field: &tla_core::ast::RecordFieldName,
    ) -> Z4Result<Term> {
        if !self.record_vars.contains_key(base_name) {
            return Err(Z4Error::UnknownVariable(format!(
                "'{base_name}' is not a declared record variable"
            )));
        }

        // For each EXCEPT spec, we need to create a new record
        // For simplicity, handle single-field EXCEPT
        if specs.len() != 1 || specs[0].path.len() != 1 {
            return Err(Z4Error::UnsupportedOp(
                "multi-field or nested record EXCEPT not yet supported in z4".to_string(),
            ));
        }

        let spec = &specs[0];
        let field_name = match &spec.path[0] {
            ExceptPathElement::Field(f) => f.name.node.clone(),
            _ => {
                return Err(Z4Error::UnsupportedOp(
                    "expected field path in record EXCEPT".to_string(),
                ))
            }
        };

        // Translate the new value
        let new_value = self
            .translate_int(&spec.value)
            .or_else(|_| self.translate_bool(&spec.value))
            .or_else(|_| self.translate_string(&spec.value))?;

        // Declare a fresh target record
        let enc = RecordEncoder::new();
        let target_name = enc.declare_fresh_record(self, "except_rec", base_name)?;

        enc.encode_record_except(self, base_name, &target_name, &field_name, new_value)
    }

    /// Translate function EXCEPT `[f EXCEPT ![a] = b]`.
    fn translate_func_except_bool(
        &mut self,
        base_name: &str,
        specs: &[tla_core::ast::ExceptSpec],
    ) -> Z4Result<Term> {
        if !self.func_vars.contains_key(base_name) {
            return Err(Z4Error::UnknownVariable(format!(
                "'{base_name}' is not a declared function variable"
            )));
        }

        let info = self
            .func_vars
            .get(base_name)
            .cloned()
            .ok_or_else(|| Z4Error::UnknownVariable(format!("function {base_name}")))?;

        // Build constraints: for each EXCEPT spec, update the corresponding element.
        // For per-variable functions, the "EXCEPT" creates equality constraints
        // on a fresh set of variables.
        let fresh_prefix = self.fresh_name("except_func");
        self.declare_func_var(
            &fresh_prefix,
            info.domain_keys.clone(),
            info.range_sort.clone(),
        )?;

        let new_info = self
            .func_vars
            .get(&fresh_prefix)
            .cloned()
            .ok_or_else(|| Z4Error::UnknownVariable(format!("function {fresh_prefix}")))?;

        // Start with all elements equal to the original
        let mut conjuncts = Vec::new();
        let mut updated_keys = std::collections::HashSet::new();

        for spec in specs {
            if spec.path.len() != 1 {
                return Err(Z4Error::UnsupportedOp(
                    "nested function EXCEPT paths not supported in z4".to_string(),
                ));
            }
            let key = match &spec.path[0] {
                ExceptPathElement::Index(idx) => self.try_expr_to_key_static(idx)?,
                ExceptPathElement::Field(_) => {
                    return Err(Z4Error::UnsupportedOp(
                        "mixed field/index EXCEPT paths not supported".to_string(),
                    ))
                }
            };

            // Translate the new value
            let new_val = self
                .translate_int(&spec.value)
                .or_else(|_| self.translate_bool(&spec.value))?;

            // Assert new_func__key = new_value
            if let Some(&new_term) = new_info.element_terms.get(&key) {
                let eq = self.solver_mut().try_eq(new_term, new_val)?;
                conjuncts.push(eq);
                updated_keys.insert(key);
            } else {
                return Err(Z4Error::UnknownVariable(format!("{fresh_prefix}[{key}]")));
            }
        }

        // For keys not updated, assert new_func__key = old_func__key
        for key in &info.domain_keys {
            if !updated_keys.contains(key) {
                let old_term = info
                    .element_terms
                    .get(key)
                    .copied()
                    .ok_or_else(|| Z4Error::UnknownVariable(format!("{base_name}[{key}]")))?;
                let new_term =
                    new_info.element_terms.get(key).copied().ok_or_else(|| {
                        Z4Error::UnknownVariable(format!("{fresh_prefix}[{key}]"))
                    })?;
                let eq = self.solver_mut().try_eq(new_term, old_term)?;
                conjuncts.push(eq);
            }
        }

        // Return conjunction of all constraints
        if conjuncts.is_empty() {
            return Ok(self.solver_mut().bool_const(true));
        }
        let mut result = conjuncts[0];
        for &c in &conjuncts[1..] {
            result = self.solver_mut().try_and(result, c)?;
        }
        Ok(result)
    }

    // =========================================================================
    // Function equality: f = g (per-variable path)
    // =========================================================================

    /// Try to translate equality as function equality.
    ///
    /// If both sides reference per-variable functions (`func_vars`), returns
    /// `Some(term)` with a conjunction of `f__key = g__key` for all domain keys.
    /// If both sides reference array-encoded functions (`array_func_vars`),
    /// delegates to `FunctionEncoder::encode_func_eq`.
    /// Otherwise returns `None` so the caller can try other equality strategies.
    ///
    /// Part of #3786: Function encoding — equality.
    pub(crate) fn try_translate_func_equality(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Z4Result<Option<Term>> {
        let (left_name, right_name) = match (&left.node, &right.node) {
            (Expr::Ident(l, _), Expr::Ident(r, _)) => (l.clone(), r.clone()),
            _ => return Ok(None),
        };

        // Per-variable function path
        if self.func_vars.contains_key(&left_name) && self.func_vars.contains_key(&right_name) {
            let f_info = self
                .func_vars
                .get(&left_name)
                .cloned()
                .ok_or_else(|| Z4Error::UnknownVariable(format!("function {left_name}")))?;
            let g_info = self
                .func_vars
                .get(&right_name)
                .cloned()
                .ok_or_else(|| Z4Error::UnknownVariable(format!("function {right_name}")))?;

            // Domain keys must match
            if f_info.domain_keys != g_info.domain_keys {
                return Ok(Some(self.solver_mut().bool_const(false)));
            }

            let mut conjuncts = Vec::with_capacity(f_info.domain_keys.len());
            for key in &f_info.domain_keys {
                let f_term = f_info
                    .element_terms
                    .get(key)
                    .copied()
                    .ok_or_else(|| Z4Error::UnknownVariable(format!("{left_name}[{key}]")))?;
                let g_term = g_info
                    .element_terms
                    .get(key)
                    .copied()
                    .ok_or_else(|| Z4Error::UnknownVariable(format!("{right_name}[{key}]")))?;
                conjuncts.push(self.solver_mut().try_eq(f_term, g_term)?);
            }

            if conjuncts.is_empty() {
                return Ok(Some(self.solver_mut().bool_const(true)));
            }
            let mut result = conjuncts[0];
            for &c in &conjuncts[1..] {
                result = self.solver_mut().try_and(result, c)?;
            }
            return Ok(Some(result));
        }

        // Array-encoded function path
        if let (Some(f_term), Some(g_term)) = (
            self.get_array_func(&left_name).copied(),
            self.get_array_func(&right_name).copied(),
        ) {
            // We need a universe for pointwise comparison.
            // Use a conservative empty universe (domain equality only) when
            // the concrete domain is unknown.
            let enc = FunctionEncoder::new(Sort::Int, Sort::Int);
            let eq = enc.encode_func_eq(self, &f_term, &g_term, &[])?;
            return Ok(Some(eq));
        }

        Ok(None)
    }

    // =========================================================================
    // Finite set enumeration as SMT array terms
    // =========================================================================

    /// Translate `{e1, ..., en}` to an SMT array set term.
    ///
    /// Uses `FiniteSetEncoder` to build an `(Array Int Bool)` term.
    /// This is for contexts where a set is needed as a first-class term
    /// (e.g., set variable constraints), not membership testing.
    pub(crate) fn translate_set_enum_term(&mut self, elements: &[Spanned<Expr>]) -> Z4Result<Term> {
        let enc = FiniteSetEncoder::new();

        if elements.is_empty() {
            return enc.empty_set(self);
        }

        let mut elem_terms = Vec::with_capacity(elements.len());
        for e in elements {
            let term = self.translate_int(e).or_else(|_| {
                // Try string (interned as Int)
                self.translate_string(e)
            })?;
            elem_terms.push(term);
        }

        enc.encode_set_enum(self, &elem_terms)
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    /// Extract integer values from a set enumeration expression.
    ///
    /// Returns `Err` if the set contains non-integer literals.
    fn extract_set_enum_ints(&self, set: &Spanned<Expr>) -> Z4Result<Vec<i64>> {
        match &set.node {
            Expr::SetEnum(elements) => {
                let mut vals = Vec::with_capacity(elements.len());
                for e in elements {
                    match &e.node {
                        Expr::Int(n) => {
                            let v: i64 = n.try_into().map_err(|_| {
                                Z4Error::IntegerOverflow(
                                    "set element too large for i64".to_string(),
                                )
                            })?;
                            vals.push(v);
                        }
                        _ => {
                            return Err(Z4Error::UnsupportedOp(
                                "non-integer set elements in function domain \
                                 not yet supported in z4"
                                    .to_string(),
                            ))
                        }
                    }
                }
                Ok(vals)
            }
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
                Ok((lo_val..=hi_val).collect())
            }
            _ => Err(Z4Error::UnsupportedOp(format!(
                "cannot extract integer set from expression: {}",
                super::extended_ops::expr_variant_name(&set.node)
            ))),
        }
    }

    // =========================================================================
    // Subseteq, Cardinality, Powerset, BigUnion (Apalache parity)
    // =========================================================================

    /// Translate `S \subseteq T` as a Bool constraint.
    ///
    /// For finite sets with known universe elements, expands pointwise:
    /// `\A u \in universe : S(u) => T(u)`
    ///
    /// Falls back to a syntactic extraction of universe elements from the set
    /// expressions.
    pub(super) fn translate_subseteq_bool(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        let enc = FiniteSetEncoder::new();

        // Translate both sides as set terms
        let set_s = self.translate_set_expr_term(left)?;
        let set_t = self.translate_set_expr_term(right)?;

        // Extract universe from both set expressions
        let universe = self.extract_universe_terms(&[left, right])?;

        enc.encode_subseteq(self, set_s, set_t, &universe)
    }

    /// Translate `Cardinality(S)` as an Int term.
    ///
    /// Encodes as `sum of ite(S[u], 1, 0)` over the universe extracted from S.
    pub(super) fn translate_cardinality_int(&mut self, set_expr: &Spanned<Expr>) -> Z4Result<Term> {
        let enc = FiniteSetEncoder::new();

        let set_term = self.translate_set_expr_term(set_expr)?;
        let universe = self.extract_universe_terms(&[set_expr])?;

        enc.encode_cardinality(self, set_term, &universe)
    }

    /// Translate a set expression to an SMT array term.
    ///
    /// Handles:
    /// - `SetEnum`: `{e1, ..., en}` -> array store chain
    /// - `Union`: `S \cup T` -> pointwise OR
    /// - `Intersect`: `S \cap T` -> pointwise AND
    /// - `SetMinus`: `S \ T` -> pointwise AND-NOT
    /// - `Powerset`: `SUBSET S` -> not directly a set term (use in membership)
    /// - `BigUnion`: `UNION S` -> pointwise OR over component sets
    /// - `Ident`: resolve from constant_defs
    pub(crate) fn translate_set_expr_term(&mut self, expr: &Spanned<Expr>) -> Z4Result<Term> {
        match &expr.node {
            Expr::SetEnum(elements) => self.translate_set_enum_term(elements),

            Expr::Union(left, right) => {
                let enc = FiniteSetEncoder::new();
                let set_s = self.translate_set_expr_term(left)?;
                let set_t = self.translate_set_expr_term(right)?;
                let universe = self.extract_universe_terms(&[left, right])?;
                enc.encode_union(self, set_s, set_t, &universe)
            }

            Expr::Intersect(left, right) => {
                let enc = FiniteSetEncoder::new();
                let set_s = self.translate_set_expr_term(left)?;
                let set_t = self.translate_set_expr_term(right)?;
                let universe = self.extract_universe_terms(&[left, right])?;
                enc.encode_intersect(self, set_s, set_t, &universe)
            }

            Expr::SetMinus(left, right) => {
                let enc = FiniteSetEncoder::new();
                let set_s = self.translate_set_expr_term(left)?;
                let set_t = self.translate_set_expr_term(right)?;
                let universe = self.extract_universe_terms(&[left, right])?;
                enc.encode_set_minus(self, set_s, set_t, &universe)
            }

            Expr::BigUnion(inner) => {
                // UNION S where S is a set of sets.
                // Currently only support S = {T1, T2, ...} (set enumeration of sets)
                match &inner.node {
                    Expr::SetEnum(component_exprs) => {
                        use super::powerset_encoder::PowersetEncoder;
                        let penc = PowersetEncoder::new();

                        let mut component_terms = Vec::with_capacity(component_exprs.len());
                        for comp in component_exprs {
                            component_terms.push(self.translate_set_expr_term(comp)?);
                        }

                        // Collect universe from all component sets
                        let comp_refs: Vec<&Spanned<Expr>> = component_exprs.iter().collect();
                        let universe = self.extract_universe_terms(&comp_refs)?;

                        penc.encode_generalized_union(self, &component_terms, &universe)
                    }
                    _ => Err(Z4Error::UnsupportedOp(
                        "UNION over non-enumerated set-of-sets not supported in z4; \
                         only UNION {S1, S2, ...} is supported"
                            .to_string(),
                    )),
                }
            }

            Expr::Range(lo, hi) => {
                // lo..hi as a set: store each element
                let lo_val = self.extract_int_literal(lo)?;
                let hi_val = self.extract_int_literal(hi)?;
                let enc = FiniteSetEncoder::new();
                let mut elem_terms = Vec::new();
                for v in lo_val..=hi_val {
                    elem_terms.push(self.solver_mut().int_const(v));
                }
                enc.encode_set_enum(self, &elem_terms)
            }

            Expr::Ident(name, _) => {
                if let Some(def) = self.constant_defs.get(name).cloned() {
                    self.translate_set_expr_term(&def)
                } else {
                    Err(Z4Error::UnsupportedOp(format!(
                        "unknown set identifier '{name}' in set expression context"
                    )))
                }
            }

            _ => Err(Z4Error::UnsupportedOp(format!(
                "cannot translate {} as a set term",
                super::extended_ops::expr_variant_name(&expr.node)
            ))),
        }
    }

    /// Extract a bounded universe of Int terms from set expressions.
    ///
    /// For finite sets like `{1, 2, 3}` or `1..5`, extracts the concrete
    /// elements. For compound sets (union, intersect, etc.), recursively
    /// extracts from subexpressions and deduplicates.
    fn extract_universe_terms(&mut self, set_exprs: &[&Spanned<Expr>]) -> Z4Result<Vec<Term>> {
        let mut values = std::collections::BTreeSet::new();
        for expr in set_exprs {
            self.collect_universe_values(expr, &mut values)?;
        }
        Ok(values
            .into_iter()
            .map(|v| self.solver_mut().int_const(v))
            .collect())
    }

    /// Recursively collect all integer values that could appear in a set expression.
    pub(crate) fn collect_universe_values(
        &self,
        expr: &Spanned<Expr>,
        values: &mut std::collections::BTreeSet<i64>,
    ) -> Z4Result<()> {
        match &expr.node {
            Expr::SetEnum(elements) => {
                for e in elements {
                    if let Ok(v) = self.extract_int_literal(e) {
                        values.insert(v);
                    }
                    // For non-literal elements (e.g., set-of-sets), skip
                }
            }
            Expr::Range(lo, hi) => {
                let lo_val = self.extract_int_literal(lo)?;
                let hi_val = self.extract_int_literal(hi)?;
                for v in lo_val..=hi_val {
                    values.insert(v);
                }
            }
            Expr::Union(left, right)
            | Expr::Intersect(left, right)
            | Expr::SetMinus(left, right)
            | Expr::Subseteq(left, right) => {
                self.collect_universe_values(left, values)?;
                self.collect_universe_values(right, values)?;
            }
            Expr::BigUnion(inner) => {
                if let Expr::SetEnum(components) = &inner.node {
                    for comp in components {
                        self.collect_universe_values(comp, values)?;
                    }
                }
            }
            Expr::Powerset(base) => {
                self.collect_universe_values(base, values)?;
            }
            Expr::Ident(name, _) => {
                if let Some(def) = self.constant_defs.get(name).cloned() {
                    self.collect_universe_values(&def, values)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Extract an integer literal from an expression.
    pub(super) fn extract_int_literal(&self, expr: &Spanned<Expr>) -> Z4Result<i64> {
        match &expr.node {
            Expr::Int(n) => n.try_into().map_err(|_| {
                Z4Error::IntegerOverflow("integer literal too large for i64".to_string())
            }),
            Expr::Neg(inner) => {
                let v = self.extract_int_literal(inner)?;
                Ok(-v)
            }
            _ => Err(Z4Error::UnsupportedOp(format!(
                "expected integer literal, got {}",
                super::extended_ops::expr_variant_name(&expr.node)
            ))),
        }
    }

    /// Try to extract a string key from an expression (static, no translation).
    fn try_expr_to_key_static(&self, expr: &Spanned<Expr>) -> Z4Result<String> {
        match &expr.node {
            Expr::Int(n) => Ok(n.to_string()),
            Expr::Bool(b) => Ok(b.to_string()),
            Expr::String(s) => Ok(s.clone()),
            Expr::Ident(name, _) => Ok(name.clone()),
            _ => Err(Z4Error::UnsupportedOp(format!(
                "cannot extract key from expression: {}",
                super::extended_ops::expr_variant_name(&expr.node)
            ))),
        }
    }
}

/// Substitute a bound variable with an integer literal in an expression.
///
/// This is a simple syntactic substitution used for function definition
/// evaluation over finite domains.
fn substitute_int_literal(expr: &Spanned<Expr>, var_name: &str, value: i64) -> Spanned<Expr> {
    let replacement = Spanned::new(Expr::Int(num_bigint::BigInt::from(value)), expr.span);

    let mut sub = tla_core::SubstituteExpr {
        subs: std::collections::HashMap::from([(var_name, &replacement)]),
        span_policy: tla_core::SpanPolicy::Preserve,
    };
    tla_core::ExprFold::fold_expr(&mut sub, expr.clone())
}
