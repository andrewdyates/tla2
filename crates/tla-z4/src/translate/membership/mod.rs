// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Set membership, function application, and domain helpers for Z4 translation.
//!
//! Handles:
//! - Set membership testing (`x \in S`) for built-in sets, enumerations, ranges, etc.
//! - Function application (`f[x]`) via ITE chains over finite domains
//! - Function set membership (`f \in [D -> R]`)
//! - Finite domain extraction and range sort inference

use std::collections::HashMap;

use tla_core::ast::Expr;
use tla_core::Spanned;
use tla_core::{ExprFold, SpanPolicy, SubstituteExpr};
use z4_dpll::api::Term;

use crate::error::{Z4Error, Z4Result};

use super::{FunctionVarInfo, TlaSort, Z4Translator};

mod apply;
mod function_sets;

impl Z4Translator {
    /// Translate set membership: x \in S
    pub(super) fn translate_membership(
        &mut self,
        elem: &Spanned<Expr>,
        set: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        match &set.node {
            // Built-in sets with simple typing constraints.
            //
            // Note: Some of these are tautologies (e.g. `b \in BOOLEAN`), but we still build a
            // term that references `elem` so z4 assigns it in the model. This matters for
            // enumeration via repeated SAT + blocking clauses.
            Expr::Ident(name, _) if name == "BOOLEAN" => match self.translate_bool(elem) {
                Ok(b) => {
                    let t = self.solver.bool_const(true);
                    let f = self.solver.bool_const(false);
                    let is_true = self.solver.try_eq(b, t)?;
                    let is_false = self.solver.try_eq(b, f)?;
                    Ok(self.solver.try_or(is_true, is_false)?)
                }
                Err(Z4Error::TypeMismatch { .. }) => Ok(self.solver.bool_const(false)),
                Err(e) => Err(e),
            },
            Expr::Ident(name, _) if name == "Int" => match self.translate_int(elem) {
                Ok(i) => Ok(self.solver.try_eq(i, i)?),
                Err(Z4Error::TypeMismatch { .. }) => Ok(self.solver.bool_const(false)),
                Err(e) => Err(e),
            },
            Expr::Ident(name, _) if name == "Nat" => match self.translate_int(elem) {
                Ok(i) => {
                    let zero = self.solver.int_const(0);
                    Ok(self.solver.try_ge(i, zero)?)
                }
                Err(Z4Error::TypeMismatch { .. }) => Ok(self.solver.bool_const(false)),
                Err(e) => Err(e),
            },

            // Part of #522: Resolve Ident references to constant definitions.
            // When `x \in DRINKS` where DRINKS is a named constant, look up
            // its definition and translate that instead.
            Expr::Ident(name, _) => {
                if let Some(def) = self.constant_defs.get(name).cloned() {
                    // Check for circular definitions (A == B, B == A)
                    if self.resolving_constants.contains(name) {
                        return Err(Z4Error::UnsupportedOp(format!(
                            "circular constant definition detected for '{name}'"
                        )));
                    }
                    // Track that we're resolving this constant
                    self.resolving_constants.insert(name.clone());
                    // Recursively translate membership with the resolved definition
                    let result = self.translate_membership(elem, &def);
                    // Remove from tracking after resolution completes
                    self.resolving_constants.remove(name);
                    result
                } else {
                    Err(Z4Error::UnsupportedOp(format!(
                        "unknown set reference '{name}' - not a built-in set or constant definition"
                    )))
                }
            }

            // Finite set enumeration: x \in {a, b, c} => (x = a) \/ (x = b) \/ (x = c)
            Expr::SetEnum(elements) => {
                if elements.is_empty() {
                    // x \in {} is always false
                    return Ok(self.solver.bool_const(false));
                }

                // Check if set contains tuples (first element is a Tuple)
                let is_tuple_set = matches!(&elements[0].node, Expr::Tuple(_));

                if is_tuple_set {
                    // Tuple membership: t \in {<<a,b>>, <<c,d>>} => (t = <<a,b>>) \/ (t = <<c,d>>)
                    let mut disjuncts = Vec::new();
                    for e in elements {
                        // Create equality expression: elem = e
                        let eq_expr = Spanned::new(
                            Expr::Eq(Box::new(elem.clone()), Box::new(e.clone())),
                            elem.span,
                        );
                        // Use translate_bool which now handles tuple equality
                        let eq_term = self.translate_bool(&eq_expr)?;
                        disjuncts.push(eq_term);
                    }
                    // Build OR of all disjuncts
                    let mut result = disjuncts[0];
                    for d in &disjuncts[1..] {
                        result = self.solver.try_or(result, *d)?;
                    }
                    Ok(result)
                } else {
                    // Scalar membership: x \in {a, b, c} with int/string/bool elements

                    // Optimization: if all elements are integer literals forming a
                    // contiguous range, use bounds (min <= x /\ x <= max) instead of
                    // disjunctions. This avoids z4 QF_LIA incompleteness on
                    // disjunctions of integer equalities (Part of #1622).
                    if let Some((min_val, max_val)) =
                        Self::try_extract_contiguous_int_range(elements)
                    {
                        // Cross-type: if elem isn't an int, it can't be in an int set
                        match self.translate_int(elem) {
                            Ok(elem_term) => {
                                let lo = self.solver.int_const(min_val);
                                let hi = self.solver.int_const(max_val);
                                let ge_lo = self.solver.try_ge(elem_term, lo)?;
                                let le_hi = self.solver.try_le(elem_term, hi)?;
                                return Ok(self.solver.try_and(ge_lo, le_hi)?);
                            }
                            Err(_) => return Ok(self.solver.bool_const(false)),
                        }
                    }

                    let elem_type = self.infer_scalar_type(elem);

                    let mut disjuncts = Vec::new();
                    for e in elements {
                        let e_type = self.infer_scalar_type(e);

                        // Check for type mismatch
                        let is_type_match = match (&elem_type, &e_type) {
                            (Some(et), Some(ft)) => {
                                std::mem::discriminant(et) == std::mem::discriminant(ft)
                            }
                            // If we can't infer types, fall back to same translation path
                            _ => true,
                        };

                        if is_type_match {
                            // Same type: translate and compare
                            let elem_term = self
                                .translate_int(elem)
                                .or_else(|_| self.translate_string(elem))
                                .or_else(|_| self.translate_bool(elem))?;
                            let e_term = self
                                .translate_int(e)
                                .or_else(|_| self.translate_string(e))
                                .or_else(|_| self.translate_bool(e))?;
                            disjuncts.push(self.solver.try_eq(elem_term, e_term)?);
                        }
                        // Cross-type: element contributes FALSE, but FALSE \/ x = x,
                        // so we just skip adding it to avoid unnecessary terms
                    }

                    // If no same-type elements found, elem can't be a member
                    if disjuncts.is_empty() {
                        return Ok(self.solver.bool_const(false));
                    }

                    // Build OR of all disjuncts
                    let mut result = disjuncts[0];
                    for d in &disjuncts[1..] {
                        result = self.solver.try_or(result, *d)?;
                    }
                    Ok(result)
                }
            }

            // Range: x \in lo..hi => (x >= lo) /\ (x <= hi)
            Expr::Range(lo, hi) => {
                let x = self.translate_int(elem)?;
                let lo_term = self.translate_int(lo)?;
                let hi_term = self.translate_int(hi)?;
                let ge_lo = self.solver.try_ge(x, lo_term)?;
                let le_hi = self.solver.try_le(x, hi_term)?;
                Ok(self.solver.try_and(ge_lo, le_hi)?)
            }

            // Function set: f \in [D -> R] for finite domain D
            Expr::FuncSet(domain, range) => self.translate_func_set_membership(elem, domain, range),

            // Set filter: elem \in {x \in S : P(x)} => (elem \in S) /\ P[elem/x]
            Expr::SetFilter(bound, pred) => {
                // Get the domain from the bound variable
                let domain = bound.domain.as_ref().ok_or_else(|| {
                    Z4Error::UnsupportedOp("SetFilter without domain not supported".to_string())
                })?;

                // Translate: elem \in S
                let in_domain = self.translate_membership(elem, domain)?;

                // Substitute elem for the bound variable in the predicate
                let bound_name = &bound.name.node;
                let mut sub = SubstituteExpr {
                    subs: HashMap::from([(bound_name.as_str(), elem)]),
                    span_policy: SpanPolicy::Preserve,
                };
                let pred_subst = sub.fold_expr(*pred.clone());
                let pred_term = self.translate_bool(&pred_subst)?;

                // Return: (elem \in S) /\ P[elem/x]
                Ok(self.solver.try_and(in_domain, pred_term)?)
            }

            // Set builder: elem \in {f(x) : x \in S} => \E x \in S : elem = f(x)
            Expr::SetBuilder(body, bounds) => {
                // Build: \E bounds : elem = body
                let eq_body = Expr::Eq(Box::new(elem.clone()), body.clone());
                let exists =
                    Expr::Exists(bounds.clone(), Box::new(Spanned::new(eq_body, set.span)));
                self.translate_bool(&Spanned::new(exists, set.span))
            }

            // Part of Apalache parity: elem \in SUBSET S
            // Membership in powerset: elem is a set, so encode as subset constraint.
            Expr::Powerset(base) => {
                let base_term = self.translate_set_expr_term(base)?;
                let elem_term = self.translate_set_expr_term(elem)?;
                let mut universe_values = std::collections::BTreeSet::new();
                self.collect_universe_values(base, &mut universe_values)?;
                let universe: Vec<_> = universe_values
                    .into_iter()
                    .map(|v| self.solver.int_const(v))
                    .collect();
                use super::powerset_encoder::PowersetEncoder;
                let penc = PowersetEncoder::new();
                penc.encode_powerset_membership(self, elem_term, base_term, &universe)
            }

            // Part of Apalache parity: elem \in (S \cup T), elem \in (S \cap T), elem \in (S \ T)
            // Translate the compound set to an SMT array term and check membership via select.
            Expr::Union(_, _) | Expr::Intersect(_, _) | Expr::SetMinus(_, _) => {
                let set_term = self.translate_set_expr_term(set)?;
                let elem_int = self.translate_int(elem)?;
                let enc = super::finite_set::FiniteSetEncoder::new();
                enc.encode_membership(self, elem_int, set_term)
            }

            // Part of #3787: x \in DOMAIN r (record/tuple/function domains)
            //
            // For records, DOMAIN returns the set of interned field name strings.
            // For tuples, DOMAIN returns {1, ..., n}.
            // For functions, DOMAIN returns the finite domain key set.
            Expr::Domain(func_expr) => {
                // Try record/tuple domain first
                if let Some(domain_ids) = self.translate_record_or_tuple_domain(func_expr)? {
                    let elem_term = self.translate_int(elem)?;
                    return build_finite_membership(self, elem_term, &domain_ids);
                }

                // Fall back to per-variable function domain
                if let Expr::Ident(name, _) = &func_expr.node {
                    if let Some(info) = self.func_vars.get(name).cloned() {
                        let elem_str = self.try_expr_to_key_static_opt(elem);
                        if let Some(key) = elem_str {
                            // Static key: check if key is in domain
                            let is_member = info.domain_keys.contains(&key);
                            return Ok(self.solver.bool_const(is_member));
                        }
                        // Dynamic key: build disjunction over domain keys
                        let elem_term = self.translate_int(elem)?;
                        let mut domain_terms = Vec::with_capacity(info.domain_keys.len());
                        for key in &info.domain_keys {
                            if let Ok(v) = key.parse::<i64>() {
                                domain_terms.push(self.solver.int_const(v));
                            } else {
                                let id = self.intern_string(key);
                                domain_terms.push(self.solver.int_const(id));
                            }
                        }
                        return build_finite_membership(self, elem_term, &domain_terms);
                    }
                }

                Err(Z4Error::UnsupportedOp(format!(
                    "DOMAIN on expression not supported in membership context"
                )))
            }

            // RecordSet: r \in [a : S, b : T] => r.a \in S /\ r.b \in T
            Expr::RecordSet(fields) => {
                // For each field in the record set, check that the
                // corresponding field of the element is in the field's domain.
                let mut conjuncts = Vec::with_capacity(fields.len());
                for (field_name, field_domain) in fields {
                    // Build r.field expression
                    let field_access = Spanned::new(
                        Expr::RecordAccess(
                            Box::new(elem.clone()),
                            tla_core::ast::RecordFieldName {
                                name: field_name.clone(),
                                field_id: tla_core::name_intern::NameId::INVALID,
                            },
                        ),
                        elem.span,
                    );
                    // Check field_access \in field_domain
                    let member = self.translate_membership(&field_access, field_domain)?;
                    conjuncts.push(member);
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

            _ => Err(Z4Error::UnsupportedOp(format!(
                "set membership over {:?} not supported",
                std::mem::discriminant(&set.node)
            ))),
        }
    }

    /// Translate function application f[x] where f returns Bool
    ///
    /// For a finite-domain function f with domain {a, b, c}, this builds:
    /// IF x = a THEN f__a ELSE IF x = b THEN f__b ELSE f__c
    ///
    /// Also handles tuple indexing t[i] where t is a tuple and i is an integer index.
    pub(super) fn translate_func_apply_bool(
        &mut self,
        func: &Spanned<Expr>,
        arg: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        // Get the function/tuple variable name
        let var_name = match &func.node {
            Expr::Ident(name, _) => name.clone(),
            _ => {
                return Err(Z4Error::UnsupportedOp(
                    "only simple variable application is supported".to_string(),
                ))
            }
        };

        // Check if this is a tuple variable
        if let Some(tuple_info) = self.tuple_vars.get(&var_name).cloned() {
            return self.translate_tuple_apply_bool(&var_name, &tuple_info, arg);
        }

        // Part of #3749: Check if this is a sequence variable
        if let Some(seq_info) = self.seq_vars.get(&var_name).cloned() {
            return self.translate_seq_apply_bool(&var_name, &seq_info, arg);
        }

        // Check if this is a declared function variable
        let info = match self.func_vars.get(&var_name) {
            Some(info) => info.clone(),
            None => {
                return Err(Z4Error::UnknownVariable(format!(
                    "{var_name} (not declared as function, tuple, or sequence)"
                )))
            }
        };

        // Verify the function returns Bool
        if info.range_sort != TlaSort::Bool {
            return Err(Z4Error::TypeMismatch {
                name: var_name,
                expected: "Bool".to_string(),
                actual: format!("{}", info.range_sort),
            });
        }

        self.build_func_apply_ite(&info, arg)
    }

    /// Translate function application f[x] where f returns Int
    ///
    /// Also handles tuple indexing t[i] and sequence indexing s[i].
    pub(super) fn translate_func_apply_int(
        &mut self,
        func: &Spanned<Expr>,
        arg: &Spanned<Expr>,
    ) -> Z4Result<Term> {
        // Get the function/tuple/sequence variable name
        let var_name = match &func.node {
            Expr::Ident(name, _) => name.clone(),
            _ => {
                return Err(Z4Error::UnsupportedOp(
                    "only simple variable application is supported".to_string(),
                ))
            }
        };

        // Check if this is a tuple variable
        if let Some(tuple_info) = self.tuple_vars.get(&var_name).cloned() {
            return self.translate_tuple_apply_int(&var_name, &tuple_info, arg);
        }

        // Part of #3749: Check if this is a sequence variable
        if let Some(seq_info) = self.seq_vars.get(&var_name).cloned() {
            return self.translate_seq_apply_int(&var_name, &seq_info, arg);
        }

        // Check if this is a declared function variable
        let info = match self.func_vars.get(&var_name) {
            Some(info) => info.clone(),
            None => {
                return Err(Z4Error::UnknownVariable(format!(
                    "{var_name} (not declared as function, tuple, or sequence)"
                )))
            }
        };

        // Verify the function returns Int
        if info.range_sort != TlaSort::Int {
            return Err(Z4Error::TypeMismatch {
                name: var_name,
                expected: "Int".to_string(),
                actual: format!("{}", info.range_sort),
            });
        }

        self.build_func_apply_ite(&info, arg)
    }

    /// Try to extract a string key from an expression without translation.
    ///
    /// Returns `Some(key)` for literals (Int, Bool, String, Ident), `None`
    /// for complex expressions.
    fn try_expr_to_key_static_opt(&self, expr: &Spanned<Expr>) -> Option<String> {
        match &expr.node {
            Expr::Int(n) => Some(n.to_string()),
            Expr::Bool(b) => Some(b.to_string()),
            Expr::String(s) => Some(s.clone()),
            Expr::Ident(name, _) => Some(name.clone()),
            _ => None,
        }
    }
}

/// Build finite membership `x \in {e1, ..., en}` as a disjunction.
///
/// Returns `(x = e1) \/ ... \/ (x = en)`. Empty set returns `false`.
/// Part of #3787.
fn build_finite_membership(
    trans: &mut Z4Translator,
    element: Term,
    set_elements: &[Term],
) -> Z4Result<Term> {
    if set_elements.is_empty() {
        return Ok(trans.solver_mut().bool_const(false));
    }
    let mut disjuncts = Vec::with_capacity(set_elements.len());
    for &set_elem in set_elements {
        let eq = trans.solver_mut().try_eq(element, set_elem)?;
        disjuncts.push(eq);
    }
    let mut result = disjuncts[0];
    for &d in &disjuncts[1..] {
        result = trans.solver_mut().try_or(result, d)?;
    }
    Ok(result)
}
