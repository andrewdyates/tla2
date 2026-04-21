// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Datatype model extraction helpers (#5412).
//!
//! Translates DT-sorted variable values from opaque UF representative names
//! (`@SortName!N`) to proper constructor expressions (`Green`, `(Some #x42)`).

use num_rational::BigRational;
use z4_core::term::TermData;
use z4_core::{Sort, TermId};

use crate::executor_format::format_value;

use super::{EvalValue, Executor, Model};

impl Executor {
    /// Check whether a symbol is a datatype-internal symbol (constructor, tester,
    /// or selector) that should be excluded from `get-model` output (#5412).
    pub(super) fn is_dt_internal_symbol(&self, name: &str) -> bool {
        if self.ctx.is_constructor(name).is_some() {
            return true;
        }
        if let Some(ctor) = name.strip_prefix("is-") {
            if self.ctx.is_constructor(ctor).is_some() {
                return true;
            }
        }
        self.ctx
            .ctor_selectors_iter()
            .any(|(_ctor, selectors)| selectors.iter().any(|sel| sel == name))
    }

    /// Resolve a DT-sorted variable's value to a constructor expression (#5412).
    ///
    /// Uses two strategies:
    /// 1. SAT model: Check tester proposition truth values (works for pure DT solver)
    /// 2. EUF model: Check equivalence classes (works for combined DT+UF solvers)
    ///
    /// For nullary constructors (e.g., `Green`), returns the constructor name.
    /// For non-nullary constructors (e.g., `Some`), evaluates selector arguments
    /// to produce e.g. `(Some #x42)`.
    pub(super) fn resolve_dt_value(
        &self,
        sort_name: &str,
        var_term_id: TermId,
        model: &Model,
    ) -> Option<String> {
        for (dt_name, constructors) in self.ctx.datatype_iter() {
            if dt_name != sort_name {
                continue;
            }
            // Strategy 1: Check tester propositions in SAT model.
            // DT axiom injection creates (is-CtorName var) terms; if the SAT model
            // assigns a tester to true, that identifies the constructor.
            // Collect ALL tester values first because the combined DT+BV solver
            // may not enforce mutual exclusivity of testers in the SAT model.
            // If multiple testers are true, prefer the one that was explicitly
            // asserted by the user.
            let mut tester_results: Vec<(&str, bool)> = Vec::new();
            for ctor_name in constructors {
                let tester_name = format!("is-{ctor_name}");
                for idx in 0..self.ctx.terms.len() {
                    let tid = TermId(idx as u32);
                    if let TermData::App(sym, args) = self.ctx.terms.get(tid) {
                        if sym.name() == tester_name && args.len() == 1 && args[0] == var_term_id {
                            let is_asserted = self.ctx.assertions.contains(&tid);
                            tester_results.push((ctor_name, is_asserted));
                            break;
                        }
                    }
                }
            }
            // Prefer explicitly asserted testers; fall back to SAT model true.
            if let Some((ctor_name, _)) = tester_results.iter().find(|&&(_, asserted)| asserted) {
                return Some(self.format_dt_ctor_value(ctor_name, var_term_id, model));
            }
            // Fall back: pick the first tester that's true in the SAT model.
            for ctor_name in constructors {
                let tester_name = format!("is-{ctor_name}");
                for idx in 0..self.ctx.terms.len() {
                    let tid = TermId(idx as u32);
                    if let TermData::App(sym, args) = self.ctx.terms.get(tid) {
                        if sym.name() == tester_name && args.len() == 1 && args[0] == var_term_id {
                            if self.term_value(&model.sat_model, &model.term_to_var, tid)
                                == Some(true)
                            {
                                return Some(self.format_dt_ctor_value(
                                    ctor_name,
                                    var_term_id,
                                    model,
                                ));
                            }
                            break;
                        }
                    }
                }
            }

            // Strategy 2: For combined DT+UF solvers with EUF model, match by
            // equivalence class (nullary constructors share the same element name).
            if let Some(ref euf_model) = model.euf_model {
                if let Some(elem) = euf_model.term_values.get(&var_term_id) {
                    for ctor_name in constructors {
                        if let Some(info) = self.ctx.symbol_info(ctor_name) {
                            if info.arg_sorts.is_empty() {
                                if let Some(ctor_term_id) = info.term {
                                    if euf_model.term_values.get(&ctor_term_id) == Some(elem) {
                                        return Some(ctor_name.clone());
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Strategy 3: Single-constructor DTs always use that constructor.
            // This handles nested DT values where no tester term exists in the
            // term store (e.g., `(val x)` returning a `Pair` with only `mkpair`) (#5432).
            if constructors.len() == 1 {
                return Some(self.format_dt_ctor_value(&constructors[0], var_term_id, model));
            }

            // Strategy 4: Check assertion equalities for constructor values (#5450).
            // In pure QF_DT, selector values like `(val m1)` may be constrained by
            // assertions like `(= (val m1) Green)`. If the assertion's other side
            // evaluates to a known constructor name, return that constructor.
            if let Some(EvalValue::Element(ref elem)) =
                self.extract_value_from_asserted_equalities(model, var_term_id)
            {
                if constructors.iter().any(|c| c == elem) {
                    return Some(elem.clone());
                }
            }

            return None; // Found the DT sort but no matching constructor
        }
        None
    }

    /// Format a DT constructor value with evaluated selector arguments.
    ///
    /// Looks up selector application terms `(sel var)` in the term store and
    /// resolves their values from theory-specific models (BV, LIA, LRA, EUF).
    fn format_dt_ctor_value(&self, ctor_name: &str, var_term_id: TermId, model: &Model) -> String {
        let selectors = self.ctx.constructor_selectors(ctor_name).unwrap_or(&[]);
        if selectors.is_empty() {
            return ctor_name.to_string();
        }
        // Non-nullary: find selector application terms and look up their values
        // directly in the theory models. evaluate_term doesn't handle unrecognized
        // function apps (like selectors) in BV/LIA models, so we look up directly.
        let mut arg_strs = Vec::new();
        for sel_name in selectors {
            let mut found = false;
            for idx in 0..self.ctx.terms.len() {
                let tid = TermId(idx as u32);
                if let TermData::App(sym, args) = self.ctx.terms.get(tid) {
                    if sym.name() == sel_name.as_str() && args.len() == 1 && args[0] == var_term_id
                    {
                        let sel_sort = self.ctx.terms.sort(tid);
                        // For DT-sorted selectors, recursively resolve to a
                        // constructor expression instead of returning the opaque
                        // element name like `@Pair!0` (#5432).
                        if let Sort::Uninterpreted(sort_name) = sel_sort {
                            if let Some(resolved) = self.resolve_dt_value(sort_name, tid, model) {
                                arg_strs.push(resolved);
                                found = true;
                                break;
                            }
                        }
                        let mut val = self.lookup_term_value(model, tid);
                        // #5506: For Int-sorted selectors with no LIA model value,
                        // scan assertions for inequality/equality constraints and
                        // pick a satisfying integer value instead of defaulting to 0.
                        if matches!(val, EvalValue::Unknown) && matches!(sel_sort, Sort::Int) {
                            if let Some(v) = self.extract_int_from_assertion_bounds(tid) {
                                val = EvalValue::Rational(BigRational::from(v));
                            }
                        }
                        // #1766: Same for Real-sorted selectors with no LRA model value.
                        if matches!(val, EvalValue::Unknown) && matches!(sel_sort, Sort::Real) {
                            if let Some(v) = self.extract_real_from_assertion_bounds(tid) {
                                val = EvalValue::Rational(v);
                            }
                        }
                        // For DT-sorted selectors whose value is unknown or an
                        // opaque internal name (`@Color!0`), default to the first
                        // nullary constructor of the sort (#5450).
                        if let Sort::Uninterpreted(ref sn) = sel_sort {
                            let needs_default = match &val {
                                EvalValue::Unknown => true,
                                EvalValue::Element(elem) => elem.starts_with('@'),
                                _ => false,
                            };
                            if needs_default {
                                if let Some(ctor) = self.first_nullary_constructor(sn) {
                                    arg_strs.push(ctor);
                                    found = true;
                                    break;
                                }
                            }
                        }
                        arg_strs.push(self.format_eval_value(&val, tid));
                        found = true;
                        break;
                    }
                }
            }
            if !found {
                if let Some(sel_sort) = self.ctx.symbol_sort(sel_name) {
                    arg_strs.push(format_value(sel_sort, None, &self.ctx.terms));
                } else {
                    arg_strs.push("?".to_string());
                }
            }
        }
        format!("({} {})", ctor_name, arg_strs.join(" "))
    }

    /// Look up a term's value directly from theory models.
    ///
    /// Unlike `evaluate_term`, this checks BV/LIA/LRA/EUF models by TermId
    /// without trying to evaluate the term recursively. This is needed for
    /// DT selector applications whose TermIds are mapped in theory models
    /// but whose function names are not recognized by `evaluate_term`.
    pub(super) fn lookup_term_value(&self, model: &Model, term_id: TermId) -> EvalValue {
        let sort = self.ctx.terms.sort(term_id);

        // Check BV model for BitVec-sorted terms.
        if let Sort::BitVec(bv) = sort {
            if let Some(ref bv_model) = model.bv_model {
                if let Some(val) = bv_model.values.get(&term_id) {
                    return EvalValue::BitVec {
                        value: val.clone(),
                        width: bv.width,
                    };
                }
            }
        }

        // Check LIA model for Int-sorted terms.
        if matches!(sort, Sort::Int) {
            if let Some(ref lia_model) = model.lia_model {
                if let Some(val) = lia_model.values.get(&term_id) {
                    return EvalValue::Rational(BigRational::from(val.clone()));
                }
            }
        }

        // Check LRA model for Real-sorted terms (and Int fallback).
        if matches!(sort, Sort::Int | Sort::Real) {
            if let Some(ref lra_model) = model.lra_model {
                if let Some(val) = lra_model.values.get(&term_id) {
                    return EvalValue::Rational(val.clone());
                }
            }
        }

        // Check EUF model for uninterpreted sorts.
        if let Some(ref euf_model) = model.euf_model {
            if let Some(elem) = euf_model.term_values.get(&term_id) {
                return EvalValue::Element(elem.clone());
            }
        }

        // Check Bool in SAT model.
        if matches!(sort, Sort::Bool) {
            if let Some(val) = self.term_value(&model.sat_model, &model.term_to_var, term_id) {
                return EvalValue::Bool(val);
            }
        }

        // For pure DT logic (no LIA/LRA/BV theory solver), selector values
        // are not tracked by any theory model. Extract the value from assertion
        // equalities like `(= (sel x) constant)` that are true in the SAT model (#5432).
        if let Some(val) = self.extract_value_from_asserted_equalities(model, term_id) {
            return val;
        }

        // Fall back to recursive evaluation for computed values.
        self.evaluate_term(model, term_id)
    }

    /// Extract a term's value from assertion equalities in the SAT model.
    ///
    /// Scans assertions for `(= term_id expr)` or `(= expr term_id)` patterns
    /// where the equality holds true in the SAT model. Evaluates the other side
    /// of the equality to obtain the value. This handles the pure DT case where
    /// no arithmetic theory solver is active (#5432).
    pub(super) fn extract_value_from_asserted_equalities(
        &self,
        model: &Model,
        term_id: TermId,
    ) -> Option<EvalValue> {
        for &assertion in &self.ctx.assertions {
            // Look for equalities involving term_id
            if let TermData::App(sym, args) = self.ctx.terms.get(assertion) {
                if sym.name() == "=" && args.len() == 2 {
                    // Check if this equality is true in the SAT model
                    let eq_true = self
                        .term_value(&model.sat_model, &model.term_to_var, assertion)
                        .unwrap_or(false);
                    if !eq_true {
                        continue;
                    }
                    // Match (= term_id other) or (= other term_id)
                    let other = if args[0] == term_id {
                        args[1]
                    } else if args[1] == term_id {
                        args[0]
                    } else {
                        continue;
                    };
                    // Evaluate the other side — constants evaluate directly
                    let val = self.evaluate_term(model, other);
                    if !matches!(val, EvalValue::Unknown) {
                        return Some(val);
                    }
                    // Nullary DT constructors are stored as TermData::Var
                    // (#1745). In pure QF_DT (no EUF model), evaluate_term
                    // returns Unknown for them. Recognize them directly.
                    if let TermData::Var(name, _) = self.ctx.terms.get(other) {
                        if self.ctx.is_constructor(name).is_some() {
                            return Some(EvalValue::Element(name.clone()));
                        }
                    }
                }
            }
        }
        None
    }

    /// Return the name of the first nullary constructor for a DT sort.
    ///
    /// Used as a default value when model extraction cannot determine the
    /// specific constructor for a DT-sorted term (#5450). Produces a valid
    /// model value instead of an internal representative like `@Color!0`.
    fn first_nullary_constructor(&self, sort_name: &str) -> Option<String> {
        for (dt_name, constructors) in self.ctx.datatype_iter() {
            if dt_name != sort_name {
                continue;
            }
            for ctor_name in constructors {
                if let Some(info) = self.ctx.symbol_info(ctor_name) {
                    if info.arg_sorts.is_empty() {
                        return Some(ctor_name.clone());
                    }
                }
            }
            break;
        }
        None
    }

    // Arithmetic bound extraction methods are in dt_bounds.rs.
}
