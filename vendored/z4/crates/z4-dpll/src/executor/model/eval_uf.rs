// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! UF (uninterpreted function) model evaluation helpers.
//!
//! Extracted from mod.rs (Packet 6 Step 2).

use num_bigint::BigInt;
use num_rational::BigRational;
use z4_bv::BvModel;
use z4_core::term::TermData;
use z4_core::{Sort, TermId};
use z4_euf::EufModel;

use super::{EvalValue, Model};
use crate::executor_format::format_bitvec;

use super::Executor;

impl Executor {
    /// Convert an evaluated value into the atom format used in EUF function tables.
    pub(super) fn eval_value_to_model_atom(&self, value: &EvalValue) -> Option<String> {
        match value {
            EvalValue::Bool(true) => Some("true".to_string()),
            EvalValue::Bool(false) => Some("false".to_string()),
            EvalValue::Element(elem) => Some(elem.clone()),
            EvalValue::Rational(r) => {
                if r.is_integer() {
                    Some(r.numer().to_string())
                } else {
                    Some(format!("(/ {} {})", r.numer(), r.denom()))
                }
            }
            EvalValue::BitVec { value, width } => Some(format_bitvec(value, *width)),
            EvalValue::Fp(fp_val) => Some(fp_val.to_smtlib()),
            EvalValue::String(s) => Some(s.clone()),
            EvalValue::Seq(_) => None, // Seq values have no atomic representation
            EvalValue::Unknown => None,
        }
    }

    /// Build the lookup key for one UF application argument in EUF function tables.
    fn uf_table_arg_key(&self, model: &Model, euf_model: &EufModel, arg: TermId) -> String {
        if matches!(self.ctx.terms.sort(arg), Sort::Bool) {
            if let Some(value) = self.term_value(&model.sat_model, &model.term_to_var, arg) {
                return if value {
                    "true".to_string()
                } else {
                    "false".to_string()
                };
            }
            if let Some(raw) = euf_model.term_values.get(&arg) {
                if raw == "true" || raw == "false" {
                    return raw.clone();
                }
            }
            if let EvalValue::Bool(value) = self.evaluate_term(model, arg) {
                return if value {
                    "true".to_string()
                } else {
                    "false".to_string()
                };
            }
            return format!("@?{}", arg.0);
        }

        if let Some(raw) = euf_model.term_values.get(&arg) {
            return raw.clone();
        }

        if let Some(key) = self.eval_value_to_model_atom(&self.evaluate_term(model, arg)) {
            return key;
        }

        format!("@?{}", arg.0)
    }

    /// Evaluate UF applications via extracted function tables when available.
    pub(super) fn evaluate_uf_app_from_function_table(
        &self,
        model: &Model,
        name: &str,
        args: &[TermId],
        result_sort: &Sort,
        target_term_id: TermId,
    ) -> Option<EvalValue> {
        let euf_model = model.euf_model.as_ref()?;
        let table = euf_model.function_tables.get(name)?;

        let resolve_table_atom = |raw: &str| {
            raw.strip_prefix("@?")
                .and_then(|id_str| id_str.parse::<u32>().ok())
                .map(TermId)
                .filter(|term_id| (term_id.0 as usize) < self.ctx.terms.len())
                .and_then(|term_id| {
                    self.eval_value_to_model_atom(&self.evaluate_term(model, term_id))
                })
                .unwrap_or_else(|| raw.to_string())
        };

        let arg_key: Vec<String> = args
            .iter()
            .map(|&arg| self.uf_table_arg_key(model, euf_model, arg))
            .collect();

        let (_entry_args, raw_result) = table.iter().find(|(entry_args, _)| {
            entry_args
                .iter()
                .map(|entry_arg| resolve_table_atom(entry_arg))
                .eq(arg_key.iter().cloned())
        })?;
        let resolved_result = raw_result
            .strip_prefix("@?")
            .and_then(|id_str| id_str.parse::<u32>().ok())
            .map(TermId)
            .filter(|&term_id| term_id != target_term_id)
            .filter(|term_id| (term_id.0 as usize) < self.ctx.terms.len())
            .and_then(|term_id| self.eval_value_to_model_atom(&self.evaluate_term(model, term_id)))
            .unwrap_or_else(|| raw_result.clone());
        let parsed = self.parse_model_value_string(&resolved_result, &Some(result_sort.clone()));
        // If parsing returned Unknown, the function table had a placeholder value
        // (e.g., "@?{id}" for Int/Real-sorted results built before term_values
        // were populated). Fall through to per-sort model lookups which have
        // correct data via func_app_const_terms or int_values (#4686).
        match parsed {
            EvalValue::Unknown => None,
            other => Some(other),
        }
    }

    /// Evaluate an uninterpreted function application by consulting theory models.
    ///
    /// This is the catch-all handler for `TermData::App` terms that do not match
    /// any known built-in theory operation (arithmetic, BV, arrays, strings, etc.).
    /// It covers DT constructors, UF function tables, SAT-literal fallback for
    /// Bool-sorted UF predicates, per-sort theory model lookups (Int, Real, BV, FP),
    /// EUF model lookups, and assertion-equality resolution for DT selectors.
    ///
    /// Extracted from mod.rs for code health (#5970).
    pub(super) fn evaluate_uninterpreted_app(
        &self,
        model: &Model,
        name: &str,
        args: &[TermId],
        sort: &Sort,
        term_id: TermId,
    ) -> EvalValue {
        // DT constructor recognition: nullary constructors like `Green`
        // or `Nothing` are 0-arity applications that should evaluate to
        // their constructor name, not Unknown. This is needed for pure
        // QF_DT where there is no EUF model to look up (#5450).
        if args.is_empty() && self.ctx.is_constructor(name).is_some() {
            return EvalValue::Element(name.to_string());
        }
        if let Some(value) =
            self.evaluate_uf_app_from_function_table(model, name, args, sort, term_id)
        {
            return value;
        }
        // Bool SAT-literal fallback is sound only for true UF predicates.
        // For known theory predicates (e.g., str.contains, str.in_re),
        // taking the SAT literal would bypass semantic validation.
        if matches!(sort, Sort::Bool) && !Self::is_known_theory_symbol(name) {
            if let Some(b) = self.term_value(&model.sat_model, &model.term_to_var, term_id) {
                return EvalValue::Bool(b);
            }
        }
        // For non-Bool applications, consult models by term ID.
        // For user-visible UF/selector apps (#5432), check EUF
        // func_app_const_terms first—it tracks explicit
        // `(= (sel x) const)` assertions and is authoritative.
        // The LIA model may have stale default values for terms
        // introduced via assert_shared_equality.
        // For solver-internal depth terms (`__z4_dt_depth_*`),
        // LIA is authoritative since it computes actual depth values.
        let is_depth_term = name.starts_with("__z4_dt_depth_");
        match sort {
            Sort::Int => {
                // For non-depth terms, EUF func_app_const_terms
                // is authoritative (#5432).
                if !is_depth_term {
                    if let Some(ref euf_model) = model.euf_model {
                        if let Some(&const_term_id) = euf_model.func_app_const_terms.get(&term_id) {
                            return self.evaluate_term(model, const_term_id);
                        }
                        if let Some(raw) = euf_model.term_values.get(&term_id) {
                            if let EvalValue::Rational(r) =
                                self.parse_model_value_string(raw, &Some(Sort::Int))
                            {
                                return EvalValue::Rational(r);
                            }
                        }
                    }
                }
                // LIA/LRA: authoritative for depth terms,
                // fallback for non-depth terms.
                if let Some(ref lia_model) = model.lia_model {
                    if let Some(val) = lia_model.values.get(&term_id) {
                        return EvalValue::Rational(BigRational::from(val.clone()));
                    }
                }
                if let Some(ref lra_model) = model.lra_model {
                    if let Some(val) = lra_model.values.get(&term_id) {
                        return EvalValue::Rational(val.clone());
                    }
                }
                // For depth terms, also check EUF after LIA misses.
                if is_depth_term {
                    if let Some(ref euf_model) = model.euf_model {
                        if let Some(&const_term_id) = euf_model.func_app_const_terms.get(&term_id) {
                            return self.evaluate_term(model, const_term_id);
                        }
                    }
                }
                if model.lia_model.is_some() || model.lra_model.is_some() {
                    return EvalValue::Unknown;
                }
                if let Some(ref euf_model) = model.euf_model {
                    if let Some(val) = euf_model.int_values.get(&term_id) {
                        return EvalValue::Rational(BigRational::from(val.clone()));
                    }
                }
            }
            Sort::Real => {
                // For non-depth terms, EUF is authoritative (#5432).
                if !is_depth_term {
                    if let Some(ref euf_model) = model.euf_model {
                        if let Some(&const_term_id) = euf_model.func_app_const_terms.get(&term_id) {
                            return self.evaluate_term(model, const_term_id);
                        }
                        if let Some(raw) = euf_model.term_values.get(&term_id) {
                            if let EvalValue::Rational(r) =
                                self.parse_model_value_string(raw, &Some(Sort::Real))
                            {
                                return EvalValue::Rational(r);
                            }
                        }
                    }
                }
                if let Some(ref lra_model) = model.lra_model {
                    if let Some(val) = lra_model.values.get(&term_id) {
                        return EvalValue::Rational(val.clone());
                    }
                }
                if model.lra_model.is_some() {
                    return EvalValue::Unknown;
                }
            }
            Sort::BitVec(bv) => {
                if let Some(ref bv_model) = model.bv_model {
                    if let Some(val) = bv_model.values.get(&term_id) {
                        return EvalValue::BitVec {
                            value: val.clone(),
                            width: bv.width,
                        };
                    }
                    // UF congruence fallback (#5461): if f(y) is not
                    // in the BV model (wasn't in assertions), find a
                    // congruent application f(x) whose arguments
                    // evaluate to the same values.
                    if let Some(val) =
                        self.find_congruent_bv_app(model, bv_model, name, args, term_id)
                    {
                        return EvalValue::BitVec {
                            value: val,
                            width: bv.width,
                        };
                    }
                }
                if let Some(ref euf_model) = model.euf_model {
                    if let Some(raw) = euf_model.term_values.get(&term_id) {
                        if let EvalValue::BitVec { value, width } =
                            self.parse_model_value_string(raw, &Some(Sort::BitVec(bv.clone())))
                        {
                            return EvalValue::BitVec { value, width };
                        }
                    }
                }
                // Congruence fallback already handled by
                // find_congruent_bv_app above (#5461).
                if model.bv_model.is_some() {
                    return EvalValue::Unknown;
                }
            }
            Sort::FloatingPoint(..) => {
                // FP-sorted unrecognized application: check FP model
                if let Some(ref fp_model) = model.fp_model {
                    if let Some(val) = fp_model.values.get(&term_id) {
                        return EvalValue::Fp(val.clone());
                    }
                }
            }
            _ => {}
        }
        // Then try EUF model
        if let Some(ref euf_model) = model.euf_model {
            if let Some(elem) = euf_model.term_values.get(&term_id) {
                return EvalValue::Element(elem.clone());
            }
            // Check for function application constant values (#385)
            // For UF applications returning Int/Real/BV, we may have recorded
            // the constant term from assertions like (= (f x) 100)
            if let Some(&const_term_id) = euf_model.func_app_const_terms.get(&term_id) {
                return self.evaluate_term(model, const_term_id);
            }
        }
        // For unrecognized Bool predicates, return Unknown instead of
        // defaulting to false, as they may be theory predicates we
        // can't evaluate without model values.
        if matches!(sort, Sort::Bool) {
            return EvalValue::Unknown;
        }
        // Final fallback: resolve from assertion equalities.
        // In QF_DT, selector values are only constrained by
        // assertions like (= (ival x) 42) with no theory model.
        // Only extract from constant terms to avoid recursion (#5432).
        // Restrict to DT-internal symbols (selectors) to prevent
        // circular self-validation of non-DT apps (#5494).
        if !self.is_dt_internal_symbol(name) {
            return EvalValue::Unknown;
        }
        for &assertion in &self.ctx.assertions {
            if let TermData::App(eq_sym, eq_args) = self.ctx.terms.get(assertion) {
                if eq_sym.name() == "=" && eq_args.len() == 2 {
                    // Check this assertion is true in the SAT model (#5497).
                    let eq_true = self
                        .term_value(&model.sat_model, &model.term_to_var, assertion)
                        .unwrap_or(false);
                    if !eq_true {
                        continue;
                    }
                    let other = if eq_args[0] == term_id {
                        Some(eq_args[1])
                    } else if eq_args[1] == term_id {
                        Some(eq_args[0])
                    } else {
                        None
                    };
                    if let Some(other_term) = other {
                        if matches!(self.ctx.terms.get(other_term), TermData::Const(_)) {
                            return self.evaluate_term(model, other_term);
                        }
                    }
                }
            }
        }
        EvalValue::Unknown
    }

    /// Find a congruent BV UF application in the BV model (#5461).
    ///
    /// When `f(y)` is not in `bv_model.values` (because it only appeared in
    /// `get-value`, not in assertions), search for another application
    /// `f(x)` of the same function where all arguments evaluate to the same
    /// BV values. Returns the BV value of the congruent application.
    pub(super) fn find_congruent_bv_app(
        &self,
        model: &Model,
        bv_model: &BvModel,
        func_name: &str,
        target_args: &[TermId],
        target_term_id: TermId,
    ) -> Option<BigInt> {
        // Evaluate the target arguments to get their model values.
        let target_arg_vals: Vec<EvalValue> = target_args
            .iter()
            .map(|&a| self.evaluate_term(model, a))
            .collect();
        // If any argument is Unknown, we cannot determine congruence.
        if target_arg_vals
            .iter()
            .any(|v| matches!(v, EvalValue::Unknown))
        {
            return None;
        }

        // Search BV model entries for a congruent application.
        for (&candidate_tid, candidate_val) in &bv_model.values {
            if candidate_tid == target_term_id {
                continue;
            }
            if let TermData::App(sym, cand_args) = self.ctx.terms.get(candidate_tid) {
                if sym.name() != func_name || cand_args.len() != target_args.len() {
                    continue;
                }
                // Check if all arguments evaluate to the same values.
                let args_match =
                    cand_args
                        .iter()
                        .zip(target_arg_vals.iter())
                        .all(|(&cand_arg, target_val)| {
                            let cand_val = self.evaluate_term(model, cand_arg);
                            &cand_val == target_val
                        });
                if args_match {
                    return Some(candidate_val.clone());
                }
            }
        }
        None
    }
}
