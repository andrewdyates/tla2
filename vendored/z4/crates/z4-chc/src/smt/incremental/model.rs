// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT model extraction and verification for incremental contexts.
//!
//! Builds a model map from SAT assignment + LIA model + propagated equalities,
//! covering Bool, Int, and BV variables. Includes model verification against
//! original background + assumption expressions.

use super::{strip_namespace_suffix, IncrementalCheckResult, IncrementalSatContext};
use crate::smt::context::SmtContext;
use crate::smt::model_verify::verify_sat_model_conjunction_strict_with_mod_retry;
use crate::smt::types::{ModelVerifyResult, SmtValue};
use crate::ChcExpr;
use num_traits::{One, ToPrimitive};
use rustc_hash::FxHashMap;
use z4_core::Sort;

impl IncrementalSatContext {
    /// Build a model map from a SAT assignment + LIA model + propagated equalities.
    ///
    /// Extracts values for Bool, Int, and BV variables from the SAT/LIA models,
    /// merges propagated equalities, adds un-namespaced aliases for aux vars (#7380),
    /// and verifies the model against the original background+assumption expressions.
    ///
    /// Returns `Sat(values)` if valid, `Unknown` if invalid or indeterminate with
    /// array/DT/mod ops.
    pub(super) fn build_incremental_model(
        &self,
        model: &[bool],
        lia_model: &Option<z4_lia::LiaModel>,
        lia: &z4_lia::LiaSolver<'_>,
        smt: &SmtContext,
        propagated_equalities: &FxHashMap<String, i64>,
        propagated_bv_equalities: &FxHashMap<String, (u128, u32)>,
        assumptions: &[ChcExpr],
    ) -> IncrementalCheckResult {
        let mut values = FxHashMap::default();
        for (name, value) in propagated_equalities {
            values.insert(name.clone(), SmtValue::Int(*value));
        }
        for (name, (value, width)) in propagated_bv_equalities {
            values.insert(name.clone(), SmtValue::BitVec(*value, *width));
        }

        let lia_model_ref = lia_model;
        for (qualified_name, &term_id) in &self.var_map {
            let name = self
                .var_original_names
                .get(qualified_name)
                .map(String::as_str)
                .unwrap_or(qualified_name);
            if values.contains_key(name) {
                continue;
            }
            match smt.terms.sort(term_id) {
                Sort::Bool => {
                    if let Some(&cnf_var) = self.term_to_var.get(&term_id) {
                        let sat_var = z4_sat::Variable::new(cnf_var - 1);
                        if let Some(value) = model.get(sat_var.index()) {
                            values.insert(name.to_owned(), SmtValue::Bool(*value));
                        }
                    }
                }
                Sort::Int => {
                    if let Some(m) = lia_model_ref {
                        if let Some(v) = m.values.get(&term_id) {
                            if let Some(i) = v.to_i64() {
                                values.insert(name.to_owned(), SmtValue::Int(i));
                            }
                            continue;
                        }
                    }
                    if let Some(v) = lia.lra_solver().get_value(term_id) {
                        if v.denom().is_one() {
                            if let Some(i) = v.numer().to_i64() {
                                values.insert(name.to_owned(), SmtValue::Int(i));
                            }
                        }
                    }
                }
                Sort::BitVec(bv_sort) => {
                    if let Some(bits) = self.bv_term_to_bits.get(&term_id) {
                        if let Some(offset) = self.bv_var_offset {
                            let mut bv_val: u128 = 0;
                            for (i, &bit_lit) in bits.iter().enumerate() {
                                if i >= 128 {
                                    break;
                                }
                                let abs_lit = bit_lit.unsigned_abs();
                                let offset_var = abs_lit
                                    .checked_add(offset as u32)
                                    .and_then(|v| v.checked_sub(1));
                                let Some(offset_var) = offset_var else {
                                    continue;
                                };
                                let sat_var = z4_sat::Variable::new(offset_var);
                                if let Some(&val) = model.get(sat_var.index()) {
                                    let bit_val = if bit_lit > 0 { val } else { !val };
                                    if bit_val {
                                        bv_val |= 1u128 << i;
                                    }
                                }
                            }
                            values.insert(name.to_owned(), SmtValue::BitVec(bv_val, bv_sort.width));
                        }
                    }
                }
                _ => {}
            }
        }
        // #7380: Also insert model values under un-namespaced names
        // for mod/ITE auxiliary variables.
        let mut extra_entries = Vec::new();
        for (name, value) in &values {
            if let Some(base) = strip_namespace_suffix(name) {
                if !values.contains_key(base) {
                    extra_entries.push((base.to_owned(), value.clone()));
                }
            }
        }
        for (name, value) in extra_entries {
            values.insert(name, value);
        }
        let verify_result = verify_sat_model_conjunction_strict_with_mod_retry(
            self.background_exprs.iter().chain(assumptions.iter()),
            &values,
        );
        if matches!(verify_result, ModelVerifyResult::Invalid) {
            tracing::warn!(
                "SAT model from check_sat_incremental violates background+assumptions; returning Unknown"
            );
            return IncrementalCheckResult::Unknown;
        }
        if matches!(verify_result, ModelVerifyResult::Indeterminate) {
            let has_array_ops = assumptions.iter().any(ChcExpr::contains_array_ops);
            let has_dt = assumptions.iter().any(ChcExpr::contains_dt_ops);
            if has_array_ops || has_dt {
                tracing::debug!(
                    "SAT model indeterminate with array/DT ops in incremental solver; degrading to Unknown"
                );
                return IncrementalCheckResult::Unknown;
            }
            let has_mod_aux = self
                .background_exprs
                .iter()
                .chain(assumptions.iter())
                .any(ChcExpr::has_mod_aux_vars);
            if has_mod_aux {
                tracing::debug!(
                    "SAT model indeterminate with mod aux vars in incremental solver; degrading to Unknown (#7380)"
                );
                return IncrementalCheckResult::Unknown;
            }
            tracing::debug!(
                "SAT model verification indeterminate in check_sat_incremental; accepting as Sat"
            );
        }
        IncrementalCheckResult::Sat(values)
    }
}
