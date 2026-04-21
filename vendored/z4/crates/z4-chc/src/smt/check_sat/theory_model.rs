// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT model extraction for the DPLL(T) theory loop.
//!
//! Extracts variable values from the SAT model, LIA model, BV bit-mappings,
//! and array solver into an `FxHashMap<String, SmtValue>` model.

use num_traits::{One, ToPrimitive};
use rustc_hash::FxHashMap;
use z4_arrays::ArraySolver;
use z4_core::{Sort, TermId, TermStore};
use z4_lia::LiaSolver;

#[cfg(not(kani))]
use hashbrown::HashMap as HbHashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HbHashMap;

use super::super::context::SmtContext;
use super::super::types::SmtValue;

/// Result of value extraction from a theory-SAT assignment.
pub(super) enum ExtractResult {
    /// Values were extracted successfully.
    Values(FxHashMap<String, SmtValue>),
    /// An integer overflow was encountered; return Unknown.
    Overflow,
}

/// Extract variable values from a theory-SAT assignment.
///
/// Iterates over `var_map` and extracts values from the LIA model, SAT model,
/// BV bit-mappings, and array solver.
///
/// This is a free function (not a method on SmtContext) to avoid borrow conflicts
/// with the LIA solver which holds a reference to the shared TermStore.
#[allow(clippy::too_many_arguments)]
pub(super) fn extract_theory_sat_values(
    terms: &TermStore,
    var_map: &FxHashMap<String, TermId>,
    var_original_names: &FxHashMap<String, String>,
    sat_model: &[bool],
    term_to_var: &std::collections::BTreeMap<TermId, u32>,
    lia: &mut LiaSolver<'_>,
    bv_term_to_bits: &HbHashMap<TermId, Vec<i32>>,
    bv_var_offset: i32,
    has_array_ops: bool,
    array_solver: &mut Option<ArraySolver<'_>>,
) -> ExtractResult {
    let mut values = FxHashMap::default();
    let lia_model = lia.extract_model();

    for (qualified_name, &term_id) in var_map {
        // #6100: var_map keys are sort-qualified; emit
        // original CHC names in the model for downstream
        // lookups via `model.get(&v.name)`.
        let name = var_original_names
            .get(qualified_name)
            .map(String::as_str)
            .unwrap_or(qualified_name);
        match terms.sort(term_id) {
            Sort::Bool => {
                if let Some(&cnf_var) = term_to_var.get(&term_id) {
                    let sat_var = z4_sat::Variable::new(cnf_var - 1);
                    if let Some(value) = sat_model.get(sat_var.index()) {
                        values.insert(name.to_owned(), SmtValue::Bool(*value));
                    }
                }
            }
            Sort::Int => {
                if let Some(m) = &lia_model {
                    if let Some(v) = m.values.get(&term_id) {
                        // #3827: skip variable on i64 overflow instead of
                        // saturating to wrong value (false SAT risk).
                        if let Some(i) = v.to_i64() {
                            values.insert(name.to_owned(), SmtValue::Int(i));
                        }
                        continue;
                    }
                }

                // Fallback: LIA may not include all `Int` vars in its extracted model,
                // but the underlying LRA solver still tracks their values.
                if let Some(v) = lia.lra_solver().get_value(term_id) {
                    if v.denom().is_one() {
                        // #3827: skip on overflow
                        if let Some(i) = v.numer().to_i64() {
                            values.insert(name.to_owned(), SmtValue::Int(i));
                        }
                    } else {
                        return ExtractResult::Overflow;
                    }
                }
            }
            Sort::BitVec(bv_sort) => {
                // Extract BV value from SAT model using bit mappings.
                if let Some(bits) = bv_term_to_bits.get(&term_id) {
                    let mut bv_val: u128 = 0;
                    for (i, &bit_lit) in bits.iter().enumerate() {
                        // Skip bits beyond u128 capacity.
                        if i >= 128 {
                            break;
                        }
                        // #6090: use u32 arithmetic to avoid i32 overflow.
                        let abs_lit = bit_lit.unsigned_abs();
                        let offset_var = abs_lit
                            .checked_add(bv_var_offset as u32)
                            .and_then(|v| v.checked_sub(1));
                        let Some(offset_var) = offset_var else {
                            continue;
                        };
                        let sat_var = z4_sat::Variable::new(offset_var);
                        if let Some(&val) = sat_model.get(sat_var.index()) {
                            let bit_val = if bit_lit > 0 { val } else { !val };
                            if bit_val {
                                bv_val |= 1u128 << i;
                            }
                        }
                    }
                    values.insert(name.to_owned(), SmtValue::BitVec(bv_val, bv_sort.width));
                }
            }
            Sort::Real => {
                // Extract rational value from the LRA solver.
                if let Some(v) = lia.lra_solver().get_value(term_id) {
                    values.insert(name.to_owned(), SmtValue::Real(v.clone()));
                }
            }
            Sort::Array(arr_sort) if has_array_ops => {
                // #6047: Extract array model values from
                // ArraySolver. Build term_values map needed
                // by ArraySolver::extract_model.
                if let Some(ref mut arr) = array_solver {
                    let term_values = SmtContext::build_term_values_map(
                        terms,
                        var_map,
                        &lia_model,
                        sat_model,
                        term_to_var,
                        bv_term_to_bits,
                        bv_var_offset,
                    );
                    let arr_model = arr.extract_model(&term_values);
                    if let Some(interp) = arr_model.array_values.get(&term_id) {
                        let smt_val = SmtContext::array_interp_to_smt_value(
                            interp,
                            &arr_sort.element_sort,
                            &arr_sort.index_sort,
                        );
                        values.insert(name.to_owned(), smt_val);
                    }
                }
            }
            _ => {}
        }
    }

    ExtractResult::Values(values)
}
