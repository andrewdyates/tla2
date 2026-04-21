// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV model extraction from SAT assignments and array model recovery.
//!
//! Converts SAT solver bit assignments back into bitvector values and
//! recovers array models from BV select terms.
//!
//! Expression evaluation (evaluate_bv_expr, evaluate_bv_bool_predicate,
//! evaluate_bool_substitution) is in `bv_eval.rs`.

#[cfg(not(kani))]
use hashbrown::HashMap;
use z4_arrays::{ArrayInterpretation, ArrayModel};
use z4_bv::{BvBits, BvModel};
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::TermData;
use z4_core::{Sort, TermId, TermStore};

use super::super::Executor;
use crate::executor_format::format_bitvec;

impl Executor {
    /// Extract a bitvector model from SAT solver bit assignments.
    ///
    /// Given a SAT model (variable truth assignments) and the mapping from BV terms
    /// to their bit-blasted SAT literals, reconstruct the bitvector values.
    /// Includes all BV-sorted terms (variables AND function applications) so the
    /// model evaluator can resolve expressions like `(bvult (f x) #x10)`.
    pub(in crate::executor) fn extract_bv_model_from_bits(
        sat_model: &[bool],
        term_bits: &HashMap<TermId, BvBits>,
        var_offset: i32,
        terms: &TermStore,
    ) -> BvModel {
        use num_bigint::BigInt;

        let mut values = HashMap::new();
        let mut stored_term_to_bits = HashMap::new();

        for (&term_id, bits) in term_bits {
            // Include all BV-sorted terms (variables and function applications).
            // Function applications like (f x) are bit-blasted and have concrete
            // SAT assignments; including them lets the model evaluator resolve
            // BV comparison predicates over uninterpreted functions.
            let sort = terms.sort(term_id);
            if !matches!(sort, Sort::BitVec(_)) {
                continue;
            }

            stored_term_to_bits.insert(term_id, bits.clone());

            // Reconstruct value from bits (LSB at index 0)
            let mut value = BigInt::from(0);
            for (i, &bit_lit) in bits.iter().enumerate() {
                let offset_lit = if bit_lit > 0 {
                    bit_lit + var_offset
                } else {
                    bit_lit - var_offset
                };
                let sat_var_idx = if offset_lit > 0 {
                    (offset_lit - 1) as usize
                } else {
                    (-offset_lit - 1) as usize
                };
                let bit_value = if sat_var_idx < sat_model.len() {
                    let sat_val = sat_model[sat_var_idx];
                    if offset_lit > 0 {
                        sat_val
                    } else {
                        !sat_val
                    }
                } else {
                    false
                };
                if bit_value {
                    value |= BigInt::from(1) << i;
                }
            }

            // BV value must fit within declared bit-width (#4661)
            if let Sort::BitVec(bv) = sort {
                debug_assert!(
                    value >= BigInt::from(0) && value < (BigInt::from(1) << bv.width),
                    "BUG: BV model value {} for term {:?} exceeds {}-bit range",
                    value,
                    term_id,
                    bv.width
                );
            }

            values.insert(term_id, value);
        }

        BvModel {
            values,
            term_to_bits: stored_term_to_bits,
            bool_overrides: HashMap::new(),
        }
    }

    // BV expression evaluators (evaluate_bv_expr, evaluate_bv_bool_predicate,
    // evaluate_bool_substitution) moved to bv_eval.rs (#7006).

    /// Extract array model from BV model for QF_ABV/QF_AUFBV (#5449).
    ///
    /// Scans bit-blasted select terms in the BV model to recover concrete
    /// index-value mappings for each root array variable. Without this,
    /// array models default to `((as const ...) 0)`.
    pub(in crate::executor) fn extract_array_model_from_bv_model(
        terms: &TermStore,
        bv_model: &BvModel,
    ) -> ArrayModel {
        use num_bigint::BigInt;

        // Group select(array_var, index) terms by array variable.
        // Only collect selects where the array arg is a variable (Var), NOT a
        // store chain. Selects through stores give the post-store value, not the
        // root array's value — collecting them would cause non-deterministic
        // model output when a direct select and a store-chain select at the same
        // index map to the same root with different values.
        // ROW2 axioms ensure that store-chain selects at non-matching indices
        // have corresponding direct selects from the root array.
        let mut selects_by_array: HashMap<TermId, Vec<(TermId, TermId)>> = HashMap::new();

        // Scan BV-sorted select terms from bv_model.values
        for &term_id in bv_model.values.keys() {
            if let TermData::App(sym, args) = terms.get(term_id) {
                if sym.name() == "select"
                    && args.len() == 2
                    && matches!(terms.get(args[0]), TermData::Var(_, _))
                {
                    selects_by_array
                        .entry(args[0])
                        .or_default()
                        .push((args[1], term_id));
                }
            }
        }

        // #6047: Also scan Bool-sorted select terms from bool_overrides.
        // Arrays like (Array BV32 Bool) have Bool-element selects whose values
        // are in the SAT assignment (seeded into bool_overrides), not bv_model.values.
        // Without this, (Array BV Bool) arrays get default const(false) models
        // even when select(arr, idx) is asserted true.
        for &term_id in bv_model.bool_overrides.keys() {
            if let TermData::App(sym, args) = terms.get(term_id) {
                if sym.name() == "select"
                    && args.len() == 2
                    && matches!(terms.get(args[0]), TermData::Var(_, _))
                {
                    selects_by_array
                        .entry(args[0])
                        .or_default()
                        .push((args[1], term_id));
                }
            }
        }

        let mut array_values = HashMap::new();
        for (root_id, selects) in selects_by_array {
            let Sort::Array(arr_sort) = terms.sort(root_id) else {
                continue;
            };
            let Sort::BitVec(idx_bv) = &arr_sort.index_sort else {
                continue;
            };
            let idx_width = idx_bv.width;

            // Element sort determines how to format the default and store values.
            // (Array BV BV) → bitvec default/values
            // (Array BV Bool) → "false"/"true" default/values
            let (default_val, is_bool_elem) = match &arr_sort.element_sort {
                Sort::BitVec(elem_bv) => (format_bitvec(&BigInt::from(0u64), elem_bv.width), false),
                Sort::Bool => ("false".to_string(), true),
                _ => continue,
            };

            let mut interp = ArrayInterpretation {
                index_sort: Some(arr_sort.index_sort.clone()),
                element_sort: Some(arr_sort.element_sort.clone()),
                default: Some(default_val),
                ..Default::default()
            };

            let mut seen_indices = hashbrown::HashSet::new();
            for &(idx_id, sel_id) in &selects {
                let idx_val = bv_model
                    .values
                    .get(&idx_id)
                    .cloned()
                    .or_else(|| Self::evaluate_bv_expr(terms, idx_id, &bv_model.values));

                // Element value: from BV model for BV elements, bool_overrides for Bool elements
                let elem_str = if is_bool_elem {
                    bv_model
                        .bool_overrides
                        .get(&sel_id)
                        .map(|&b| if b { "true" } else { "false" }.to_string())
                } else {
                    bv_model
                        .values
                        .get(&sel_id)
                        .cloned()
                        .or_else(|| Self::evaluate_bv_expr(terms, sel_id, &bv_model.values))
                        .map(|ev| {
                            let Sort::BitVec(elem_bv) = &arr_sort.element_sort else {
                                unreachable!(
                                    "BUG: BV array element sort is not BitVec in model extraction"
                                );
                            };
                            format_bitvec(&ev, elem_bv.width)
                        })
                };

                if let (Some(iv), Some(ev_str)) = (idx_val, elem_str) {
                    let idx_str = format_bitvec(&iv, idx_width);
                    if seen_indices.insert(idx_str.clone()) {
                        interp.stores.push((idx_str, ev_str));
                    }
                }
            }

            array_values.insert(root_id, interp);
        }

        ArrayModel { array_values }
    }
}

#[cfg(test)]
#[path = "bv_model_tests.rs"]
mod tests;
