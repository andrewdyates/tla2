// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array model extraction helpers for CHC SMT.
//!
//! Builds the term-values map that `ArraySolver::extract_model` requires
//! (combining LIA, SAT-Bool, and BV bit-level assignments), and converts
//! `ArrayInterpretation` into the CHC-level `SmtValue` representation.

use super::context::SmtContext;
use super::types::SmtValue;
use super::value_parse;
#[cfg(not(kani))]
use hashbrown::HashMap as HbHashMap;
use rustc_hash::FxHashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HbHashMap;
use z4_core::{Sort, TermId, TermStore};

impl SmtContext {
    /// Build a term-values map from the current model for array model extraction.
    /// Maps TermId → String value, combining LIA model, SAT Bool assignments, and BV values.
    /// This is the "EUF model" substitute that ArraySolver::extract_model needs.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn build_term_values_map(
        terms: &TermStore,
        var_map: &FxHashMap<String, TermId>,
        lia_model: &Option<z4_lia::LiaModel>,
        sat_model: &[bool],
        term_to_var: &std::collections::BTreeMap<TermId, u32>,
        bv_term_to_bits: &HbHashMap<TermId, Vec<i32>>,
        bv_var_offset: i32,
    ) -> hashbrown::HashMap<TermId, String> {
        let mut term_values = hashbrown::HashMap::<TermId, String>::new();

        // Add LIA model values (Int/Real terms)
        if let Some(ref m) = lia_model {
            for (&tid, val) in &m.values {
                term_values.insert(tid, val.to_string());
            }
        }

        // Add Bool and BV values from SAT model
        for &tid in var_map.values() {
            match terms.sort(tid) {
                Sort::Bool => {
                    if let Some(&cv) = term_to_var.get(&tid) {
                        let sv = z4_sat::Variable::new(cv - 1);
                        if let Some(&v) = sat_model.get(sv.index()) {
                            term_values.insert(tid, if v { "true" } else { "false" }.to_string());
                        }
                    }
                }
                Sort::BitVec(bvs) => {
                    if let Some(bits) = bv_term_to_bits.get(&tid) {
                        let mut bv_val: u64 = 0;
                        for (i, &bit_lit) in bits.iter().enumerate() {
                            if i >= 64 {
                                break;
                            }
                            let abs_lit = bit_lit.unsigned_abs();
                            let offset_var = abs_lit
                                .checked_add(bv_var_offset as u32)
                                .and_then(|v| v.checked_sub(1));
                            let Some(offset_var) = offset_var else {
                                continue;
                            };
                            let sv = z4_sat::Variable::new(offset_var);
                            if let Some(&val) = sat_model.get(sv.index()) {
                                let bit_val = if bit_lit > 0 { val } else { !val };
                                if bit_val {
                                    bv_val |= 1u64 << i;
                                }
                            }
                        }
                        term_values.insert(
                            tid,
                            format!(
                                "#x{:0>width$x}",
                                bv_val,
                                width = (bvs.width as usize).div_ceil(4)
                            ),
                        );
                    }
                }
                _ => {}
            }
        }

        term_values
    }

    /// Convert an ArrayInterpretation from the array solver into an SmtValue.
    pub(super) fn array_interp_to_smt_value(
        interp: &z4_arrays::ArrayInterpretation,
        element_sort: &Sort,
        index_sort: &Sort,
    ) -> SmtValue {
        let default_val = interp
            .default
            .as_ref()
            .and_then(|d| value_parse::parse_smt_value_str(d, element_sort))
            .unwrap_or_else(|| value_parse::default_smt_value(element_sort));

        if interp.stores.is_empty() {
            SmtValue::ConstArray(Box::new(default_val))
        } else {
            let entries: Vec<(SmtValue, SmtValue)> = interp
                .stores
                .iter()
                .map(|(k, v)| {
                    let key = value_parse::parse_smt_value_str(k, index_sort)
                        .unwrap_or_else(|| value_parse::default_smt_value(index_sort));
                    let val = value_parse::parse_smt_value_str(v, element_sort)
                        .unwrap_or_else(|| value_parse::default_smt_value(element_sort));
                    (key, val)
                })
                .collect();
            SmtValue::ArrayMap {
                default: Box::new(default_val),
                entries,
            }
        }
    }
}

#[cfg(test)]
#[path = "array_model_tests.rs"]
mod tests;
