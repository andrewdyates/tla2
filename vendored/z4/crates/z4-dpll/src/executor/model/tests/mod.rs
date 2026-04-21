// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for model construction, evaluation, validation, and formatting.

// Re-export model items + common dependencies for sub-modules.
// Sub-modules use `use super::*;` to get everything they need.
pub(crate) use hashbrown::HashMap;
pub(crate) use num_bigint::BigInt;
pub(crate) use num_rational::BigRational;
pub(crate) use num_traits::{One, Zero};
pub(crate) use z4_arrays::ArrayModel;
pub(crate) use z4_bv::BvModel;
pub(crate) use z4_core::term::Symbol;
pub(crate) use z4_core::{Sort, TermId};
pub(crate) use z4_euf::EufModel;
pub(crate) use z4_lia::LiaModel;
pub(crate) use z4_lra::LraModel;
pub(crate) use z4_seq::SeqModel;
pub(crate) use z4_strings::StringModel;

pub(crate) use crate::executor_types::{SolveResult, UnknownReason};

pub(crate) use super::*;

mod eval_term_bitvec_array;
mod eval_term_bv_compound;
mod eval_term_core;
mod eval_term_dtbv_accounting;
mod eval_term_fp_seq;
mod eval_term_logic_arith;
mod eval_term_misc;
mod eval_term_theory_validation;
mod eval_term_validation_regressions;

// ==========================================================================
// Shared test helpers
// ==========================================================================

pub(super) fn empty_model() -> Model {
    Model {
        sat_model: vec![],
        term_to_var: HashMap::new(),
        euf_model: None,
        array_model: None,
        lra_model: None,
        lia_model: None,
        bv_model: None,
        fp_model: None,
        string_model: None,
        seq_model: None,
    }
}

pub(super) fn bv_model(values: &[(TermId, i64)]) -> Model {
    let mut model = empty_model();
    let mut bv = HashMap::new();
    for &(t, v) in values {
        bv.insert(t, BigInt::from(v));
    }
    model.bv_model = Some(BvModel {
        values: bv,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });
    model
}

// contains_array_term helper is in validation.rs (#[cfg(test)])

pub(super) fn model_with_sat_assignments(assignments: &[(TermId, bool)]) -> Model {
    let mut sat_model = Vec::with_capacity(assignments.len());
    let mut term_to_var = HashMap::new();

    for (idx, (term, value)) in assignments.iter().enumerate() {
        let var = idx as u32;
        sat_model.push(*value);
        term_to_var.insert(*term, var);
    }

    Model {
        sat_model,
        term_to_var,
        euf_model: None,
        array_model: None,
        lra_model: None,
        lia_model: None,
        bv_model: None,
        fp_model: None,
        string_model: None,
        seq_model: None,
    }
}
