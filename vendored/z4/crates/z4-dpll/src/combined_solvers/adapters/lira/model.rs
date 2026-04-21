// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model extraction and `to_int` value patching for the LIRA combined solver.
//!
//! After extracting LIA and LRA models independently, patches the LIA model
//! so that `to_int(x)` values agree with `floor(x)` from the LRA model.
//! Without this, LIA treats `to_int(x)` as a free integer variable (#5944).

use z4_lia::LiaModel;
use z4_lra::LraModel;

use super::LiraSolver;

impl LiraSolver<'_> {
    /// Extract both models for model generation.
    ///
    /// After extracting, patches LIA model values for `to_int(x)` terms
    /// so that the LIA model agrees with `floor(x)` from the LRA model.
    /// Without this, the LIA and LRA models may disagree on `to_int` values
    /// because LIA treats `to_int(x)` as a free integer variable (#5944).
    pub(crate) fn extract_models(&mut self) -> (Option<LiaModel>, LraModel) {
        let mut lia_model = self.lia.extract_model();
        let mut lra_model = self.lra.extract_model();

        // Patch to_int values: use floor(arg_value) from LRA model
        if let Some(ref mut lia) = lia_model {
            for &(to_int_var, inner_arg_term) in self.lra.to_int_terms() {
                if let Some(to_int_term) = self.lra.var_term_id(to_int_var) {
                    if let Some(arg_val) = lra_model.values.get(&inner_arg_term) {
                        let floored = arg_val.floor().to_integer();
                        lia.values.insert(to_int_term, floored);
                    }
                }
            }

            // Patch LRA model for Int-sorted shared variables (#6227):
            // When z = to_real(y) and y = to_int(x), the LRA model may have
            // y's value as the raw simplex value (not floor(x)). Copy LIA's
            // patched integer values into the LRA model for shared terms, then
            // propagate to Real-sorted variables constrained equal via asserted
            // equality atoms in main LRA.
            let mut patched_lra_terms = Vec::new();
            for (&term, val) in &lia.values {
                if let Some(lra_val) = lra_model.values.get(&term) {
                    let lia_rational = num_rational::BigRational::from(val.clone());
                    if *lra_val != lia_rational {
                        lra_model.values.insert(term, lia_rational);
                        patched_lra_terms.push(term);
                    }
                }
            }
            // For each patched term, propagate to equal Real-sorted variables
            // via asserted equality atoms in LRA.
            if !patched_lra_terms.is_empty() {
                let patched_var_ids: hashbrown::HashSet<u32> = patched_lra_terms
                    .iter()
                    .filter_map(|t| self.lra.term_to_var().get(t).copied())
                    .collect();
                self.lra
                    .propagate_model_equalities(&mut lra_model, &patched_var_ids);
            }
        }

        (lia_model, lra_model)
    }
}
