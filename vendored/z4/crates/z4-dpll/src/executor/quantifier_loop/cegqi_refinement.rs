// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CEGQI arithmetic refinement and neighbor enumeration.
//!
//! Multi-round counterexample-guided quantifier instantiation: extract model values
//! for CE variables, compute selection terms via `ArithInstantiator`, create ground
//! instantiations, and re-solve. Includes neighbor enumeration fallback for integer
//! variables where bound extraction fails (div/mod patterns).

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::{Sort, TermId};

use super::super::model::EvalValue;
use super::super::Executor;
use crate::cegqi::arith::ArithInstantiator;
use crate::cegqi::CegqiInstantiator;
use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::features::StaticFeatures;
use crate::logic_detection::LogicCategory;

impl Executor {
    /// Attempt multi-round CEGQI arithmetic refinement.
    ///
    /// Extract model values for CE variables, use `ArithInstantiator` to compute
    /// selection terms, create ground instantiations, and re-solve. If still SAT,
    /// extract new model and repeat up to `MAX_CEGQI_ROUNDS` times.
    ///
    /// Returns `Some(result)` if refinement was attempted and produced a result,
    /// or `None` if refinement was not applicable (no model, no arithmetic vars).
    #[allow(clippy::used_underscore_items)]
    pub(super) fn try_cegqi_arith_refinement(
        &mut self,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        category: LogicCategory,
        ce_lemma_ids: &[TermId],
    ) -> Option<Result<SolveResult>> {
        const MAX_CEGQI_ROUNDS: usize = 8;

        self.last_model.as_ref()?;

        // Bail early on nonlinear or div/mod terms under linear logic (#6042, #6889).
        // Integer div/mod creates opaque auxiliary variables in LIA preprocessing
        // that prevent CEGQI bound extraction from converging. Each refinement
        // round runs a full branch-and-bound pipeline, causing severe slowdown.
        if matches!(
            category,
            LogicCategory::QfLia | LogicCategory::Lia | LogicCategory::QfLra | LogicCategory::Lra
        ) {
            let features = StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions);
            if features.has_nonlinear_int || features.has_nonlinear_real || features.has_int_div_mod
            {
                self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                return Some(Ok(SolveResult::Unknown));
            }
        }

        let mut prev_instantiation_count = self.ctx.assertions.len();
        let mut seen_instantiations: HashSet<TermId> = HashSet::new();

        for _round in 0..MAX_CEGQI_ROUNDS {
            // Clone model to avoid overlapping borrows: last_model is borrowed
            // immutably for the model reference, but instantiate_cegqi_round
            // needs &mut self to modify ctx.assertions.
            let model = match self.last_model.clone() {
                Some(m) => m,
                None => break,
            };

            let any_added =
                self.instantiate_cegqi_round(cegqi_state, &model, &mut seen_instantiations);

            if !any_added {
                if _round == 0 {
                    return None;
                }
                break;
            }

            if self.ctx.assertions.len() == prev_instantiation_count {
                break;
            }
            prev_instantiation_count = self.ctx.assertions.len();

            match self.solve_for_category(category) {
                Ok(SolveResult::Unsat) => {
                    return Some(self.disambiguate_cegqi_unsat(category, ce_lemma_ids, false));
                }
                Ok(SolveResult::Sat) => continue,
                other => return Some(other),
            }
        }

        // Neighbor enumeration fallback for integer variables.
        if let Some(result) = self.try_cegqi_neighbor_enumeration(
            cegqi_state,
            category,
            &mut seen_instantiations,
            ce_lemma_ids,
        ) {
            return Some(result);
        }

        self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
        Some(Ok(SolveResult::Unknown))
    }

    /// Execute one CEGQI refinement round: extract model values for CE variables,
    /// compute selection terms via `ArithInstantiator`, and create ground instantiations.
    ///
    /// Returns `true` if any new instantiation was added.
    #[allow(clippy::used_underscore_items)]
    fn instantiate_cegqi_round(
        &mut self,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        model: &super::super::model::Model,
        seen_instantiations: &mut HashSet<TermId>,
    ) -> bool {
        let mut any_instantiation_added = false;

        for (_quant_id, inst) in cegqi_state {
            if !inst.is_forall() {
                continue;
            }

            let mut var_values: HashMap<String, TermId> = HashMap::new();

            for (var_name, &ce_var) in inst._ce_variables() {
                let eval = self.evaluate_term(model, ce_var);
                let sort = self.ctx.terms.sort(ce_var).clone();
                let is_integer = matches!(sort, Sort::Int);

                let mut arith = ArithInstantiator::new();

                let assertion_ids: Vec<TermId> = self.ctx.assertions.clone();
                for &assertion in &assertion_ids {
                    arith.process_assertion(&mut self.ctx.terms, assertion, ce_var);
                }

                let model_value: num_rational::BigRational = match &eval {
                    EvalValue::Rational(r) => r.clone(),
                    _ => continue,
                };

                // Populate model values on bounds for tightest-bound selection
                // and rho computation (Reynolds et al. FMSD 2017).
                for bound in &mut arith.lower_bounds {
                    if let EvalValue::Rational(r) = self.evaluate_term(model, bound.term) {
                        bound.model_value = Some(r);
                    }
                }
                for bound in &mut arith.upper_bounds {
                    if let EvalValue::Rational(r) = self.evaluate_term(model, bound.term) {
                        bound.model_value = Some(r);
                    }
                }

                if let Some(selection) =
                    arith.select_term(&mut self.ctx.terms, ce_var, &model_value, is_integer)
                {
                    var_values.insert(var_name.clone(), selection);
                } else {
                    let fallback = if is_integer {
                        let int_val = model_value.numer().clone() / model_value.denom();
                        self.ctx.terms.mk_int(int_val)
                    } else {
                        self.ctx.terms.mk_rational(model_value.clone())
                    };
                    var_values.insert(var_name.clone(), fallback);
                }
            }

            if let Some(ground_inst) =
                inst._create_model_instantiation(&mut self.ctx.terms, &var_values)
            {
                if seen_instantiations.insert(ground_inst) {
                    self.ctx.assertions.push(ground_inst);
                    any_instantiation_added = true;
                }
            }
        }

        any_instantiation_added
    }

    /// Neighbor enumeration fallback for CEGQI: try instantiating with values
    /// near the model value (v±1, v±2, ..., v±4) for integer CE variables.
    #[allow(clippy::used_underscore_items)]
    fn try_cegqi_neighbor_enumeration(
        &mut self,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        category: LogicCategory,
        seen_instantiations: &mut HashSet<TermId>,
        ce_lemma_ids: &[TermId],
    ) -> Option<Result<SolveResult>> {
        const MAX_NEIGHBOR_DISTANCE: i64 = 4;

        let model = self.last_model.as_ref()?;

        let mut int_ce_vars: Vec<(String, TermId, num_bigint::BigInt)> = Vec::new();
        for (_quant_id, inst) in cegqi_state {
            if !inst.is_forall() {
                continue;
            }
            for (var_name, &ce_var) in inst._ce_variables() {
                let sort = self.ctx.terms.sort(ce_var).clone();
                if !matches!(sort, Sort::Int) {
                    continue;
                }
                if let EvalValue::Rational(r) = self.evaluate_term(model, ce_var) {
                    let int_val = r.numer().clone() / r.denom();
                    int_ce_vars.push((var_name.clone(), ce_var, int_val));
                }
            }
        }

        if int_ce_vars.is_empty() {
            return None;
        }

        for distance in 1..=MAX_NEIGHBOR_DISTANCE {
            for offset in &[distance, -distance] {
                let mut any_new = false;

                for (_quant_id, inst) in cegqi_state {
                    if !inst.is_forall() {
                        continue;
                    }

                    let mut var_values: HashMap<String, TermId> = HashMap::new();

                    for (var_name, _ce_var, base_val) in &int_ce_vars {
                        let neighbor_val = base_val + num_bigint::BigInt::from(*offset);
                        let neighbor_term = self.ctx.terms.mk_int(neighbor_val);
                        var_values.insert(var_name.clone(), neighbor_term);
                    }

                    if let Some(ground_inst) =
                        inst._create_model_instantiation(&mut self.ctx.terms, &var_values)
                    {
                        if seen_instantiations.insert(ground_inst) {
                            self.ctx.assertions.push(ground_inst);
                            any_new = true;
                        }
                    }
                }

                if !any_new {
                    continue;
                }

                let re_result = self.solve_for_category(category);
                match re_result {
                    Ok(SolveResult::Unsat) => {
                        return Some(self.disambiguate_cegqi_unsat(category, ce_lemma_ids, false));
                    }
                    Ok(SolveResult::Sat) => {
                        continue;
                    }
                    other => {
                        return Some(other);
                    }
                }
            }
        }

        None
    }
}
