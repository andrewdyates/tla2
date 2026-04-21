// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-Based Quantifier Instantiation (MBQI).
//!
//! Implements the quick-check phase of Z3's MBQI algorithm (Ge & de Moura, CAV 2009).
//! After E-matching and CEGQI, if the ground solver returns SAT but unhandled
//! universal quantifiers remain, MBQI evaluates each quantifier body under the
//! candidate model with ground term substitutions. If the body evaluates to false
//! for some ground term combination, that instantiation is a counterexample —
//! the ground lemma is added and the solver re-checks.
//!
//! When no existing ground terms are available for a variable's sort, MBQI
//! synthesizes default candidates from the model (model value injection).
//! For interpreted sorts (Int, Real, BV, etc.) this uses theory defaults (0, 0.0,
//! etc.) plus model-assigned values. For uninterpreted sorts, the EUF model's
//! sort universe provides concrete element constants.
//!
//! Reference: Z3 `sat/smt/q_mbi.cpp` (quick_check, check_forall,
//! replace_model_value, add_universe_restriction).
//!
//! Unlike CEGQI, MBQI does NOT inject CE lemma variables into the assertion set.
//! It produces ground instantiations only, avoiding CE-lemma interaction bugs
//! (#6045, #5975).

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::{Sort, TermData, TermId};

use super::model::EvalValue;
use super::Executor;
use crate::ematching::subst_vars;
use crate::executor_types::{Result, SolveResult};
use crate::logic_detection::LogicCategory;

/// Maximum MBQI refinement rounds before giving up.
const MAX_MBQI_ROUNDS: usize = 5;

/// Maximum candidate substitutions per quantifier per round.
/// Prevents combinatorial explosion for multi-variable quantifiers with many
/// ground terms per sort.
const MAX_QUICK_CHECK_CANDIDATES: usize = 1000;

/// Maximum number of synthesized default candidates per sort.
/// Keeps model value injection bounded for sorts with many model values.
const MAX_SYNTHESIZED_CANDIDATES: usize = 8;

impl Executor {
    /// Run MBQI refinement loop: check unhandled quantifiers against the current
    /// model, add counterexample instantiations, and re-solve.
    ///
    /// Called from `map_quantifier_result` when the ground solver returns SAT
    /// but unhandled universal quantifiers remain. Returns the final solve result
    /// after MBQI refinement, or `None` if MBQI found no counterexamples
    /// (indicating the SAT result may be genuine or MBQI is incomplete).
    ///
    /// # Arguments
    /// * `unhandled_quantifiers` - Universal quantifiers not covered by E-matching/CEGQI
    /// * `category` - Logic category for the re-solve dispatch
    pub(in crate::executor) fn try_mbqi_refinement(
        &mut self,
        unhandled_quantifiers: &[TermId],
        category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        if unhandled_quantifiers.is_empty() {
            return None;
        }

        // Only process universal quantifiers.
        let forall_quants: Vec<TermId> = unhandled_quantifiers
            .iter()
            .copied()
            .filter(|&q| matches!(self.ctx.terms.get(q), TermData::Forall(..)))
            .collect();

        if forall_quants.is_empty() {
            return None;
        }

        let mut seen_instantiations: HashSet<TermId> = HashSet::new();

        for _round in 0..MAX_MBQI_ROUNDS {
            if self.last_model.is_none() {
                break;
            }

            // Collect ground terms by sort from current assertions.
            let ground_by_sort = crate::ematching::collect_ground_terms_by_sort(
                &self.ctx.terms,
                &self.ctx.assertions,
            );

            // Collect sorts that need synthesized candidates: sorts that appear
            // as bound variable sorts in our quantifiers but have no ground terms.
            let needed_sorts: HashSet<Sort> = forall_quants
                .iter()
                .filter_map(|&q| match self.ctx.terms.get(q) {
                    TermData::Forall(vars, _, _) => Some(vars.clone()),
                    _ => None,
                })
                .flatten()
                .map(|(_, sort)| sort)
                .filter(|sort| ground_by_sort.get(sort).is_none_or(Vec::is_empty))
                .collect();

            // Synthesize default candidates for sorts with no ground terms.
            let synthesized = if needed_sorts.is_empty() {
                HashMap::new()
            } else {
                self.synthesize_mbqi_candidates(&needed_sorts)
            };

            let mut new_instantiations: Vec<TermId> = Vec::new();
            let mut all_satisfied = true;

            for &quant in &forall_quants {
                let (vars, body) = match self.ctx.terms.get(quant) {
                    TermData::Forall(v, b, _) => (v.clone(), *b),
                    _ => continue,
                };

                if vars.is_empty() {
                    continue;
                }

                // Collect candidate terms per variable. Fall back to synthesized
                // defaults when no existing ground terms are available (#5971).
                let mut candidates_per_var: Vec<Vec<TermId>> = Vec::with_capacity(vars.len());
                let mut any_empty = false;
                for (_name, sort) in vars.iter() {
                    let mut candidates = ground_by_sort.get(sort).cloned().unwrap_or_default();
                    if candidates.is_empty() {
                        candidates = synthesized.get(sort).cloned().unwrap_or_default();
                    }
                    if candidates.is_empty() {
                        any_empty = true;
                        break;
                    }
                    candidates_per_var.push(candidates);
                }
                if any_empty {
                    all_satisfied = false;
                    continue;
                }

                let var_names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();

                // Enumerate substitutions (cartesian product with budget).
                let mut indices: Vec<usize> = vec![0; vars.len()];
                let mut checked = 0usize;
                let mut quant_all_true = true;

                loop {
                    if checked >= MAX_QUICK_CHECK_CANDIDATES {
                        quant_all_true = false;
                        all_satisfied = false;
                        break;
                    }

                    // Build binding.
                    let binding: Vec<TermId> = indices
                        .iter()
                        .enumerate()
                        .map(|(var_idx, &term_idx)| candidates_per_var[var_idx][term_idx])
                        .collect();

                    // Create ground instance via substitution (hash-consed, cheap).
                    let subst_map: HashMap<String, TermId> = var_names
                        .iter()
                        .zip(binding.iter())
                        .map(|(name, &t)| (name.clone(), t))
                        .collect();
                    let ground_body = subst_vars(&mut self.ctx.terms, body, &subst_map);

                    // Evaluate under the model.
                    // Re-borrow model each iteration to satisfy the borrow checker
                    // (subst_vars borrows &mut self.ctx.terms above).
                    let eval = if let Some(ref model) = self.last_model {
                        self.evaluate_term(model, ground_body)
                    } else {
                        EvalValue::Unknown
                    };

                    match eval {
                        EvalValue::Bool(true) => {
                            // Satisfies the quantifier — continue.
                        }
                        EvalValue::Bool(false) => {
                            // Counterexample! The model falsifies the quantifier for
                            // this substitution. Add the ground instance as a lemma.
                            if seen_instantiations.insert(ground_body) {
                                new_instantiations.push(ground_body);
                            }
                            quant_all_true = false;
                            all_satisfied = false;
                            // Continue checking — multiple counterexamples per round
                            // help convergence.
                        }
                        _ => {
                            // Unknown — can't determine. Mark incomplete but continue
                            // trying other substitutions.
                            quant_all_true = false;
                            all_satisfied = false;
                        }
                    }

                    checked += 1;

                    // Advance to next combination.
                    let mut carry = true;
                    for i in (0..vars.len()).rev() {
                        if carry {
                            indices[i] += 1;
                            if indices[i] < candidates_per_var[i].len() {
                                carry = false;
                            } else {
                                indices[i] = 0;
                            }
                        }
                    }
                    if carry {
                        break; // All combinations exhausted.
                    }
                }

                let _ = quant_all_true;
            }

            if new_instantiations.is_empty() {
                if all_satisfied {
                    // Every quantifier body is true under the model for all checked
                    // ground substitutions. The SAT result is genuine (modulo
                    // completeness of the ground term set).
                    return Some(Ok(SolveResult::Sat));
                }
                // No counterexamples found but not all satisfied (evaluation was
                // Unknown or budget hit). MBQI is incomplete.
                break;
            }

            // Add counterexample instantiations to assertions and re-solve.
            for inst in &new_instantiations {
                self.ctx.assertions.push(*inst);
            }

            let re_result = self.solve_for_category(category);
            match re_result {
                Ok(SolveResult::Sat) => {
                    // Still SAT with new lemmas. Next round will re-check with
                    // the updated model.
                    continue;
                }
                Ok(SolveResult::Unsat) => {
                    // The counterexample instantiations made the problem UNSAT.
                    // This is genuine: the quantifiers were violated.
                    return Some(Ok(SolveResult::Unsat));
                }
                other => {
                    return Some(other);
                }
            }
        }

        // MBQI did not find definitive result. Return None to let caller
        // fall back to Unknown.
        None
    }

    /// Synthesize default candidate terms for sorts with no existing ground terms.
    ///
    /// For each sort in `needed_sorts`, creates a small set of candidate TermIds
    /// by combining theory defaults with values from the current model.
    ///
    /// Strategy per sort (mirrors Z3 `replace_model_value` + `get_some_value`):
    /// - `Bool`: `true`, `false`
    /// - `Int`: `0` + all distinct Int values from the LIA/EUF model
    /// - `Real`: `0.0` + all distinct Real values from the LRA model
    /// - `BitVec(w)`: `0` of width `w` + model values from the BV model
    /// - `String`: `""` (empty string)
    /// - `Uninterpreted(name)`: fresh constant per element in the EUF sort universe
    /// - Other sorts: no candidates (MBQI skips these quantifiers)
    fn synthesize_mbqi_candidates(
        &mut self,
        needed_sorts: &HashSet<Sort>,
    ) -> HashMap<Sort, Vec<TermId>> {
        let mut result: HashMap<Sort, Vec<TermId>> = HashMap::new();

        for sort in needed_sorts {
            let mut candidates: Vec<TermId> = Vec::new();

            match sort {
                Sort::Bool => {
                    candidates.push(self.ctx.terms.mk_bool(true));
                    candidates.push(self.ctx.terms.mk_bool(false));
                }
                Sort::Int => {
                    // Default: 0
                    candidates.push(self.ctx.terms.mk_int(num_bigint::BigInt::ZERO));
                    // Add distinct model values from LIA/EUF.
                    if let Some(ref model) = self.last_model {
                        let mut seen_values: HashSet<num_bigint::BigInt> = HashSet::new();
                        seen_values.insert(num_bigint::BigInt::ZERO);
                        if let Some(ref lia_model) = model.lia_model {
                            for val in lia_model.values.values() {
                                if candidates.len() >= MAX_SYNTHESIZED_CANDIDATES {
                                    break;
                                }
                                if seen_values.insert(val.clone()) {
                                    candidates.push(self.ctx.terms.mk_int(val.clone()));
                                }
                            }
                        }
                        if let Some(ref euf_model) = model.euf_model {
                            for val in euf_model.int_values.values() {
                                if candidates.len() >= MAX_SYNTHESIZED_CANDIDATES {
                                    break;
                                }
                                if seen_values.insert(val.clone()) {
                                    candidates.push(self.ctx.terms.mk_int(val.clone()));
                                }
                            }
                        }
                    }
                }
                Sort::Real => {
                    // Default: 0.0
                    candidates.push(self.ctx.terms.mk_rational(num_rational::BigRational::new(
                        num_bigint::BigInt::ZERO,
                        num_bigint::BigInt::from(1),
                    )));
                    // Add model values from LRA.
                    if let Some(ref model) = self.last_model {
                        let mut seen: HashSet<TermId> = candidates.iter().copied().collect();
                        if let Some(ref lra_model) = model.lra_model {
                            for val in lra_model.values.values() {
                                if candidates.len() >= MAX_SYNTHESIZED_CANDIDATES {
                                    break;
                                }
                                let term = self.ctx.terms.mk_rational(val.clone());
                                if seen.insert(term) {
                                    candidates.push(term);
                                }
                            }
                        }
                    }
                }
                Sort::BitVec(bv_sort) => {
                    let width = bv_sort.width;
                    // Default: 0 of this width
                    candidates.push(self.ctx.terms.mk_bitvec(num_bigint::BigInt::ZERO, width));
                    // Add model values from BV.
                    if let Some(ref model) = self.last_model {
                        let mut seen: HashSet<TermId> = candidates.iter().copied().collect();
                        if let Some(ref bv_model) = model.bv_model {
                            for (&term_id, _) in &bv_model.values {
                                if candidates.len() >= MAX_SYNTHESIZED_CANDIDATES {
                                    break;
                                }
                                // Only use values whose term has matching BV width
                                if self.ctx.terms.sort(term_id) == &Sort::BitVec(bv_sort.clone())
                                    && seen.insert(term_id)
                                {
                                    candidates.push(term_id);
                                }
                            }
                        }
                    }
                }
                Sort::String => {
                    // Default: empty string
                    candidates.push(self.ctx.terms.mk_string(String::new()));
                }
                Sort::Uninterpreted(name) => {
                    // Use the EUF model's sort universe to get concrete elements.
                    // Each element (e.g., "@Color!0") becomes a fresh constant.
                    if let Some(ref model) = self.last_model {
                        if let Some(ref euf_model) = model.euf_model {
                            if let Some(elements) = euf_model.sort_elements.get(name) {
                                for elem_name in elements {
                                    if candidates.len() >= MAX_SYNTHESIZED_CANDIDATES {
                                        break;
                                    }
                                    let sort_clone = sort.clone();
                                    let term = self.ctx.terms.mk_var(elem_name.clone(), sort_clone);
                                    candidates.push(term);
                                }
                            }
                        }
                    }
                    // If no universe elements, create a single fresh constant.
                    if candidates.is_empty() {
                        let fresh_name = self.ctx.terms.mk_internal_symbol("mbqi_elem");
                        let term = self.ctx.terms.mk_var(fresh_name, sort.clone());
                        candidates.push(term);
                    }
                }
                // Array, FP, Seq, Datatype, RegLan: complex sorts where synthesizing
                // defaults is non-trivial. MBQI skips these for now — future work
                // could handle them via model-based construction.
                _ => {}
            }

            if !candidates.is_empty() {
                result.insert(sort.clone(), candidates);
            }
        }

        result
    }
}
