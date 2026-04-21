// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-preserving counterexample minimization.
//!
//! After a SAT result, tries replacing variable values with smaller candidates
//! while re-evaluating all assertions to ensure the model remains valid.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Signed;
use z4_core::{Sort, TermData, TermId};

// Re-exported for tests (used via `use super::*` in tests.rs).
#[cfg(test)]
use {num_traits::One, num_traits::Zero, z4_arrays::ArrayInterpretation};

use super::{EvalValue, Model};
use crate::executor::Executor;

mod candidates;
use candidates::*;

/// Maximum minimization passes. After shrinking one variable, others may
/// become shrinkable (e.g., x + y = 10: shrinking x enables shrinking y).
const MAX_MINIMIZATION_PASSES: usize = 3;

/// A pending minimization attempt: which variable to try, what value.
enum MinAttempt {
    Lia(TermId, Vec<BigInt>),
    Lra(TermId, Vec<BigRational>),
    Bv(TermId, Vec<BigInt>),
}

/// Extract leading u64 digit from a BigUint magnitude (0 if empty).
fn leading_u64(mag: &num_bigint::BigUint) -> u64 {
    mag.to_u64_digits().first().copied().unwrap_or(0)
}

impl MinAttempt {
    /// Magnitude of the current value, for sorting (largest first).
    fn magnitude(&self) -> u64 {
        match self {
            Self::Lia(_, c) | Self::Bv(_, c) => {
                c.last().map(|v| leading_u64(v.magnitude())).unwrap_or(0)
            }
            Self::Lra(_, c) => c
                .last()
                .map(|v| leading_u64(v.abs().to_integer().magnitude()))
                .unwrap_or(0),
        }
    }
}

impl Executor {
    /// Minimize the stored model in-place, preserving satisfiability.
    ///
    /// For each variable in the LIA, LRA, and BV models, tries smaller
    /// candidate values and validates all assertions still hold. Only keeps
    /// a replacement when the model evaluator confirms validity.
    ///
    /// Uses multi-pass convergence: after shrinking one variable, dependent
    /// variables may become shrinkable. Runs up to MAX_MINIMIZATION_PASSES.
    ///
    /// Call this after `self.last_model` is populated and before
    /// `finalize_sat_model_validation`.
    pub(in crate::executor) fn minimize_model_sat_preserving(&mut self) {
        for _pass in 0..MAX_MINIMIZATION_PASSES {
            // Phase 1: Collect all variables and their candidate lists.
            let mut attempts = match self.last_model.as_ref() {
                Some(model) => self.collect_min_attempts(model),
                None => return,
            };

            if attempts.is_empty() {
                break;
            }

            // Sort by descending magnitude — try the largest values first
            // since they have the most room to shrink.
            attempts.sort_by_key(|a| std::cmp::Reverse(a.magnitude()));

            // Phase 2: For each variable, try candidates via mutate-check-revert.
            let mut any_changed = false;
            for attempt in attempts {
                let changed = match attempt {
                    MinAttempt::Lia(term_id, candidates) => {
                        self.try_lia_candidates(term_id, candidates)
                    }
                    MinAttempt::Lra(term_id, candidates) => {
                        self.try_lra_candidates(term_id, candidates)
                    }
                    MinAttempt::Bv(term_id, candidates) => {
                        self.try_bv_candidates(term_id, candidates)
                    }
                };
                any_changed |= changed;
            }

            // If nothing changed this pass, no point in another pass.
            if !any_changed {
                break;
            }
        }

        // Phase 3: Structural array minimization (#4522).
        //
        // Reduces array model size by choosing the most common store value as
        // the default, then removing stores that match the default. This is
        // purely structural — it preserves the array's semantics exactly —
        // so it is safe even with the #5478 evaluator bug that blocks scalar
        // minimization when arrays are present.
        self.minimize_array_models();
    }

    /// Collect all minimization attempts from the current model.
    fn collect_min_attempts(&self, model: &Model) -> Vec<MinAttempt> {
        let mut attempts = Vec::new();
        let has_datatypes = self.ctx.ctor_selectors_iter().next().is_some();
        // Skip ALL theory minimization when array model exists (#5478).
        // The SAT-level fallback in evaluate_term (mod.rs:669-682) overrides
        // correctly-computed Bool(false) with the stale SAT model truth value
        // for any equality involving an array subterm. This affects LIA, LRA,
        // and BV equally — not just BV as originally fixed.
        let has_arrays = model.array_model.is_some();

        if !has_arrays {
            if let Some(ref lia_model) = model.lia_model {
                for (&term_id, original) in &lia_model.values {
                    // Skip DT selector application terms — minimization would
                    // clobber their values since DT assertions are not evaluable (#5432).
                    if has_datatypes && self.is_dt_selector_app(term_id) {
                        continue;
                    }
                    let candidates = int_candidates(original);
                    if candidates.len() > 1 || candidates.first() != Some(original) {
                        attempts.push(MinAttempt::Lia(term_id, candidates));
                    }
                }
            }
        }

        if !has_arrays {
            if let Some(ref lra_model) = model.lra_model {
                for (&term_id, original) in &lra_model.values {
                    if has_datatypes && self.is_dt_selector_app(term_id) {
                        continue;
                    }
                    let candidates = rational_candidates(original);
                    if candidates.len() > 1 || candidates.first() != Some(original) {
                        attempts.push(MinAttempt::Lra(term_id, candidates));
                    }
                }
            }
        }

        if !has_arrays {
            if let Some(ref bv_model) = model.bv_model {
                for (&term_id, original) in &bv_model.values {
                    if has_datatypes && self.is_dt_selector_app(term_id) {
                        continue;
                    }
                    let width = match self.ctx.terms.sort(term_id) {
                        Sort::BitVec(bv) => bv.width,
                        _ => continue,
                    };
                    let candidates = bv_candidates(original, width);
                    if candidates.len() > 1 || candidates.first() != Some(original) {
                        attempts.push(MinAttempt::Bv(term_id, candidates));
                    }
                }
            }
        }

        attempts
    }

    /// Check if a term is a DT selector application (e.g., `(ival x)`).
    ///
    /// When datatypes are present, selector applications produce theory-model
    /// values that the model evaluator cannot validate (DT assertions are
    /// skipped). Minimizing these terms silently clobbers correct values (#5432).
    fn is_dt_selector_app(&self, term_id: TermId) -> bool {
        let name = match self.ctx.terms.get(term_id) {
            TermData::App(sym, _) => sym.name(),
            TermData::Var(name, _) => name.as_str(),
            _ => return false,
        };
        self.ctx
            .ctor_selectors_iter()
            .any(|(_, selectors)| selectors.iter().any(|sel| sel == name))
    }

    /// Try replacing a LIA variable with smaller candidates. Returns true if changed.
    fn try_lia_candidates(&mut self, term_id: TermId, candidates: Vec<BigInt>) -> bool {
        let original = match self
            .last_model
            .as_ref()
            .and_then(|m| m.lia_model.as_ref())
            .and_then(|lia| lia.values.get(&term_id))
        {
            Some(v) => v.clone(),
            None => return false,
        };

        for candidate in candidates {
            if candidate == original {
                break;
            }
            // Mutate
            if let Some(ref mut model) = self.last_model {
                if let Some(ref mut lia) = model.lia_model {
                    lia.values.insert(term_id, candidate.clone());
                }
            }
            // Check
            if self.model_satisfies_assertions() {
                return true; // Keep the smaller value
            }
            // Revert
            if let Some(ref mut model) = self.last_model {
                if let Some(ref mut lia) = model.lia_model {
                    lia.values.insert(term_id, original.clone());
                }
            }
        }
        false
    }

    /// Try replacing a LRA variable with smaller candidates. Returns true if changed.
    fn try_lra_candidates(&mut self, term_id: TermId, candidates: Vec<BigRational>) -> bool {
        let original = match self
            .last_model
            .as_ref()
            .and_then(|m| m.lra_model.as_ref())
            .and_then(|lra| lra.values.get(&term_id))
        {
            Some(v) => v.clone(),
            None => return false,
        };

        for candidate in candidates {
            if candidate == original {
                break;
            }
            if let Some(ref mut model) = self.last_model {
                if let Some(ref mut lra) = model.lra_model {
                    lra.values.insert(term_id, candidate.clone());
                }
            }
            if self.model_satisfies_assertions() {
                return true;
            }
            if let Some(ref mut model) = self.last_model {
                if let Some(ref mut lra) = model.lra_model {
                    lra.values.insert(term_id, original.clone());
                }
            }
        }
        false
    }

    /// Try replacing a BV variable with smaller candidates. Returns true if changed.
    fn try_bv_candidates(&mut self, term_id: TermId, candidates: Vec<BigInt>) -> bool {
        let original = match self
            .last_model
            .as_ref()
            .and_then(|m| m.bv_model.as_ref())
            .and_then(|bv| bv.values.get(&term_id))
        {
            Some(v) => v.clone(),
            None => return false,
        };

        for candidate in candidates {
            if candidate == original {
                break;
            }
            if let Some(ref mut model) = self.last_model {
                if let Some(ref mut bv) = model.bv_model {
                    bv.values.insert(term_id, candidate.clone());
                }
            }
            if self.model_satisfies_assertions() {
                return true;
            }
            if let Some(ref mut model) = self.last_model {
                if let Some(ref mut bv) = model.bv_model {
                    bv.values.insert(term_id, original.clone());
                }
            }
        }
        false
    }

    /// Check whether all assertions evaluate to true under the stored model.
    fn model_satisfies_assertions(&self) -> bool {
        let model = match self.last_model.as_ref() {
            Some(m) => m,
            None => return false,
        };
        for &assertion in &self.ctx.assertions {
            if self.contains_internal_symbol(assertion)
                || self.contains_quantifier(assertion)
                || self.contains_datatype_term(assertion)
            {
                continue;
            }
            match self.evaluate_term(model, assertion) {
                EvalValue::Bool(true) => {}
                _ => return false,
            }
        }
        true
    }

    /// Structurally minimize array models by reducing store count.
    ///
    /// For each array in the model:
    /// 1. Find the most frequent value among explicit stores.
    /// 2. If it occurs more than the current default, change the default to
    ///    that value and remove all stores that now match the default.
    /// 3. Remove any remaining stores where value == default.
    ///
    /// This is semantics-preserving: every `select` on the minimized array
    /// returns the same value as before. No evaluator calls needed.
    fn minimize_array_models(&mut self) {
        let model = match self.last_model.as_mut() {
            Some(m) => m,
            None => return,
        };
        let array_model = match model.array_model.as_mut() {
            Some(am) => am,
            None => return,
        };

        for interp in array_model.array_values.values_mut() {
            minimize_array_interpretation(interp);
        }
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
