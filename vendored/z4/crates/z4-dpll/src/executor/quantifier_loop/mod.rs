// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier processing pipeline for check-sat-internal.
//!
//! Orchestrates E-matching (multi-round with chaining), CEGQI (counterexample-guided
//! quantifier instantiation), promote-unsat optimization, CEGQI result mapping,
//! arithmetic refinement, and logic-category dispatch.
//!
//! Submodules:
//! - `preprocess`: finite-domain expansion, Skolemization, E-matching rounds,
//!   instance filtering, promote-unsat, CEGQI setup, assertion flattening.
//! - `result_mapping`: CEGQI/E-matching result interpretation and assertion restore.
//! - `cegqi_refinement`: multi-round arithmetic refinement and neighbor enumeration.
//! - `dispatch`: logic-category re-solve dispatch and interleaved E-matching.

mod cegqi_refinement;
mod dispatch;
mod preprocess;
mod result_mapping;

use z4_core::{TermData, TermId};

use super::Executor;
use crate::cegqi::CegqiInstantiator;
use crate::ematching::contains_quantifier;
use crate::quantifier_manager::QuantifierManager;

/// Result of quantifier preprocessing: flags consumed by `map_quantifier_result`.
pub(in crate::executor) struct QuantifierProcessingResult {
    /// Whether any quantifiers had no E-matching instantiations.
    pub has_uninstantiated_quantifiers: bool,
    /// Whether E-matching hit its round or per-round budget.
    pub reached_instantiation_limit: bool,
    /// Whether deferred instantiations remain.
    pub has_deferred: bool,
    /// Whether CEGQI handled at least one forall quantifier.
    pub cegqi_has_forall: bool,
    /// Whether CEGQI handled at least one exists quantifier.
    pub cegqi_has_exists: bool,
    /// Whether E-matching added any new ground instantiations.
    pub ematching_added_instantiations: bool,
    /// Assertion snapshot after finite-domain expansion and Skolemization but
    /// before stripping quantified formulas. Interleaved refinement should use
    /// this preprocessed view instead of reintroducing the original shapes.
    pub refinement_assertions: Option<Vec<TermId>>,
    /// CE lemma TermIds added by CEGQI, tracked by ID for position-independent
    /// filtering. Refinement rounds push ground instantiations after CE lemmas,
    /// so positional slicing from the end is incorrect (#5975 offset bug).
    pub cegqi_ce_lemma_ids: Vec<TermId>,
    /// Whether any quantifiers are completely unhandled (neither E-matching nor CEGQI).
    pub has_completely_unhandled_quantifiers: bool,
    /// Quantifiers not handled by either E-matching or CEGQI (#5971).
    /// Passed to MBQI for model-based counterexample checking.
    pub unhandled_quantifiers: Vec<TermId>,
    /// Whether E-matching processed any exists quantifiers (#3593).
    /// When true, UNSAT results are unreliable because E-matching adds exists
    /// instances as conjunctive assertions (all must hold), but exists semantics
    /// require a disjunction (at least one must hold).
    pub ematching_has_exists: bool,
    /// Original assertions snapshot (before E-matching modifications).
    /// `Some` when quantifiers were present; used to restore assertions after solving.
    pub original_assertions: Option<Vec<TermId>>,
    /// CEGQI state for refinement: (quantifier_id, instantiator) pairs.
    /// Used by `map_quantifier_result` to compute model-based instantiations
    /// when the CE lemma yields SAT (counterexample found).
    pub cegqi_state: Vec<(TermId, CegqiInstantiator)>,
}

impl QuantifierProcessingResult {
    /// Create a no-op result for the case when no quantifiers are present.
    pub(super) fn no_quantifiers() -> Self {
        Self {
            has_uninstantiated_quantifiers: false,
            reached_instantiation_limit: false,
            has_deferred: false,
            cegqi_has_forall: false,
            cegqi_has_exists: false,
            ematching_added_instantiations: false,
            refinement_assertions: None,
            cegqi_ce_lemma_ids: Vec::new(),
            has_completely_unhandled_quantifiers: false,
            unhandled_quantifiers: Vec::new(),
            ematching_has_exists: false,
            original_assertions: None,
            cegqi_state: Vec::new(),
        }
    }
}

impl Executor {
    /// Run quantifier preprocessing: E-matching, CEGQI, promote-unsat, assertion filtering.
    ///
    /// Returns a [`QuantifierProcessingResult`] with flags for result mapping and the
    /// original assertion snapshot for restoration after solving.
    ///
    /// This modifies `self.ctx.assertions` in place: E-matching instantiations are added,
    /// CEGQI CE lemmas are appended, and quantified formulas are stripped. The original
    /// assertions are saved in the result for post-solve restoration.
    pub(in crate::executor) fn process_quantifiers(&mut self) -> QuantifierProcessingResult {
        // 1. Early exit if no quantifiers present.
        // contains_quantifier uses memoization (visited set) to avoid
        // exponential re-traversal on DAG-structured terms.
        let has_quantifiers = self
            .ctx
            .assertions
            .iter()
            .any(|&a| contains_quantifier(&self.ctx.terms, a));
        if !has_quantifiers {
            return QuantifierProcessingResult::no_quantifiers();
        }

        // 2. Snapshot assertions for post-solve restoration (#2844).
        let original_assertions = Some(self.ctx.assertions.clone());

        // 3. Finite-domain expansion + Skolemization. Re-check for remaining quantifiers.
        self.expand_finite_domains();
        self.skolemize_existentials();

        let still_has_quantifiers = self
            .ctx
            .assertions
            .iter()
            .any(|&a| contains_quantifier(&self.ctx.terms, a));
        if !still_has_quantifiers {
            return QuantifierProcessingResult::no_quantifiers();
        }
        let refinement_assertions = Some(self.ctx.assertions.clone());

        // 4. E-matching rounds.
        let ematching = self.run_ematching_rounds();

        // 5. Add E-matching instances (duplicate + model-satisfied filtering).
        let ematching_added = self.add_ematching_instances(ematching.instantiations);

        // 6. Promote-unsat: promote conflict-producing deferred instantiations.
        let _promoted = self.promote_deferred_conflicts();

        // 7. Check remaining deferred state.
        let deferred_exists = self
            .quantifier_manager
            .as_ref()
            .is_some_and(QuantifierManager::has_deferred);

        // 8. Collect quantifiers and track exists E-matching processing (#3593).
        let quantifiers: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .copied()
            .filter(|&a| contains_quantifier(&self.ctx.terms, a))
            .collect();

        let ematching_has_exists = quantifiers.iter().any(|&q| {
            matches!(self.ctx.terms.get(q), TermData::Exists(..))
                && !ematching.uninstantiated_quantifiers.contains(&q)
        });

        // 9. CEGQI setup for unhandled quantifiers + FlattenAnd + strip quantifiers.
        let cegqi = self.setup_cegqi_for_unhandled(
            &quantifiers,
            ematching.has_uninstantiated,
            &ematching.uninstantiated_quantifiers,
        );

        // 10. Post-CEGQI E-matching pass (#7979): enumerative instantiation and
        // CEGQI may have introduced new ground terms (e.g., f(6)) that trigger
        // patterns in quantifiers that had no matches in step 4. Run one more
        // E-matching round over the current assertions (which now include
        // enumerative instances) combined with the original quantifiers.
        //
        // At this point, quantifiers have been stripped from self.ctx.assertions
        // by flatten_and_strip_quantifiers in step 9. We re-add them from the
        // refinement snapshot for this E-matching pass, then add any new
        // instances to the stripped assertion set.
        //
        // Guard: only run the extra round when CEGQI or enumerative
        // instantiation actually added new ground terms AND there are still
        // uninstantiated quantifiers that might benefit. When CEGQI didn't
        // handle any quantifiers, no new ground terms were produced, so the
        // post-CEGQI E-matching round would be redundant — and can cause
        // severe slowdowns (17x on sunder produces/reflexivity pattern).
        let cegqi_produced_new_terms = cegqi.cegqi_has_forall || cegqi.cegqi_has_exists;
        let (post_cegqi_added, post_cegqi_ematching) =
            if ematching.has_uninstantiated && cegqi_produced_new_terms {
                self.run_post_cegqi_ematching(
                    &refinement_assertions,
                    &ematching.uninstantiated_quantifiers,
                )
            } else {
                (false, None)
            };
        let ematching_added = ematching_added || post_cegqi_added;
        // Post-CEGQI E-matching may have resolved previously-uninstantiated quantifiers.
        let has_uninstantiated = post_cegqi_ematching
            .as_ref()
            .map_or(ematching.has_uninstantiated, |e| e.has_uninstantiated);
        let reached_limit = ematching.reached_limit
            || post_cegqi_ematching
                .as_ref()
                .is_some_and(|e| e.reached_limit);

        QuantifierProcessingResult {
            has_uninstantiated_quantifiers: has_uninstantiated,
            reached_instantiation_limit: reached_limit,
            has_deferred: deferred_exists,
            cegqi_has_forall: cegqi.cegqi_has_forall,
            cegqi_has_exists: cegqi.cegqi_has_exists,
            ematching_added_instantiations: ematching_added,
            refinement_assertions,
            cegqi_ce_lemma_ids: cegqi.cegqi_ce_lemma_ids,
            has_completely_unhandled_quantifiers: cegqi.has_completely_unhandled_quantifiers,
            unhandled_quantifiers: cegqi.unhandled_quantifiers,
            ematching_has_exists,
            original_assertions,
            cegqi_state: cegqi.cegqi_state,
        }
    }
}

/// Collect AND-conjuncts of a term transitively (#5991).
///
/// If `term` is `(and A B)`, recursively collects conjuncts `A`, `B` (and
/// their sub-conjuncts if they are also ANDs). Non-AND terms produce no output.
/// Used to expand CE lemma IDs after AND-flattening so that disambiguation
/// correctly filters out flattened CE lemma components.
pub(super) fn collect_and_conjuncts(
    terms: &z4_core::TermStore,
    term: TermId,
    out: &mut Vec<TermId>,
) {
    if let TermData::App(z4_core::Symbol::Named(ref name), args) = terms.get(term) {
        if name == "and" {
            for &arg in args {
                out.push(arg);
                collect_and_conjuncts(terms, arg, out);
            }
        }
    }
}
