// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier preprocessing helpers for `process_quantifiers`.
//!
//! Contains finite-domain expansion, Skolemization, E-matching rounds,
//! instance filtering, promote-unsat, CEGQI setup, and assertion flattening.
//! These are private `impl Executor` methods called from the orchestrator
//! in `mod.rs`.

#[cfg(not(kani))]
use hashbrown::HashSet;
#[cfg(kani)]
use z4_core::kani_compat::DetHashSet as HashSet;
use z4_core::{TermData, TermId};

use super::super::model::EvalValue;
use super::super::Executor;
use super::collect_and_conjuncts;
use crate::cegqi::{is_cegqi_candidate, CegqiInstantiator};
use crate::ematching::{contains_quantifier, enumerative_instantiation};
use crate::preprocess::{FlattenAnd, PreprocessingPass};
use crate::quantifier_manager::QuantifierManager;

// MAX_EMATCHING_ROUNDS is now accessed via self.ematching_round_limit() (#7893)

/// Intermediate results from the E-matching phase.
pub(super) struct EmatchingSummary {
    pub instantiations: Vec<TermId>,
    pub has_uninstantiated: bool,
    pub uninstantiated_quantifiers: HashSet<TermId>,
    pub reached_limit: bool,
}

/// Intermediate results from CEGQI setup.
pub(super) struct CegqiPreparation {
    pub cegqi_has_forall: bool,
    pub cegqi_has_exists: bool,
    pub cegqi_ce_lemma_ids: Vec<TermId>,
    pub has_completely_unhandled_quantifiers: bool,
    pub unhandled_quantifiers: Vec<TermId>,
    pub cegqi_state: Vec<(TermId, CegqiInstantiator)>,
}

impl Executor {
    /// Expand finite-domain quantifiers (Bool, small BV) into ground conjunctions/disjunctions.
    ///
    /// For `(forall ((b Bool)) (P b))` → `(and (P true) (P false))`.
    /// For `(exists ((b Bool)) (P b))` → `(or (P true) (P false))`.
    /// Runs BEFORE Skolemization so finite-domain existentials get ground expansion
    /// instead of Skolem constants. Up to 256 combinations per quantifier. (#5848)
    pub(super) fn expand_finite_domains(&mut self) {
        let mut expanded = Vec::new();
        for i in 0..self.ctx.assertions.len() {
            let a = self.ctx.assertions[i];
            if let Some(ground) = crate::skolemize::finite_domain_expand(&mut self.ctx.terms, a) {
                expanded.push((i, ground));
            }
        }
        for (idx, ground) in expanded {
            self.ctx.assertions[idx] = ground;
        }
    }

    /// Skolemize existential quantifiers via polarity-aware deep walk.
    ///
    /// - Positive Exists(vars, body) → body[vars := fresh_constants]
    /// - Negative Forall(vars, body) → (¬body)[vars := fresh_constants]
    ///
    /// Handles existentials nested inside conjunctions/disjunctions, matching
    /// Z3's NNF Skolemizer (reference/z3/src/ast/normal_forms/nnf.cpp:407).
    /// Runs after finite domain expansion so only non-finite-domain existentials
    /// are Skolemized. (#5840)
    pub(super) fn skolemize_existentials(&mut self) {
        let mut skolemized = Vec::new();
        for i in 0..self.ctx.assertions.len() {
            let a = self.ctx.assertions[i];
            if let Some(body) = crate::skolemize::skolemize_deep(&mut self.ctx.terms, a, true) {
                skolemized.push((i, body));
            }
        }
        for (idx, body) in skolemized {
            self.ctx.assertions[idx] = body;
        }
    }

    /// Run multi-round E-matching, collecting instantiations across rounds.
    ///
    /// Uses the persistent `QuantifierManager` for generation tracking (#573).
    /// Extracts the EUF model from the last solve for congruence-aware matching
    /// (Phase B1b, #3325).
    pub(super) fn run_ematching_rounds(&mut self) -> EmatchingSummary {
        let max_rounds = self.ematching_round_limit();
        let euf_model_ref = self.last_model.as_ref().and_then(|m| m.euf_model.as_ref());

        let qm = self
            .quantifier_manager
            .get_or_insert_with(QuantifierManager::new);
        let mut assertions_for_round = self.ctx.assertions.clone();
        let mut seen_instantiations: HashSet<TermId> =
            assertions_for_round.iter().copied().collect();
        let mut all_instantiations = Vec::new();
        let mut has_uninstantiated = false;
        let mut uninstantiated_quantifiers = HashSet::new();
        let mut reached_limit = false;
        let mut exhausted_round_budget = false;

        for round_idx in 0..max_rounds {
            let ematching_result =
                qm.run_ematching_round(&mut self.ctx.terms, &assertions_for_round, euf_model_ref);
            let round_reached_limit = ematching_result.reached_limit;
            let round_has_uninstantiated = ematching_result.has_uninstantiated;
            let round_uninstantiated_quantifiers = ematching_result.uninstantiated_quantifiers;
            let mut round_added = 0usize;

            for inst in ematching_result.instantiations {
                if seen_instantiations.insert(inst) {
                    assertions_for_round.push(inst);
                    all_instantiations.push(inst);
                    round_added += 1;
                }
            }

            has_uninstantiated = round_has_uninstantiated;
            uninstantiated_quantifiers = round_uninstantiated_quantifiers;
            reached_limit |= round_reached_limit;

            if round_reached_limit || round_added == 0 {
                break;
            }

            // We still made progress on the last allowed round, so there may be
            // additional instantiations if we continued. Treat this as incomplete.
            if round_idx + 1 == max_rounds {
                exhausted_round_budget = true;
            }
        }

        if exhausted_round_budget {
            reached_limit = true;
        }

        // Post-loop invariant: all_instantiations is a deduplicated set
        // and its items are a subset of assertions_for_round.
        debug_assert!(
            all_instantiations.len() <= assertions_for_round.len() - self.ctx.assertions.len(),
            "E-matching: more unique instantiations ({}) than new assertions ({})",
            all_instantiations.len(),
            assertions_for_round.len() - self.ctx.assertions.len()
        );

        EmatchingSummary {
            instantiations: all_instantiations,
            has_uninstantiated,
            uninstantiated_quantifiers,
            reached_limit,
        }
    }

    /// Add E-matching instantiations to assertions, filtering duplicates and
    /// model-satisfied instances (Phase C, #575).
    ///
    /// Returns `true` if any new instantiation was added.
    pub(super) fn add_ematching_instances(&mut self, instantiations: Vec<TermId>) -> bool {
        let existing: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut skipped_satisfied = 0usize;
        let mut added_count = 0usize;
        for inst in instantiations {
            if existing.contains(&inst) {
                continue;
            }
            // Phase C (#575): Skip instantiations already satisfied by model
            if let Some(ref model) = self.last_model {
                if matches!(self.evaluate_term(model, inst), EvalValue::Bool(true)) {
                    skipped_satisfied += 1;
                    continue;
                }
            }
            self.ctx.assertions.push(inst);
            added_count += 1;
        }
        let _ = skipped_satisfied;
        added_count > 0
    }

    /// Promote-unsat optimization (Phase D, #557): check deferred instantiations
    /// against the current model and promote conflict-producing ones.
    ///
    /// Returns the number of promoted instantiations.
    pub(super) fn promote_deferred_conflicts(&mut self) -> usize {
        let existing: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();

        let promoted_count = if let Some(ref model) = self.last_model {
            // Phase 1: Extract deferred entries and instantiate terms
            let deferred_with_terms: Vec<_> = {
                let qm = self
                    .quantifier_manager
                    .as_mut()
                    .expect("invariant: quantifier_manager populated by get_or_insert_with above");
                qm.deferred
                    .drain(..)
                    .map(|def| {
                        let inst_term = def.instantiate(&mut self.ctx.terms);
                        (def, inst_term)
                    })
                    .collect()
            };

            // Phase 2: Evaluate each term and decide promote/keep
            let mut promoted = 0usize;
            let mut remaining_deferred = std::collections::VecDeque::new();
            for (def, inst_opt) in deferred_with_terms {
                if let Some(inst_term) = inst_opt {
                    let negated = self.ctx.terms.mk_not(inst_term);
                    match self.evaluate_term(model, negated) {
                        EvalValue::Bool(true) => {
                            if !existing.contains(&inst_term) {
                                self.ctx.assertions.push(inst_term);
                                promoted += 1;
                            }
                        }
                        _ => {
                            remaining_deferred.push_back(def);
                        }
                    }
                } else {
                    remaining_deferred.push_back(def);
                }
            }

            // Phase 3: Put back non-promoted deferred
            if let Some(ref mut qm) = self.quantifier_manager {
                qm.deferred = remaining_deferred;
            }
            promoted
        } else {
            0
        };
        promoted_count
    }

    /// Set up CEGQI for arithmetic quantifiers that E-matching couldn't handle.
    ///
    /// Only applied to quantifiers with no E-matching instantiations (#1939).
    /// Also runs enumerative instantiation for triggerless forall quantifiers
    /// (#3441/#5042). Tracks completely unhandled quantifiers for MBQI (#2865/#5971).
    pub(super) fn setup_cegqi_for_unhandled(
        &mut self,
        quantifiers: &[TermId],
        ematching_has_uninstantiated: bool,
        ematching_uninstantiated_quantifiers: &HashSet<TermId>,
    ) -> CegqiPreparation {
        let mut cegqi_has_forall = false;
        let mut cegqi_has_exists = false;
        let mut raw_ce_lemma_ids: Vec<TermId> = Vec::new();
        let mut cegqi_ce_lemma_ids: Vec<TermId> = Vec::new();
        let mut has_completely_unhandled_quantifiers = false;
        let mut unhandled_quantifier_list: Vec<TermId> = Vec::new();
        let mut cegqi_state: Vec<(TermId, CegqiInstantiator)> = Vec::new();
        // Enumerative instantiation is an incomplete fallback. It should range
        // over ground terms already present in the preprocessed problem, not
        // recursively bootstrap on sibling instantiations added earlier in the
        // same pass. Using the growing assertion set lets later triggerless
        // quantifiers enumerate terms synthesized by earlier ones, creating a
        // one-shot saturation loop on recursive axiom families (#7883).
        let enum_seed_assertions = self.ctx.assertions.clone();

        if ematching_has_uninstantiated {
            for &quant in quantifiers {
                if !ematching_uninstantiated_quantifiers.contains(&quant) {
                    continue;
                }
                let has_triggers = match self.ctx.terms.get(quant) {
                    TermData::Forall(_, _, triggers) | TermData::Exists(_, _, triggers) => {
                        !triggers.is_empty()
                    }
                    _ => false,
                };

                // #3441/#5042: For triggerless FORALL quantifiers, run enumerative
                // instantiation as a complement to CEGQI.
                let is_forall = matches!(self.ctx.terms.get(quant), TermData::Forall(..));
                if !has_triggers && is_forall {
                    let enum_insts = enumerative_instantiation(
                        &mut self.ctx.terms,
                        &enum_seed_assertions,
                        quant,
                        100,
                    );
                    for inst in enum_insts {
                        self.ctx.assertions.push(inst);
                    }
                }

                let mut handled_by_cegqi = false;
                // #6045: Skip CEGQI for trigger-annotated quantifiers.
                if !has_triggers && is_cegqi_candidate(&self.ctx.terms, quant) {
                    if let Some(inst) = CegqiInstantiator::new(quant, &mut self.ctx.terms) {
                        if let Some(ce_lemma) = inst.create_ce_lemma(&mut self.ctx.terms) {
                            if inst.is_forall() {
                                cegqi_has_forall = true;
                            } else {
                                cegqi_has_exists = true;
                            }
                            self.ctx.assertions.push(ce_lemma);
                            raw_ce_lemma_ids.push(ce_lemma);
                            handled_by_cegqi = true;
                            cegqi_state.push((quant, inst));
                        }
                    }
                }
                if !handled_by_cegqi && !has_triggers {
                    has_completely_unhandled_quantifiers = true;
                    unhandled_quantifier_list.push(quant);
                }
            }
        }

        // Flatten, recompute CE lemma IDs, and strip quantifiers.
        self.flatten_and_strip_quantifiers(&raw_ce_lemma_ids, &mut cegqi_ce_lemma_ids);

        CegqiPreparation {
            cegqi_has_forall,
            cegqi_has_exists,
            cegqi_ce_lemma_ids,
            has_completely_unhandled_quantifiers,
            unhandled_quantifiers: unhandled_quantifier_list,
            cegqi_state,
        }
    }

    /// Flatten top-level AND assertions (#4877), recompute CE lemma IDs after
    /// flattening (#5991), and strip quantified formulas from assertions.
    fn flatten_and_strip_quantifiers(
        &mut self,
        raw_ce_lemma_ids: &[TermId],
        cegqi_ce_lemma_ids: &mut Vec<TermId>,
    ) {
        {
            let mut flatten = FlattenAnd::new();
            flatten.apply(&mut self.ctx.terms, &mut self.ctx.assertions);
        }

        if !raw_ce_lemma_ids.is_empty() {
            let mut expanded = Vec::new();
            for &ce_id in raw_ce_lemma_ids {
                expanded.push(ce_id);
                collect_and_conjuncts(&self.ctx.terms, ce_id, &mut expanded);
            }
            let ce_set: HashSet<TermId> = expanded.into_iter().collect();
            *cegqi_ce_lemma_ids = self
                .ctx
                .assertions
                .iter()
                .copied()
                .filter(|a| ce_set.contains(a))
                .collect();
        }

        self.ctx
            .assertions
            .retain(|&a| !contains_quantifier(&self.ctx.terms, a));
    }

    /// Post-CEGQI E-matching pass (#7979): run one E-matching round over the
    /// current (quantifier-stripped) assertions combined with the original
    /// quantifiers from the refinement snapshot.
    ///
    /// Enumerative instantiation and CEGQI may have introduced new ground terms
    /// (e.g., `f(6)` from a triggerless `forall y. y > 5 => f(y) > 0`) that
    /// can trigger patterns in other quantifiers. Without this pass, the
    /// triggered quantifier never sees the ground term and returns Unknown.
    ///
    /// Returns `(added_any, Option<EmatchingSummary>)`.
    pub(super) fn run_post_cegqi_ematching(
        &mut self,
        refinement_assertions: &Option<Vec<TermId>>,
        _prev_uninstantiated: &HashSet<TermId>,
    ) -> (bool, Option<EmatchingSummary>) {
        let Some(ref_assertions) = refinement_assertions else {
            return (false, None);
        };

        // Build combined assertion set: current stripped assertions + quantifiers
        // from the refinement snapshot. This lets E-matching see both the new
        // ground terms from enumerative/CEGQI and the quantifier patterns.
        let mut combined = self.ctx.assertions.clone();
        for &a in ref_assertions {
            if contains_quantifier(&self.ctx.terms, a) && !combined.contains(&a) {
                combined.push(a);
            }
        }

        let euf_model_ref = self.last_model.as_ref().and_then(|m| m.euf_model.as_ref());
        let qm = self
            .quantifier_manager
            .get_or_insert_with(QuantifierManager::new);

        let ematching_result =
            qm.run_ematching_round(&mut self.ctx.terms, &combined, euf_model_ref);

        let existing: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut added_count = 0usize;

        for &inst in &ematching_result.instantiations {
            if existing.contains(&inst) {
                continue;
            }
            // Skip quantifier-containing terms (they should not be added as ground instances)
            if contains_quantifier(&self.ctx.terms, inst) {
                continue;
            }
            self.ctx.assertions.push(inst);
            added_count += 1;
        }

        if added_count > 0 {
            let summary = EmatchingSummary {
                instantiations: ematching_result.instantiations,
                has_uninstantiated: ematching_result.has_uninstantiated,
                uninstantiated_quantifiers: ematching_result.uninstantiated_quantifiers,
                reached_limit: ematching_result.reached_limit,
            };
            (true, Some(summary))
        } else {
            (false, None)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use z4_core::{Sort, Symbol, TermData};
    use z4_frontend::parse;

    #[test]
    fn test_triggerless_enumeration_uses_frozen_seed_assertions_7883() {
        let smt = r#"
            (set-logic ALL)
            (declare-sort S 0)
            (declare-fun a () S)
            (declare-fun g (S) S)
            (declare-fun P (S) Bool)
            (assert (P a))
            (assert (forall ((x S)) (P (g x))))
            (assert (forall ((y S)) (=> (P y) false)))
        "#;
        let commands = parse(smt).expect("valid SMT-LIB input");
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).expect("commands execute");
        assert!(
            outputs.is_empty(),
            "setup-only script should not emit output"
        );

        let quantifiers: Vec<TermId> = exec
            .ctx
            .assertions
            .iter()
            .copied()
            .filter(|&a| contains_quantifier(&exec.ctx.terms, a))
            .collect();
        assert_eq!(quantifiers.len(), 2, "expected two triggerless quantifiers");

        let uninstantiated: HashSet<TermId> = quantifiers.iter().copied().collect();

        let ground_assertion = exec.ctx.assertions[0];
        let (p_sym, a_term) = match exec.ctx.terms.get(ground_assertion) {
            TermData::App(sym, args) if args.len() == 1 => (sym.clone(), args[0]),
            other => panic!("expected ground assertion P(a), got {other:?}"),
        };
        let a_sort = exec.ctx.terms.sort(a_term).clone();
        let g_a = exec
            .ctx
            .terms
            .mk_app(Symbol::named("g"), vec![a_term], a_sort);
        let p_g_a = exec.ctx.terms.mk_app(p_sym, vec![g_a], Sort::Bool);
        let not_p_a = exec.ctx.terms.mk_not(ground_assertion);
        let not_p_g_a = exec.ctx.terms.mk_not(p_g_a);

        let _prep = exec.setup_cegqi_for_unhandled(&quantifiers, true, &uninstantiated);

        assert!(
            exec.ctx.assertions.contains(&p_g_a),
            "first quantifier should still enumerate x := a and add P(g(a))"
        );
        assert!(
            exec.ctx.assertions.contains(&not_p_a),
            "second quantifier should still enumerate over the original seed term a"
        );
        assert!(
            !exec.ctx.assertions.contains(&not_p_g_a),
            "second quantifier must not bootstrap on P(g(a)) added earlier in the same pass"
        );
    }
}
