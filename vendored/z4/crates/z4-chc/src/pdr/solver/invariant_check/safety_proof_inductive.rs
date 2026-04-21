// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inductive-subset model building for safety proofs.
//!
//! When the algebraic-only model doesn't block errors, builds a model from
//! algebraic lemmas + individually self-inductive non-algebraic lemmas.
//! Also includes error-guided lemma discovery for multi-predicate problems.

use super::*;

/// Result of the inductive-subset model search.
pub(super) enum InductiveSubsetOutcome {
    /// Found a verified model that blocks all errors.
    Proven(InvariantModel),
    /// Inductive subset was tried but doesn't block errors (multi-pred).
    /// The caller should skip the verification cascade.
    Insufficient,
    /// No result from inductive subset; returns the model for cascade.
    Cascade(InvariantModel),
}

impl PdrSolver {
    /// Inductive-subset fast-accept (#5425/#5401).
    ///
    /// When the algebraic-only model doesn't block errors, build a model from
    /// algebraic lemmas + individually self-inductive non-algebraic lemmas. If this
    /// inductive subset still blocks all errors, accept it immediately.
    ///
    /// This handles multi-predicate problems like s_multipl_25 where:
    /// - Sum invariants (algebraic) are discovered for all predicates
    /// - Propagated bounds from inter-predicate transitions are in frame[1]
    ///   but are NOT self-inductive (they hold at entry but not through self-loops)
    /// - The algebraic model alone doesn't block errors
    /// - verify_model_fast times out because non-inductive frame lemmas create
    ///   Unknown SMT results on transition clauses
    ///
    /// The inductive-subset model excludes non-inductive propagated bounds,
    /// keeping only algebraically-verified + self-inductive lemmas.
    ///
    /// For multi-predicate: also requires entry-inductiveness of each non-algebraic
    /// lemma, because self-inductiveness alone doesn't guarantee the lemma holds
    /// at inter-predicate transitions.
    ///
    /// `model` is the full frame model, consumed for the all-inductive path.
    pub(super) fn try_inductive_subset_model(
        &mut self,
        queries: &[HornClause],
        model: InvariantModel,
    ) -> InductiveSubsetOutcome {
        let is_multi_pred = self.problem.predicates().len() > 1;
        let non_algebraic_lemmas: Vec<(PredicateId, ChcExpr)> = self.frames[1]
            .lemmas
            .iter()
            .filter(|lemma| !lemma.algebraically_verified)
            .map(|lemma| (lemma.predicate, lemma.formula.clone()))
            .collect();

        if non_algebraic_lemmas.is_empty() {
            return InductiveSubsetOutcome::Cascade(model);
        }

        let mut inductive_lemmas: Vec<(PredicateId, ChcExpr)> = Vec::new();
        let mut all_inductive = true;

        // #5652: Check frame[1] consistency per predicate. If frame[1]
        // contains contradictory lemmas (e.g., x>10 AND x<=10 on
        // reachable_abort_unsafe_000), frame-strengthened self-inductiveness
        // is vacuously true (the pre-condition is UNSAT, so everything is
        // "inductive"). Use strict self-inductiveness for inconsistent
        // predicates to avoid accepting non-inductive lemmas.
        let inconsistent_preds: rustc_hash::FxHashSet<PredicateId> = {
            let mut inconsistent = rustc_hash::FxHashSet::default();
            let mut checked = rustc_hash::FxHashSet::default();
            for (pred, _) in &non_algebraic_lemmas {
                if !checked.insert(*pred) {
                    continue;
                }
                let frame_lemmas: Vec<ChcExpr> = self.frames[1]
                    .lemmas
                    .iter()
                    .filter(|l| l.predicate == *pred)
                    .map(|l| l.formula.clone())
                    .collect();
                if frame_lemmas.len() >= 2 {
                    let conjunction = ChcExpr::and_all(frame_lemmas);
                    let bounded = self.bound_int_vars(conjunction);
                    self.smt.reset();
                    match self
                        .smt
                        .check_sat_with_timeout(&bounded, std::time::Duration::from_millis(200))
                    {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: check_invariants_prove_safety: frame[1] for pred {} is INCONSISTENT, using strict self-inductiveness",
                                    pred.index()
                                );
                            }
                            inconsistent.insert(*pred);
                        }
                        _ => {}
                    }
                }
            }
            inconsistent
        };

        // Track whether all lemmas are strictly self-inductive (no frame
        // strengthening). Only strictly self-inductive models can safely skip
        // portfolio transition validation, because the portfolio's fresh solver
        // has no frame context.
        let mut all_strictly_inductive = true;
        let mut strictly_inductive_lemmas: Vec<(PredicateId, ChcExpr)> = Vec::new();

        for (pred, formula) in &non_algebraic_lemmas {
            let blocking = ChcExpr::not(formula.clone());
            let strict_ind = self.is_strictly_self_inductive_blocking(&blocking, *pred);
            let self_ind = if strict_ind {
                true
            } else if !inconsistent_preds.contains(pred) {
                self.is_self_inductive_blocking(&blocking, *pred)
            } else {
                false
            };
            if !strict_ind {
                all_strictly_inductive = false;
            }
            let init_valid =
                !self.predicate_has_facts(*pred) || self.blocks_initial_states(*pred, &blocking);
            let entry_ind = !is_multi_pred || self.is_entry_inductive(formula, *pred, 1);
            if self_ind && init_valid && entry_ind {
                inductive_lemmas.push((*pred, formula.clone()));
                if strict_ind {
                    strictly_inductive_lemmas.push((*pred, formula.clone()));
                }
            } else {
                all_inductive = false;
                if self.config.verbose {
                    if !self_ind {
                        safe_eprintln!(
                            "PDR: check_invariants_prove_safety: non-algebraic lemma {} for pred {} not self-inductive",
                            formula, pred.index()
                        );
                    } else if !init_valid {
                        safe_eprintln!(
                            "PDR: check_invariants_prove_safety: non-algebraic lemma {} for pred {} not init-valid",
                            formula, pred.index()
                        );
                    } else {
                        safe_eprintln!(
                            "PDR: check_invariants_prove_safety: non-algebraic lemma {} for pred {} not entry-inductive",
                            formula, pred.index()
                        );
                    }
                }
            }
        }

        // #7964: When the problem has no BV sorts, SMT reasoning over
        // Bool+Int is complete, so frame-relative self-inductiveness is
        // reliable. This covers:
        // - BvToBool-expanded problems (PDR with bv_bit_groups set)
        // - PDKIND/TPA running on the BvToBool-expanded problem (no
        //   bv_bit_groups but still no BV sorts)
        // - Pure LIA/Bool problems (where verify_model_fresh already
        //   succeeds, so this flag is redundant but harmless)
        //
        // Native BV problems (has_bv_sorts()=true) may have SMT
        // incompleteness on BV transition constraints, so frame-relative
        // inductiveness is not sufficient for them.
        let no_bv_sorts = !self.problem.has_bv_sorts();

        if all_inductive {
            // When ALL non-algebraic lemmas are frame-relative self-inductive,
            // the model is proven at the PDR level. The individually_inductive
            // flag controls whether safety_checks.rs skips verify_model_with_budget.
            //
            // #7964: For problems with no BV sorts, SMT reasoning over LIA/Bool
            // is complete, so frame-relative self-inductiveness is reliable.
            // Mark individually_inductive=true to skip verify_model_with_budget
            // which may fail on complex transitions (dillig03_m clause 4).
            //
            // SOUNDNESS NOTE: The false-Safe risk (conditional_branch_unsafe,
            // two_phase_unsafe, reachable_abort_unsafe) does NOT come from this
            // all_inductive path — those benchmarks have non-inductive lemmas
            // and reach the subset path below. The all_inductive path is safe
            // because every lemma passed is_self_inductive_blocking.
            let safe_individually_inductive = all_strictly_inductive || no_bv_sorts;
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety: all {} non-algebraic lemmas individually inductive ({}-predicate, strictly_inductive={}, individually_inductive={})",
                    non_algebraic_lemmas.len(),
                    self.problem.predicates().len(),
                    all_strictly_inductive,
                    safe_individually_inductive,
                );
            }
            let mut model = model;
            model.individually_inductive = safe_individually_inductive;
            return InductiveSubsetOutcome::Proven(model);
        }

        // Some non-algebraic lemmas are not inductive. Try the inductive subset.
        if !inductive_lemmas.is_empty() {
            let subset_model = self.build_model_from_algebraic_plus_inductive(1, &inductive_lemmas);
            let subset_blocks = self.algebraic_model_blocks_all_errors(&subset_model, queries);
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety: inductive-subset model ({} algebraic + {} inductive) blocks errors: {}",
                    self.frames[1].lemmas.iter().filter(|l| l.algebraically_verified).count(),
                    inductive_lemmas.len(),
                    subset_blocks
                );
            }

            // Error-guided lemma discovery (#5425)
            if is_multi_pred && !all_strictly_inductive {
                if let Some(guided_model) =
                    self.try_error_guided_discovery(queries, &strictly_inductive_lemmas)
                {
                    return InductiveSubsetOutcome::Proven(guided_model);
                }
            }

            if subset_blocks {
                // Check if strictly-inductive-only subset also blocks errors
                if !strictly_inductive_lemmas.is_empty() {
                    let all_strict = strictly_inductive_lemmas.len() == inductive_lemmas.len();
                    let mut strict_model = self
                        .build_model_from_algebraic_plus_inductive(1, &strictly_inductive_lemmas);
                    let strict_blocks = all_strict
                        || self.algebraic_model_blocks_all_errors(&strict_model, queries);
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: strictly-inductive-only subset ({} lemmas, all_strict={}) blocks errors: {}",
                            strictly_inductive_lemmas.len(),
                            all_strict,
                            strict_blocks
                        );
                    }
                    if strict_blocks {
                        strict_model.individually_inductive = true;
                        return InductiveSubsetOutcome::Proven(strict_model);
                    }
                } else if self.config.verbose {
                    safe_eprintln!(
                        "PDR: no strictly-inductive lemmas found; cannot build strict subset"
                    );
                }
                // #7964: Only force cascade for NATIVE BV single-predicate
                // problems, not for BvToBool-expanded problems. BvToBool
                // expansion converts BV sorts to Bool, so has_bv_sorts()
                // is false but bv_bit_groups is non-empty. BvToBool
                // transitions are fully expanded to Boolean logic, so
                // frame-relative self-inductiveness is more reliable than
                // on native BV where SMT verification of the BV transition
                // constraints can fail.
                let is_native_bv = self.problem.has_bv_sorts();
                let needs_bv_verification_cascade =
                    is_native_bv && self.problem.predicates().len() == 1 && !all_strictly_inductive;
                if needs_bv_verification_cascade {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: single-predicate BV inductive-subset candidate is non-strict; forcing verification cascade (#7964)"
                        );
                    }
                    return InductiveSubsetOutcome::Cascade(subset_model);
                }
                // SOUNDNESS FIX (#8827): The inductive-subset model
                // contains frame-relative (non-strict) lemmas whose
                // inductiveness may be circular. The strictly-inductive
                // subset was tried above and didn't block errors, so the
                // extra lemmas are only inductively valid WITH frame
                // strengthening. Route through verification cascade so
                // verify_model_fresh confirms actual inductiveness.
                // This catches false-Safe on conditional_branch_unsafe
                // and two_phase_unsafe. For correct models (dillig32),
                // the cascade's verify_model_fresh succeeds and accepts.
                //
                // For multi-predicate LIA with no BV sorts,
                // cross-predicate entry-inductiveness provides an
                // additional correctness signal — accept directly.
                if no_bv_sorts && is_multi_pred {
                    let mut model = subset_model;
                    model.individually_inductive = true;
                    return InductiveSubsetOutcome::Proven(model);
                }
                return InductiveSubsetOutcome::Cascade(subset_model);
            }
        }

        // Inductive subset was tried and doesn't block errors.
        if is_multi_pred {
            InductiveSubsetOutcome::Insufficient
        } else {
            InductiveSubsetOutcome::Cascade(model)
        }
    }

    /// Error-guided lemma discovery (#5425).
    ///
    /// For multi-predicate problems with non-strictly-inductive lemmas,
    /// build a strictly-self-inductive model by extracting error
    /// constraint negation components as candidate lemmas.
    fn try_error_guided_discovery(
        &mut self,
        queries: &[HornClause],
        strictly_inductive_lemmas: &[(PredicateId, ChcExpr)],
    ) -> Option<InvariantModel> {
        let mut error_guided_lemmas = strictly_inductive_lemmas.to_vec();
        let mut found_new = false;

        for query in queries {
            if query.body.predicates.len() != 1 {
                continue;
            }
            let (qpred_id, qbody_args) = &query.body.predicates[0];
            let qpred = *qpred_id;

            let qcanonical_vars = match self.canonical_vars(qpred) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            let mut qvar_map: FxHashMap<String, ChcVar> = FxHashMap::default();
            for (arg, canon) in qbody_args.iter().zip(qcanonical_vars.iter()) {
                match arg {
                    ChcExpr::Var(v) => {
                        qvar_map.insert(v.name.clone(), canon.clone());
                    }
                    expr => {
                        for v in expr.vars() {
                            qvar_map
                                .entry(v.name.clone())
                                .or_insert_with(|| canon.clone());
                        }
                    }
                }
            }

            let qerror = match &query.body.constraint {
                Some(c) => match Self::to_canonical(c, &qvar_map) {
                    Some(ec) => ec,
                    None => continue,
                },
                None => continue,
            };

            let conjuncts = Self::extract_conjuncts(&qerror);
            for conjunct in &conjuncts {
                let negated = Self::negate_atomic_constraint(conjunct);
                if let Some(candidate) = negated {
                    let blocking = ChcExpr::not(candidate.clone());
                    let strict = self.is_strictly_self_inductive_blocking(&blocking, qpred);
                    if !strict {
                        continue;
                    }
                    let init_valid = !self.predicate_has_facts(qpred)
                        || self.blocks_initial_states(qpred, &blocking);
                    if !init_valid {
                        continue;
                    }
                    let entry = self.is_entry_inductive(&candidate, qpred, 1);
                    if !entry {
                        continue;
                    }
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: error-guided discovery: found strictly self-inductive lemma {} for pred {}",
                            candidate, qpred.index()
                        );
                    }
                    error_guided_lemmas.push((qpred, candidate.clone()));
                    let lemma = Lemma::new(qpred, candidate, 1);
                    self.frames[1].add_lemma(lemma);
                    found_new = true;
                }
            }
        }

        if found_new {
            let guided_model =
                self.build_model_from_algebraic_plus_inductive(1, &error_guided_lemmas);
            let guided_blocks = self.algebraic_model_blocks_all_errors(&guided_model, queries);
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: error-guided model ({} strictly-ind + error-guided) blocks errors: {}",
                    error_guided_lemmas.len(),
                    guided_blocks
                );
            }
            if guided_blocks {
                let mut guided_model = guided_model;
                guided_model.individually_inductive = true;
                return Some(guided_model);
            }
        }

        None
    }
}
