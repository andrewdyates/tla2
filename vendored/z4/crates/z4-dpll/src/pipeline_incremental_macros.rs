// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental theory pipeline macro (without splits).
//!
//! Split from `pipeline_macros.rs` (#6321). Contains
//! [`solve_incremental_theory_pipeline`] for incremental theory solving
//! that maintains a persistent SAT solver across check-sat calls.
//!
//! The split-loop variant is in [`pipeline_incremental_split_macros`].

/// Incremental theory solving pipeline macro.
///
/// Extracts the common incremental DPLL(T) loop pattern shared by
/// `solve_euf`, `solve_lra_incremental`, and similar methods.
/// The incremental path maintains a persistent SAT solver and TseitinState
/// across check-sat calls, using SAT scope selectors for correct scoping.
///
/// # Parameters
/// - `$self`: the Executor instance
/// - `tag`: string label for debug messages (e.g., "EUF", "LRA")
/// - `create_theory`: expression producing a fresh theory solver each DPLL(T) iteration
/// - `extract_models`: closure `|theory: &mut T| -> TheoryModels`
/// - `track_theory_stats`: bool — track round_trips/theory_conflicts and call
///   `collect_theory_stats!(incremental: ...)`
/// - `set_unknown_on_error`: bool — set `UnknownReason::Incomplete` on verification failures
/// - `debug_semantic_check`: (optional) block for theory-specific debug semantic verification
macro_rules! solve_incremental_theory_pipeline {
    ($self:ident,
        tag: $tag:expr,
        create_theory: $create_theory:expr,
        extract_models: |$theory_var:ident| $extract:expr,
        track_theory_stats: $track_stats:expr,
        set_unknown_on_error: $set_unknown:expr
        $(, pre_sat_solve: |$sat_solver:ident, $ttv_ref:ident| $pre_sat_solve:expr)?
        $(, extra_active_atoms: $extra_atoms:expr)?
        $(, debug_semantic_check: |$dbg_conflict:ident, $dbg_terms:ident| $dbg_check:expr)?
    ) => {{
        use hashbrown::{HashMap, HashSet};
        use z4_core::{TermId, Tseitin, TseitinEncodedAssertion, TseitinResult};
        use z4_sat::{Literal as SatLiteral, SatResult, Solver as SatSolver, Variable as SatVariable};
        use $crate::executor_types::{SolveResult, UnknownReason};
        use $crate::incremental_state::{collect_active_theory_atoms, IncrementalTheoryState};
        use $crate::verification::{
            log_conflict_debug, verify_theory_conflict, verify_theory_conflict_with_farkas,
        };
        #[cfg(debug_assertions)]
        use $crate::verification::verify_theory_conflict_with_farkas_full;
        use $crate::executor::theories::freeze_var_if_needed;
        use $crate::executor::theories::solve_harness::TheoryModels;

        let proof_enabled = $self.produce_proofs_enabled();
        let _itp_problem_assertions = if proof_enabled {
            $self.proof_problem_assertions()
        } else {
            Vec::new()
        };
        let random_seed = $self.current_random_seed();
        let should_record_random_seed = match $self.incr_theory_state.as_ref() {
            Some(state) => state.persistent_sat.is_none(),
            None => true,
        };
        if should_record_random_seed {
            $self.record_applied_sat_random_seed_for_test(random_seed);
        }

        // Initialize or get incremental state
        let state = $self
            .incr_theory_state
            .get_or_insert_with(IncrementalTheoryState::new);

        if $track_stats {
            collect_theory_stats!(incremental: $self, state);
        }

        pipeline_incremental_setup!(
            $self, state, proof_enabled, random_seed, $tag,
            sat_field: persistent_sat,
            tseitin_field: tseitin_state,
            encoded_field: encoded_assertions,
            activation_scope_field: assertion_activation_scope,
            solver_init: { state.apply_pending_pushes(); },
            out: (new_assertion_set, solver, tseitin, var_to_term, term_to_var, pending_activations)
        );

        // Save tseitin num_vars before consuming, then release &TermStore borrow
        let _itp_tseitin_num_vars = tseitin.num_vars();
        state.tseitin_state = tseitin.into_state();

        // Proof tracking setup: tracker, assumptions, negation map (#6705, #6735, #5814 Packet A)
        pipeline_register_proof_context!(
            $self,
            proof_enabled,
            $tag,
            problem_assertions: _itp_problem_assertions
        );
        let mut _itp_negations = $crate::incremental_proof_cache::IncrementalNegationCache::seed(
            &mut $self.ctx.terms,
            var_to_term.values().copied(),
            proof_enabled,
        );

        // Make maps mutable so NeedLemmas/NeedModelEquality can allocate new SAT variables
        let mut var_to_term = var_to_term;
        let mut term_to_var = term_to_var;
        let mut _itp_next_var = _itp_tseitin_num_vars;
        let mut _itp_model_eq_retries: HashMap<(TermId, TermId), u32> = HashMap::new();

        state.persistent_sat = Some(solver);
        let solver = state
            .persistent_sat
            .as_mut()
            .expect(concat!("incremental ", $tag, " must store persistent SAT solver before solve"));
        $(
            let $sat_solver = &mut *solver;
            let $ttv_ref = &term_to_var;
            $pre_sat_solve;
        )?

        // Collect theory atoms in active assertions only
        let active_atoms = collect_active_theory_atoms(&$self.ctx.terms, &$self.ctx.assertions);
        // Extend with caller-supplied extra atoms (e.g., derived or_eq_lemma eq_terms)
        $(
            let active_atoms = {
                let mut _aa = active_atoms;
                for _ea_term in $extra_atoms {
                    _aa.insert(_ea_term);
                }
                _aa
            };
        )?
        for &term in &active_atoms {
            if let Some(&var) = term_to_var.get(&term) {
                freeze_var_if_needed(solver, SatVariable::new(var));
            }
        }
        // #6853: Apply deferred activations immediately (no private push in non-split path).
        pipeline_apply_pending_activations_immediate!(
            solver, pending_activations, proof_enabled, state
        );

        // Stash proof data for post-loop finalization (#6705).
        // We can't assign to $self fields inside the loop because solver/state
        // hold mutable borrows into $self.incr_theory_state.
        let mut _itp_proof_stash: Option<(
            Option<z4_sat::ClauseTrace>,
            HashMap<u32, TermId>,
            HashMap<TermId, TermId>,
            Vec<Option<z4_core::ClausificationProof>>,
            Vec<Option<z4_core::TheoryLemmaProof>>,
        )> = None;

        let mut _itp_refinement_count: u32 = 0;
        const _ITP_MAX_REFINEMENTS: u32 = 10_000;

        // In incremental mode, compute reachable terms to filter dead-scope
        // theory responses (#6726). After pop, the TermStore still contains
        // terms from popped scopes. The theory combiner scans all terms and
        // may produce NeedLemmas/NeedModelEquality for dead terms.
        let _itp_reachable: Option<HashSet<TermId>> = if $self.incremental_mode {
            Some($crate::executor::theories::reachable_term_set(
                &$self.ctx.terms,
                &$self.ctx.assertions,
            ))
        } else {
            None
        };

        // Lazy DPLL(T) loop
        let _itp_result: $crate::executor_types::Result<SolveResult> = loop {
            _itp_refinement_count += 1;
            if _itp_refinement_count > _ITP_MAX_REFINEMENTS {
                tracing::warn!(
                    tag = $tag,
                    refinements = _itp_refinement_count,
                    "incremental pipeline: max theory refinements exceeded; returning Unknown"
                );
                $self.last_result = Some(SolveResult::Unknown);
                break Ok(SolveResult::Unknown);
            }
            if $track_stats {
                state.round_trips += 1;
            }

            let sat_result = solver.solve().into_inner();
            if let Some(r) = solver.last_unknown_reason() {
                $self.last_unknown_reason = Some($crate::executor::Executor::map_sat_unknown_reason(r));
            }

            collect_sat_stats!($self, solver);

            if $track_stats {
                collect_theory_stats!(incremental: $self, state);
            }

                match sat_result {
                    SatResult::Sat(model) => {
                        _itp_negations.sync_pending(&mut $self.ctx.terms);
                        let mut theory = $create_theory;
                        z4_core::TheorySolver::reset(&mut theory);

                    for lemma in &state.theory_lemmas {
                        z4_core::TheorySolver::note_applied_theory_lemma(
                            &mut theory,
                            &lemma.clause,
                        );
                    }

                    // Sync model to theory
                    for (var, term) in $crate::iter_var_to_term_sorted(&var_to_term) {
                        if $crate::is_theory_atom(&$self.ctx.terms, term)
                            && active_atoms.contains(&term)
                        {
                            let value = match model.get(var as usize).copied() {
                                Some(v) => v,
                                None => match solver.value(SatVariable::new(var)) {
                                    Some(v) => v,
                                    // Unassigned theory atom — skip rather than
                                    // defaulting to false (#6188).
                                    None => continue,
                                },
                            };
                            z4_core::TheorySolver::assert_literal(&mut theory, term, value);
                        }
                    }

                    let _itp_theory_result = z4_core::TheorySolver::check(&mut theory);
                    // In incremental mode, filter dead-term NeedModelEquality responses
                    // (#6726). After pop(), the TermStore still has terms from popped
                    // scopes. The theory combiner (ArraySolver::populate_caches) scans
                    // all terms and may produce NeedModelEquality for dead terms.
                    // Treat these as SAT since the model is consistent for live terms.
                    let _itp_theory_result = match _itp_theory_result {
                        z4_core::TheoryResult::NeedModelEquality(ref eq)
                            if _itp_reachable
                                .as_ref()
                                .is_some_and(|r| !r.contains(&eq.lhs) || !r.contains(&eq.rhs)) =>
                        {
                            z4_core::TheoryResult::Sat
                        }
                        z4_core::TheoryResult::NeedModelEqualities(ref eqs)
                            if _itp_reachable.as_ref().is_some_and(|r| {
                                eqs.iter()
                                    .all(|eq| !r.contains(&eq.lhs) || !r.contains(&eq.rhs))
                            }) =>
                        {
                            z4_core::TheoryResult::Sat
                        }
                        other => other,
                    };
                    match _itp_theory_result {
                        z4_core::TheoryResult::Sat => {
                            let $theory_var = &mut theory;
                            let _itp_models = $extract;

                            let fake_result = TseitinResult::new(
                                vec![],
                                term_to_var
                                    .iter()
                                    .map(|(&t, &v)| (t, v + 1))
                                    .collect(),
                                var_to_term
                                    .iter()
                                    .map(|(&v, &t)| (v + 1, t))
                                    .collect(),
                                1,
                                _itp_tseitin_num_vars,
                            );
                            break $self.solve_and_store_model_with_theories(
                                SatResult::Sat(model),
                                &fake_result,
                                _itp_models,
                            );
                        }
                        z4_core::TheoryResult::Unsat(conflict_terms) => {
                            log_conflict_debug(&conflict_terms, concat!("incremental ", $tag, " UNSAT"));
                            if let Err(e) = verify_theory_conflict(&conflict_terms) {
                                tracing::error!(
                                    error = %e,
                                    conflict_len = conflict_terms.len(),
                                    concat!("BUG(#4666): ", $tag, " conflict verification failed; returning Unknown")
                                );
                                if $set_unknown {
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                }
                                $self.last_result = Some(SolveResult::Unknown);
                                break Ok(SolveResult::Unknown);
                            }

                            // Optional: semantic check
                            $(
                                {
                                    let $dbg_conflict = &conflict_terms;
                                    let $dbg_terms = &$self.ctx.terms;
                                    if let Err(e) = $dbg_check {
                                        tracing::error!(
                                            error = %e,
                                            concat!("BUG(#4666): ", $tag, " semantic verification failed; returning Unknown")
                                        );
                                        $self.last_result = Some(SolveResult::Unknown);
                                        break Ok(SolveResult::Unknown);
                                    }
                                }
                            )?

                            if proof_enabled {
                                // Record single theory lemma; proof-time
                                // decomposition in decompose_combined_real_conflict_lemmas
                                // handles EUF+LRA split (#6756 Packet 2).
                                let _ = $crate::theory_inference::record_theory_conflict_unsat(
                                    &mut $self.proof_tracker,
                                    Some(&$self.ctx.terms),
                                    _itp_negations.as_map(),
                                    &conflict_terms,
                                );
                            }

                            if $track_stats {
                                state.theory_conflicts = state.theory_conflicts.saturating_add(1);
                                collect_theory_stats!(incremental: $self, state);
                            }

                            pipeline_add_incremental_conflict_clause!(
                                $self,
                                state: state,
                                solver: solver,
                                term_to_var: term_to_var,
                                conflict_terms: conflict_terms,
                                tag: $tag,
                                set_unknown_on_error: $set_unknown,
                                unmapped_message: "incremental pipeline: theory conflict terms all failed to map; returning Unknown"
                            );
                        }
                        z4_core::TheoryResult::UnsatWithFarkas(conflict) => {
                            log_conflict_debug(
                                &conflict.literals,
                                concat!("incremental ", $tag, " UnsatWithFarkas"),
                            );
                            let mut _itp_farkas_proof_valid = conflict.farkas.is_some();
                            if let Err(e) = verify_theory_conflict_with_farkas(&conflict) {
                                if e.is_missing_annotation() {
                                    // Missing Farkas annotation (#6535): conflict is sound but
                                    // proof certificate cannot be recorded. Continue learning
                                    // the conflict clause without aborting.
                                    _itp_farkas_proof_valid = false;
                                    tracing::debug!(
                                        conflict_len = conflict.literals.len(),
                                        concat!($tag, " Farkas annotation missing; conflict clause is sound, skipping proof cert")
                                    );
                                } else {
                                    _itp_farkas_proof_valid = false;
                                    tracing::error!(
                                        error = %e,
                                        conflict_len = conflict.literals.len(),
                                        concat!("BUG(#4666): ", $tag, " Farkas structural verification failed; returning Unknown")
                                    );
                                    if $set_unknown {
                                        $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    }
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break Ok(SolveResult::Unknown);
                                }
                            }
                            // Semantic Farkas verification. Debug-only: BigRational
                            // arithmetic per conflict is too expensive for release (W16-5).
                            #[cfg(debug_assertions)]
                            if _itp_farkas_proof_valid && conflict.farkas.is_some() {
                                if let Err(e) =
                                    verify_theory_conflict_with_farkas_full(&conflict, &$self.ctx.terms)
                                {
                                    _itp_farkas_proof_valid = false;
                                    tracing::error!(
                                        error = %e,
                                        conflict_len = conflict.literals.len(),
                                        concat!("BUG(#4666): ", $tag, " Farkas semantic verification failed; returning Unknown")
                                    );
                                    if $set_unknown {
                                        $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    }
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break Ok(SolveResult::Unknown);
                                }
                            }

                            if proof_enabled && _itp_farkas_proof_valid {
                                let _ = $crate::theory_inference::record_theory_conflict_unsat_with_farkas(
                                    &mut $self.proof_tracker,
                                    Some(&$self.ctx.terms),
                                    _itp_negations.as_map(),
                                    &conflict,
                                );
                            }

                            if $track_stats {
                                state.theory_conflicts = state.theory_conflicts.saturating_add(1);
                                collect_theory_stats!(incremental: $self, state);
                            }

                            pipeline_add_incremental_conflict_clause!(
                                $self,
                                state: state,
                                solver: solver,
                                term_to_var: term_to_var,
                                conflict_terms: conflict.literals,
                                tag: $tag,
                                set_unknown_on_error: $set_unknown,
                                unmapped_message: "incremental pipeline: Farkas conflict terms all failed to map; returning Unknown"
                            );
                        }
                        z4_core::TheoryResult::NeedLemmas(lemmas) => {
                            let mut any_new = false;
                            let mut new_lemmas = Vec::new();
                            for lemma in &lemmas {
                                if !state.theory_lemma_keys.insert(lemma.clause.clone()) {
                                    continue;
                                }
                                any_new = true;
                                let recorded_in_trace = $crate::executor::theories::split_incremental::apply_theory_lemma_incremental_persistent(
                                    solver,
                                    &mut term_to_var,
                                    &mut var_to_term,
                                    &mut _itp_negations,
                                    &lemma.clause,
                                );
                                z4_core::TheorySolver::note_applied_theory_lemma(
                                    &mut theory,
                                    &lemma.clause,
                                );
                                new_lemmas.push((lemma.clone(), recorded_in_trace));
                            }

                            if !any_new {
                                if $set_unknown {
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                }
                                $self.last_result = Some(SolveResult::Unknown);
                                break Ok(SolveResult::Unknown);
                            }

                            let _ = theory;

                            if proof_enabled {
                                _itp_negations.sync_pending(&mut $self.ctx.terms);
                                for (lemma, recorded_in_trace) in &new_lemmas {
                                    let terms: Vec<TermId> = lemma
                                        .clause
                                        .iter()
                                        .map(|lit| {
                                            if lit.value {
                                                lit.term
                                            } else {
                                                *_itp_negations
                                                    .as_map()
                                                    .get(&lit.term)
                                                    .expect("persistent theory-lemma negation cache should be synced")
                                            }
                                        })
                                        .collect();
                                    // #8106: Infer specific theory lemma kind instead
                                    // of defaulting to Generic/trust. NeedLemmas are
                                    // typically array ROW2 axioms.
                                    let kind =
                                        $crate::theory_inference::infer_theory_lemma_kind_from_clause_terms(
                                            &$self.ctx.terms,
                                            &terms,
                                        );
                                    match kind {
                                        z4_core::TheoryLemmaKind::Generic => {
                                            let _ = $self.proof_tracker.add_theory_lemma(terms);
                                        }
                                        _ => {
                                            let _ = $self
                                                .proof_tracker
                                                .add_theory_lemma_with_kind(terms, kind);
                                        }
                                    }
                                    if *recorded_in_trace {
                                        state.clausification_proofs.push(None);
                                        state.original_clause_theory_proofs.push(Some(
                                            z4_core::TheoryLemmaProof {
                                                kind,
                                                farkas: None,
                                                lia: None,
                                            },
                                        ));
                                    }
                                }
                            }
                            state
                                .theory_lemmas
                                .extend(new_lemmas.into_iter().map(|(lemma, _)| lemma));
                            continue;
                        }
                        z4_core::TheoryResult::NeedModelEquality(eq) => {
                            // Encode the equality atom into the SAT solver so the
                            // next solve round can decide it. Dead-term requests
                            // are already filtered to Sat above (#6726).
                            let retry = _itp_model_eq_retries
                                .entry((eq.lhs, eq.rhs))
                                .or_insert(0);
                            *retry += 1;
                            if *retry > 2 {
                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                $self.last_result = Some(SolveResult::Unknown);
                                break Ok(SolveResult::Unknown);
                            }
                            pipeline_encode_model_equality!(
                                $self, solver, term_to_var, var_to_term,
                                _itp_next_var, _itp_negations, eq
                            );
                            continue;
                        }
                        z4_core::TheoryResult::NeedModelEqualities(eqs) => {
                            // Dead-term requests are already filtered to Sat above (#6726).
                            for eq in &eqs {
                                let retry = _itp_model_eq_retries
                                    .entry((eq.lhs, eq.rhs))
                                    .or_insert(0);
                                *retry += 1;
                                if *retry > 2 {
                                    continue;
                                }
                                pipeline_encode_model_equality!(
                                    $self, solver, term_to_var, var_to_term,
                                    _itp_next_var, _itp_negations, *eq
                                );
                            }
                            continue;
                        }
                        z4_core::TheoryResult::Unknown
                        | z4_core::TheoryResult::NeedSplit(_)
                        | z4_core::TheoryResult::NeedDisequalitySplit(_)
                        | z4_core::TheoryResult::NeedExpressionSplit(_)
                        | z4_core::TheoryResult::NeedStringLemma(_) => {
                            $self.last_result = Some(SolveResult::Unknown);
                            break Ok(SolveResult::Unknown);
                        }
                            // All current TheoryResult variants are handled above.
                            // This arm is required by #[non_exhaustive] and catches future variants.
                            other => unreachable!("unhandled TheoryResult variant in incremental pipeline: {other:?}"),
                    }
                }
                SatResult::Unsat => {
                    // Stash proof data for post-loop finalization (#6705)
                    if proof_enabled {
                        _itp_negations.sync_pending(&mut $self.ctx.terms);
                        let _itp_clause_trace = solver.clause_trace().cloned();
                        // Resize clausification proofs to match trace (#6705, #6686)
                        if let Some(ref trace) = _itp_clause_trace {
                            let original_count = trace.original_clauses().count();
                            if state.clausification_proofs.len() < original_count {
                                state.clausification_proofs.resize(original_count, None);
                            }
                            if state.original_clause_theory_proofs.len() < original_count {
                                state.original_clause_theory_proofs.resize(original_count, None);
                            }
                        }
                        _itp_proof_stash = Some((
                            _itp_clause_trace,
                            var_to_term.iter().map(|(&v, &t)| (v, t)).collect(),
                            _itp_negations.as_map().clone(),
                            state.clausification_proofs.clone(),
                            state.original_clause_theory_proofs.clone(),
                        ));
                    }
                    $self.last_model = None;
                    $self.last_result = Some(SolveResult::Unsat);
                    break Ok(SolveResult::Unsat);
                }
                SatResult::Unknown => {
                    $self.last_model = None;
                    if $self.last_unknown_reason.is_none() {
                        $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    }
                    $self.last_result = Some(SolveResult::Unknown);
                    break Ok(SolveResult::Unknown);
                }
                #[allow(unreachable_patterns)]
                _ => unreachable!(),
            }
        };

        // Finalize proof after loop exits (borrows on state/solver are released) (#6705)
        if let Some((_itp_ct, _itp_vtm, _itp_neg, _itp_cp, _itp_tp)) = _itp_proof_stash {
            $self.last_clause_trace = _itp_ct;
            $self.last_var_to_term = Some(_itp_vtm);
            $self.last_negations = Some(_itp_neg);
            $self.last_clausification_proofs = Some(_itp_cp);
            $self.last_original_clause_theory_proofs = Some(_itp_tp);
            $self.build_unsat_proof();
        }

        _itp_result
    }};
}
