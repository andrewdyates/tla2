// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eager-persistent arm of the incremental split-loop pipeline.
//!
//! Extracted from `pipeline_incremental_split_macros.rs` (#6680).
//! Contains the persistent-theory lifecycle: theory is created once before
//! the loop and warm-reset each iteration instead of recreated.
//! Preserves simplex basis and variable values across iterations,
//! matching Z3's persistent lar_solver architecture.

/// Eager-persistent arm implementation for `solve_incremental_split_loop_pipeline!`.
///
/// Key differences from @eager:
/// 1. Theory created once before the loop, soft_reset_warm() each iteration
/// 2. set_terms()/unset_terms() bracket each iteration's term access
/// 3. No structural snapshot needed (theory persists)
/// 4. Theory is NOT dropped before split atom creation — only unset_terms()
macro_rules! pipeline_incremental_split_eager_persistent_arm {
    ($self:ident,
        tag: $tag:expr,
        persistent_sat_field: $sat_field:ident,
        tseitin_field: $tseitin_field:ident,
        encoded_field: $encoded_field:ident,
        activation_scope_field: $activation_scope_field:ident,
        create_theory: $create_theory:expr,
        extract_models: |$theory_var:ident| $extract:expr,
        max_splits: $max_splits:expr,
        pre_theory_import: |$import_theory:ident, $import_lc:ident, $import_hc:ident, $import_ds:ident| $import_expr:expr,
        post_theory_export: |$export_theory:ident| $export_expr:expr
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
    ) => {{
        use hashbrown::{HashMap, HashSet};
        use z4_core::{TermId, Tseitin, TseitinEncodedAssertion};
        use z4_sat::{Literal as SatLiteral, SatResult, Solver as SatSolver, Variable as SatVariable};
        use $crate::executor_types::{SolveResult, UnknownReason};
        use $crate::incremental_state::{collect_active_theory_atoms, IncrementalTheoryState};
        use $crate::executor::theories::freeze_var_if_needed;

        let proof_enabled = $self.produce_proofs_enabled();
        let _islp_problem_assertions = if proof_enabled {
            $self.proof_problem_assertions()
        } else {
            Vec::new()
        };
        let random_seed = $self.current_random_seed();
        let should_record_random_seed = match $self.incr_theory_state.as_ref() {
            Some(state) => state.$sat_field.is_none(),
            None => true,
        };
        if should_record_random_seed {
            $self.record_applied_sat_random_seed_for_test(random_seed);
        }

        // Initialize or get incremental state
        let state = $self
            .incr_theory_state
            .get_or_insert_with(IncrementalTheoryState::new);
        collect_theory_stats!(incremental: $self, state);

        pipeline_incremental_setup!(
            $self, state, proof_enabled, random_seed, $tag,
            sat_field: $sat_field,
            tseitin_field: $tseitin_field,
            encoded_field: $encoded_field,
            activation_scope_field: $activation_scope_field,
            solver_init: {
                if let Some(ref mut sat) = state.$sat_field {
                    for _ in 0..state.scope_depth {
                        sat.push();
                    }
                }
            },
            out: (new_assertion_set, solver, tseitin, base_var_to_term, base_term_to_var, pending_activations)
        );
        state.$sat_field = Some(solver);

        // Save Tseitin state back
        state.$tseitin_field = tseitin.into_state();

        // Collect theory atoms in active assertions only
        let base_active_atoms = collect_active_theory_atoms(&$self.ctx.terms, &$self.ctx.assertions);
        let solver = state
            .$sat_field
            .as_mut()
            .expect(concat!("incremental ", $tag, " should initialize persistent SAT solver"));
        for &term in &base_active_atoms {
            if let Some(&var) = base_term_to_var.get(&term) {
                freeze_var_if_needed(solver, SatVariable::new(var));
            }
        }
        // #6853: Apply deferred activations immediately (no private push in eager-persistent arm).
        pipeline_apply_pending_activations_immediate!(
            solver, pending_activations, proof_enabled, state
        );

        let _islp_scope_depth_unsupported = state.scope_depth != 0;

        // Local variable maps grow as splits are added
        let mut local_term_to_var: HashMap<TermId, u32> = base_term_to_var;
        let mut local_var_to_term: HashMap<u32, TermId> = base_var_to_term.clone();
        let mut local_next_var: u32 = u32::try_from(solver.user_num_vars() + solver.scope_depth())
            .expect("SAT solver variable count does not fit in u32");
        let base_active_atom_set: HashSet<TermId> = base_active_atoms.iter().copied().collect();
        let mut _islp_added_split_clauses: HashSet<
            $crate::executor::theories::split_incremental::SplitClauseKey,
        > = HashSet::new();
        let mut _islp_added_refinement_clauses: HashSet<
            $crate::executor::theories::split_incremental::BoundRefinementReplayKey,
        > = HashSet::new();
        let mut _islp_added_axioms: HashSet<$crate::extension::TheoryAxiomKey> = HashSet::new();

        // Learned state persisted across theory instances
        let mut _islp_learned_cuts: Vec<z4_lia::StoredCut> = Vec::new();
        let mut _islp_seen_hnf_cuts: HashSet<z4_lia::HnfCutKey> = HashSet::new();
        let mut _islp_dioph_state = z4_lia::DiophState::default();

        // Split value trends for unbounded oscillation detection
        let mut _islp_last_split_values: $crate::executor::theories::solve_harness::SplitOscillationMap = HashMap::new();
        // Keep model-equality adapter clauses idempotent across repeated
        // fixed-term/offset requests from the persistent theory.
        let mut _islp_added_model_eq_atoms: HashSet<TermId> = HashSet::new();
        let mut _islp_model_eq_rounds: usize = 0;
        const _ISLP_MODEL_EQ_MAX_ROUNDS: usize = 20;

        // Per-theory statistics saved from the most recent theory instance (#6579).
        let mut _islp_last_theory_stats: Vec<(&'static str, u64)> = Vec::new();

        // Split-loop timing (#6503).
        let mut _islp_timing = $crate::SplitLoopTimingStats::default();
        let _islp_total_start = std::time::Instant::now();
        let mut _islp_eager_stats = $crate::DpllEagerStats::default();

        // #6590 Packet 3: Create persistent theory ONCE before the loop.
        // The theory's terms_ptr is null initially; set_terms() is called
        // at the start of each iteration.
        let mut theory = $create_theory;

        // Proof ledger clone + context registration (#5814 Packet A)
        // Reordered: proof labels -> negation cache (parity with lazy/assume arms).
        let (mut _islp_local_clausification_proofs, mut _islp_local_original_clause_theory_proofs) =
            pipeline_clone_local_proof_ledgers!(state, proof_enabled);
        pipeline_register_proof_context!(
            $self,
            proof_enabled,
            $tag,
            problem_assertions: _islp_problem_assertions
        );
        // Negation cache seeding (#6660, #6735): build negation map once and
        // sync only newly encoded terms before proof consumers run.
        let mut _islp_negations = $crate::incremental_proof_cache::IncrementalNegationCache::seed(
            &mut $self.ctx.terms,
            local_var_to_term.values().copied(),
            proof_enabled,
        );

        let _islp_result: $crate::executor_types::Result<SolveResult> = 'split_loop: {
            if _islp_scope_depth_unsupported {
                tracing::warn!(
                    scope_depth = state.scope_depth,
                    concat!(
                        "Incremental eager persistent ",
                        $tag,
                        " split-loop requires isolated scope depth 0; returning Unknown"
                    )
                );
                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                $self.last_result = Some(SolveResult::Unknown);
                break 'split_loop Ok(SolveResult::Unknown);
            }

            for _iteration in 0..$max_splits {
                // Pre-iteration check (interrupt/deadline)
                $(
                    {
                        let $pic_self = &();
                        if $pic_expr {
                            let _ = solver.pop();
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                    }
                )?

                state.round_trips += 1;
                _islp_timing.dpll.round_trips += 1;

                // #6590: Set terms pointer for this iteration and warm-reset
                // the theory (clears assertion/bound state, preserves simplex
                // basis and variable values for warm-start).
                theory.set_terms(&$self.ctx.terms);
                if _iteration > 0 {
                    theory.soft_reset_warm();
                }

                if _iteration < 5 || _iteration % 1000 == 0 {
                    tracing::debug!(
                        iter = _iteration,
                        vars = local_var_to_term.len(),
                        splits = _islp_added_split_clauses.len(),
                        "#6590 persistent loop state"
                    );
                }

                let active_theory_atoms: Vec<TermId> =
                    $crate::iter_var_to_term_sorted(&local_var_to_term)
                        .map(|(_, term)| term)
                        .filter(|term| {
                            base_active_atom_set.contains(term)
                                || $crate::is_theory_atom(&$self.ctx.terms, *term)
                        })
                        .collect();
                let active_theory_atom_set: HashSet<TermId> =
                    active_theory_atoms.iter().copied().collect();

                // Import learned state (no-op for LRA, used by LIA).
                {
                    let $import_theory = &mut theory;
                    let $import_lc = &mut _islp_learned_cuts;
                    let $import_hc = &mut _islp_seen_hnf_cuts;
                    let $import_ds = &mut _islp_dioph_state;
                    $import_expr;
                }
                theory.replay_learned_cuts();

                // Sync only the fresh atoms introduced by prior iterations (#6735).
                _islp_negations.sync_pending(&mut $self.ctx.terms);

                let (sat_result, _ext_conflicts, _ext_propagations,
                     _ext_partial, pending_split, pending_refinements) =
                    pipeline_build_eager_extension!(
                        $self, solver, theory,
                        local_var_to_term, local_term_to_var,
                        active_theory_atoms, active_theory_atom_set,
                        proof_enabled, _islp_negations,
                        _islp_added_refinement_clauses, _islp_added_axioms,
                        _islp_eager_stats, _islp_timing, state
                    );

                // Save per-theory statistics (#6579).
                _islp_last_theory_stats = z4_core::TheorySolver::collect_statistics(&theory);

                let pending_split = match pending_split {
                    Some(z4_core::TheoryResult::NeedModelEquality(eq)) => {
                        theory.unset_terms();
                        _islp_model_eq_rounds += 1;
                        if _islp_model_eq_rounds > _ISLP_MODEL_EQ_MAX_ROUNDS {
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                        pipeline_encode_model_equality!(
                            $self, solver, local_term_to_var, local_var_to_term,
                            local_next_var, _islp_negations, eq,
                            added_model_eqs: _islp_added_model_eq_atoms
                        );
                        continue;
                    }
                    Some(z4_core::TheoryResult::NeedModelEqualities(eqs)) => {
                        theory.unset_terms();
                        _islp_model_eq_rounds += 1;
                        if _islp_model_eq_rounds > _ISLP_MODEL_EQ_MAX_ROUNDS {
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                        for eq in eqs {
                            pipeline_encode_model_equality!(
                                $self, solver, local_term_to_var, local_var_to_term,
                                local_next_var, _islp_negations, eq,
                                added_model_eqs: _islp_added_model_eq_atoms
                            );
                        }
                        continue;
                    }
                    Some(z4_core::TheoryResult::NeedLemmas(lemmas)) => {
                        theory.unset_terms();
                        for lemma in &lemmas {
                            $crate::executor::theories::split_incremental::apply_theory_lemma_incremental(
                                &$self.ctx.terms,
                                solver,
                                &mut local_term_to_var,
                                &mut local_var_to_term,
                                &mut local_next_var,
                                &mut _islp_negations,
                                &lemma.clause,
                            );
                        }
                        if proof_enabled {
                            _islp_negations.sync_pending(&mut $self.ctx.terms);
                            for lemma in &lemmas {
                                let terms: Vec<z4_core::TermId> = lemma
                                    .clause
                                    .iter()
                                    .map(|lit| {
                                        if lit.value {
                                            lit.term
                                        } else {
                                            *_islp_negations
                                                .as_map()
                                                .get(&lit.term)
                                                .expect("persistent eager theory-lemma negation cache should be synced")
                                        }
                                    })
                                    .collect();
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
                                _islp_local_clausification_proofs.push(None);
                                _islp_local_original_clause_theory_proofs.push(Some(
                                    z4_core::TheoryLemmaProof {
                                        kind,
                                        farkas: None,
                                        lia: None,
                                    },
                                ));
                            }
                        }
                        continue;
                    }
                    other => other,
                };

                match sat_result {
                    SatResult::Sat(model) => {
                        if _iteration < 5 || _iteration % 1000 == 0 {
                            tracing::debug!(
                                iter = _iteration,
                                conflicts = _ext_conflicts,
                                propagations = _ext_propagations,
                                partial = _ext_partial,
                                split = pending_split.is_some(),
                                refine = !pending_refinements.is_empty(),
                                "#6590 persistent SAT result"
                            );
                        }
                        // Soundness guard: escalate SAT→Unknown when theory
                        // conflicts were dropped (parity with solve_eager_step).
                        if _ext_partial > 0 {
                            tracing::warn!(
                                partial_clauses = _ext_partial,
                                concat!("Eager persistent ", $tag, " produced SAT with dropped theory conflicts; escalating to Unknown")
                            );
                            theory.unset_terms();
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            break 'split_loop Ok(SolveResult::Unknown);
                        }

                        // Final full-check for combined/persistent theories (#5462).
                        // The eager extension only runs the lightweight
                        // BCP-time check; theories that opt into a final SAT
                        // fixpoint must be rechecked here before accepting SAT.
                        if z4_core::TheorySolver::needs_final_check_after_sat(&theory)
                            && pending_split.is_none()
                        {
                            let _fc_result = z4_core::TheorySolver::check(&mut theory);
                            match _fc_result {
                                z4_core::TheoryResult::Sat => {
                                    // Final check passed.
                                }
                                z4_core::TheoryResult::NeedSplit(_)
                                | z4_core::TheoryResult::NeedDisequalitySplit(_)
                                | z4_core::TheoryResult::NeedExpressionSplit(_) => {
                                    pipeline_export_theory_state!(
                                        theory, $export_theory, $export_expr,
                                        _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                    );
                                    theory.unset_terms();

                                    pipeline_incremental_split_eager_dispatch_split!(
                                        'split_loop, $self, solver,
                                        tag: $tag, suffix: "-INC-EAGER-PERSIST-FC",
                                        local_term_to_var, local_var_to_term, local_next_var, _islp_negations,
                                        _islp_added_split_clauses, _islp_last_split_values,
                                        split_result: _fc_result,
                                        fallthrough: {
                                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                            $self.last_result = Some(SolveResult::Unknown);
                                            break 'split_loop Ok(SolveResult::Unknown);
                                        }
                                    );
                                }
                                z4_core::TheoryResult::NeedModelEquality(eq) => {
                                    // #7966: Suppress stale model equalities whose
                                    // atoms are already encoded in the SAT solver,
                                    // matching the extension-level filter in check.rs.
                                    let _fc_eq_stale = $self.ctx.terms.find_eq(eq.lhs, eq.rhs)
                                        .is_some_and(|ea| local_term_to_var.contains_key(&ea));
                                    if _fc_eq_stale {
                                        tracing::debug!(
                                            lhs = ?eq.lhs, rhs = ?eq.rhs,
                                            "#7966 persistent final-check suppressed stale NeedModelEquality"
                                        );
                                        // Treat as Sat — the equality is already encoded.
                                    } else {
                                        pipeline_export_theory_state!(
                                            theory, $export_theory, $export_expr,
                                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                        );
                                        theory.unset_terms();
                                        _islp_model_eq_rounds += 1;
                                        if _islp_model_eq_rounds > _ISLP_MODEL_EQ_MAX_ROUNDS {
                                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                            $self.last_result = Some(SolveResult::Unknown);
                                            break 'split_loop Ok(SolveResult::Unknown);
                                        }
                                        pipeline_encode_model_equality!(
                                            $self, solver, local_term_to_var, local_var_to_term,
                                            local_next_var, _islp_negations, eq,
                                            added_model_eqs: _islp_added_model_eq_atoms
                                        );
                                        continue;
                                    }
                                }
                                z4_core::TheoryResult::NeedModelEqualities(eqs) => {
                                    // #7966: Filter out already-encoded model equalities
                                    // before consuming a round budget slot.
                                    let _fc_fresh_eqs: Vec<z4_core::ModelEqualityRequest> = eqs
                                        .into_iter()
                                        .filter(|eq| {
                                            !$self.ctx.terms.find_eq(eq.lhs, eq.rhs)
                                                .is_some_and(|ea| local_term_to_var.contains_key(&ea))
                                        })
                                        .collect();
                                    if _fc_fresh_eqs.is_empty() {
                                        tracing::debug!(
                                            "#7966 persistent final-check suppressed all stale NeedModelEqualities"
                                        );
                                        // Treat as Sat — all equalities already encoded.
                                    } else {
                                        pipeline_export_theory_state!(
                                            theory, $export_theory, $export_expr,
                                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                        );
                                        theory.unset_terms();
                                        _islp_model_eq_rounds += 1;
                                        if _islp_model_eq_rounds > _ISLP_MODEL_EQ_MAX_ROUNDS {
                                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                            $self.last_result = Some(SolveResult::Unknown);
                                            break 'split_loop Ok(SolveResult::Unknown);
                                        }
                                        for eq in _fc_fresh_eqs {
                                            pipeline_encode_model_equality!(
                                                $self, solver, local_term_to_var, local_var_to_term,
                                                local_next_var, _islp_negations, eq,
                                                added_model_eqs: _islp_added_model_eq_atoms
                                            );
                                        }
                                        continue;
                                    }
                                }
                                z4_core::TheoryResult::NeedLemmas(lemmas) => {
                                    pipeline_export_theory_state!(
                                        theory, $export_theory, $export_expr,
                                        _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                    );
                                    theory.unset_terms();
                                    for lemma in &lemmas {
                                        $crate::executor::theories::split_incremental::apply_theory_lemma_incremental(
                                            &$self.ctx.terms,
                                            solver,
                                            &mut local_term_to_var,
                                            &mut local_var_to_term,
                                            &mut local_next_var,
                                            &mut _islp_negations,
                                            &lemma.clause,
                                        );
                                    }
                                    if proof_enabled {
                                        _islp_negations.sync_pending(&mut $self.ctx.terms);
                                        for lemma in &lemmas {
                                            let terms: Vec<z4_core::TermId> = lemma
                                                .clause
                                                .iter()
                                                .map(|lit| {
                                                    if lit.value {
                                                        lit.term
                                                    } else {
                                                        *_islp_negations
                                                            .as_map()
                                                            .get(&lit.term)
                                                            .expect("persistent final-check theory-lemma negation cache should be synced")
                                                    }
                                                })
                                                .collect();
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
                                            _islp_local_clausification_proofs.push(None);
                                            _islp_local_original_clause_theory_proofs.push(Some(
                                                z4_core::TheoryLemmaProof {
                                                    kind,
                                                    farkas: None,
                                                    lia: None,
                                                },
                                            ));
                                        }
                                    }
                                    continue;
                                }
                                _ => {
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break 'split_loop Ok(SolveResult::Unknown);
                                }
                            }
                        }

                        if let Some(split_result) = pending_split {
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );
                            // #6590: unset terms before mutating self.ctx.terms
                            // for split atom creation. Theory persists.
                            theory.unset_terms();

                            pipeline_incremental_split_eager_dispatch_split!(
                                'split_loop, $self, solver,
                                tag: $tag, suffix: "-INC-EAGER-PERSIST",
                                local_term_to_var, local_var_to_term, local_next_var, _islp_negations,
                                _islp_added_split_clauses, _islp_last_split_values,
                                split_result: split_result,
                                fallthrough: {
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break 'split_loop Ok(SolveResult::Unknown);
                                }
                            );
                        }

                        // Check if there are genuinely NEW refinements that the SAT
                        // solver hasn't seen.  With a persistent theory, soft_reset()
                        // can re-derive the same bound refinements the SAT solver
                        // already contains.  Re-running the loop in that case leads
                        // to an infinite refinement cycle (#6590).
                        let has_new_refinements = pending_refinements.iter().any(|r| {
                            let key = $crate::executor::theories::split_incremental::BoundRefinementReplayKey::new(r);
                            !_islp_added_refinement_clauses.contains(&key)
                        });

                        if has_new_refinements {
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );
                            theory.unset_terms();

                            if !$crate::executor::theories::split_incremental::replay_incremental_bound_refinements(
                                &mut $self.ctx.terms,
                                solver,
                                &mut local_term_to_var,
                                &mut local_var_to_term,
                                &mut local_next_var,
                                &mut _islp_negations,
                                &pending_refinements,
                                &mut _islp_added_refinement_clauses,
                            ) {
                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                $self.last_result = Some(SolveResult::Unknown);
                                break 'split_loop Ok(SolveResult::Unknown);
                            }

                            continue;
                        }

                        // No pending split — theory is SAT. Extract model.
                        pipeline_store_sat_model!(
                            'split_loop, $self, solver, model,
                            local_term_to_var, local_var_to_term, local_next_var,
                            _islp_timing, theory, $theory_var, $extract,
                            pre_store: { theory.unset_terms(); }
                        );
                    }
                    SatResult::Unsat => {
                        // #6812: Soundness guard — when theory conflicts had terms
                        // that couldn't map to SAT literals (partial clauses), the
                        // learned clauses are stronger than what the theory proved.
                        // A propositional UNSAT derived from such clauses is unsound.
                        if _ext_partial > 0 {
                            tracing::warn!(
                                partial_clauses = _ext_partial,
                                concat!("Eager persistent ", $tag, " produced UNSAT with dropped theory conflicts; escalating to Unknown")
                            );
                            theory.unset_terms();
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                        // #6846: Expression split clauses (NeedSplit: x ≤ k ∨ x ≥ k+1)
                        // are tautological over integers and cannot make a
                        // satisfiable formula UNSAT. Model equalities are only
                        // SAT decision hints (`try_true_first`), not permanent
                        // clauses. In the persistent eager arm, the theory
                        // solver also persists across iterations, so learned
                        // clauses remain sound. UNSAT accepted.
                        if !_islp_added_split_clauses.is_empty() {
                            tracing::debug!(
                                split_clauses = _islp_added_split_clauses.len(),
                                concat!("Eager persistent ", $tag, " UNSAT after expression splits (tautological, accepted)")
                            );
                        }
                        theory.unset_terms();
                        _islp_negations.sync_pending(&mut $self.ctx.terms);
                        pipeline_incremental_split_eager_build_unsat_proof!(
                            'split_loop, $self, solver, state,
                            local_var_to_term, _islp_negations, proof_enabled,
                            _islp_local_clausification_proofs, _islp_local_original_clause_theory_proofs
                        );
                    }
                    SatResult::Unknown => {
                        if let Some(split_result) = pending_split {
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );
                            theory.unset_terms();

                            pipeline_incremental_split_eager_dispatch_split!(
                                'split_loop, $self, solver,
                                tag: $tag, suffix: "-INC-EAGER-PERSIST",
                                local_term_to_var, local_var_to_term, local_next_var, _islp_negations,
                                _islp_added_split_clauses, _islp_last_split_values,
                                split_result: split_result,
                                fallthrough: {}
                            );
                        }

                        // Same duplicate-refinement guard as the SAT path (#6590).
                        let has_new_refinements_unk = pending_refinements.iter().any(|r| {
                            let key = $crate::executor::theories::split_incremental::BoundRefinementReplayKey::new(r);
                            !_islp_added_refinement_clauses.contains(&key)
                        });

                        if has_new_refinements_unk {
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );
                            theory.unset_terms();

                            if !$crate::executor::theories::split_incremental::replay_incremental_bound_refinements(
                                &mut $self.ctx.terms,
                                solver,
                                &mut local_term_to_var,
                                &mut local_var_to_term,
                                &mut local_next_var,
                                &mut _islp_negations,
                                &pending_refinements,
                                &mut _islp_added_refinement_clauses,
                            ) {
                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                $self.last_result = Some(SolveResult::Unknown);
                                break 'split_loop Ok(SolveResult::Unknown);
                            }

                            continue;
                        }

                        theory.unset_terms();
                        $self.last_model = None;
                        if $self.last_unknown_reason.is_none() {
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        }
                        $self.last_result = Some(SolveResult::Unknown);
                        break 'split_loop Ok(SolveResult::Unknown);
                    }
                    #[allow(unreachable_patterns)]
                    _ => unreachable!(),
                }
            }

            // Too many splits - return unknown
            theory.unset_terms();
            if $self.last_unknown_reason.is_none() {
                $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
            }
            $self.last_result = Some(SolveResult::Unknown);
            Ok(SolveResult::Unknown)
        };

        pipeline_split_epilogue!(
            $self, _islp_timing, _islp_total_start,
            _islp_last_theory_stats, _islp_result,
            eager: { pipeline_export_split_loop_eager_stats!($self, _islp_eager_stats); },
            restore: {}
        )
    }};
    // Default-fields rule: when tseitin_field/encoded_field/activation_scope_field
    // are not provided, use the standard IncrementalTheoryState field names (#6853).
    ($self:ident,
        tag: $tag:expr,
        persistent_sat_field: $sat_field:ident,
        create_theory: $create_theory:expr,
        extract_models: |$theory_var:ident| $extract:expr,
        max_splits: $max_splits:expr,
        pre_theory_import: |$import_theory:ident, $import_lc:ident, $import_hc:ident, $import_ds:ident| $import_expr:expr,
        post_theory_export: |$export_theory:ident| $export_expr:expr
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
    ) => {{
        pipeline_incremental_split_eager_persistent_arm!($self,
            tag: $tag,
            persistent_sat_field: $sat_field,
            tseitin_field: tseitin_state,
            encoded_field: encoded_assertions,
            activation_scope_field: assertion_activation_scope,
            create_theory: $create_theory,
            extract_models: |$theory_var| $extract,
            max_splits: $max_splits,
            pre_theory_import: |$import_theory, $import_lc, $import_hc, $import_ds| $import_expr,
            post_theory_export: |$export_theory| $export_expr
            $(, pre_iter_check: |$pic_self| $pic_expr)?
        )
    }};
}
