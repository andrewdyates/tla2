// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eager arm of the incremental split-loop pipeline.
//!
//! Extracted from `pipeline_incremental_split_macros.rs` (#6680).
//! Contains the eager theory-SAT interleaving path via TheoryExtension.
//! Each iteration creates a fresh theory for borrow safety. SAT solver
//! runs with TheoryExtension for inline BCP propagation.

#![allow(unused_macros)]

/// Eager arm implementation for `solve_incremental_split_loop_pipeline!`.
///
/// Key differences from the lazy arm:
/// 1. Each iteration creates a fresh theory (same as lazy) for borrow safety
/// 2. SAT solver runs with TheoryExtension for inline BCP propagation
/// 3. Theory conflicts are learned during search (not after full model)
/// 4. TheoryExtension handles push/pop for backtracking within one solve
/// 5. Theory is dropped before split atom creation (needs &mut TermStore)
// Live call sites: AUFLIA (combined.rs), UF+LRA (combined.rs), UF+LIA (combined.rs).
// The eager-persistent arm (with persistent_theory: true) is used by lra.rs.
macro_rules! pipeline_incremental_split_eager_arm {
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
        $(, disable_preprocess: $disable_preprocess:expr)?
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
        $(, accept_unsat_after_splits: $accept_unsat:expr)?
        $(, max_string_lemma_requests: $max_slr:expr,
           handle_string_lemma: |$sl_lemma:ident, $sl_negations:ident| $sl_handler:expr)?
    ) => {{
        use hashbrown::{HashMap, HashSet};
        use z4_core::{TermId, Tseitin, TseitinEncodedAssertion};
        use z4_sat::{Literal as SatLiteral, SatResult, Solver as SatSolver, Variable as SatVariable};
        use $crate::executor_types::{SolveResult, UnknownReason};
        use $crate::incremental_state::{collect_active_theory_atoms, IncrementalTheoryState};
        use $crate::executor::theories::freeze_var_if_needed;

        let proof_enabled = $self.produce_proofs_enabled();

        // Take ownership so NeedStringLemma handlers can borrow $self.
        let random_seed = $self.current_random_seed();
        let should_record_random_seed = match $self.incr_theory_state.as_ref() {
            Some(state) => state.$sat_field.is_none(),
            None => true,
        };
        if should_record_random_seed {
            $self.record_applied_sat_random_seed_for_test(random_seed);
        }
        let _ = $self
            .incr_theory_state
            .get_or_insert_with(IncrementalTheoryState::new);
        let mut state = $self
            .incr_theory_state
            .take()
            .expect("invariant: incr_theory_state initialized by get_or_insert_with above");
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
        $(
            solver.set_preprocess_enabled(!$disable_preprocess);
        )?
        for &term in &base_active_atoms {
            if let Some(&var) = base_term_to_var.get(&term) {
                freeze_var_if_needed(solver, SatVariable::new(var));
            }
        }
        // #6853: Apply deferred activations immediately (no private push in eager arm).
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
        // Model equality diagnostics (#5814 Packet 4a, #6846).
        let mut _islp_model_eq_counts: HashMap<(TermId, TermId), usize> = HashMap::new();
        // Global model-eq round counter. Returns Unknown (never SAT) after
        // hitting the limit, preventing divergence on non-persistent theory
        // combiners. Old per-pair retry limit of 2 was too aggressive and
        // led to false-SAT (#6846).
        let mut _islp_model_eq_rounds: usize = 0;
        const _ISLP_MODEL_EQ_MAX_ROUNDS: usize = 20;
        // #6846: Total non-convergence iteration counter. The non-persistent
        // eager arm recreates the theory each iteration, losing convergence
        // state. When the solver alternates between NeedExpressionSplit and
        // NeedModelEqualities without making progress, this cap ensures
        // termination with Unknown within reasonable time.
        let mut _islp_no_progress_iters: usize = 0;
        const _ISLP_MAX_NO_PROGRESS_ITERS: usize = 100;

        // Per-theory statistics saved from the most recent theory instance (#6579).
        let mut _islp_last_theory_stats: Vec<(&'static str, u64)> = Vec::new();
        let mut _islp_string_lemma_clauses: Vec<Vec<TermId>> = Vec::new();
        let mut _islp_string_lemma_requests = 0usize;

        // Split-loop timing (#6503).
        let mut _islp_timing = $crate::SplitLoopTimingStats::default();
        let _islp_total_start = std::time::Instant::now();
        let mut _islp_eager_stats = $crate::DpllEagerStats::default();

        // Proof ledger clone + context registration (#5814 Packet A)
        // Reordered: proof labels -> negation cache (parity with lazy/assume arms).
        let (mut _islp_local_clausification_proofs, mut _islp_local_original_clause_theory_proofs) =
            pipeline_clone_local_proof_ledgers!(state, proof_enabled);
        pipeline_register_proof_context!($self, proof_enabled, $tag);
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
                        "Incremental eager ",
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

                // #6846: non-convergence guard for non-persistent eager arm.
                // Increment on every iteration. Reset to 0 when UNSAT is
                // reached (real progress). If the solver oscillates between
                // splits and model equalities without converging, bail out.
                _islp_no_progress_iters += 1;
                if _islp_no_progress_iters > _ISLP_MAX_NO_PROGRESS_ITERS {
                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    $self.last_result = Some(SolveResult::Unknown);
                    break 'split_loop Ok(SolveResult::Unknown);
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
                // Sync only the fresh atoms introduced by prior iterations (#6735).
                _islp_negations.sync_pending(&mut $self.ctx.terms);

                let mut theory = $create_theory;
                {
                    let $import_theory = &mut theory;
                    let $import_lc = &mut _islp_learned_cuts;
                    let $import_hc = &mut _islp_seen_hnf_cuts;
                    let $import_ds = &mut _islp_dioph_state;
                    $import_expr;
                }
                theory.replay_learned_cuts();

                let (sat_result, _ext_conflicts, _, _ext_partial, pending_split, pending_refinements) =
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
                    Some(z4_core::TheoryResult::NeedStringLemma(_islp_sl)) => {
                        $(
                            _islp_string_lemma_requests += 1;
                            if _islp_string_lemma_requests >= $max_slr {
                                $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                                $self.last_result = Some(SolveResult::Unknown);
                                break 'split_loop Ok(SolveResult::Unknown);
                            }
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );
                            drop(theory);
                            let $sl_lemma = _islp_sl;
                            let $sl_negations = &mut _islp_negations;
                            let (_islp_new_sl_clauses, _islp_sl_stall): (Vec<Vec<TermId>>, bool) =
                                $sl_handler;
                            if _islp_sl_stall {
                                $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                                $self.last_result = Some(SolveResult::Unknown);
                                break 'split_loop Ok(SolveResult::Unknown);
                            }
                            for _sl_clause in &_islp_new_sl_clauses {
                                $crate::executor::theories::split_incremental::apply_string_lemma_incremental(
                                    &$self.ctx.terms,
                                    solver,
                                    &mut local_term_to_var,
                                    &mut local_var_to_term,
                                    &mut local_next_var,
                                    &mut _islp_negations,
                                    _sl_clause,
                                );
                                if proof_enabled {
                                    // #8106: String lemma clauses from NeedStringLemma
                                    // are content axioms (decomposition, contains, substr).
                                    // Use StringContentAxiom instead of Generic/trust.
                                    let _ = $self.proof_tracker.add_theory_lemma_with_kind(
                                        _sl_clause.to_vec(),
                                        z4_core::TheoryLemmaKind::StringContentAxiom,
                                    );
                                    // #6725: append indexed proof entries in lockstep with SAT clause creation.
                                    _islp_local_clausification_proofs.push(None);
                                    _islp_local_original_clause_theory_proofs.push(Some(z4_core::TheoryLemmaProof {
                                        kind: z4_core::TheoryLemmaKind::StringContentAxiom,
                                        farkas: None,
                                        lia: None,
                                    }));
                                }
                            }
                            _islp_negations.sync_pending(&mut $self.ctx.terms);
                            _islp_string_lemma_clauses.extend(_islp_new_sl_clauses);
                            continue;
                        )?
                        #[allow(unreachable_code)]
                        {
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                    }
                    Some(z4_core::TheoryResult::NeedLemmas(lemmas)) => {
                        pipeline_export_theory_state!(
                            theory, $export_theory, $export_expr,
                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                        );
                        drop(theory);
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
                                                .expect("eager theory-lemma negation cache should be synced")
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
                                // #6725: append indexed proof entries in lockstep with SAT clause creation.
                                _islp_local_clausification_proofs.push(None);
                                _islp_local_original_clause_theory_proofs.push(Some(z4_core::TheoryLemmaProof {
                                    kind,
                                    farkas: None,
                                    lia: None,
                                }));
                            }
                        }
                        continue;
                    }
                    Some(z4_core::TheoryResult::NeedModelEquality(eq)) => {
                        pipeline_export_theory_state!(
                            theory, $export_theory, $export_expr,
                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                        );
                        drop(theory);

                        _islp_model_eq_rounds += 1;
                        if _islp_model_eq_rounds > _ISLP_MODEL_EQ_MAX_ROUNDS {
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            break 'split_loop Ok(SolveResult::Unknown);
                        }

                        *_islp_model_eq_counts.entry((eq.lhs, eq.rhs)).or_insert(0) += 1;
                        pipeline_encode_model_equality!(
                            $self, solver, local_term_to_var, local_var_to_term,
                            local_next_var, _islp_negations, eq
                        );
                        continue;
                    }
                    Some(z4_core::TheoryResult::NeedModelEqualities(eqs)) => {
                        pipeline_export_theory_state!(
                            theory, $export_theory, $export_expr,
                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                        );
                        drop(theory);

                        _islp_model_eq_rounds += 1;
                        if _islp_model_eq_rounds > _ISLP_MODEL_EQ_MAX_ROUNDS {
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            break 'split_loop Ok(SolveResult::Unknown);
                        }

                        for eq in eqs {
                            *_islp_model_eq_counts.entry((eq.lhs, eq.rhs)).or_insert(0) += 1;
                            pipeline_encode_model_equality!(
                                $self, solver, local_term_to_var, local_var_to_term,
                                local_next_var, _islp_negations, eq
                            );
                        }
                        continue;
                    }
                    other => other,
                };

                match sat_result {
                    SatResult::Sat(model) => {
                        // Soundness guard: escalate SAT→Unknown when theory
                        // conflicts were dropped (parity with solve_eager_step).
                        if _ext_partial > 0 {
                            tracing::warn!(
                                partial_clauses = _ext_partial,
                                concat!("Eager ", $tag, " produced SAT with dropped theory conflicts; escalating to Unknown")
                            );
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            break 'split_loop Ok(SolveResult::Unknown);
                        }

                        // Final full-check for combined theories (#5462 Packet 3).
                        // BCP-time check was local-only; run the full fixpoint
                        // once on the candidate model before accepting SAT.
                        //
                        // Skip when the extension already ran the full check and
                        // captured a pending split — the extension's check() already
                        // invoked theory.check() and the result is in pending_split.
                        // Running check() again would operate on modified state.
                        if z4_core::TheorySolver::needs_final_check_after_sat(&theory)
                            && pending_split.is_none()
                        {
                            let _fc_result = z4_core::TheorySolver::check(&mut theory);
                            match _fc_result {
                                z4_core::TheoryResult::Sat => {
                                    // Full check passed — fall through to existing
                                    // pending_split / refinements / model extraction.
                                }
                                z4_core::TheoryResult::NeedSplit(_)
                                | z4_core::TheoryResult::NeedDisequalitySplit(_)
                                | z4_core::TheoryResult::NeedExpressionSplit(_) => {
                                    pipeline_export_theory_state!(
                                        theory, $export_theory, $export_expr,
                                        _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                    );
                                    pipeline_incremental_split_eager_dispatch_split!(
                                        'split_loop, $self, solver,
                                        tag: $tag, suffix: "-INC-EAGER-FC",
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
                                    pipeline_export_theory_state!(
                                        theory, $export_theory, $export_expr,
                                        _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                    );
                                    drop(theory);
                                    _islp_model_eq_rounds += 1;
                                    if _islp_model_eq_rounds > _ISLP_MODEL_EQ_MAX_ROUNDS {
                                        $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                        $self.last_result = Some(SolveResult::Unknown);
                                        break 'split_loop Ok(SolveResult::Unknown);
                                    }
                                    *_islp_model_eq_counts.entry((eq.lhs, eq.rhs)).or_insert(0) += 1;
                                    pipeline_encode_model_equality!(
                                        $self, solver, local_term_to_var, local_var_to_term,
                                        local_next_var, _islp_negations, eq
                                    );
                                    continue;
                                }
                                z4_core::TheoryResult::NeedModelEqualities(eqs) => {
                                    pipeline_export_theory_state!(
                                        theory, $export_theory, $export_expr,
                                        _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                    );
                                    drop(theory);
                                    _islp_model_eq_rounds += 1;
                                    if _islp_model_eq_rounds > _ISLP_MODEL_EQ_MAX_ROUNDS {
                                        $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                        $self.last_result = Some(SolveResult::Unknown);
                                        break 'split_loop Ok(SolveResult::Unknown);
                                    }
                                    for eq in eqs {
                                        *_islp_model_eq_counts.entry((eq.lhs, eq.rhs)).or_insert(0) += 1;
                                        pipeline_encode_model_equality!(
                                            $self, solver, local_term_to_var, local_var_to_term,
                                            local_next_var, _islp_negations, eq
                                        );
                                    }
                                    continue;
                                }
                                z4_core::TheoryResult::NeedLemmas(lemmas) => {
                                    // Final-check lemmas: replay into SAT solver and
                                    // continue the split loop (parity with pre-SAT
                                    // NeedLemmas handling and lazy shared arm).
                                    pipeline_export_theory_state!(
                                        theory, $export_theory, $export_expr,
                                        _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                    );
                                    drop(theory);
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
                                                            .expect("final-check theory-lemma negation cache should be synced")
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
                                            _islp_local_original_clause_theory_proofs.push(Some(z4_core::TheoryLemmaProof {
                                                kind,
                                                farkas: None,
                                                lia: None,
                                            }));
                                        }
                                    }
                                    continue;
                                }
                                _ => {
                                    // Unsat/UnsatWithFarkas/Unknown/NeedStringLemma:
                                    // conservative escalation to Unknown.
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

                            pipeline_incremental_split_eager_dispatch_split!(
                                'split_loop, $self, solver,
                                tag: $tag, suffix: "-INC-EAGER",
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

                        if !pending_refinements.is_empty() {
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );

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
                            pre_store: {}
                        );
                    }
                    SatResult::Unsat => {
                        if !_islp_string_lemma_clauses.is_empty() {
                            $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                            $self.last_result = Some(SolveResult::Unknown);
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                        // #6812: Soundness guard — when theory conflicts had terms
                        // that couldn't map to SAT literals (partial clauses), the
                        // learned clauses are stronger than what the theory proved.
                        // A propositional UNSAT derived from such clauses is unsound.
                        if _ext_partial > 0 {
                            tracing::warn!(
                                partial_clauses = _ext_partial,
                                concat!("Eager ", $tag, " produced UNSAT with dropped theory conflicts; escalating to Unknown")
                            );
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                            $self.last_result = Some(SolveResult::Unknown);
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                        // #6812: Soundness guard — in the non-persistent eager
                        // arm, theory conflicts from the extension persist as
                        // learned SAT clauses. A fresh theory in a later iteration
                        // may be inconsistent with these stale learned conflicts,
                        // causing false-UNSAT. By default, escalate to Unknown
                        // when split clauses exist to prevent this.
                        //
                        // #6846: Callers that use tautological expression splits
                        // (e.g., AUFLIA with model equalities) can opt into
                        // accepting UNSAT after splits via accept_unsat_after_splits.
                        // In those logics, the split clauses are tautological and
                        // cannot cause false-UNSAT.
                        if !_islp_added_split_clauses.is_empty() {
                            let _accept = false;
                            $(let _accept = $accept_unsat;)?
                            if !_accept {
                                tracing::warn!(
                                    split_clauses = _islp_added_split_clauses.len(),
                                    concat!("Eager ", $tag, " UNSAT after expression splits; escalating to Unknown")
                                );
                                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                $self.last_result = Some(SolveResult::Unknown);
                                break 'split_loop Ok(SolveResult::Unknown);
                            }
                            tracing::debug!(
                                split_clauses = _islp_added_split_clauses.len(),
                                concat!("Eager ", $tag, " UNSAT after expression splits (accepted via opt-in)")
                            );
                        }
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

                            pipeline_incremental_split_eager_dispatch_split!(
                                'split_loop, $self, solver,
                                tag: $tag, suffix: "-INC-EAGER",
                                local_term_to_var, local_var_to_term, local_next_var, _islp_negations,
                                _islp_added_split_clauses, _islp_last_split_values,
                                split_result: split_result,
                                fallthrough: {}
                            );
                        }

                        if !pending_refinements.is_empty() {
                            pipeline_export_theory_state!(
                                theory, $export_theory, $export_expr,
                                _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                            );

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
            restore: { $self.incr_theory_state = Some(state); }
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
        $(, disable_preprocess: $disable_preprocess:expr)?
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
        $(, accept_unsat_after_splits: $accept_unsat:expr)?
        $(, max_string_lemma_requests: $max_slr:expr,
           handle_string_lemma: |$sl_lemma:ident, $sl_negations:ident| $sl_handler:expr)?
    ) => {{
        pipeline_incremental_split_eager_arm!($self,
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
            $(, disable_preprocess: $disable_preprocess)?
            $(, pre_iter_check: |$pic_self| $pic_expr)?
            $(, accept_unsat_after_splits: $accept_unsat)?
            $(, max_string_lemma_requests: $max_slr,
               handle_string_lemma: |$sl_lemma, $sl_negations| $sl_handler)?
        )
    }};
}
