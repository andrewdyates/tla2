// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazy arm of the incremental split-loop pipeline.
//!
//! Extracted from `pipeline_incremental_split_macros.rs` (#6680).
//! Contains the lazy theory-check path: SAT solves to completion,
//! then theory checks the full model. Used by LIA and combined theories
//! that don't yet benefit from eager propagation.

/// Lazy arm implementation for `solve_incremental_split_loop_pipeline!`.
macro_rules! pipeline_incremental_split_lazy_arm {
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
        $(, max_string_lemma_requests: $max_slr:expr,
           handle_string_lemma: |$sl_lemma:ident, $sl_negations:ident| $sl_handler:expr)?
    ) => {{
        use hashbrown::{HashMap, HashSet};
        use z4_core::{TermId, Tseitin, TseitinEncodedAssertion};
        use z4_sat::{Literal as SatLiteral, SatResult, Solver as SatSolver, Variable as SatVariable};
        use $crate::executor_types::{SolveResult, UnknownReason};
        use $crate::incremental_state::{collect_active_theory_atoms, IncrementalTheoryState};
        use $crate::executor::theories::freeze_var_if_needed;
        use $crate::executor::theories::split_incremental::{
            map_conflict_to_blocking_clause,
            BlockingClauseResult,
        };

        let proof_enabled = $self.produce_proofs_enabled();
        let random_seed = $self.current_random_seed();
        let should_record_random_seed = match $self.incr_theory_state.as_ref() {
            Some(state) => state.$sat_field.is_none(),
            None => true,
        };
        if should_record_random_seed {
            $self.record_applied_sat_random_seed_for_test(random_seed);
        }

        // Initialize or get incremental state.
        // Take ownership so $self remains borrowable by the string-lemma handler.
        // Restored to $self.incr_theory_state at macro exit.
        let _ = $self
            .incr_theory_state
            .get_or_insert_with(IncrementalTheoryState::new);
        let mut state = $self.incr_theory_state.take()
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
        // Proof ledger clone + context registration (#5814 Packet A)
        let (mut _islp_local_clausification_proofs, mut _islp_local_original_clause_theory_proofs) =
            pipeline_clone_local_proof_ledgers!(state, proof_enabled);
        pipeline_register_proof_context!($self, proof_enabled, $tag);

        // Collect theory atoms in active assertions only
        let base_active_atoms = collect_active_theory_atoms(&$self.ctx.terms, &$self.ctx.assertions);
        let solver = state
            .$sat_field
            .as_mut()
            .expect(concat!("incremental ", $tag, " should initialize persistent SAT solver"));
        // SMT push/pop owns the persistent solver's outer scopes via
        // IncrementalTheoryState::{push,pop}. The lazy split loop adds exactly
        // one private frame per check-sat, and every exit-path pop below
        // balances only that local frame.
        solver.push();
        // #6853: Apply deferred activation clauses inside the private push scope.
        pipeline_apply_pending_activations!(
            solver, pending_activations, proof_enabled, state
        );
        for &term in &base_active_atoms {
            if let Some(&var) = base_term_to_var.get(&term) {
                freeze_var_if_needed(solver, SatVariable::new(var));
            }
        }

        // Bound axiom injection (#6579): shared macro (#5814 Packet 1)
        pipeline_inject_bound_axioms!(
            $self, solver, base_active_atoms, base_term_to_var,
            $create_theory, proof_enabled, $tag,
            _islp_local_clausification_proofs, _islp_local_original_clause_theory_proofs
        );

        // Local variable maps grow as splits are added
        let mut local_term_to_var: HashMap<TermId, u32> = base_term_to_var;
        let mut local_var_to_term: HashMap<u32, TermId> = base_var_to_term.clone();
        let mut local_next_var: u32 = u32::try_from(solver.user_num_vars() + solver.scope_depth())
            .expect("SAT solver variable count does not fit in u32");
        let base_vars: HashSet<u32> = base_var_to_term.keys().copied().collect();
        let mut _islp_added_split_clauses: HashSet<
            $crate::executor::theories::split_incremental::SplitClauseKey,
        > = HashSet::new();
        let mut _islp_model_eq_counts: HashMap<(TermId, TermId), usize> = HashMap::new();
        let mut _islp_model_eq_rounds: usize = 0;
        const _ISLP_MODEL_EQ_MAX_ROUNDS: usize = 100;

        // Learned state persisted across theory instances
        let mut _islp_learned_cuts: Vec<z4_lia::StoredCut> = Vec::new();
        let mut _islp_seen_hnf_cuts: HashSet<z4_lia::HnfCutKey> = HashSet::new();
        let mut _islp_dioph_state = z4_lia::DiophState::default();
        let mut _islp_theory_lemmas: Vec<z4_core::TheoryLemma> = Vec::new();

        // Split value trends for unbounded oscillation detection
        let mut _islp_last_split_values: $crate::executor::theories::solve_harness::SplitOscillationMap = HashMap::new();

        // Per-theory statistics saved from the most recent theory instance (#6579).
        let mut _islp_last_theory_stats: Vec<(&'static str, u64)> = Vec::new();

        // Split-loop timing (#6503). dpll_create/replay_splits stay zero (no rebuild).
        let mut _islp_timing = $crate::SplitLoopTimingStats::default();
        let _islp_total_start = std::time::Instant::now();

        // Structural snapshot for fast theory reconstruction (#6590).
        // On the first iteration, the snapshot is None and register_atom parses
        // all atoms from scratch. On subsequent iterations, the snapshot provides
        // a pre-populated atom cache so register_atom skips parsing.
        let mut _islp_theory_snapshot: Option<Box<dyn std::any::Any>> = None;

        // String lemma tracking (#6688): only present when handle_string_lemma is provided.
        $(
            let mut _islp_string_lemma_requests: usize = 0;
            let _islp_max_string_lemma_requests: usize = $max_slr;
            let mut _islp_string_lemma_clauses: Vec<Vec<TermId>> = Vec::new();
        )?

        // Proof tracking setup (#6660, #6735): build negation map once and
        // sync only newly encoded terms.
        let mut _islp_negations = $crate::incremental_proof_cache::IncrementalNegationCache::seed(
            &mut $self.ctx.terms,
            local_var_to_term.values().copied(),
            proof_enabled,
        );
        let mut _islp_theory_lemma_seen =
            $crate::incremental_proof_cache::TheoryLemmaSeenSet::default();
        let _islp_result: $crate::executor_types::Result<SolveResult> = 'split_loop: {
            for _iteration in 0..$max_splits {
                // Pre-iteration check (interrupt/deadline)
                $(
                    {
                        // Note: $pic_self is NOT bound to $self to avoid borrow conflicts
                        // with `state`. The caller's closure should capture what it needs
                        // before the macro invocation.
                        let $pic_self = &();
                        if $pic_expr {
                            let _ = solver.pop();
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                    }
                )?

                state.round_trips += 1;
                _islp_timing.dpll.round_trips += 1;

                debug_assert!(
                    !solver.has_empty_clause(),
                    "BUG: persistent SAT solver has_empty_clause=true BEFORE \
                     solve() in split loop iteration {}. Scope depth: {}, \
                     active scopes: {}. This indicates a stale UNSAT state \
                     from a previous check-sat that was not cleared on pop.",
                    _iteration,
                    solver.scope_depth(),
                    solver.scope_depth(),
                );
                let _islp_sat_start = std::time::Instant::now();
                let sat_result = solver.solve().into_inner();
                _islp_timing.dpll.sat_solve += _islp_sat_start.elapsed();
                if let Some(r) = solver.last_unknown_reason() {
                    $self.last_unknown_reason = Some($crate::executor::Executor::map_sat_unknown_reason(r));
                }
                collect_sat_stats!($self, solver);
                collect_theory_stats!(incremental: $self, state);

                match sat_result {
                    SatResult::Sat(model) => {
                        _islp_negations.sync_pending(&mut $self.ctx.terms);
                        let mut theory = $create_theory;

                        // Import structural snapshot from previous iteration (#6590).
                        // This pre-populates atom_cache so register_atom skips parsing.
                        if let Some(snapshot) = _islp_theory_snapshot.take() {
                            <_ as z4_core::TheorySolver>::import_structural_snapshot(&mut theory, snapshot);
                        }

                        {
                            let $import_theory = &mut theory;
                            let $import_lc = &mut _islp_learned_cuts;
                            let $import_hc = &mut _islp_seen_hnf_cuts;
                            let $import_ds = &mut _islp_dioph_state;
                            $import_expr;
                        }

                        // Register theory atoms (#6579, bypasses TheoryExtension).
                        for &atom in &base_active_atoms {
                            z4_core::TheorySolver::register_atom(&mut theory, atom);
                        }
                        for lemma in &_islp_theory_lemmas {
                            z4_core::TheorySolver::note_applied_theory_lemma(
                                &mut theory,
                                &lemma.clause,
                            );
                        }

                        // Sync model to theory
                        for (var, term) in $crate::iter_var_to_term_sorted(&local_var_to_term) {
                            let is_dynamic_split = !base_vars.contains(&var);
                            let is_active = is_dynamic_split || base_active_atoms.contains(&term);
                            if $crate::is_theory_atom(&$self.ctx.terms, term) && is_active {
                                // Register dynamic split atoms created in prior
                                // iterations; base atoms already registered above.
                                if is_dynamic_split {
                                    z4_core::TheorySolver::register_atom(&mut theory, term);
                                }
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
                        theory.replay_learned_cuts();

                        // DEBUG(#6683): count asserted atoms
                        if _iteration < 3 {
                            let _dbg_asserted: Vec<_> = $crate::iter_var_to_term_sorted(&local_var_to_term)
                                .filter(|(var, term)| {
                                    let is_dynamic = !base_vars.contains(var);
                                    let is_active = is_dynamic || base_active_atoms.contains(term);
                                    $crate::is_theory_atom(&$self.ctx.terms, *term) && is_active
                                })
                                .map(|(var, term)| {
                                    let val = model.get(var as usize).copied()
                                        .or_else(|| solver.value(SatVariable::new(var)));
                                    (term.0, val)
                                })
                                .collect();
                            if crate::debug_dpll_enabled() {
                                safe_eprintln!(
                                    "[{}] iter={} asserted_atoms={} base_active={}",
                                    $tag, _iteration, _dbg_asserted.len(), base_active_atoms.len()
                                );
                            }
                        }

                        let _islp_theory_start = std::time::Instant::now();
                        let theory_result = z4_core::TheorySolver::check(&mut theory);
                        _islp_timing.dpll.theory_check += _islp_theory_start.elapsed();

                        // DEBUG(#6683): trace theory results + conflict details
                        if crate::debug_dpll_enabled()
                            && (_iteration < 10 || _iteration % 1000 == 0)
                        {
                            match &theory_result {
                                z4_core::TheoryResult::Unsat(ref ct) => {
                                    safe_eprintln!(
                                        "[{}] split_iter={} dpll_iter={} UNSAT conflict_len={} terms={:?}",
                                        $tag, _iteration, state.round_trips, ct.len(),
                                        ct.iter().map(|l| (l.term.0, l.value)).collect::<Vec<_>>()
                                    );
                                }
                                z4_core::TheoryResult::UnsatWithFarkas(ref cf) => {
                                    safe_eprintln!(
                                        "[{}] split_iter={} dpll_iter={} UnsatWithFarkas conflict_len={} terms={:?}",
                                        $tag, _iteration, state.round_trips, cf.literals.len(),
                                        cf.literals.iter().map(|l| (l.term.0, l.value)).collect::<Vec<_>>()
                                    );
                                }
                                other => {
                                    safe_eprintln!(
                                        "[{}] split_iter={} dpll_iter={} theory_result={:?}",
                                        $tag, _iteration, state.round_trips, std::mem::discriminant(other)
                                    );
                                }
                            }
                        }

                        // Save per-theory statistics before dispatch may drop theory (#6579).
                        _islp_last_theory_stats = z4_core::TheorySolver::collect_statistics(&theory);

                        // Export structural snapshot for the next iteration (#6590).
                        // This saves the atom cache so the next theory creation skips parsing.
                        _islp_theory_snapshot = <_ as z4_core::TheorySolver>::export_structural_snapshot(&theory);
                        pipeline_incremental_split_lazy_dispatch_theory_result!(
                            'split_loop, $self, solver, state,
                            tag: $tag,
                            theory,
                            theory_result: theory_result,
                            export_theory: |$export_theory| $export_expr,
                            local_term_to_var, local_var_to_term, local_next_var,
                            _islp_added_split_clauses, _islp_last_split_values, _islp_model_eq_counts, _islp_model_eq_rounds, _ISLP_MODEL_EQ_MAX_ROUNDS,
                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state, _islp_theory_lemmas, _islp_theory_lemma_seen,
                            _islp_negations, proof_enabled,
                            _islp_local_clausification_proofs, _islp_local_original_clause_theory_proofs,
                            sat_handler: {
                                pipeline_store_sat_model!(
                                    'split_loop, $self, solver, model,
                                    local_term_to_var, local_var_to_term, local_next_var,
                                    _islp_timing, theory, $theory_var, $extract,
                                    pre_store: { let _ = solver.pop(); }
                                );
                            },
                            remaining_arms: {
                                z4_core::TheoryResult::NeedStringLemma(_islp_sl) => {
                                    $(
                                        _islp_string_lemma_requests += 1;
                                        if _islp_string_lemma_requests >= $max_slr {
                                            let _ = solver.pop();
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
                                        let (_islp_new_sl_clauses, _islp_sl_stall): (Vec<Vec<TermId>>, bool) = $sl_handler;
                                        if _islp_sl_stall {
                                            let _ = solver.pop();
                                            $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                                            $self.last_result = Some(SolveResult::Unknown);
                                            break 'split_loop Ok(SolveResult::Unknown);
                                        }
                                        for _sl_clause in &_islp_new_sl_clauses {
                                            $crate::executor::theories::split_incremental::apply_string_lemma_incremental(
                                                &$self.ctx.terms, solver,
                                                &mut local_term_to_var, &mut local_var_to_term,
                                                &mut local_next_var, &mut _islp_negations, _sl_clause,
                                            );
                                            if proof_enabled {
                                                let _ = $self.proof_tracker.add_theory_lemma(
                                                    _sl_clause.to_vec(),
                                                );
                                            }
                                        }
                                        _islp_negations.sync_pending(&mut $self.ctx.terms);
                                        _islp_string_lemma_clauses.extend(_islp_new_sl_clauses);
                                        continue;
                                    )?
                                    let _ = solver.pop();
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break 'split_loop Ok(SolveResult::Unknown);
                                }
                                z4_core::TheoryResult::Unknown => {
                                    let _ = solver.pop();
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break 'split_loop Ok(SolveResult::Unknown);
                                }
                                other => unreachable!("unhandled TheoryResult variant in split loop: {other:?}"),
                            }
                        );
                    }
                    SatResult::Unsat => {
                        // SLIA soundness guard (#6273, #6688): if string lemma
                        // clauses were added, SAT UNSAT may be caused by the
                        // guard literals over-constraining the solver. Return
                        // Unknown instead of claiming UNSAT.
                        $(
                            let _ = $max_slr; // anchor syntax variable for $()?
                            if !_islp_string_lemma_clauses.is_empty() {
                                let _ = solver.pop();
                                $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                                $self.last_result = Some(SolveResult::Unknown);
                                break 'split_loop Ok(SolveResult::Unknown);
                            }
                        )?
                        // UNSAT proof capture + pop: shared macro (#5814 Packet 3)
                        pipeline_build_unsat_proof_with_pop!(
                            'split_loop, $self, solver,
                            local_var_to_term, _islp_negations, proof_enabled,
                            _islp_local_clausification_proofs, _islp_local_original_clause_theory_proofs
                        );
                    }
                    SatResult::Unknown => {
                        $self.last_model = None;
                        let _ = solver.pop();
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
            let _ = solver.pop();
            if $self.last_unknown_reason.is_none() {
                $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
            }
            $self.last_result = Some(SolveResult::Unknown);
            Ok(SolveResult::Unknown)
        };

        pipeline_split_epilogue!(
            $self, _islp_timing, _islp_total_start,
            _islp_last_theory_stats, _islp_result,
            eager: {},
            restore: { $self.incr_theory_state = Some(state); }
        )
    }};
}
