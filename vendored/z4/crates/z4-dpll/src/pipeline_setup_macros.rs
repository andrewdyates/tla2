// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared composable macros for the active DPLL(T) pipelines.
//!
//! After the final `pipeline_macros.rs` retirement (#6688/#6659), this module
//! holds the still-live stats collection, incremental setup, and split-loop
//! timing export macros.
//!
//! These are `macro_rules!` (not functions) for the same borrow-checker reason
//! as the pipeline code they support: theory executors hold `&self.ctx.terms`
//! through `DpllT`, so `&mut self` method calls on `Executor` would conflict.

/// Collect SAT solver statistics and record its unknown reason (#4622).
///
/// Uses a macro instead of a method to avoid `&mut self` borrow conflicts:
/// theory executors hold `&self.ctx.terms` through `DpllT`, so a method call
/// on `&mut self` would conflict. The macro expands to disjoint field accesses
/// which the borrow checker can verify independently.
macro_rules! collect_sat_stats {
    ($self:ident, $sat:expr) => {
        $self.last_statistics.conflicts = ($sat).num_conflicts();
        $self.last_statistics.decisions = ($sat).num_decisions();
        $self.last_statistics.propagations = ($sat).num_propagations();
        $self.last_statistics.restarts = ($sat).num_restarts();
        $self.last_statistics.learned_clauses = ($sat).num_learned_clauses();
        $self.pending_sat_unknown_reason = ($sat).last_unknown_reason();
        // NOTE: consistency checks are NOT called here because theory
        // stats (theory_conflicts, theory_propagations) may still hold stale
        // values from a prior check-sat. The consistency check runs in
        // collect_theory_stats! after
        // both SAT and theory counters are set.
    };
}

/// Collect theory-level statistics from incremental raw-theory state (#4705).
///
/// Pairs with `collect_sat_stats!` on the incremental pipelines, which
/// accumulate counters in `IncrementalTheoryState` rather than `DpllT`.
macro_rules! collect_theory_stats {
    (incremental: $self:ident, $state:expr) => {
        let theory_conflicts = ($state).theory_conflicts;
        let theory_propagations = ($state).theory_propagations;
        collect_theory_stats!(@clamp_and_check $self,
            theory_conflicts, theory_propagations, "incremental: ");
        // Mirror round_trips so incremental paths expose the same stat as DpllT (#4802).
        $self
            .last_statistics
            .set_int("dpll.round_trips", ($state).round_trips);
        // Export timing keys so :all-statistics includes them even on incremental paths (#5175).
        $self
            .last_statistics
            .set_float("time.dpll.sat_solve", ($state).sat_solve_secs);
        $self
            .last_statistics
            .set_float("time.dpll.theory_sync", ($state).theory_sync_secs);
        $self
            .last_statistics
            .set_float("time.dpll.theory_check", ($state).theory_check_secs);
        $self.last_statistics.debug_assert_consistency();
    };
    // Shared: set theory counters, pre-clamping debug check, and clamp
    (@clamp_and_check $self:ident, $tc:ident, $tp:ident, $prefix:expr) => {
        $self.last_statistics.theory_conflicts = $tc;
        $self.last_statistics.theory_propagations = $tp;
        // Pre-clamping check: log when theory counters exceed SAT counters (#4706).
        #[cfg(debug_assertions)]
        {
            let sat_conflicts = $self.last_statistics.conflicts;
            let sat_propagations = $self.last_statistics.propagations;
            if $tc > sat_conflicts {
                tracing::debug!(
                    target: "z4::dpll",
                    theory_conflicts = $tc,
                    sat_conflicts,
                    gap = $tc - sat_conflicts,
                    concat!($prefix, "theory conflicts exceed SAT conflicts (clamping will normalize)")
                );
            }
            if $tp > sat_propagations {
                tracing::debug!(
                    target: "z4::dpll",
                    theory_propagations = $tp,
                    sat_propagations,
                    gap = $tp - sat_propagations,
                    concat!($prefix, "theory propagations exceed SAT propagations (clamping will normalize)")
                );
            }
        }
        // Theory conflicts/propagations may exceed raw SAT counters.
        // Clamp SAT counters to preserve Statistics subset invariants (#4758).
        $self.last_statistics.conflicts = $self.last_statistics.conflicts.max($tc);
        $self.last_statistics.propagations =
            $self.last_statistics.propagations.max($tp);
    };
}

/// Common incremental pipeline setup: find new assertions, Tseitin-encode them,
/// initialize or reuse the persistent SAT solver, add assertion clauses, and
/// re-activate roots after pop().
///
/// This is the shared first phase of `solve_incremental_theory_pipeline` and
/// `solve_incremental_split_loop_pipeline`, which was duplicated (~120 lines)
/// with only the SAT solver field and solver-init hook differing.
///
/// After this macro expands, the following output bindings are live in the caller:
/// - `$new_assertion_set`: `HashSet<TermId>` (needed by some callers for dedup)
/// - `$solver_out`: `SatSolver` — the persistent SAT solver, taken out of state
/// - `$tseitin_out`: `Tseitin` — still live, caller must call `.into_state()`
/// - `$var_to_term`: `HashMap<u32, TermId>` — 0-indexed var-to-term map
/// - `$term_to_var`: `HashMap<TermId, u32>` — 0-indexed term-to-var map
///
/// The caller is responsible for:
/// 1. Storing `$solver_out` back into `$state.$sat_field` when done
///
/// All identifiers must be passed as parameters (Rust macro hygiene):
/// - `$self`: the `Executor`
/// - `$state`: the `&mut IncrementalTheoryState`
/// - `$proof_enabled`: the proof flag
/// - `$tag`: string tag for debug messages
/// - `$sat_field`: field on `IncrementalTheoryState` holding the SAT solver
/// - `solver_init`: hook block executed when a fresh solver is created
/// - `out`: tuple of output binding names
macro_rules! pipeline_incremental_setup {
    (
        $self:ident, $state:ident, $proof_enabled:ident, $random_seed:expr, $tag:expr,
        sat_field: $sat_field:ident,
        tseitin_field: $tseitin_field:ident,
        encoded_field: $encoded_field:ident,
        activation_scope_field: $activation_scope_field:ident,
        solver_init: $solver_init:block,
        out: ($new_assertion_set:ident, $solver_out:ident, $tseitin_out:ident,
              $var_to_term:ident, $term_to_var:ident, $pending_out:ident)
    ) => {
        // Find assertions that need to be Tseitin-transformed
        let $new_assertion_set: HashSet<TermId> = {
            let mut _pis_seen = HashSet::new();
            let _pis_new: Vec<TermId> = $self
                .ctx
                .assertions
                .iter()
                .copied()
                .filter(|term| !$state.$encoded_field.contains_key(term))
                .filter(|term| _pis_seen.insert(*term))
                .collect();
            _pis_new.iter().copied().collect()
        };
        let _pis_new_assertions: Vec<TermId> =
            $new_assertion_set.iter().copied().collect();
        let _pis_assertion_depths = $self.ctx.active_assertion_min_scope_depths();

        // Lift arithmetic ITEs from new assertions
        let _pis_lifted = $self.ctx.terms.lift_arithmetic_ite_all(&_pis_new_assertions);

        // Sync per-solver Tseitin state: advance next_var past this solver's
        // total_num_vars to avoid collisions with scope selectors (#6853).
        if let Some(ref sat) = $state.$sat_field {
            let sat_total =
                u32::try_from(sat.total_num_vars()).expect("SAT solver vars fit u32");
            $state.$tseitin_field.next_var = $state.$tseitin_field.next_var.max(sat_total + 1);
        }

        // When the SAT solver for this pipeline doesn't exist yet, its
        // initialization will push `scope_depth` scope selectors at variable
        // indices starting at num_vars. Reserve space for them (#6853).
        if $state.$sat_field.is_none() && $state.scope_depth > 0 {
            let _pis_reserve = $state.scope_depth as u32;
            $state.$tseitin_field.next_var += _pis_reserve;
        }

        let mut $tseitin_out = if $proof_enabled {
            Tseitin::from_state_with_proofs(
                &$self.ctx.terms,
                std::mem::take(&mut $state.$tseitin_field),
            )
        } else {
            Tseitin::from_state(&$self.ctx.terms, std::mem::take(&mut $state.$tseitin_field))
        };

        // Encode new assertions
        let _pis_encoded: Vec<(TermId, TseitinEncodedAssertion)> = _pis_new_assertions
            .iter()
            .zip(_pis_lifted.iter())
            .map(|(&orig, &lifted)| (orig, $tseitin_out.encode_assertion(lifted)))
            .collect();

        let _pis_total_vars = $tseitin_out.num_vars();

        // Initialize or resize persistent SAT solver
        let _pis_solver_is_new;
        let mut $solver_out = if let Some(s) = $state.$sat_field.take() {
            _pis_solver_is_new = false;
            s
        } else {
            _pis_solver_is_new = true;
            let mut sat = SatSolver::new(_pis_total_vars as usize);
            sat.set_random_seed($random_seed);
            // Mirror DpllT::from_tseitin so SMT incremental pipelines honor
            // Z4_TRACE_FILE JSONL emission as soon as the persistent SAT solver
            // is created.
            z4_sat::TlaTraceable::maybe_enable_tla_trace_from_env(&mut sat);
            if $proof_enabled {
                sat.enable_clause_trace();
            }
            if let Some(seed) = $self.random_seed {
                sat.set_random_seed(seed);
            }
            if $self.progress_enabled {
                sat.set_progress_enabled(true);
            }
            // Adaptive reorder gate for large incremental instances (#8118).
            if _pis_total_vars as usize > 50_000 {
                sat.set_reorder_enabled(false);
            }
            sat
        };
        $solver_out.ensure_num_vars(_pis_total_vars as usize);

        // If solver was just created, run the init hook for scope synchronization
        if _pis_solver_is_new {
            $state.$sat_field = Some($solver_out);
            $solver_init
            $solver_out = $state
                .$sat_field
                .take()
                .expect(concat!(
                    "incremental ", $tag,
                    " should preserve persistent SAT solver across init"
                ));
        }

        let _pis_cnf_to_sat = $crate::cnf_lit_to_sat;

        // #6853: Collect pending activations instead of adding them directly.
        let mut $pending_out: Vec<(SatLiteral, usize)> = Vec::new();

        // Add encoded assertions: definitions globally, activations deferred
        for (_pis_term, _pis_enc) in _pis_encoded {
            let TseitinEncodedAssertion {
                root_lit: _pis_root_lit,
                def_clauses: _pis_def_clauses,
                def_proof_annotations: _pis_def_proof_annotations,
            } = _pis_enc;

            if $proof_enabled {
                let _pis_annotations = _pis_def_proof_annotations
                    .as_ref()
                    .expect("proof-enabled incremental Tseitin encoding should carry annotations");
                debug_assert_eq!(
                    _pis_annotations.len(),
                    _pis_def_clauses.len(),
                    "incremental clause annotations must stay aligned with SAT clause order"
                );
                for (_pis_idx, clause) in _pis_def_clauses.iter().enumerate() {
                    let lits: Vec<SatLiteral> = clause
                        .literals()
                        .iter()
                        .map(|&lit| _pis_cnf_to_sat(lit))
                        .collect();
                    $solver_out.add_clause_global(lits);
                    $state
                        .clausification_proofs
                        .push(_pis_annotations[_pis_idx].clone());
                    $state.original_clause_theory_proofs.push(None);
                }
            } else {
                for clause in &_pis_def_clauses {
                    let lits: Vec<SatLiteral> = clause
                        .literals()
                        .iter()
                        .map(|&lit| _pis_cnf_to_sat(lit))
                        .collect();
                    $solver_out.add_clause_global(lits);
                }
            }

            let _pis_root = _pis_cnf_to_sat(_pis_root_lit);
            freeze_var_if_needed(&mut $solver_out, _pis_root.variable());
            let _pis_activation_depth =
                $state.desired_activation_depth(_pis_term, &_pis_assertion_depths);
            // Activation clause: force the Tseitin root variable true.
            // Global (depth 0) activations MUST use add_clause_global so they
            // survive SMT-level pop operations. Making them scoped causes model
            // validation failures in LRA/EUF incremental push/pop scenarios.
            if _pis_activation_depth == 0 {
                $solver_out.add_clause_global(vec![_pis_root]);
            } else {
                $solver_out.add_clause_at_scope_depth(vec![_pis_root], _pis_activation_depth);
            }
            if $proof_enabled {
                $state.clausification_proofs.push(None);
                $state.original_clause_theory_proofs.push(None);
            }

            $state.$encoded_field.insert(_pis_term, _pis_root_lit);
            $state
                .$activation_scope_field
                .insert(_pis_term, _pis_activation_depth);
        }

        // Re-activate currently asserted roots only after a pop()
        if $state.needs_activation_reassert {
            let mut _pis_seen_active = HashSet::new();
            for &assertion in &$self.ctx.assertions {
                if !_pis_seen_active.insert(assertion) {
                    continue;
                }
                if $new_assertion_set.contains(&assertion) {
                    continue;
                }
                if $state
                    .$activation_scope_field
                    .get(&assertion)
                    .copied()
                    .is_some_and(|depth| {
                        depth
                            <= $state.desired_activation_depth(assertion, &_pis_assertion_depths)
                    })
                {
                    continue;
                }
                if let Some(&root_lit) = $state.$encoded_field.get(&assertion) {
                    let _pis_root = _pis_cnf_to_sat(root_lit);
                    let _pis_activation_depth =
                        $state.desired_activation_depth(assertion, &_pis_assertion_depths);
                    freeze_var_if_needed(&mut $solver_out, _pis_root.variable());
                    // Defer re-activation to inside the private push scope (#6853)
                    $pending_out.push((_pis_root, _pis_activation_depth));
                    $state
                        .$activation_scope_field
                        .insert(assertion, _pis_activation_depth);
                }
            }
            $state.needs_activation_reassert = false;
        }

        // Build var_to_term and term_to_var maps (convert 1-indexed to 0-indexed)
        let $var_to_term: HashMap<u32, TermId> = $tseitin_out
            .var_to_term()
            .iter()
            .map(|(&v, &t)| (v - 1, t))
            .collect();
        let $term_to_var: HashMap<TermId, u32> = $tseitin_out
            .term_to_var()
            .iter()
            .map(|(&t, &v)| (t, v - 1))
            .collect();
    };
}

/// Apply pending activation clauses inside a private push scope (#6853).
macro_rules! pipeline_apply_pending_activations {
    ($solver:expr, $pending:expr, $proof_enabled:expr,
     $state:expr) => {
        for &(_apa_root, _apa_depth) in &$pending {
            $solver.add_clause(vec![_apa_root]);
            if $proof_enabled {
                $state.clausification_proofs.push(None);
                $state.original_clause_theory_proofs.push(None);
            }
        }
    };
}

/// Apply pending activation clauses immediately at their desired depth (#6853).
macro_rules! pipeline_apply_pending_activations_immediate {
    ($solver:expr, $pending:expr, $proof_enabled:expr,
     $state:expr) => {
        for &(_apa_root, _apa_depth) in &$pending {
            if _apa_depth == 0 {
                $solver.add_clause_global(vec![_apa_root]);
            } else {
                $solver.add_clause_at_scope_depth(vec![_apa_root], _apa_depth);
            }
            if $proof_enabled {
                $state.clausification_proofs.push(None);
                $state.original_clause_theory_proofs.push(None);
            }
        }
    };
}

/// Re-activate ALL encoded assertions inside a private push scope (#6853).
///
/// The lazy and assume arms use private push/pop around each solve. Pop removes
/// all clauses added during the push. This macro re-adds activation unit clauses
/// for every active encoded assertion, ensuring the SAT solver sees them during
/// solve. Skips assertions already in `$pending` (from blocks 1/2 in setup).
///
/// Only needed by lazy/assume arms. Eager/non-split arms persist activations
/// across check-sats and don't need this.
macro_rules! pipeline_reactivate_all_in_scope {
    ($self:expr, $solver:expr, $state:expr, $pending:expr,
     $proof_enabled:expr, $encoded_field:ident) => {{
        let _pras_cnf_to_sat = $crate::cnf_lit_to_sat;
        let mut _pras_seen: hashbrown::HashSet<z4_sat::Literal> = $pending
            .iter()
            .map(|&(lit, _): &(z4_sat::Literal, usize)| lit)
            .collect();
        for &assertion in &$self.ctx.assertions {
            if let Some(&root_lit) = $state.$encoded_field.get(&assertion) {
                let _pras_root = _pras_cnf_to_sat(root_lit);
                if _pras_seen.insert(_pras_root) {
                    $solver.add_clause(vec![_pras_root]);
                    if $proof_enabled {
                        $state.clausification_proofs.push(None);
                        $state.original_clause_theory_proofs.push(None);
                    }
                }
            }
        }
    }};
}

/// Export split-loop solve timing totals into `Statistics.extra`.
macro_rules! pipeline_export_split_loop_timing_stats {
    ($self:ident, $stats:expr) => {
        $self
            .last_statistics
            .set_float("time.dpll.sat_solve", ($stats).dpll.sat_solve.as_secs_f64());
        $self.last_statistics.set_float(
            "time.dpll.theory_sync",
            ($stats).dpll.theory_sync.as_secs_f64(),
        );
        $self.last_statistics.set_float(
            "time.dpll.theory_check",
            ($stats).dpll.theory_check.as_secs_f64(),
        );
        $self
            .last_statistics
            .set_int("dpll.round_trips", ($stats).dpll.round_trips);
        $self.last_statistics.set_float(
            "time.split_loop.model_extract",
            ($stats).model_extract.as_secs_f64(),
        );
        $self.last_statistics.set_float(
            "time.split_loop.store_model",
            ($stats).store_model.as_secs_f64(),
        );
        $self
            .last_statistics
            .set_float("time.split_loop.total", ($stats).total.as_secs_f64());
    };
}

/// Export theory learned state (cuts, HNF cuts, Dioph state) from a theory
/// instance into local variables. Shared across all split-loop arms.
///
/// Extracted by #5814 Packet 2 to eliminate ~20 duplicate 5-line blocks
/// across eager, eager-persistent, and lazy-shared macro files.
macro_rules! pipeline_export_theory_state {
    ($theory:expr, $export_theory:ident, $export_expr:expr,
     $learned_cuts:expr, $seen_hnf_cuts:expr, $dioph_state:expr) => {{
        let $export_theory = &mut $theory;
        let (_ec, _eh, _ed) = $export_expr;
        $learned_cuts = _ec;
        $seen_hnf_cuts = _eh;
        $dioph_state = _ed;
    }};
}

/// Capture proof state, pop solver, and break with UNSAT for lazy/assume arms.
///
/// Shared between the lazy and assume split-loop arms. These arms use push/pop
/// scoping and must clone proof state before popping. The eager arms use a
/// different macro (`pipeline_incremental_split_eager_build_unsat_proof!`) that
/// skips the pop.
///
/// Extracted by #5814 Packet 3 to eliminate duplicate UNSAT proof capture code.
macro_rules! pipeline_build_unsat_proof_with_pop {
    ($loop_label:lifetime, $self:ident, $solver:ident,
     $local_var_to_term:ident, $negations:ident, $proof_enabled:ident,
     $local_clausification_proofs:ident, $local_theory_proofs:ident
    ) => {
        $self.last_model = None;
        if $proof_enabled {
            $negations.sync_pending(&mut $self.ctx.terms);
            let _bup_clause_trace = $solver.clause_trace().cloned();
            let (_bup_cp, _bup_tp) = {
                if let Some(ref _bup_trace) = _bup_clause_trace {
                    let _bup_oc = _bup_trace.original_clauses().count();
                    if $local_clausification_proofs.len() < _bup_oc {
                        $local_clausification_proofs.resize(_bup_oc, None);
                    }
                    if $local_theory_proofs.len() < _bup_oc {
                        $local_theory_proofs.resize(_bup_oc, None);
                    }
                }
                (
                    $local_clausification_proofs.clone(),
                    $local_theory_proofs.clone(),
                )
            };
            let _bup_vtm = $local_var_to_term.clone();
            let _bup_neg = $negations.as_map().clone();
            let _ = $solver.pop();
            $self.last_clause_trace = _bup_clause_trace;
            $self.last_clausification_proofs = Some(_bup_cp);
            $self.last_original_clause_theory_proofs = Some(_bup_tp);
            $self.last_var_to_term = Some(_bup_vtm);
            $self.last_negations = Some(_bup_neg);
            $self.build_unsat_proof();
        } else {
            let _ = $solver.pop();
        }
        $self.last_result = Some(SolveResult::Unsat);
        break $loop_label Ok(SolveResult::Unsat);
    };
}

/// Inject bound axiom binary clauses (#6579): (x<=3)=>(x<=5) so BCP propagates
/// bound ordering. Shared between the lazy and assume split-loop arms.
///
/// Extracted by #5814 Packet 1 to eliminate duplication between
/// `pipeline_incremental_split_lazy_macros.rs` and
/// `pipeline_incremental_split_assume_macros.rs`.
macro_rules! pipeline_inject_bound_axioms {
    ($self:expr, $solver:expr, $base_active_atoms:expr, $base_term_to_var:expr,
     $create_theory:expr, $proof_enabled:expr, $tag:expr,
     $local_clausification_proofs:expr, $local_original_clause_theory_proofs:expr) => {{
        let mut axiom_theory = $create_theory;
        for &atom in &$base_active_atoms {
            z4_core::TheorySolver::register_atom(&mut axiom_theory, atom);
        }
        z4_core::TheorySolver::sort_atom_index(&mut axiom_theory);
        let axiom_pairs = z4_core::TheorySolver::generate_bound_axiom_terms(&axiom_theory);
        let mut axiom_count = 0usize;
        for (t1, p1, t2, p2) in axiom_pairs {
            if let (Some(&v1), Some(&v2)) = ($base_term_to_var.get(&t1), $base_term_to_var.get(&t2))
            {
                let l1 = if p1 {
                    z4_sat::Literal::positive(z4_sat::Variable::new(v1))
                } else {
                    z4_sat::Literal::negative(z4_sat::Variable::new(v1))
                };
                let l2 = if p2 {
                    z4_sat::Literal::positive(z4_sat::Variable::new(v2))
                } else {
                    z4_sat::Literal::negative(z4_sat::Variable::new(v2))
                };
                $solver.add_clause(vec![l1, l2]);
                if $proof_enabled {
                    let clause_terms = vec![
                        if p1 { t1 } else { $self.ctx.terms.mk_not(t1) },
                        if p2 { t2 } else { $self.ctx.terms.mk_not(t2) },
                    ];
                    let mut check_lra = z4_lra::LraSolver::new(&$self.ctx.terms);
                    z4_core::TheorySolver::assert_literal(&mut check_lra, t1, !p1);
                    z4_core::TheorySolver::assert_literal(&mut check_lra, t2, !p2);
                    let farkas = match z4_core::TheorySolver::check(&mut check_lra) {
                        z4_core::TheoryResult::UnsatWithFarkas(conflict) => conflict.farkas,
                        _ => None,
                    };
                    let kind =
                        $crate::theory_inference::infer_theory_lemma_kind_from_clause_terms_and_farkas(
                            &$self.ctx.terms,
                            &clause_terms,
                            farkas.as_ref(),
                        );
                    match (&kind, &farkas) {
                        (_, Some(farkas)) => {
                            let _ = $self.proof_tracker.add_theory_lemma_with_farkas_and_kind(
                                clause_terms,
                                farkas.clone(),
                                kind,
                            );
                        }
                        (z4_core::TheoryLemmaKind::Generic, None) => {
                            let _ = $self.proof_tracker.add_theory_lemma(clause_terms);
                        }
                        (_, None) => {
                            let _ = $self
                                .proof_tracker
                                .add_theory_lemma_with_kind(clause_terms, kind);
                        }
                    }
                    $local_clausification_proofs.push(None);
                    $local_original_clause_theory_proofs.push(Some(z4_core::TheoryLemmaProof {
                        kind,
                        farkas,
                        lia: None,
                    }));
                }
                axiom_count += 1;
            }
        }
        if axiom_count > 0 {
            tracing::info!(
                axiom_count,
                theory_atoms = $base_active_atoms.len(),
                concat!("Incremental ", $tag, " bound axiom injection (#6579)")
            );
        }
    }};
}

/// Export split-loop eager-extension counters into `Statistics.extra`.
macro_rules! pipeline_export_split_loop_eager_stats {
    ($self:ident, $stats:expr) => {
        $self
            .last_statistics
            .set_int("dpll.eager.propagate_calls", ($stats).propagate_calls);
        $self.last_statistics.set_int(
            "dpll.eager.state_unchanged_skips",
            ($stats).state_unchanged_skips,
        );
        $self.last_statistics.set_int(
            "dpll.eager.bound_refinement_handoffs",
            ($stats).bound_refinement_handoffs,
        );
        $self
            .last_statistics
            .set_int("dpll.eager.batch_defers", ($stats).batch_defers);
        $self.last_statistics.set_int(
            "dpll.eager.level0_batch_guard_hits",
            ($stats).level0_batch_guard_hits,
        );
        $self
            .last_statistics
            .set_int("dpll.eager.level0_checks", ($stats).level0_checks);
    };
}

/// Register proof context for incremental pipelines (#5814 Packet A).
///
/// Owns exactly:
/// - `proof_tracker.set_theory($tag)` — exactly once
/// - base `h{idx}` assumption registration for all active assertions
/// - optional `ha{idx}` registration when an assumptions slice is provided
///
/// Does NOT own: ledger cloning, negation-cache seeding, UNSAT proof export.
macro_rules! pipeline_register_proof_context {
    ($self:expr, $proof_enabled:expr, $tag:expr) => {{
        let problem_assertions = $self.proof_problem_assertions();
        pipeline_register_proof_context!(
            $self,
            $proof_enabled,
            $tag,
            problem_assertions: problem_assertions
        );
    }};
    ($self:expr, $proof_enabled:expr, $tag:expr, problem_assertions: $problem_assertions:expr) => {{
        if $proof_enabled {
            $self.proof_tracker.set_theory($tag);
            if $self.proof_problem_assertion_provenance.is_some() {
                // #6759: inside deferred-postprocessing, register ALL temporary
                // assertions as Assumes so ensure_empty_clause_derivation can
                // resolve through auxiliary constraints (mod/div side conditions,
                // array axioms). Only problem-provenance assertions get h{idx}
                // labels; the demotion pass demotes unlabeled ones to Trust.
                let problem_set: hashbrown::HashSet<z4_core::TermId> =
                    $problem_assertions.into_iter().collect();
                for (idx, &assertion) in $self.ctx.assertions.iter().enumerate() {
                    let label = if problem_set.contains(&assertion) {
                        Some(format!("h{idx}"))
                    } else {
                        None
                    };
                    let _ = $self.proof_tracker.add_assumption(assertion, label);
                }
            } else {
                for (idx, assertion) in $problem_assertions.into_iter().enumerate() {
                    let _ = $self
                        .proof_tracker
                        .add_assumption(assertion, Some(format!("h{idx}")));
                }
            }
        }
    }};
    ($self:expr, $proof_enabled:expr, $tag:expr,
     problem_assertions: $problem_assertions:expr, assumptions: $assumptions:expr) => {{
        if $proof_enabled {
            $self.proof_tracker.set_theory($tag);
            if $self.proof_problem_assertion_provenance.is_some() {
                // #6759: same as above — register all assertions, label only
                // problem-provenance ones.
                let problem_set: hashbrown::HashSet<z4_core::TermId> =
                    $problem_assertions.into_iter().collect();
                for (idx, &assertion) in $self.ctx.assertions.iter().enumerate() {
                    let label = if problem_set.contains(&assertion) {
                        Some(format!("h{idx}"))
                    } else {
                        None
                    };
                    let _ = $self.proof_tracker.add_assumption(assertion, label);
                }
            } else {
                for (idx, assertion) in $problem_assertions.into_iter().enumerate() {
                    let _ = $self
                        .proof_tracker
                        .add_assumption(assertion, Some(format!("h{idx}")));
                }
            }
            for (idx, &(_preprocessed, original)) in $assumptions.iter().enumerate() {
                let _ = $self
                    .proof_tracker
                    .add_assumption(original, Some(format!("ha{idx}")));
            }
        }
    }};
}

/// Clone split-local proof ledgers from incremental state (#5814 Packet A).
///
/// Owns exactly: cloning `state.clausification_proofs` and
/// `state.original_clause_theory_proofs` into split-loop locals.
///
/// Returns `(Vec<Option<ClausificationProof>>, Vec<Option<TheoryLemmaProof>>)`.
/// Export timing stats, theory stats, and optionally eager stats and
/// state restore at the end of a split-loop arm.
///
/// Shared across all 4 split-loop arms (#5814 Packet C). The `eager` block
/// is for `pipeline_export_split_loop_eager_stats!` (eager/eager-persistent only).
/// The `restore` block is for `$self.incr_theory_state = Some(state)` (lazy/eager
/// only, where state was taken via `.take()`).
macro_rules! pipeline_split_epilogue {
    ($self:ident, $timing:expr, $total_start:expr,
     $last_theory_stats:expr, $result:expr,
     eager: { $($eager:tt)* }, restore: { $($restore:tt)* }) => {{
        $timing.total = $total_start.elapsed();
        pipeline_export_split_loop_timing_stats!($self, $timing);
        $($eager)*
        $self.last_statistics.set_int("dpll.rebuilds", 0);
        for (name, value) in &$last_theory_stats {
            $self.last_statistics.set_int(name, *value);
        }
        $($restore)*
        $result
    }};
}

/// Used only by the four split arms (not the no-split incremental macro).
macro_rules! pipeline_clone_local_proof_ledgers {
    ($state:expr, $proof_enabled:expr) => {{
        let local_clausification_proofs = if $proof_enabled {
            $state.clausification_proofs.clone()
        } else {
            Vec::new()
        };
        let local_original_clause_theory_proofs = if $proof_enabled {
            $state.original_clause_theory_proofs.clone()
        } else {
            Vec::new()
        };
        (
            local_clausification_proofs,
            local_original_clause_theory_proofs,
        )
    }};
}
