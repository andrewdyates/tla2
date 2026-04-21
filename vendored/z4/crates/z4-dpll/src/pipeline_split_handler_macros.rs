// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared split-handler macros for active DPLL(T) pipelines.
//!
//! The remaining macros centralize the incremental conflict and replay helpers
//! that are still shared after the legacy split-loop deletion.

/// Convert a verified incremental theory conflict into a SAT blocking clause.
///
/// Used by `solve_incremental_theory_pipeline!` for both plain theory
/// conflicts and Farkas conflicts once structural/semantic verification has
/// already succeeded.
macro_rules! pipeline_add_incremental_conflict_clause {
    (
        $self:ident,
        state: $state:ident,
        solver: $solver:ident,
        term_to_var: $term_to_var:ident,
        conflict_terms: $conflict_terms:expr,
        tag: $tag:expr,
        set_unknown_on_error: $set_unknown:expr,
        unmapped_message: $unmapped_message:literal
    ) => {{
        let clause: Vec<SatLiteral> = $conflict_terms
            .iter()
            .filter_map(|t| {
                $term_to_var.get(&t.term).map(|&var| {
                    if t.value {
                        SatLiteral::negative(SatVariable::new(var))
                    } else {
                        SatLiteral::positive(SatVariable::new(var))
                    }
                })
            })
            .collect();
        if clause.is_empty() {
            if !$conflict_terms.is_empty() {
                tracing::warn!(
                    tag = $tag,
                    num_conflict_terms = $conflict_terms.len(),
                    $unmapped_message
                );
                if $set_unknown {
                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                }
                $self.last_result = Some(SolveResult::Unknown);
                break Ok(SolveResult::Unknown);
            }
            $self.last_result = Some(SolveResult::Unsat);
            break Ok(SolveResult::Unsat);
        }
        $solver.add_clause(clause);
    }};
}

/// Persist a verified incremental split-loop conflict as a blocking clause.
///
/// Used by `solve_incremental_split_loop_pipeline!` after the conflict has
/// been verified, regardless of whether it came from a plain theory conflict
/// or a Farkas explanation.
///
/// Proof capture (#6660 Packet 7): when `proof_enabled` is true, the Unsat
/// exit clones proof data from solver/state, pops the SAT frame, then assigns
/// to `$self` and calls `build_unsat_proof()`. The clone-pop-assign ordering
/// avoids double-mutable-borrow of `$self` through the `state -> solver` chain.
macro_rules! pipeline_map_incremental_split_conflict_clause {
    (
        $self:ident,
        label: $label:lifetime,
        state: $state:ident,
        solver: $solver:ident,
        theory: $theory:ident,
        export_theory: |$export_theory:ident| $export_expr:expr,
        learned_cuts: $learned_cuts:ident,
        seen_hnf_cuts: $seen_hnf_cuts:ident,
        dioph_state: $dioph_state:ident,
        local_term_to_var: $local_term_to_var:ident,
        conflict_terms: $conflict_terms:expr,
        proof_enabled: $proof_enabled:expr,
        negations: $negations:expr,
        local_var_to_term: $local_var_to_term:expr,
        local_clausification_proofs: $local_clausification_proofs:ident,
        local_theory_proofs: $local_theory_proofs:ident,
        theory_proof: $theory_proof:expr
    ) => {{
        $state.theory_conflicts = $state.theory_conflicts.saturating_add(1);
        collect_theory_stats!(incremental: $self, $state);

        let extra_conflicts = $theory.lra_solver().collect_all_bound_conflicts(true);
        pipeline_export_theory_state!(
            $theory, $export_theory, $export_expr,
            $learned_cuts, $seen_hnf_cuts, $dioph_state
        );

        match map_conflict_to_blocking_clause(
            $solver,
            &$conflict_terms,
            &extra_conflicts,
            &$local_term_to_var,
        ) {
            BlockingClauseResult::Unmapped => {
                $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                break;
            }
            BlockingClauseResult::Unsat => {
                if $proof_enabled {
                    let _pmc_clause_trace = $solver.clause_trace().cloned();
                    let (_pmc_clausification_proofs, _pmc_theory_proofs) = {
                        if let Some(ref _pmc_trace) = _pmc_clause_trace {
                            let _pmc_count = _pmc_trace.original_clauses().count();
                            if $local_clausification_proofs.len() < _pmc_count {
                                $local_clausification_proofs.resize(_pmc_count, None);
                            }
                            if $local_theory_proofs.len() < _pmc_count {
                                $local_theory_proofs.resize(_pmc_count, None);
                            }
                        }
                        (
                            $local_clausification_proofs.clone(),
                            $local_theory_proofs.clone(),
                        )
                    };
                    let _pmc_vtm = $local_var_to_term.clone();
                    let _pmc_neg = $negations.clone();
                    let _ = $solver.pop();
                    $self.last_clause_trace = _pmc_clause_trace;
                    $self.last_clausification_proofs = Some(_pmc_clausification_proofs);
                    $self.last_original_clause_theory_proofs = Some(_pmc_theory_proofs);
                    $self.last_var_to_term = Some(_pmc_vtm);
                    $self.last_negations = Some(_pmc_neg);
                    $self.build_unsat_proof();
                } else {
                    let _ = $solver.pop();
                }
                $self.last_result = Some(SolveResult::Unsat);
                break $label Ok(SolveResult::Unsat);
            }
            BlockingClauseResult::Added => {
                if let Some(_pmc_theory_proof) = $theory_proof {
                    $local_clausification_proofs.push(None);
                    $local_theory_proofs.push(Some(_pmc_theory_proof));
                }
            }
        }
    }};
}

/// Encode a model equality atom, set its phase hint, and bump its activity.
///
/// This matches `DpllT::apply_model_equality()`: internalize the equality as a
/// retractable SAT decision and bias CDCL to try the equality first rather than
/// asserting it as a permanent unit clause.
///
/// For Int/Real-sorted terms, also adds triangle axioms connecting the equality
/// to arithmetic: `(= a b) <=> (a <= b) AND (b <= a)`. This is the Z3
/// `arith_eq_adapter` pattern: the SAT solver's model equality decision is
/// backed by arithmetic constraints that the LIA/LRA theory can reason about.
/// Without these axioms, model equalities are free Boolean variables
/// disconnected from arithmetic (#6846).
///
/// Shared core of the NeedModelEquality / NeedModelEqualities handlers across
/// the no-split, lazy-shared, and eager split-loop arms. The surrounding
/// retry-counter and control-flow logic differs between arms and stays inline.
///
/// Extracted by #5814 Packet 4 to eliminate 6 duplicate encode+bias blocks.
macro_rules! pipeline_encode_model_equality {
    ($self:expr, $solver:expr, $term_to_var:expr, $var_to_term:expr,
     $next_var:expr, $negations:expr, $eq:expr, added_model_eqs: $added_model_eqs:expr) => {{
        let _pipeline_eq_atom = $self.ctx.terms.mk_eq($eq.lhs, $eq.rhs);
        let _pipeline_add_triangle_clauses = ($added_model_eqs).insert(_pipeline_eq_atom);
        pipeline_encode_model_equality!(
            @impl
            $self,
            $solver,
            $term_to_var,
            $var_to_term,
            $next_var,
            $negations,
            $eq,
            _pipeline_eq_atom,
            _pipeline_add_triangle_clauses
        );
    }};
    ($self:expr, $solver:expr, $term_to_var:expr, $var_to_term:expr,
     $next_var:expr, $negations:expr, $eq:expr) => {{
        let _pipeline_eq_atom = $self.ctx.terms.mk_eq($eq.lhs, $eq.rhs);
        pipeline_encode_model_equality!(
            @impl
            $self,
            $solver,
            $term_to_var,
            $var_to_term,
            $next_var,
            $negations,
            $eq,
            _pipeline_eq_atom,
            true
        );
    }};
    (@impl
     $self:expr, $solver:expr, $term_to_var:expr, $var_to_term:expr,
     $next_var:expr, $negations:expr, $eq:expr, $eq_atom:expr,
     $add_triangle_clauses:expr) => {{
        let eq_var = $crate::executor::theories::split_incremental::ensure_incremental_atom_encoded(
            &$self.ctx.terms,
            $solver,
            &mut $term_to_var,
            &mut $var_to_term,
            &mut $next_var,
            &mut $negations,
            $eq_atom,
        );
        $solver.set_var_phase(eq_var, true);
        for _ in 0..20 {
            $solver.bump_variable_activity(eq_var);
        }

        // #6846: Triangle axioms for Int/Real model equalities.
        // (= a b) <=> (a <= b) AND (b <= a)
        // This connects the model equality to arithmetic so LIA/LRA can
        // reason about it (Z3 arith_eq_adapter pattern).
        let _lhs_sort = $self.ctx.terms.sort($eq.lhs);
        if matches!(_lhs_sort, z4_core::Sort::Int | z4_core::Sort::Real) {
            use z4_sat::Literal as _TriLit;

            let le_atom = $self.ctx.terms.mk_le($eq.lhs, $eq.rhs);
            let ge_atom = $self.ctx.terms.mk_le($eq.rhs, $eq.lhs);

            let le_var =
                $crate::executor::theories::split_incremental::ensure_incremental_atom_encoded(
                    &$self.ctx.terms,
                    $solver,
                    &mut $term_to_var,
                    &mut $var_to_term,
                    &mut $next_var,
                    &mut $negations,
                    le_atom,
                );
            let ge_var =
                $crate::executor::theories::split_incremental::ensure_incremental_atom_encoded(
                    &$self.ctx.terms,
                    $solver,
                    &mut $term_to_var,
                    &mut $var_to_term,
                    &mut $next_var,
                    &mut $negations,
                    ge_atom,
                );

            if $add_triangle_clauses {
                // Persistent split loops may request the same model equality
                // many times while converging. Re-adding the same adapter
                // clauses bloats the SAT state without adding information.
                // Encode the triangle only on the first request for an eq atom.
                $solver.add_clause(vec![_TriLit::negative(eq_var), _TriLit::positive(le_var)]);
                $solver.add_clause(vec![_TriLit::negative(eq_var), _TriLit::positive(ge_var)]);
                $solver.add_clause(vec![
                    _TriLit::negative(le_var),
                    _TriLit::negative(ge_var),
                    _TriLit::positive(eq_var),
                ]);
            }

            // Propagate phase bias to le/ge atoms (Z3 arith_eq_adapter pattern).
            $solver.set_var_phase(le_var, true);
            $solver.set_var_phase(ge_var, true);
        }
    }};
}

/// Build a `TseitinResult` from local maps, run `solve_and_store_model_with_theories`,
/// and break out of the split loop with the result.
///
/// Shared across all 4 split-loop arms (#5814 Packet B). The `pre_store` block
/// runs between TseitinResult construction and the store call — use it for
/// arm-specific cleanup (`solver.pop()`, `theory.unset_terms()`, or `{}`).
macro_rules! pipeline_store_sat_model {
    ($loop_label:lifetime, $self:expr, $solver:expr, $model:expr,
     $local_term_to_var:expr, $local_var_to_term:expr, $local_next_var:expr,
     $timing:expr, $theory:ident, $theory_var:ident, $extract:expr,
     pre_store: { $($pre_store:tt)* }) => {{
        let _psm_extract_start = std::time::Instant::now();
        let $theory_var = &mut $theory;
        let _psm_models = $extract;
        $timing.model_extract += _psm_extract_start.elapsed();

        let _psm_fake_result = z4_core::TseitinResult::new(
            vec![],
            $local_term_to_var.iter().map(|(&t, &v)| (t, v + 1)).collect(),
            $local_var_to_term.iter().map(|(&v, &t)| (v + 1, t)).collect(),
            1,
            $local_next_var,
        );
        $($pre_store)*
        let _psm_store_start = std::time::Instant::now();
        let _psm_store_result = $self.solve_and_store_model_with_theories(
            z4_sat::SatResult::Sat($model), &_psm_fake_result, _psm_models,
        );
        $timing.store_model += _psm_store_start.elapsed();
        break $loop_label _psm_store_result;
    }};
}

/// Build a `TheoryExtension`, run `solve_with_extension`, collect stats, and
/// return `(sat_result, partial_count, pending_split, pending_refinements)`.
///
/// Shared between the eager and eager-persistent split-loop arms (#5814
/// Packet D). The extension construction, SAT solve, and stats collection
/// are character-identical between the two arms.
macro_rules! pipeline_build_eager_extension {
    ($self:ident, $solver:expr, $theory:ident,
     $local_var_to_term:expr, $local_term_to_var:expr,
     $active_theory_atoms:expr, $active_theory_atom_set:expr,
     $proof_enabled:expr, $negations:expr,
     $added_refinement_clauses:expr, $added_axioms:expr,
     $eager_stats:expr, $timing:expr, $state:expr) => {{
        let mut _pbe_ext = $crate::extension::TheoryExtension::new(
            &mut $theory,
            &$local_var_to_term,
            &$local_term_to_var,
            &$active_theory_atoms,
            &$active_theory_atom_set,
            Some(&$self.ctx.terms),
            None,
        )
        .with_inline_bound_refinement_replay(&$added_refinement_clauses);
        if $proof_enabled {
            _pbe_ext = _pbe_ext.with_proof_tracking(
                &mut $self.proof_tracker, $negations.as_map(),
            );
        }
        _pbe_ext.retain_new_axioms(&mut $added_axioms);

        let _pbe_sat_start = std::time::Instant::now();
        let _pbe_sat_result = $solver.solve_with_extension(&mut _pbe_ext).into_inner();
        let _pbe_sat_elapsed = _pbe_sat_start.elapsed();
        $timing.dpll.sat_solve += _pbe_sat_elapsed;
        if let Some(_pbe_r) = $solver.last_unknown_reason() {
            $self.last_unknown_reason =
                Some($crate::executor::Executor::map_sat_unknown_reason(_pbe_r));
        }

        let _pbe_ext_conflicts = _pbe_ext.num_theory_conflicts();
        let _pbe_ext_propagations = _pbe_ext.num_theory_propagations();
        let _pbe_ext_partial = _pbe_ext.num_partial_clauses();
        $eager_stats.accumulate_from(_pbe_ext.eager_stats());
        let _pbe_pending_split = _pbe_ext.take_pending_split();
        let _pbe_pending_refinements = _pbe_ext.take_pending_bound_refinements();
        drop(_pbe_ext);

        $state.theory_conflicts =
            $state.theory_conflicts.saturating_add(_pbe_ext_conflicts);
        $state.theory_propagations =
            $state.theory_propagations.saturating_add(_pbe_ext_propagations);
        $state.sat_solve_secs = $timing.dpll.sat_solve.as_secs_f64();
        $state.theory_sync_secs = $timing.dpll.theory_sync.as_secs_f64();
        $state.theory_check_secs = $timing.dpll.theory_check.as_secs_f64();
        collect_sat_stats!($self, $solver);
        collect_theory_stats!(incremental: $self, $state);

        (_pbe_sat_result, _pbe_ext_conflicts, _pbe_ext_propagations,
         _pbe_ext_partial, _pbe_pending_split, _pbe_pending_refinements)
    }};
}
