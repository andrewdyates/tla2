// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared helper macros for eager and eager-persistent split-loop arms.
//!
//! Extracted from per-arm files (#6680 Packet 5). These macros own the
//! duplicated split-dispatch and UNSAT proof code that is identical
//! between the eager and eager-persistent execution modes.

/// Dispatches a pending split result (NeedSplit, NeedDisequalitySplit,
/// NeedExpressionSplit) into SAT solver clause additions.
///
/// Must be invoked inside a `'split_loop`-labeled block within a `for` loop.
/// Uses `continue` when a split clause is successfully added, and
/// `break $loop_label` when the split cannot proceed (oscillation, encoding
/// failure, or unrecognized theory result).
///
/// The `fallthrough` block handles the `_` match arm (other TheoryResult
/// variants). In the SAT path this breaks with Unknown; in the Unknown path
/// it is typically empty.
macro_rules! pipeline_incremental_split_eager_dispatch_split {
    ($loop_label:lifetime, $self:ident, $solver:ident,
     tag: $tag:expr, suffix: $suffix:expr,
     $local_term_to_var:ident, $local_var_to_term:ident, $local_next_var:ident, $negations:ident,
     $islp_added_split_clauses:ident, $islp_last_split_values:ident,
     split_result: $split_result:expr,
     fallthrough: { $($fallthrough:tt)* }
    ) => {
        use z4_core::TheoryResult;
        match $split_result {
            TheoryResult::NeedSplit(split) => {
                debug_assert!(
                    !split.value.is_integer(),
                    concat!("BUG: ", $tag, $suffix, " NeedSplit value {} is integral"),
                    split.value
                );

                let oscillation_detected = $crate::executor::theories::solve_harness::check_split_oscillation(
                    &mut $islp_last_split_values, split.variable, &split.value,
                );

                let (le_atom, ge_atom, _prefer_ceil) =
                    $crate::executor::theories::solve_harness::create_int_split_atoms(
                        &mut $self.ctx.terms, &split,
                    );

                let (le_var, ge_var) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                    &$self.ctx.terms, $solver,
                    &mut $local_term_to_var, &mut $local_var_to_term,
                    &mut $local_next_var, &mut $negations,
                    le_atom, ge_atom, None,
                    &mut $islp_added_split_clauses,
                );

                if oscillation_detected {
                    // Unbounded drift detected: force the OPPOSITE branch.
                    // Positive count = value increasing -> force floor (le).
                    // Negative count = value decreasing -> force ceil (ge).
                    let force_le = $islp_last_split_values.get(&split.variable)
                        .map_or(true, |(_, count)| *count > 0);
                    if force_le {
                        $solver.add_clause(vec![SatLiteral::positive(le_var)]);
                        $solver.set_var_phase(le_var, true);
                        $solver.set_var_phase(ge_var, false);
                    } else {
                        $solver.add_clause(vec![SatLiteral::positive(ge_var)]);
                        $solver.set_var_phase(ge_var, true);
                        $solver.set_var_phase(le_var, false);
                    }
                    $islp_last_split_values.remove(&split.variable);
                } else if _prefer_ceil == Some(true) {
                    $solver.set_var_phase(ge_var, true);
                    $solver.set_var_phase(le_var, false);
                } else {
                    $solver.set_var_phase(le_var, true);
                    $solver.set_var_phase(ge_var, false);
                }
                continue;
            }
            TheoryResult::NeedDisequalitySplit(split) => {
                use $crate::executor::theories::solve_harness::DisequalitySplitAtoms;
                match $crate::executor::theories::solve_harness::create_disequality_split_atoms(
                    &mut $self.ctx.terms, &split,
                ) {
                    DisequalitySplitAtoms::Skip => { continue; }
                    DisequalitySplitAtoms::IntFractional { le, ge } => {
                        let (le_var, ge_var) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                            &$self.ctx.terms, $solver,
                            &mut $local_term_to_var, &mut $local_var_to_term,
                            &mut $local_next_var, &mut $negations, le, ge, None,
                            &mut $islp_added_split_clauses,
                        );
                        $crate::executor::theories::split_incremental::bias_positive_split_clause_vars(
                            $solver, le_var, ge_var,
                        );
                    }
                    DisequalitySplitAtoms::IntExact { le, ge, disequality_term, is_distinct } => {
                        let guard = disequality_term.map(|dt| (dt, is_distinct));
                        let (le_var, ge_var) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                            &$self.ctx.terms, $solver,
                            &mut $local_term_to_var, &mut $local_var_to_term,
                            &mut $local_next_var, &mut $negations, le, ge, guard,
                            &mut $islp_added_split_clauses,
                        );
                        $crate::executor::theories::split_incremental::bias_positive_split_clause_vars(
                            $solver, le_var, ge_var,
                        );
                    }
                    DisequalitySplitAtoms::Real { lt, gt, disequality_term, is_distinct } => {
                        let guard = disequality_term.map(|dt| (dt, is_distinct));
                        let (lt_var, gt_var) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                            &$self.ctx.terms, $solver,
                            &mut $local_term_to_var, &mut $local_var_to_term,
                            &mut $local_next_var, &mut $negations, lt, gt, guard,
                            &mut $islp_added_split_clauses,
                        );
                        $crate::executor::theories::split_incremental::bias_positive_split_clause_vars(
                            $solver, lt_var, gt_var,
                        );
                    }
                }
                continue;
            }
            TheoryResult::NeedExpressionSplit(split) => {
                let Some((lt_atom, gt_atom, is_distinct)) =
                    $crate::executor::theories::create_expression_split_atoms(
                        &mut $self.ctx.terms,
                        split.disequality_term,
                    )
                else {
                    $self.last_unknown_reason = Some(UnknownReason::ExpressionSplit);
                    $self.last_result = Some(SolveResult::Unknown);
                    break $loop_label Ok(SolveResult::Unknown);
                };

                let guard = Some((split.disequality_term, is_distinct));
                let (lt_var, gt_var) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                    &$self.ctx.terms, $solver,
                    &mut $local_term_to_var, &mut $local_var_to_term,
                    &mut $local_next_var, &mut $negations,
                    lt_atom, gt_atom, guard,
                    &mut $islp_added_split_clauses,
                );
                $crate::executor::theories::split_incremental::bias_positive_split_clause_vars(
                    $solver, lt_var, gt_var,
                );
                continue;
            }
            _ => {
                $($fallthrough)*
            }
        }
    };
}

/// Captures proof state and builds an UNSAT proof for the eager split-loop.
///
/// Must be invoked inside a `'split_loop`-labeled block. Always breaks out
/// of the loop with `Ok(SolveResult::Unsat)`.
///
/// #6725: accepts local clausification and theory-proof ledgers and exports
/// both, matching the lazy arm's dual-ledger contract.
macro_rules! pipeline_incremental_split_eager_build_unsat_proof {
    ($loop_label:lifetime, $self:ident, $solver:ident, $state:ident,
     $local_var_to_term:ident, $islp_negations:ident, $proof_enabled:ident,
     $local_clausification_proofs:ident, $local_theory_proofs:ident
    ) => {
        $self.last_model = None;
        if $proof_enabled {
            let _islp_clause_trace = $solver.clause_trace().cloned();
            if let Some(ref _islp_trace) = _islp_clause_trace {
                let _islp_original_count = _islp_trace.original_clauses().count();
                if $local_clausification_proofs.len() < _islp_original_count {
                    $local_clausification_proofs.resize(_islp_original_count, None);
                }
                if $local_theory_proofs.len() < _islp_original_count {
                    $local_theory_proofs.resize(_islp_original_count, None);
                }
            }
            $self.last_clause_trace = _islp_clause_trace;
            $self.last_clausification_proofs = Some($local_clausification_proofs.clone());
            $self.last_original_clause_theory_proofs = Some($local_theory_proofs.clone());
            $self.last_var_to_term = Some($local_var_to_term.clone());
            $self.last_negations = Some($islp_negations.as_map().clone());
            $self.build_unsat_proof();
        }
        $self.last_result = Some(SolveResult::Unsat);
        break $loop_label Ok(SolveResult::Unsat);
    };
}
