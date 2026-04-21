// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared helper macros for lazy and assumption split-loop arms.
//!
//! Extracted from per-arm files (#6680 Packet 2). This macro owns the
//! duplicated theory-result dispatch code that is identical between the
//! lazy and assumption execution modes.

/// Dispatches a theory result (Sat, Unsat, UnsatWithFarkas, NeedSplit,
/// NeedDisequalitySplit, NeedExpressionSplit, NeedLemmas, NeedModelEquality,
/// NeedModelEqualities) inside the lazy/assumption split loop.
///
/// Must be invoked inside a `'split_loop`-labeled block within a `for` loop.
/// The Sat handler and remaining arms (NeedStringLemma, Unknown, catchall)
/// are provided by the caller as token blocks.
///
/// The `$theory` variable is consumed (dropped) by non-Sat arms that need
/// to create split atoms or encode lemmas. The Sat handler block receives
/// `$theory` still alive.
macro_rules! pipeline_incremental_split_lazy_dispatch_theory_result {
    ($loop_label:lifetime, $self:ident, $solver:ident, $state:ident,
     tag: $tag:expr,
     $theory:ident,
     theory_result: $theory_result:expr,
     export_theory: |$export_theory:ident| $export_expr:expr,
     $ltv:ident, $lvt:ident, $lnv:ident,
     $asc:ident, $lsv:ident, $mec:ident, $mer:ident, $mer_max:ident,
     $lc:ident, $shc:ident, $ds:ident, $tl:ident, $tls:ident,
     $neg:ident, $pe:ident, $lcp:ident, $ltp:ident,
     sat_handler: { $($sat_handler:tt)* },
     remaining_arms: { $($remaining_arms:tt)* }
    ) => {
        match $theory_result {
            z4_core::TheoryResult::Sat => {
                $($sat_handler)*
            }
            z4_core::TheoryResult::Unsat(conflict_terms) => {
                $crate::verification::log_conflict_debug_with_terms(
                    &conflict_terms,
                    concat!("incremental ", $tag, " UNSAT"),
                    &$self.ctx.terms,
                );
                if let Err(e) = $crate::verification::verify_theory_conflict(&conflict_terms) {
                    tracing::error!(
                        error = %e,
                        conflict_len = conflict_terms.len(),
                        concat!("BUG(#4666): ", $tag, " conflict verification failed; returning Unknown")
                    );
                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    break;
                }
                // Semantic conflict verification must stay domain-aware here.
                // Mixed UFLIA/AUFLIA conflicts can legitimately include EUF
                // atoms; re-checking them with a standalone LiaSolver alone
                // turns real combined-theory UNSAT results into false Unknown.
                if let Err(e) = $crate::verification::verify_conflict_semantic(
                    &conflict_terms,
                    &$self.ctx.terms,
                ) {
                    tracing::error!(
                        error = %e,
                        conflict_len = conflict_terms.len(),
                        conflict = ?conflict_terms,
                        concat!("BUG(#6853): ", $tag, " LIA conflict is SAT under fresh LiaSolver; returning Unknown")
                    );
                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    break;
                }
                // Record structured theory proof (#6725) — mirrors no-split
                // incremental path (pipeline_incremental_macros.rs:248).
                let _sld_theory_proof = if $pe {
                    Some(z4_core::TheoryLemmaProof {
                        kind: $crate::theory_inference::infer_theory_conflict_kind(
                            Some(&$self.ctx.terms),
                            $neg.as_map(),
                            &conflict_terms,
                            None,
                        ),
                        farkas: None,
                        lia: None,
                    })
                } else {
                    None
                };
                if $pe {
                    let _ = $crate::theory_inference::record_theory_conflict_unsat(
                        &mut $self.proof_tracker,
                        Some(&$self.ctx.terms),
                        $neg.as_map(),
                        &conflict_terms,
                    );
                }
                pipeline_map_incremental_split_conflict_clause!(
                    $self,
                    label: $loop_label,
                    state: $state,
                    solver: $solver,
                    theory: $theory,
                    export_theory: |$export_theory| $export_expr,
                    learned_cuts: $lc,
                    seen_hnf_cuts: $shc,
                    dioph_state: $ds,
                    local_term_to_var: $ltv,
                    conflict_terms: conflict_terms,
                    proof_enabled: $pe,
                    negations: $neg.as_map(),
                    local_var_to_term: $lvt,
                    local_clausification_proofs: $lcp,
                    local_theory_proofs: $ltp,
                    theory_proof: _sld_theory_proof
                );
            }
            z4_core::TheoryResult::UnsatWithFarkas(conflict) => {
                $crate::verification::log_conflict_debug_with_terms(
                    &conflict.literals,
                    concat!("incremental ", $tag, " UnsatWithFarkas"),
                    &$self.ctx.terms,
                );
                let mut _sld_farkas_proof_valid = conflict.farkas.is_some();
                if let Err(e) = $crate::verification::verify_theory_conflict_with_farkas(&conflict) {
                    if e.is_missing_annotation() {
                        _sld_farkas_proof_valid = false;
                        tracing::debug!(
                            conflict_len = conflict.literals.len(),
                            concat!($tag, " Farkas annotation missing; conflict clause is sound, skipping proof cert")
                        );
                    } else {
                        _sld_farkas_proof_valid = false;
                        tracing::error!(
                            error = %e,
                            conflict_len = conflict.literals.len(),
                            concat!("BUG(#4666): ", $tag, " Farkas verification failed; returning Unknown")
                        );
                        $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        break;
                    }
                }
                // Record structured theory proof with Farkas coefficients (#6725)
                // — mirrors no-split incremental path (pipeline_incremental_macros.rs:321-327).
                let _sld_theory_proof = if $pe {
                    Some(if _sld_farkas_proof_valid {
                        z4_core::TheoryLemmaProof {
                            kind: $crate::theory_inference::infer_theory_conflict_kind(
                                Some(&$self.ctx.terms),
                                $neg.as_map(),
                                &conflict.literals,
                                conflict.farkas.as_ref(),
                            ),
                            farkas: conflict.farkas.clone(),
                            lia: None,
                        }
                    } else {
                        z4_core::TheoryLemmaProof {
                            kind: $crate::theory_inference::infer_theory_conflict_kind(
                                Some(&$self.ctx.terms),
                                $neg.as_map(),
                                &conflict.literals,
                                None,
                            ),
                            farkas: None,
                            lia: None,
                        }
                    })
                } else {
                    None
                };
                if $pe {
                    if _sld_farkas_proof_valid {
                        let _ = $crate::theory_inference::record_theory_conflict_unsat_with_farkas(
                            &mut $self.proof_tracker,
                            Some(&$self.ctx.terms),
                            $neg.as_map(),
                            &conflict,
                        );
                    } else {
                        let _ = $crate::theory_inference::record_theory_conflict_unsat(
                            &mut $self.proof_tracker,
                            Some(&$self.ctx.terms),
                            $neg.as_map(),
                            &conflict.literals,
                        );
                    }
                }
                pipeline_map_incremental_split_conflict_clause!(
                    $self,
                    label: $loop_label,
                    state: $state,
                    solver: $solver,
                    theory: $theory,
                    export_theory: |$export_theory| $export_expr,
                    learned_cuts: $lc,
                    seen_hnf_cuts: $shc,
                    dioph_state: $ds,
                    local_term_to_var: $ltv,
                    conflict_terms: conflict.literals,
                    proof_enabled: $pe,
                    negations: $neg.as_map(),
                    local_var_to_term: $lvt,
                    local_clausification_proofs: $lcp,
                    local_theory_proofs: $ltp,
                    theory_proof: _sld_theory_proof
                );
            }
            z4_core::TheoryResult::NeedSplit(split) => {
                debug_assert!(
                    !split.value.is_integer(),
                    concat!("BUG: ", $tag, "-INC NeedSplit value {} is integral"),
                    split.value
                );

                let oscillation_detected = $crate::executor::theories::solve_harness::check_split_oscillation(
                    &mut $lsv, split.variable, &split.value,
                );

                pipeline_export_theory_state!(
                    $theory, $export_theory, $export_expr,
                    $lc, $shc, $ds
                );
                drop($theory);

                let (le_atom, ge_atom, _prefer_ceil) =
                    $crate::executor::theories::solve_harness::create_int_split_atoms(
                        &mut $self.ctx.terms, &split,
                    );

                let (le_var, ge_var) = $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                    &$self.ctx.terms, $solver,
                    &mut $ltv, &mut $lvt,
                    &mut $lnv, &mut $neg,
                    le_atom, ge_atom, None,
                    &mut $asc,
                );

                if oscillation_detected {
                    // Unbounded drift detected (#6729): the split variable's
                    // value has moved monotonically in one direction for
                    // UNBOUNDED_THRESHOLD iterations. Instead of returning
                    // Unknown, force the OPPOSITE branch by adding a unit
                    // clause for the bounding direction. This explores the
                    // bounded region of the feasible polyhedron.
                    //
                    // Determine drift direction from the oscillation tracking
                    // counter: positive count = value increasing → force
                    // floor (le); negative count = value decreasing → force
                    // ceil (ge).
                    let force_le = $lsv.get(&split.variable)
                        .map_or(true, |(_, count)| *count > 0);
                    if force_le {
                        $solver.add_clause(vec![
                            SatLiteral::positive(le_var),
                        ]);
                        $solver.set_var_phase(le_var, true);
                        $solver.set_var_phase(ge_var, false);
                    } else {
                        $solver.add_clause(vec![
                            SatLiteral::positive(ge_var),
                        ]);
                        $solver.set_var_phase(ge_var, true);
                        $solver.set_var_phase(le_var, false);
                    }
                    // Reset the oscillation counter for this variable so the
                    // solver gets a fresh window in the bounded direction.
                    $lsv.remove(&split.variable);
                } else if _prefer_ceil == Some(true) {
                    $solver.set_var_phase(ge_var, true);
                    $solver.set_var_phase(le_var, false);
                } else {
                    $solver.set_var_phase(le_var, true);
                    $solver.set_var_phase(ge_var, false);
                }
            }
            z4_core::TheoryResult::NeedDisequalitySplit(split) => {
                pipeline_export_theory_state!(
                    $theory, $export_theory, $export_expr,
                    $lc, $shc, $ds
                );
                drop($theory);

                use $crate::executor::theories::solve_harness::DisequalitySplitAtoms;
                match $crate::executor::theories::solve_harness::create_disequality_split_atoms(
                    &mut $self.ctx.terms, &split,
                ) {
                    DisequalitySplitAtoms::Skip => { continue; }
                    DisequalitySplitAtoms::IntFractional { le, ge } => {
                        $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                            &$self.ctx.terms, $solver,
                            &mut $ltv, &mut $lvt,
                            &mut $lnv, &mut $neg, le, ge, None,
                            &mut $asc,
                        );
                    }
                    DisequalitySplitAtoms::IntExact { le, ge, disequality_term, is_distinct } => {
                        let guard = disequality_term.map(|dt| (dt, is_distinct));
                        $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                            &$self.ctx.terms, $solver,
                            &mut $ltv, &mut $lvt,
                            &mut $lnv, &mut $neg, le, ge, guard,
                            &mut $asc,
                        );
                    }
                    DisequalitySplitAtoms::Real { lt, gt, disequality_term, is_distinct } => {
                        let guard = disequality_term.map(|dt| (dt, is_distinct));
                        $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                            &$self.ctx.terms, $solver,
                            &mut $ltv, &mut $lvt,
                            &mut $lnv, &mut $neg, lt, gt, guard,
                            &mut $asc,
                        );
                    }
                }
            }
            z4_core::TheoryResult::NeedExpressionSplit(split) => {
                pipeline_export_theory_state!(
                    $theory, $export_theory, $export_expr,
                    $lc, $shc, $ds
                );
                drop($theory);

                let Some((lt_atom, gt_atom, is_distinct)) =
                    $crate::executor::theories::create_expression_split_atoms(
                        &mut $self.ctx.terms,
                        split.disequality_term,
                    )
                else {
                    let _ = $solver.pop();
                    $self.last_unknown_reason = Some(UnknownReason::ExpressionSplit);
                    $self.last_result = Some(SolveResult::Unknown);
                    break $loop_label Ok(SolveResult::Unknown);
                };

                let guard = Some((split.disequality_term, is_distinct));
                $crate::executor::theories::split_incremental::encode_and_add_split_clause(
                    &$self.ctx.terms, $solver,
                    &mut $ltv, &mut $lvt,
                    &mut $lnv, &mut $neg,
                    lt_atom, gt_atom, guard,
                    &mut $asc,
                );
            }
            z4_core::TheoryResult::NeedLemmas(lemmas) => {
                pipeline_export_theory_state!(
                    $theory, $export_theory, $export_expr,
                    $lc, $shc, $ds
                );
                drop($theory);

                for lemma in &lemmas {
                    $crate::executor::theories::split_incremental::apply_theory_lemma_incremental(
                        &$self.ctx.terms,
                        $solver,
                        &mut $ltv,
                        &mut $lvt,
                        &mut $lnv,
                        &mut $neg,
                        &lemma.clause,
                    );
                }
                if $pe {
                    $neg.sync_pending(&mut $self.ctx.terms);
                }
                for lemma in &lemmas {
                    if $pe {
                        let terms: Vec<z4_core::TermId> = lemma
                            .clause
                            .iter()
                            .map(|lit| {
                                if lit.value {
                                    lit.term
                                } else {
                                    *$neg
                                        .as_map()
                                        .get(&lit.term)
                                        .expect("theory-lemma negation cache should be synced")
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
                                let _ = $self.proof_tracker.add_theory_lemma_with_kind(terms, kind);
                            }
                        }
                        $lcp.push(None);
                        $ltp.push(Some(z4_core::TheoryLemmaProof { kind, farkas: None , lia: None }));
                    }
                    if $tls.insert(&lemma.clause) {
                        $tl.push(lemma.clone());
                    }
                }
                continue;
            }
            z4_core::TheoryResult::NeedModelEquality(eq) => {
                pipeline_export_theory_state!(
                    $theory, $export_theory, $export_expr,
                    $lc, $shc, $ds
                );
                drop($theory);

                $mer += 1;
                if $mer > $mer_max {
                    let _ = $solver.pop();
                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    $self.last_result = Some(SolveResult::Unknown);
                    break $loop_label Ok(SolveResult::Unknown);
                }
                *$mec.entry((eq.lhs, eq.rhs)).or_insert(0) += 1;

                pipeline_encode_model_equality!(
                    $self, $solver, $ltv, $lvt, $lnv, $neg, eq
                );
            }
            z4_core::TheoryResult::NeedModelEqualities(eqs) => {
                pipeline_export_theory_state!(
                    $theory, $export_theory, $export_expr,
                    $lc, $shc, $ds
                );
                drop($theory);

                $mer += 1;
                if $mer > $mer_max {
                    let _ = $solver.pop();
                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    $self.last_result = Some(SolveResult::Unknown);
                    break $loop_label Ok(SolveResult::Unknown);
                }

                for eq in eqs {
                    *$mec.entry((eq.lhs, eq.rhs)).or_insert(0) += 1;
                    pipeline_encode_model_equality!(
                        $self, $solver, $ltv, $lvt, $lnv, $neg, eq
                    );
                }
            }
            $($remaining_arms)*
        }
    };
}
