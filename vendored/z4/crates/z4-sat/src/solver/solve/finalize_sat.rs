// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT model finalization, verification, and result shaping.
//!
//! Hosts `finalize_sat_model` (reconstruction + original-formula verification)
//! and the `declare_sat_*` / `declare_unknown_*` API methods.

use super::super::*;
use crate::solver_log::solver_log;

impl Solver {
    #[cfg(debug_assertions)]
    #[inline]
    pub(in crate::solver) fn debug_assert_sat_result_model(
        &self,
        sat_model: &[bool],
        context: &'static str,
    ) {
        let model = self.get_model();
        debug_assert!(
            self.verify_model(&model),
            "BUG: {context}: current assignment does not satisfy clause_db",
        );
        match self.finalize_sat_model(model) {
            Ok(model) => {
                debug_assert_eq!(
                    model, sat_model,
                    "BUG: {context}: returned SAT model diverges from finalized current assignment",
                );
            }
            Err(detail) => {
                panic!("BUG: {context}: finalize_sat_model failed in debug validation: {detail}");
            }
        }
    }

    /// Finalize SAT model: reconstruct, verify, and truncate
    ///
    /// This method centralizes SAT model finalization to ensure all SAT returns
    /// go through verification. All SAT return sites MUST use this method.
    ///
    /// # Invariants enforced
    ///
    /// 1. **Reconstruction**: Variables eliminated by BVE/sweeping are restored
    ///    to values consistent with the original formula.
    /// 2. **Verification**: always-on SAT contract validates the model satisfies
    ///    ALL clauses (including internal selector variables for incremental solving).
    /// 3. **Truncation**: Internal variables are removed; only user-visible
    ///    variables (0..user_num_vars) are returned.
    ///
    /// Returns `Err(detail)` if model verification fails after reconstruction.
    pub(in crate::solver) fn finalize_sat_model(
        &self,
        model: Vec<bool>,
    ) -> Result<Vec<bool>, String> {
        tracing::debug!(
            num_vars = self.num_vars,
            user_num_vars = self.user_num_vars,
            reconstruction_len = self.inproc.reconstruction.len(),
            original_clauses = self.cold.original_ledger.num_clauses(),
            has_scopes = !self.cold.scope_selectors.is_empty(),
            "finalize_sat_model: entry"
        );

        // Pre-reconstruction: verify internal model against clause_db.
        #[cfg(debug_assertions)]
        debug_assert!(
            self.verify_clause_db_only(&model, false),
            "BUG: SAT model does not satisfy clause_db before reconstruction"
        );

        // #5012 Family C: validate reconstruction stack before applying it.
        #[cfg(debug_assertions)]
        self.validate_reconstruction_stack();

        // #7917: Early unit-clause check. Original unit clauses must be
        // satisfied by the internal model *before* reconstruction. Unit
        // clauses cannot be affected by BVE reconstruction (they have no
        // eliminated variables to restore), so a violation here indicates
        // a core CDCL or preprocessing bug, not a reconstruction issue.
        // This check runs in O(unit_clauses) and provides a precise
        // diagnostic that distinguishes core-solver bugs from reconstruction
        // bugs.
        {
            for (ci, clause) in self.cold.original_ledger.iter_clauses().enumerate() {
                if clause.len() != 1 {
                    continue;
                }
                let lit = clause[0];
                let vi = lit.variable().index();
                // Map external variable to internal for pre-reconstruction check.
                if vi < self.cold.e2i.len() {
                    let int_var = self.cold.e2i[vi];
                    if int_var != compact::UNMAPPED {
                        let int_var = int_var as usize;
                        if int_var < model.len() {
                            let model_val = model[int_var];
                            let expected = lit.is_positive();
                            if model_val != expected {
                                let detail =
                                    format!(
                                    "BUG: original unit clause {} (ext_var{}, pos={}) violated \
                                     by internal model BEFORE reconstruction — core solver or \
                                     preprocessing bug, not reconstruction. int_var={}, \
                                     model_val={}, clause_index={}",
                                    lit.to_dimacs(), vi, expected, int_var, model_val, ci,
                                );
                                tracing::error!(detail = detail.as_str(), "unit clause violation");
                                return Err(detail);
                            }
                        }
                    }
                }
            }
        }

        // Under active scopes, skip reconstruction. Reconstruction entries from
        // base-formula preprocessing (GBCE/BVE) may flip variables that violate
        // scoped constraints. The model already satisfies all non-deleted clauses
        // (verified above). After pop(), the no-assumptions path re-applies
        // reconstruction correctly for the base formula.
        if self.cold.scope_selectors.is_empty() {
            // Build external model from internal assignments via e2i (#5250).
            // Reference: CaDiCaL extend.cpp:134-144.
            let ext_num_vars = self.cold.e2i.len();
            let mut ext_model = vec![false; ext_num_vars];
            for (ext_var, val) in ext_model.iter_mut().enumerate() {
                let int_var = self.cold.e2i[ext_var];
                if int_var == compact::UNMAPPED {
                    continue;
                }
                let int_var = int_var as usize;
                if int_var < self.num_vars {
                    // Active variable: read current assignment from vals
                    *val = self.vals[int_var * 2] > 0;
                }
                // Unmapped (eliminated) external vars: left as false.
                // Reconstruction will assign them correctly.
            }

            let ext_model_before = ext_model.clone();

            // Apply reconstruction (external index space, #5250).
            let reconstruction = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                self.inproc.reconstruction.reconstruct(&mut ext_model);
            }));
            if let Err(payload) = reconstruction {
                let detail = if let Some(s) = payload.downcast_ref::<&str>() {
                    (*s).to_owned()
                } else if let Some(s) = payload.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "non-string panic payload".to_owned()
                };
                return Err(format!("reconstruction panic: {detail}"));
            }

            // Log reconstruction impact for diagnostics (#7917).
            let vars_changed = ext_model
                .iter()
                .zip(ext_model_before.iter())
                .filter(|(a, b)| a != b)
                .count();
            tracing::debug!(
                vars_changed,
                ext_num_vars,
                reconstruction_len = self.inproc.reconstruction.len(),
                "finalize_sat_model: reconstruction complete"
            );

            // Repair pass REMOVED (#6892): The greedy repair pass introduced in
            // #5522 would iterate original clauses and flip eliminated variables
            // to satisfy unsatisfied clauses. This caused oscillation — flipping
            // a variable for one clause would break a clause that reconstruction
            // had correctly satisfied. On crn_11_99_u (UNSAT), reconstruction
            // correctly set var287=true via its witness entry, but the repair
            // pass flipped it back to false for an earlier clause containing
            // ¬287, creating an infinite oscillation that never converges.
            //
            // CaDiCaL does NOT have a repair pass (extend.cpp:121-204) — it
            // trusts reconstruction to produce a correct model extension. If
            // reconstruction alone cannot satisfy all original clauses, that
            // indicates either:
            //   (a) the reconstruction stack is missing entries (a BVE bug), or
            //   (b) the formula is actually UNSAT.
            // In case (a), the proper fix is in the BVE/reconstruction code,
            // not a greedy repair. In case (b), returning Unknown is correct.

            // Verify against original-formula ledger (#4999: always-on).
            // Original clauses are in external index space (#5250).
            //
            // CaDiCaL's External::check_assignment (external.cpp:704-749)
            // checks ALL original clauses after reconstruction — no skip.
            // Z4 does the same: reconstruction has already run. Any clause
            // still unsatisfied is a genuine reconstruction bug → Unknown.
            //
            // When push/pop was used (#5077, #5522): skip scoped clauses,
            // because they may contain scope-selector literals that are
            // no longer asserted after pop().
            let fail_idx = self.cold.original_ledger.iter_clauses().position(|clause| {
                // Skip clauses containing scope selector variables.
                if self.cold.has_ever_scoped {
                    let has_scope = clause.iter().any(|lit| {
                        let vi = lit.variable().index();
                        vi < self.cold.was_scope_selector.len() && self.cold.was_scope_selector[vi]
                    });
                    if has_scope {
                        return false;
                    }
                }
                !clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < ext_model.len() && (ext_model[vi] == lit.is_positive())
                })
            });
            if let Some(fi) = fail_idx {
                let clause = self.cold.original_ledger.clause(fi);
                let clause_dimacs: Vec<i32> = clause
                    .iter()
                    .map(|&lit| {
                        let v = lit.variable().0 as i32 + 1;
                        if lit.is_positive() {
                            v
                        } else {
                            -v
                        }
                    })
                    .collect();
                let lit_details: Vec<String> = clause
                    .iter()
                    .map(|&lit| {
                        let vi = lit.variable().index();
                        let model_val = if vi < ext_model.len() {
                            Some(ext_model[vi])
                        } else {
                            None
                        };
                        let before_val = if vi < ext_model_before.len() {
                            Some(ext_model_before[vi])
                        } else {
                            None
                        };
                        format!(
                            "ext_var{}=before:{:?}->after:{:?}(pos={})",
                            vi,
                            before_val,
                            model_val,
                            lit.is_positive()
                        )
                    })
                    .collect();
                let was_sat_before = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < ext_model_before.len() && (ext_model_before[vi] == lit.is_positive())
                });
                let changed_vars: Vec<usize> = (0..ext_model.len().max(ext_model_before.len()))
                    .filter(|&vi| {
                        let a = ext_model_before.get(vi).copied().unwrap_or(false);
                        let b = ext_model.get(vi).copied().unwrap_or(false);
                        a != b
                    })
                    .collect();
                #[cfg(debug_assertions)]
                let recon_entries: Vec<String> = {
                    let clause_vars: std::collections::HashSet<usize> =
                        clause.iter().map(|l| l.variable().index()).collect();
                    let mut entries = Vec::new();
                    for (si, step) in self.inproc.reconstruction.iter_steps().enumerate() {
                        if let crate::reconstruct::ReconstructionStep::Witness(wc) = step {
                            let involves = wc
                                .witness
                                .iter()
                                .chain(wc.clause.iter())
                                .any(|l| clause_vars.contains(&l.variable().index()));
                            if involves {
                                let w: Vec<i32> =
                                    wc.witness.iter().map(|l| l.to_dimacs()).collect();
                                let c: Vec<i32> = wc.clause.iter().map(|l| l.to_dimacs()).collect();
                                entries.push(format!("  stack[{si}]: witness={w:?}, clause={c:?}"));
                            }
                        }
                    }
                    entries
                };
                #[cfg(not(debug_assertions))]
                let recon_entries: Vec<String> = Vec::new();
                let detail = format!(
                    "BUG: original clause {}/{} unsatisfied, reconstruction_len={}, num_original={}, \
                     clause_dimacs={:?}, lit_details=[{}], root_satisfied_saved={}, \
                     was_sat_before_recon={}, changed_vars_count={}, changed_vars={:?}, \
                     recon_entries_involving_clause=[{}]",
                    fi,
                    self.cold.original_ledger.num_clauses(),
                    self.inproc.reconstruction.len(),
                    self.num_original_clauses,
                    clause_dimacs,
                    lit_details.join(", "),
                    self.cold.root_satisfied_saved.len(),
                    was_sat_before,
                    changed_vars.len(),
                    &changed_vars[..changed_vars.len().min(30)],
                    recon_entries.join("\n"),
                );
                tracing::error!(
                    detail = detail.as_str(),
                    "original formula verification failed"
                );
                eprintln!("FINALIZE_SAT_FAIL: {detail}");
                return Err(detail);
            }

            // Verify root-satisfied clauses (external space, debug only).
            #[cfg(debug_assertions)]
            for (ri, clause) in self.cold.root_satisfied_saved.iter().enumerate() {
                let satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    vi < ext_model.len() && (ext_model[vi] == lit.is_positive())
                });
                assert!(
                    satisfied,
                    "BUG: root-satisfied clause {} unsatisfied in post-reconstruction \
                     external model! num_ext_vars={}, recon_steps={}",
                    ri,
                    ext_num_vars,
                    self.inproc.reconstruction.len(),
                );
            }

            #[cfg(debug_assertions)]
            {
                let mut model = vec![false; self.num_vars];
                for (int_var, val) in model.iter_mut().enumerate() {
                    let ext_var = self.cold.i2e[int_var] as usize;
                    debug_assert!(
                        ext_var < ext_model.len(),
                        "BUG: reconstructed SAT model missing external var {ext_var} for internal var {int_var}",
                    );
                    *val = ext_model[ext_var];
                }
                debug_assert!(
                    self.verify_model(&model),
                    "BUG: reconstructed SAT model does not satisfy clause_db"
                );
            }

            // Truncate external model to user-visible variables.
            // User variables are the first user_num_vars external variables.
            let mut result = ext_model;
            result.truncate(self.user_num_vars);

            return Ok(result);
        }

        // Under scope: only verify non-deleted clause_db (skip removed-clause check).
        // Reconstruction entries may reference clauses incompatible with scoped constraints.
        #[cfg(debug_assertions)]
        debug_assert!(
            self.verify_clause_db_only(&model, false),
            "BUG: SAT model does not satisfy clause_db under scope"
        );

        // Scoped path: verify internal model against clause_db and truncate.
        // No reconstruction applied (entries may conflict with scoped constraints).
        if let Some(violation) = self.first_model_violation(&model, false) {
            let detail = match &violation {
                preprocess::ModelViolation::ClauseDb {
                    clause_index,
                    clause_dimacs,
                } => {
                    format!("clause_db[{clause_index}] unsatisfied; clause={clause_dimacs:?}")
                }
            };
            return Err(detail);
        }
        let mut result = model;
        #[cfg(debug_assertions)]
        debug_assert!(
            self.verify_model(&result),
            "BUG: scoped SAT model does not satisfy clause_db"
        );
        result.truncate(self.user_num_vars);
        Ok(result)
    }

    #[inline]
    pub(in crate::solver) fn declare_sat_from_model(&mut self, model: Vec<bool>) -> SatResult {
        let model = match self.finalize_sat_model(model) {
            Ok(model) => model,
            Err(detail) => {
                tracing::error!(
                    detail = detail.as_str(),
                    "sat model verification failed after reconstruction"
                );
                self.cold.last_unknown_detail = Some(detail);
                return self.declare_unknown_with_reason(SatUnknownReason::InvalidSatModel);
            }
        };
        #[cfg(debug_assertions)]
        self.debug_assert_sat_result_model(&model, "declare_sat_from_model");
        // #7912: verify the finalized external model against all original clauses.
        // Belt-and-suspenders: finalize_sat_model already checks this (always-on),
        // and debug_assert_sat_result_model verifies the internal model. This
        // assertion catches any regression in either of those checks.
        debug_assert!(
            self.verify_external_model(&model),
            "BUG: Invalid SAT model — finalized model does not satisfy original clauses"
        );
        solver_log!(
            self,
            "SAT: {} conflicts, {} decisions, model size {}",
            self.num_conflicts,
            self.num_decisions,
            model.len()
        );
        tracing::info!(
            num_conflicts = self.num_conflicts,
            num_decisions = self.num_decisions,
            model_size = model.len(),
            "solve: sat"
        );
        self.emit_diagnostic_sat_summary(model.len());
        SatResult::Sat(model)
    }

    #[inline]
    pub(in crate::solver) fn declare_sat_from_current_assignment(&mut self) -> SatResult {
        self.declare_sat_from_model(self.get_model())
    }

    #[inline]
    pub(in crate::solver) fn declare_unknown_with_reason(
        &mut self,
        reason: SatUnknownReason,
    ) -> SatResult {
        if std::env::var("Z4_DEBUG_UNKNOWN").is_ok() {
            let detail_str = self.cold.last_unknown_detail.as_deref().unwrap_or("(none)");
            eprintln!(
                "DECLARE_UNKNOWN: reason={}, conflicts={}, decisions={}, propagations={}, detail={}",
                reason.diagnostic_label(),
                self.num_conflicts,
                self.num_decisions,
                self.num_propagations,
                detail_str,
            );
        }
        self.cold.last_unknown_reason = Some(reason);
        self.emit_diagnostic_unknown_summary(reason.diagnostic_label());
        SatResult::Unknown
    }

    #[inline]
    pub(in crate::solver) fn declare_assume_sat_from_model(
        &mut self,
        model: Vec<bool>,
    ) -> AssumeResult {
        let model = match self.finalize_sat_model(model) {
            Ok(model) => model,
            Err(detail) => {
                tracing::error!(
                    detail = detail.as_str(),
                    "assumption SAT model verification failed after reconstruction"
                );
                self.cold.last_unknown_detail = Some(detail);
                return self.declare_assume_unknown_with_reason(SatUnknownReason::InvalidSatModel);
            }
        };
        #[cfg(debug_assertions)]
        self.debug_assert_sat_result_model(&model, "declare_assume_sat_from_model");
        // #7912: verify the finalized external model against all original clauses.
        debug_assert!(
            self.verify_external_model(&model),
            "BUG: Invalid SAT model — assumption-path model does not satisfy original clauses"
        );
        self.emit_diagnostic_sat_summary(model.len());
        AssumeResult::Sat(model)
    }

    #[inline]
    pub(in crate::solver) fn declare_assume_unknown_with_reason(
        &mut self,
        reason: SatUnknownReason,
    ) -> AssumeResult {
        self.cold.last_unknown_reason = Some(reason);
        self.emit_diagnostic_unknown_summary(reason.diagnostic_label());
        AssumeResult::Unknown
    }

    #[inline]
    pub(in crate::solver) fn declare_assume_sat_from_current_assignment(&mut self) -> AssumeResult {
        self.declare_assume_sat_from_model(self.get_model())
    }

    pub(in crate::solver) fn finalize_assumption_api_result(
        &self,
        result: AssumeResult,
    ) -> AssumeResult {
        match result {
            AssumeResult::Sat(mut sat_model) => {
                #[cfg(debug_assertions)]
                self.debug_assert_sat_result_model(&sat_model, "finalize_assumption_api_result");
                // #7912: verify the full model BEFORE truncation, so clauses
                // containing internal variables beyond user_num_vars are checked
                // correctly. (Other call sites verify before truncation too.)
                debug_assert!(
                    self.verify_external_model(&sat_model),
                    "BUG: Invalid SAT model in finalize_assumption_api_result"
                );
                sat_model.truncate(self.user_num_vars);
                AssumeResult::Sat(sat_model)
            }
            AssumeResult::Unsat(core) => {
                AssumeResult::Unsat(self.filter_scope_selectors_from_core(core))
            }
            AssumeResult::Unknown => AssumeResult::Unknown,
        }
    }

    pub(in crate::solver) fn filter_scope_selectors_from_core(
        &self,
        core: Vec<Literal>,
    ) -> Vec<Literal> {
        core.into_iter()
            .filter(|lit| {
                let idx = lit.variable().index();
                idx >= self.cold.scope_selector_set.len() || !self.cold.scope_selector_set[idx]
            })
            .collect()
    }
}
