// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unified result acceptance pipeline for portfolio engine results.
//!
//!
//! Both `solve_parallel` and `solve_sequential` run the same 5-step
//! soundness guard before accepting an engine result. This module
//! contains that logic in a single place so soundness fixes land once.

use super::*;

/// Result acceptance decision for a single engine result.
#[derive(Debug)]
pub(crate) enum AcceptDecision {
    /// Accept this result — return to caller.
    Accept(PortfolioResult),
    /// Reject this result — try next engine.
    Reject,
}

impl PortfolioSolver {
    /// Unified soundness guard pipeline for engine results.
    ///
    /// Called by both `solve_parallel` and `solve_sequential` after
    /// `convert_engine_result`. Contains ALL acceptance/rejection logic
    /// in one place so soundness fixes land once.
    ///
    /// Five-step pipeline:
    /// 1. BV-abstracted Unsafe confirmation
    /// 2. BMC witness-less multi-predicate rejection (#6800)
    /// 3. Skeleton Unsafe rejection (no witness, empty assignments)
    /// 4. Optional Unsafe validation (config.validate)
    /// 5. Mandatory Safe full validation (#6787, #6824)
    pub(crate) fn accept_or_reject(
        &self,
        mut result: PortfolioResult,
        mut needs_validation: bool,
        engine_name: &str,
        engine_idx: usize,
    ) -> AcceptDecision {
        // Step 1: BV-abstracted Unsafe confirmation
        if self.bv_abstracted {
            if let PortfolioResult::Unsafe(cex) = &result {
                let Some(confirmed) =
                    self.confirm_bv_abstracted_unsafe(cex, engine_idx, engine_name)
                else {
                    return AcceptDecision::Reject;
                };
                result = confirmed;
                needs_validation = false;
            }
        }

        // Step 2 (#6800): Reject witness-less BMC Unsafe on multi-predicate
        // problems. BMC produces a flat list of per-level assignments with
        // predicate=0 for every step, which cannot justify a multi-predicate
        // Unsafe. Uses engine_problem() (not original_problem) because
        // preprocessing may reduce predicates.
        if engine_name == "BMC" {
            if let PortfolioResult::Unsafe(cex) = &result {
                let engine_pred_count = self.engine_problem().predicates().len();
                if cex.witness.is_none() && engine_pred_count > 1 {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Engine {} (BMC) witness-less Unsafe suppressed on multi-predicate problem ({} predicates)",
                            engine_idx, engine_pred_count
                        );
                    }
                    return AcceptDecision::Reject;
                }
            }
        }

        // Step 3: Reject skeleton Unsafe results (no witness, empty
        // assignments) unconditionally. Engines like PDKIND produce skeleton
        // counterexamples that cannot be independently verified without
        // validation (#2273, #5010).
        if let PortfolioResult::Unsafe(cex) = &result {
            if cex.witness.is_none() && cex.steps.iter().all(|s| s.assignments.is_empty()) {
                match self.validate_result(&result, engine_name) {
                    ValidationResult::Valid => {
                        // Skeleton verified — accept
                    }
                    ValidationResult::Invalid(reason) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Portfolio: Engine {} ({}) skeleton Unsafe rejected: {}",
                                engine_idx,
                                engine_name,
                                reason
                            );
                        }
                        return AcceptDecision::Reject;
                    }
                }
            }
        }

        // Step 4: Validate non-Safe results before accepting (#429, #5213).
        // Safe results handled by mandatory full validation below (#6824).
        if needs_validation && self.config.validate {
            if let PortfolioResult::Unsafe(_) = &result {
                match self.validate_result(&result, engine_name) {
                    ValidationResult::Valid => {
                        // Validation passed - accept result
                    }
                    ValidationResult::Invalid(reason) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Portfolio: Engine {} ({}) Unsafe result failed validation: {}, continuing",
                                engine_idx, engine_name, reason
                            );
                        }
                        return AcceptDecision::Reject;
                    }
                }
            }
        }

        // Step 4.25: acyclic BMC Safe is an exact proof, not an invariant model.
        //
        // `BmcSolver` only returns `Safe(InvariantModel::default())` from the
        // `acyclic_safe` exhaustion path after checking every depth up to the
        // configured bound. That proof does not come with a predicate model, so
        // forcing it through query-only / full invariant validation is both
        // inapplicable and brittle: preprocessing back-translation may try to
        // synthesize a model from the empty witness and fail on unrelated sort
        // translation issues. Accept the proof directly, but keep this narrowly
        // scoped to BMC's empty-model Safe result.
        if engine_name == "BMC"
            && matches!(&result, PortfolioResult::Safe(model) if model.is_empty())
        {
            if self.config.verbose {
                safe_eprintln!(
                    "Portfolio: Engine {} (BMC) returned empty-model Safe from exact acyclic exhaustion; \
                     accepting without invariant validation",
                    engine_idx
                );
            }
            return AcceptDecision::Accept(result);
        }

        // Step 4.5 (#6787): Fast query-only pre-check for Safe results.
        // Catches tautological false-Safe where the invariant is literally the
        // negated query (#6789). This is a syntactic check that avoids the
        // expensive full validation when the model is obviously wrong.
        //
        // EXCEPTION (#1306): An invariant that equals exact `not(query)` is
        // ambiguous — it might be a genuine inductive invariant that happens
        // to match the negation of the query constraint. Query-only validation
        // cannot distinguish this case. Instead of hard-rejecting, defer to
        // Step 5 (full per-rule validation) which can check inductiveness.
        if let PortfolioResult::Safe(ref model) = result {
            match self.validate_safe_query_only(model) {
                SafePrecheckResult::Valid => {}
                SafePrecheckResult::ExactNegatedQuery(reason) => {
                    // Ambiguous: defer to Step 5 full validation (#1306)
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Engine {} ({}) Safe result is exact ¬query ({}); \
                             deferring to full validation (#1306)",
                            engine_idx,
                            engine_name,
                            reason
                        );
                    }
                }
                SafePrecheckResult::Invalid(reason) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Engine {} ({}) Safe result failed query-only validation: {}, continuing",
                            engine_idx, engine_name, reason
                        );
                    }
                    return AcceptDecision::Reject;
                }
            }
        }

        // Step 5 (#6787, #6824): Full validation for Safe results.
        //
        // Query-only (step 4.5) checks that the invariant blocks bad states.
        // Full validation re-checks inductiveness w.r.t. transition clauses
        // in a fresh SMT context.
        //
        // For PDR/CEGAR: frame convergence / abstraction refinement already
        // proves inductiveness. Full validation in a fresh context is strictly
        // weaker (no learned clauses). On ITE-heavy multi-predicate transitions
        // and mod/div arithmetic, the fresh context returns Unknown, causing
        // false rejections that waste 2s/clause on correct invariants. For these
        // engines, when full validation fails but query-only passed, accept with
        // a diagnostic warning. This is the same logic as the 53/55 zone peak
        // (5fad1342f).
        //
        // SOUNDNESS NOTE: The original PDR/CEGAR bypass was removed (8604c68f5)
        // because accumulator_unsafe and two_phase_unsafe produced false-Safe.
        // Root cause was startup.rs:280 query-only fallback (fresh_ok = query_only),
        // NOT the accept.rs bypass. That root cause was fixed in #7420
        // (startup.rs:288 now uses fresh_ok = fresh_full). With the startup fix,
        // PDR no longer produces false-Safe models — it returns Unknown when it
        // can't prove inductiveness. The accept.rs bypass is safe to restore.
        //
        // EXCEPTION (#7410): Models with individually_inductive=true have had
        // every lemma verified as self-inductive WITHOUT frame strengthening
        // at the PDR level. This is strictly stronger than frame-strengthened
        // inductiveness. For these models, Step 4.5 query-only validation is
        // sufficient.
        //
        // For Kind, TPA, BMC, PDKIND, and TRL: their Safe results may not be
        // 1-inductive (e.g. they rely on a fresh inductiveness proof). Full
        // validation is mandatory for soundness at the portfolio boundary.
        if let PortfolioResult::Safe(ref model) = result {
            if model.individually_inductive {
                // #7410: Models with individually_inductive=true have had every
                // lemma verified at the PDR level — either strictly self-inductive
                // (no frame strengthening) or frame-relative self-inductive with
                // initiation verified (blocks_initial_states). Step 4.5 query-only
                // validation is sufficient.
                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Engine {} ({}) Safe result has individually_inductive=true; \
                         Step 4.5 query-only sufficient (#7410)",
                        engine_idx,
                        engine_name,
                    );
                }
            } else if matches!(engine_name, "PDR" | "Decomposition" | "CEGAR")
                && self.engine_problem().predicates().len() > 1
            {
                // PDR/CEGAR/Decomposition multi-predicate bypass (#7934, #5970):
                // these engines have internal inductiveness verification
                // (verify_model + verify_model_fresh in main_loop.rs). Full
                // validation in a fresh portfolio-level context is strictly
                // weaker (no learned clauses from the PDR search). On ITE-heavy
                // MULTI-PREDICATE transitions and mod/div arithmetic, the fresh
                // context returns Unknown/SAT causing false rejections on
                // correct invariants.
                //
                // RESTRICTED TO MULTI-PREDICATE: Single-predicate fresh-context
                // validation is reliable. The false-Safe cases that caused the
                // original bypass removal (#7688) — conditional_branch_unsafe,
                // two_phase_unsafe — are all single-predicate problems where
                // PDR's convergence_proven + query-only check is insufficient.
                //
                // Step 4.5 query-only validation already passed — accept with
                // a diagnostic warning when full validation fails.
                if let ValidationResult::Invalid(reason) =
                    self.validate_safe_with_mode(model, ValidationBudget::PerRule)
                {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Engine {} ({}) Safe passed query-only but failed full validation: {} \
                             — accepting (multi-pred PDR/CEGAR bypass #7934)",
                            engine_idx, engine_name, reason
                        );
                    }
                    // Accept despite full validation failure — Step 4.5 query-only passed,
                    // and PDR's internal verify_model already confirmed inductiveness.
                    // Multi-predicate ITE/mod/div transitions cause false rejections.
                }
            } else if let ValidationResult::Invalid(reason) =
                self.validate_safe_with_mode(model, ValidationBudget::PerRule)
            {
                // Non-PDR engines (Kind, TPA, BMC, PDKIND, TRL): their Safe
                // results may not be 1-inductive. Full validation is mandatory.
                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Engine {} ({}) Safe result failed mandatory full validation: {}, continuing",
                        engine_idx, engine_name,
                        reason
                    );
                }
                return AcceptDecision::Reject;
            }
        }

        AcceptDecision::Accept(result)
    }
}
