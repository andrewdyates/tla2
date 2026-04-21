// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Startup invariant discovery pipeline for the PDR solver.
//!
//! Extracted from `solve()` to improve navigability (#2998, #3301).
//! This module contains the proactive invariant discovery passes that run
//! before the main PDR blocking loop. The pipeline discovers bounds,
//! equalities, sums, differences, parity, affine, relational, and other
//! invariant patterns to seed the frame system.

mod fixpoint;
mod nonfixpoint;

use super::{PdrResult, PdrSolver};
use crate::ChcExpr;

impl PdrSolver {
    /// Native BV direct-route problems should reach the blocking loop before we
    /// try to certify safety from startup-discovered frame[1] lemmas.
    ///
    /// On #5877-style benchmarks, startup discovery can produce frame-relative
    /// BV/Bool lemmas that block the query syntactically but are not a stable
    /// proof. Defer the direct safety shortcut so the main PDR loop can do the
    /// backward-reachability work first.
    fn skip_startup_direct_safety_proof(&self) -> bool {
        self.problem.predicates().len() == 1
            && self.problem.has_bv_sorts()
            && self.problem.transitions().count() == 1
            && !self.uses_arrays
            && !self.problem.has_real_sorts()
            && !self.config.bv_to_int_relaxed
    }

    /// Large native-BV simple loops should skip the full startup discovery
    /// pipeline and go straight to the lighter BV startup path.
    ///
    /// The original #5877 fast-path rationale was driven by very large BV
    /// transitions (thousands of AST nodes, e.g. `bist_cell`). Applying that
    /// same shortcut to every native-BV simple loop also starves small BV
    /// problems of the normal discovery passes that can seed the blocking loop
    /// with useful Boolean/relational lemmas. Keep the broad "no startup direct
    /// safety proof" policy, but only use the heavyweight startup skip when the
    /// extracted transition system is actually large.
    fn use_bv_native_fast_startup_path(&self) -> bool {
        if !self.skip_startup_direct_safety_proof() {
            return false;
        }

        const LARGE_BV_NATIVE_TRANSITION_NODES: usize = 256;

        crate::transition_system::TransitionSystem::from_chc_problem(&self.problem)
            .map(|ts| ts.transition.node_count(10_000) > LARGE_BV_NATIVE_TRANSITION_NODES)
            .unwrap_or(true)
    }

    /// Whether this solve call is a quick soundness check with minimal resource budgets.
    ///
    /// Quick checks skip startup invariant discovery to avoid expensive passes.
    /// This is intentionally keyed off existing budget knobs (frames/iterations/obligations)
    /// to avoid introducing new configuration flags.
    pub(in crate::pdr::solver) fn is_quick_check_mode(&self) -> bool {
        self.config.max_frames <= 2
            && self.config.max_iterations <= 10
            && self.config.max_obligations <= 1_000
    }

    /// Run the startup invariant discovery pipeline and direct safety check.
    ///
    /// This discovers invariants proactively (bounds, equalities, sums, differences,
    /// parity, affine, relational, etc.) before entering the main PDR blocking loop.
    ///
    /// Returns `Some(result)` if the solver should return early:
    /// - `Some(PdrResult::Safe(...))` if discovered invariants prove safety directly
    /// - `Some(PdrResult::Unknown)` if cancelled during discovery
    ///
    /// Returns `None` if discovery completed normally and the main loop should proceed.
    pub(in crate::pdr::solver) fn run_startup_discovery(&mut self) -> Option<PdrResult> {
        // Some startup invariant discovery passes can be very expensive. If the caller
        // provides extremely small resource limits (typically for quick soundness checks),
        // skip the discovery pipeline and rely on the bounded main PDR loop instead.
        if self.is_quick_check_mode() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Skipping startup invariant discovery (max_frames={}, max_iterations={}, max_obligations={})",
                    self.config.max_frames, self.config.max_iterations, self.config.max_obligations
                );
            }
        } else if self.use_bv_native_fast_startup_path() {
            // #5877: BV-native single-predicate problems have transition relations
            // with thousands of BV nodes. Each startup discovery pass requires SMT
            // queries involving BV bit-blasting, which is 10-100x more expensive
            // than the LIA queries the startup pipeline was designed for. On
            // bist_cell (10000-node transition), the fixpoint loop (3 iterations ×
            // 7 passes per iteration) consumes the entire portfolio budget before
            // the main PDR blocking loop even starts.
            //
            // Skip the full startup discovery for BV-native problems and run only
            // the lightweight BV range invariant pass (2s budget) to seed basic
            // frame lemmas. The main PDR blocking loop will discover invariants
            // incrementally via counterexample-guided generalization.
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: BV-native fast startup — skipping full discovery pipeline (#5877)"
                );
            }
            let _startup_smt_timeout_guard = if self.config.cancellation_token.is_some()
                || self.config.solve_timeout.is_some()
            {
                Some(
                    self.smt
                        .scoped_check_timeout(Some(std::time::Duration::from_secs(5))),
                )
            } else {
                None
            };

            // Lane C fix: run lightweight equality discovery before BV range pass.
            // BV-native equality discovery operates on BV-sorted variables
            // (typically 5-20 per predicate), not expanded Bool variables. The
            // equality pass uses O(n^2) SMT checks where n = BV var count,
            // which is tractable. Without these seeds, the blocking loop produces
            // point lemmas that never converge to inductive invariants.
            if !self.is_cancelled() {
                let eq_start = std::time::Instant::now();
                self.discover_equality_invariants();
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: BV-native equality discovery took {:?}",
                        eq_start.elapsed()
                    );
                }
            }

            self.discover_bv_range_invariants();
        } else {
            // Apply a per-query SMT timeout during startup discovery when cooperative
            // cancellation or a solve timeout is in effect. Without this, a single
            // expensive SMT query inside a discovery pass can block indefinitely —
            // the cancellation token is only checked *between* passes, not during
            // individual SMT calls. Use 10s (longer than the 5s main-loop cap)
            // since startup queries are legitimately heavier.
            let _startup_smt_timeout_guard = if self.config.cancellation_token.is_some()
                || self.config.solve_timeout.is_some()
            {
                Some(
                    self.smt
                        .scoped_check_timeout(Some(std::time::Duration::from_secs(10))),
                )
            } else {
                None
            };

            let fixpoint_cancelled = if let Some(result) = self.run_fixpoint_discovery() {
                if !matches!(result, PdrResult::Unknown) {
                    return Some(result);
                }
                // Fixpoint was cancelled (solve_deadline or portfolio). Don't
                // return yet — kernel discovery below has its own 1.5s budget
                // and can find equalities in case-split sub-problems (#5399).
                true
            } else {
                false
            };

            if !fixpoint_cancelled {
                // Normal path: run full nonfixpoint discovery.
                if let Some(result) = self.run_nonfixpoint_discovery() {
                    return Some(result);
                }
            } else {
                // Cancelled path: only run kernel discovery, which has its own
                // internal 1.5s budget. In case-split sub-problems (e.g.,
                // dillig12_m E=1), the kernel can discover relatively-inductive
                // equalities like D=2C that require A=B as a hypothesis (#5399).
                // The fixpoint loop already discovered A=B before timing out.
                //
                // Temporarily extend the solve_deadline so that
                // add_discovered_invariant's internal is_cancelled() checks don't
                // reject valid kernel-discovered equalities. 10s covers Phase A
                // pass 2 adds (can take 6.4s for SCC re-verification of
                // structurally-different-but-semantically-equivalent equalities)
                // plus Phase B transition checks + adds. The kernel's own per-phase
                // 1.5s budget limits the actual useful SMT work.
                let saved_deadline = self.solve_deadline;
                if let Some(ref mut deadline) = self.solve_deadline {
                    // Cap the post-cancel extension to min(solve_timeout, 10s).
                    // Without this, a sub-solver with a 2s budget gets silently
                    // extended to 10s, starving other engines of their budget.
                    let ext = self
                        .config
                        .solve_timeout
                        .map_or(std::time::Duration::from_secs(10), |t| {
                            t.min(std::time::Duration::from_secs(10))
                        });
                    *deadline = std::time::Instant::now() + ext;
                }

                let _t_post = std::time::Instant::now();
                self.discover_affine_invariants_via_kernel(None);
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: post-cancel kernel discovery took {:?}",
                        _t_post.elapsed()
                    );
                }

                // Check safety BEFORE restoring the expired deadline (#5399).
                // check_invariants_prove_safety has an is_cancelled() guard that
                // would return None if the original deadline is restored first.
                if self.skip_startup_direct_safety_proof() {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Skipping post-cancel startup direct safety proof for native \
                             single-predicate BV; defer to blocking loop (#5877)"
                        );
                    }
                } else {
                    let _t15 = std::time::Instant::now();
                    if let Some(mut model) = self.check_invariants_prove_safety() {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: check_invariants_prove_safety took {:?}",
                                _t15.elapsed()
                            );
                            safe_eprintln!(
                                "PDR: Discovered invariants prove safety directly (post-cancel)!"
                            );
                        }
                        // SOUNDNESS (#5922): Fresh-context confirmation.
                        //
                        // When the startup fixpoint converged without conjunct
                        // filtering, the model is convergence_proven: the full
                        // frame conjunction is inductive by construction. In that
                        // case, fresh query-only validation is the right sound
                        // check; requiring a fresh transition proof is an
                        // unnecessary SMT re-check that can fail spuriously on
                        // gj2007-style phase chains.
                        let fresh_ok = if model.convergence_proven {
                            self.verify_model_fresh_query_only(&model)
                        } else {
                            self.verify_model_fresh(&model)
                        };
                        if !fresh_ok {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: startup post-cancel model fails fresh-context \
                                     verification (#5922); continuing"
                                );
                            }
                        } else {
                            // SOUNDNESS (#5922): Save model before simplification.
                            let original_model = model.clone();
                            let simp = self.simplify_model(&mut model);
                            // Re-verify when simplification modified the model (#5805, #5922).
                            if simp.modified() && !self.verify_model(&model) {
                                if simp.free_vars_sanitized {
                                    // Free-var sanitization modified the model and re-verification
                                    // failed. The original model already passed verify_model_fresh
                                    // at line 180. Accept it directly — re-running query-only
                                    // verification would be redundant and can fail due to SMT
                                    // non-determinism on mod/div query clauses (#1362).
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: simplified startup model fails re-verification \
                                             after free-variable sanitization; falling back to \
                                             original model (verify_model_fresh passed) (#1362)"
                                        );
                                    }
                                    self.solve_deadline = saved_deadline;
                                    return Some(self.finish_with_result_trace(PdrResult::Safe(
                                        original_model,
                                    )));
                                } else {
                                    // Only redundancy removal — fall back (#5922).
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: simplified startup model fails re-verification; \
                                             falling back to pre-simplification model"
                                        );
                                    }
                                    self.solve_deadline = saved_deadline;
                                    return Some(self.finish_with_result_trace(PdrResult::Safe(
                                        original_model,
                                    )));
                                }
                            } else {
                                self.solve_deadline = saved_deadline;
                                return Some(self.finish_with_result_trace(PdrResult::Safe(model)));
                            }
                        }
                    }
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: check_invariants_prove_safety took {:?}",
                            _t15.elapsed()
                        );
                    }
                }

                // Restore original deadline.
                self.solve_deadline = saved_deadline;
            }
        }

        if self.skip_startup_direct_safety_proof() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Skipping startup direct safety proof for native single-predicate BV; \
                     defer to blocking loop (#5877)"
                );
            }
            return None;
        }

        // Direct safety check: if discovered invariants prove all error states unreachable,
        // return Safe immediately without going through the iterative PDR loop.
        let _t15 = std::time::Instant::now();
        if let Some(mut model) = self.check_invariants_prove_safety() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety took {:?}",
                    _t15.elapsed()
                );
                safe_eprintln!("PDR: Discovered invariants prove safety directly!");
            }
            // SOUNDNESS (#5922): Fresh-context confirmation.
            // #8782: convergence_proven models were built from a converged fixpoint
            // (frame[k] = frame[k+1]) without conjunct filtering. The full frame
            // conjunction is inductive by the PDR convergence theorem. Full
            // transition verification in a fresh context can fail due to SMT
            // budget exhaustion on complex multi-predicate models where some
            // predicates have vacuously-false frames. Query-only validation
            // confirms the invariant blocks the error (soundness-critical).
            // Matches the pattern in nonfixpoint.rs line 114-118.
            // (#8782): Skip expensive fresh-context verification for
            // individually_inductive models. Each lemma was already proven
            // self-inductive independently of the frame. The portfolio's
            // query-only validation (Step 4.5) provides the soundness gate.
            let fresh_full = if model.individually_inductive {
                true // Skip — already proven at PDR level
            } else if model.convergence_proven {
                self.verify_model_fresh_query_only(&model)
            } else {
                self.verify_model_fresh(&model)
            };
            let fresh_ok = fresh_full || model.individually_inductive;

            // #1362: When verify_model_fresh fails due to SMT incompleteness,
            // fall back to individual lemma verification. If every frame[1]
            // lemma is individually STRICTLY self-inductive (algebraically
            // verified OR SMT-checked WITHOUT frame strengthening), accept the
            // model with the individually_inductive flag (routes to query-only
            // validation at portfolio level).
            //
            // D3 #1362: Uses is_strictly_self_inductive_blocking (no frame
            // context) to match the contract accept.rs expects at lines
            // 168-176. With strict self-inductiveness, the has_algebraic_mod
            // gate is no longer needed — each lemma is verified on its own
            // merits, not relative to other frame lemmas. The D2 frame
            // consistency check remains as defense-in-depth against vacuous
            // inductiveness from contradictory frames.
            // #7469: Hyperedge clauses (>1 body predicate) make per-lemma
            // entry-inductiveness checks unsound — must-summaries/frame
            // constraints for body predicates may be weaker than the actual
            // reachable set. Require full verification for hyperedge problems.
            // Mirror: safety_checks.rs:57-62.
            let has_hyperedge = self
                .problem
                .clauses()
                .iter()
                .any(|c| c.body.predicates.len() > 1);
            let individually_verified = !fresh_ok && self.frames.len() > 1 && !has_hyperedge && {
                // D2 #1362: Check frame[1] consistency before
                // individually_verified bypass. Contradictory frame lemmas
                // can make inductiveness checks vacuously true.
                // Mirror: safety_proof.rs:535-580.
                let frame_has_contradiction = {
                    let mut found = false;
                    let mut checked_preds = rustc_hash::FxHashSet::default();
                    for lemma in &self.frames[1].lemmas {
                        if !checked_preds.insert(lemma.predicate) {
                            continue;
                        }
                        let pred_lemmas: Vec<ChcExpr> = self.frames[1]
                            .lemmas
                            .iter()
                            .filter(|l| l.predicate == lemma.predicate)
                            .map(|l| l.formula.clone())
                            .collect();
                        if pred_lemmas.len() >= 2 {
                            let conjunction = ChcExpr::and_all(pred_lemmas);
                            let bounded = self.bound_int_vars(conjunction);
                            self.smt.reset();
                            let result = self.smt.check_sat_with_timeout(
                                &bounded,
                                std::time::Duration::from_millis(200),
                            );
                            if result.is_unsat() {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: individually_verified skipped: \
                                             frame[1] pred {} has contradictory \
                                             lemmas (#1362 D2)",
                                        lemma.predicate.index()
                                    );
                                }
                                found = true;
                                break;
                            }
                        }
                    }
                    found
                };
                if frame_has_contradiction {
                    false
                } else {
                    let lemmas: Vec<_> = self.frames[1]
                        .lemmas
                        .iter()
                        .map(|l| (l.predicate, l.formula.clone(), l.algebraically_verified))
                        .collect();
                    let is_multi_pred = self.problem.predicates().len() > 1;
                    lemmas.iter().all(|(pred, formula, alg_verified)| {
                        if *alg_verified {
                            // Algebraically verified lemmas are sound per-predicate.
                            // For multi-pred, also verify entry-inductiveness to
                            // cover cross-predicate transitions.
                            return !is_multi_pred || self.is_entry_inductive(formula, *pred, 1);
                        }
                        // D3 #1362: Strict self-inductiveness WITHOUT frame
                        // strengthening. Each lemma must be self-inductive on
                        // its own, matching the contract accept.rs expects.
                        let blocking = ChcExpr::not(formula.clone());
                        let self_ind = self.is_strictly_self_inductive_blocking(&blocking, *pred);
                        if !self_ind {
                            return false;
                        }
                        // For multi-pred: also require entry-inductiveness to
                        // cover cross-predicate transitions (P1→P0).
                        !is_multi_pred || self.is_entry_inductive(formula, *pred, 1)
                    })
                }
            };

            // NOTE: A query_only_verified fallback was here (#1362) but was
            // UNSOUND — same root cause as safety_checks.rs query-only bypass.
            // Query-only checks only verify the invariant blocks the error;
            // they do not verify inductiveness. Removed for soundness.

            if !fresh_ok && !individually_verified {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: startup-direct model fails fresh-context \
                         verification (#5922); continuing"
                    );
                }
            } else {
                if !fresh_ok && self.config.verbose {
                    safe_eprintln!(
                        "PDR: startup-direct model fails verify_model_fresh but all \
                         {} lemmas individually verified (#1362); accepting",
                        self.frames[1].lemmas.len()
                    );
                }
                // #7410: Propagate individually_verified to the model so
                // portfolio accept.rs can use query-only validation instead
                // of full fresh-context validation (which fails on mod/div).
                if individually_verified {
                    model.individually_inductive = true;
                }
                // SOUNDNESS (#5922): Save model before simplification.
                let original_model = model.clone();
                // Simplify the invariant (Z3 Spacer's unconditional solve-completion cleanup).
                // Portfolio always runs full verification (#5745).
                let simp = self.simplify_model(&mut model);
                // Re-verify when simplification modified the model (#5805, #5922).
                // (#8782): Skip re-verification for individually_inductive models.
                // Each lemma was already proven self-inductive independently.
                let reverify_needed =
                    simp.modified() && !model.individually_inductive && !individually_verified;
                if reverify_needed && !self.verify_model(&model) {
                    if individually_verified {
                        // #1362: When individually_verified, simplification may
                        // invalidate the model (e.g., free-var sanitization on
                        // parametric init like 2*A). Fall back to original model.
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: simplified startup-direct model fails re-verification; \
                                 falling back to individually-verified original model (#1362)"
                            );
                        }
                        return Some(
                            self.finish_with_result_trace(PdrResult::Safe(original_model)),
                        );
                    } else if simp.free_vars_sanitized {
                        // Free-var sanitization modified the model and re-verification
                        // failed. The original model already passed fresh verification
                        // (fresh_ok was true at line 275). Accept it directly — re-running
                        // verify_model_fresh_query_only here is redundant and can fail
                        // due to SMT non-determinism on mod/div query clauses (e.g.,
                        // phases_m clause 4 has `mod C 2`). (#1362)
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: simplified startup-direct model fails re-verification \
                                 after free-variable sanitization; falling back to original \
                                 model (fresh_ok already confirmed) (#1362)"
                            );
                        }
                        return Some(
                            self.finish_with_result_trace(PdrResult::Safe(original_model)),
                        );
                    } else {
                        // Only redundancy removal — fall back (#5922).
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: simplified startup-direct model fails re-verification; \
                                 falling back to pre-simplification model"
                            );
                        }
                        return Some(
                            self.finish_with_result_trace(PdrResult::Safe(original_model)),
                        );
                    }
                } else {
                    return Some(self.finish_with_result_trace(PdrResult::Safe(model)));
                }
            }
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: check_invariants_prove_safety took {:?}",
                _t15.elapsed()
            );
        }

        None
    }
}

#[cfg(test)]
mod tests;
