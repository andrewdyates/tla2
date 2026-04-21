// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unified BV solve pipeline (eager bit-blasting) for all BV logics (#6691).
//!
//! All BV logic variants (QF_BV, QF_ABV, QF_UFBV, QF_AUFBV) and modes
//! (single-shot, incremental push/pop) enter through `solve_bv_core_inner`.
//! The `BvSolveConfig` parameterizes features (preprocessing, array axioms,
//! UF congruence, incremental state management) so the pipeline phases are
//! written once. Shared helpers (`propagate_bv_unknown_reason`,
//! `finalize_bv_unsat`, `finalize_bv_unknown`, `save_bv_unsat_proof_state`)
//! are used by both the fresh and persistent code paths.
//!
//! Model extraction lives in `bv_model.rs`, axiom generation in
//! `bv_axioms_array.rs` and `bv_axioms_euf.rs`.
//! Configuration in `bv_config.rs`.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;

use z4_bv::BvSolver;
use z4_core::term::TermData;
use z4_core::{Sort, TermId, Tseitin};
use z4_sat::{
    AssumeResult, ClauseTrace, Literal as SatLiteral, SatResult, Solver as SatSolver,
    Variable as SatVariable,
};

use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::preprocess::Preprocessor;

use super::super::Executor;
use super::bv_encoding;
use super::{debug_ite_conditions_enabled, debug_preprocessed_enabled};

// Re-export so existing `use super::bv::BvSolveConfig` paths continue to work.
pub(in crate::executor) use super::bv_config::BvSolveConfig;

impl Executor {
    // Model extraction (extract_bv_model_from_bits) is in bv_model.rs.
    // Array axiom generation is in bv_axioms_array.rs.
    // EUF congruence axiom generation is in bv_axioms_euf.rs.

    /// Solve using Bitvector theory (eager bit-blasting).
    /// Dispatcher for QF_BV — delegates to `solve_bv_core` with QF_BV config.
    /// In incremental mode (push/pop), uses `qf_bv_incremental` config which
    /// activates persistent SAT solver and cached Tseitin/BV state.
    pub(in crate::executor) fn solve_bv(&mut self) -> Result<SolveResult> {
        if self.incremental_mode {
            return self.solve_bv_core(BvSolveConfig::qf_bv_incremental(), &[]);
        }
        self.solve_bv_core(BvSolveConfig::qf_bv(), &[])
    }

    /// Solve QF_ABV (Arrays + Bitvectors) using eager bit-blasting with array axioms
    pub(in crate::executor) fn solve_abv(&mut self) -> Result<SolveResult> {
        if self.incremental_mode {
            return self.solve_bv_core(BvSolveConfig::qf_abv_incremental(), &[]);
        }
        self.solve_bv_core(BvSolveConfig::qf_abv(), &[])
    }

    /// Solve QF_UFBV (UF + Bitvectors) using eager bit-blasting with UF congruence
    pub(in crate::executor) fn solve_ufbv(&mut self) -> Result<SolveResult> {
        if self.incremental_mode {
            return self.solve_bv_core(BvSolveConfig::qf_ufbv_incremental(), &[]);
        }
        self.solve_bv_core(BvSolveConfig::qf_ufbv(), &[])
    }

    /// Solve QF_AUFBV (Arrays + UF + Bitvectors) using eager bit-blasting
    /// with array and EUF congruence axioms
    pub(in crate::executor) fn solve_aufbv(&mut self) -> Result<SolveResult> {
        if self.incremental_mode {
            return self.solve_bv_core(BvSolveConfig::qf_aufbv_incremental(), &[]);
        }
        self.solve_bv_core(BvSolveConfig::qf_aufbv(), &[])
    }

    /// Shared BV solve pipeline. ALL BV logic variants route through this
    /// function: QF_BV, QF_ABV, QF_UFBV, QF_AUFBV (non-incremental), and
    /// QF_BV incremental (push/pop). Configuration via `BvSolveConfig`.
    pub(in crate::executor) fn solve_bv_core(
        &mut self,
        config: BvSolveConfig,
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        self.solve_bv_core_inner(config, assumptions, &[])
    }

    /// BV solve pipeline with extra root terms for assumption-aware array
    /// axiom generation (#6736). In incremental mode, assumption terms are
    /// not in `self.ctx.assertions` and would be excluded from the reachable
    /// set that scopes axiom generation. This variant includes
    /// `assumption_roots` so array operations appearing only in assumptions
    /// get proper axioms.
    pub(in crate::executor) fn solve_bv_core_with_assumption_roots(
        &mut self,
        config: BvSolveConfig,
        assumptions: &[TermId],
        assumption_roots: &[TermId],
    ) -> Result<SolveResult> {
        self.solve_bv_core_inner(config, assumptions, assumption_roots)
    }

    fn solve_bv_core_inner(
        &mut self,
        config: BvSolveConfig,
        assumptions: &[TermId],
        assumption_roots: &[TermId],
    ) -> Result<SolveResult> {
        // Early exit if already timed out or interrupted (#3070).
        // Without this, the entire encoding pipeline (Tseitin, bitblasting,
        // axiom generation) runs to completion even when the deadline has
        // already passed, causing certus to hang on wide BV queries.
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        // --- Phase 0a: BV1 bvand flattening ---
        // Flatten `(= #b1 (bvand t1 t2 ...))` into separate assertions.
        // The try3/try5 QF_ABV benchmarks encode their entire formula as a
        // single assertion with a giant bvand tree at BV1 width. Flattening
        // exposes individual constraints (including store equalities) for
        // the array axiom fixpoint and store-flat substitution to operate on.
        if config.array_axioms {
            self.flatten_bv1_bvand_assertions();
        }

        // --- Phase 0b: Array axiom fixpoint (if enabled) ---
        // Must run before Tseitin because it adds new assertion-level terms.
        if config.array_axioms {
            // Ensure negation terms exist for array equalities inside ITE
            // conditions. Without this, `add_array_extensionality_axioms` skips
            // array equalities used only as ITE conditions (no standalone
            // negation), leaving them unconstrained and causing unknown/wrong-SAT
            // on QF_ABV benchmarks with `(ite (= array1 array2) ...)` patterns.
            self.ensure_array_eq_ite_negations();
            self.add_array_extensionality_axioms();

            // Adaptive fixpoint gate: skip the array axiom fixpoint on formulas
            // with many selects. The fixpoint loop creates new selects via
            // congruence axioms, compounding the O(N^2) FC explosion. For
            // formulas with >40 initial selects, the expand_select_store pass
            // and ROW axioms in generate_array_bv_axioms provide sufficient
            // array reasoning without the fixpoint.
            let total_selects = self.count_array_selects_in_assertions();
            if total_selects <= 40 {
                if assumption_roots.is_empty() {
                    self.run_array_axiom_fixpoint_5();
                } else {
                    self.run_array_axiom_fixpoint_5_with_roots(assumption_roots);
                }
            }

            // Expand select(store(a, I, v), J) into ITE chains. This converts
            // remaining select-over-store patterns into boolean structure that
            // Tseitin + BV bitblasting encode directly, avoiding expensive
            // bit-level ROW axiom generation in generate_array_bv_axioms.
            // Concrete-distinct indices skip through without generating ITEs.
            // Z3 ref: array_rewriter.cpp:354-381.
            self.ctx.assertions = self.ctx.terms.expand_select_store_all(&self.ctx.assertions);
        }

        // --- Phase 1: Proof setup ---
        let proof_enabled = self.produce_proofs_enabled();
        if proof_enabled {
            self.proof_tracker.set_theory(config.theory_tag);
            for (idx, &assertion) in self.ctx.assertions.iter().enumerate() {
                let _ = self
                    .proof_tracker
                    .add_assumption(assertion, Some(format!("h{idx}")));
            }
        }

        // --- Incremental path: persistent SAT solver with push/pop scoping ---
        // When config.incremental is true, uses IncrementalBvState for cached
        // Tseitin/BvSolver/SatSolver state management. This path only encodes NEW
        // assertions incrementally and adds definitional clauses globally.
        if config.incremental {
            return self.solve_bv_incremental_inner(&config, proof_enabled);
        }

        // Interrupt check after array axiom fixpoint and proof setup (#3070).
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        // --- Phase 2: Optional preprocessing (QF_BV only) ---
        // Work on a local copy to preserve original assertions for incremental
        // mode, model verification, and proof production.
        //
        // Preprocessing MUST be disabled when assumptions are present (#5581):
        // VariableSubstitution and PropagateValues can eliminate the relationship
        // between assumption terms and the formula. For example, `(= p (= x #x00))`
        // with `(= x #xFF)` can be simplified away, disconnecting the assumption
        // literal `p` from the BV encoding. The Tseitin variable for `p` then has
        // no clauses connecting it to the rest of the formula, allowing the SAT
        // solver to assign it freely and produce a wrong-SAT result.
        let var_subst = if config.preprocess && assumptions.is_empty() {
            let mut preprocessed = self.ctx.assertions.clone();
            let (mut preprocessor, var_subst) = Preprocessor::new_with_subst();
            preprocessor.preprocess(&mut self.ctx.terms, &mut preprocessed);
            if debug_preprocessed_enabled() {
                safe_eprintln!(
                    "[preprocess] assertions after preprocessing: {}",
                    preprocessed.len()
                );
                for (idx, &assertion) in preprocessed.iter().enumerate() {
                    safe_eprintln!("[preprocess] {}: {}", idx, self.format_term(assertion));
                }
            }
            if debug_ite_conditions_enabled() {
                use std::collections::HashMap;
                let mut cond_terms: HashMap<String, Vec<(usize, TermId)>> = HashMap::new();
                for (idx, &assertion) in preprocessed.iter().enumerate() {
                    if let TermData::Ite(cond, _, _) = self.ctx.terms.get(assertion) {
                        let cond = *cond;
                        let cond_str = self.format_term(cond);
                        cond_terms.entry(cond_str).or_default().push((idx, cond));
                    }
                }
                for (cond_str, occurrences) in &cond_terms {
                    let ids: Vec<_> = occurrences.iter().map(|(_, id)| id.index()).collect();
                    let same = occurrences.iter().all(|(_, id)| *id == occurrences[0].1);
                    safe_eprintln!(
                        "[ite-cond] '{}': TermIds {:?}, unified={}",
                        cond_str,
                        ids,
                        same
                    );
                }
            }
            // Swap assertions with preprocessed version for Tseitin/bitblast.
            // Original assertions are preserved in `saved_assertions` and restored
            // at the end of the function for incremental mode, model verification,
            // and proof production.
            std::mem::swap(&mut self.ctx.assertions, &mut preprocessed);
            Some((var_subst, preprocessed))
        } else {
            None
        };

        // --- Phase 3: Tseitin transformation (incremental API) ---
        // Use incremental Tseitin so we can encode assumptions without asserting
        // them as unit clauses. This ensures assumption terms (e.g., UF applications
        // in `distinct(f(x), f(y))`) get Tseitin variables assigned and are visible
        // to downstream axiom generation (EUF congruence, array axioms).
        let mut tseitin = Tseitin::new(&self.ctx.terms);
        for &assertion in &self.ctx.assertions {
            tseitin.assert_term(assertion);
        }

        // --- Phase 3b: Assumption handling ---
        // Encode assumption terms via Tseitin (without adding unit clauses) so they
        // get CNF variables. This fixes #5535: assumption terms not in assertions
        // were silently dropped because they had no Tseitin encoding.
        let has_assumptions = !assumptions.is_empty();
        let (sat_assumptions, assumption_to_term): (Vec<SatLiteral>, Vec<(SatLiteral, TermId)>) =
            if has_assumptions {
                let mut sat_assumps = Vec::new();
                let mut map = Vec::new();
                for &assumption in assumptions {
                    let (base_term, positive) = match self.ctx.terms.get(assumption) {
                        TermData::Not(inner) => (*inner, false),
                        _ => (assumption, true),
                    };
                    // Encode the base term to get/create its CNF variable
                    let cnf_lit = tseitin.encode(base_term, true);
                    let sat_var = SatVariable::new(cnf_lit.unsigned_abs() - 1);
                    let sat_lit = if (cnf_lit > 0) == positive {
                        SatLiteral::positive(sat_var)
                    } else {
                        SatLiteral::negative(sat_var)
                    };
                    sat_assumps.push(sat_lit);
                    map.push((sat_lit, assumption));
                }
                (sat_assumps, map)
            } else {
                (Vec::new(), Vec::new())
            };

        // Build TseitinResult from incremental state
        let tseitin_result = z4_core::TseitinResult::new(
            tseitin.all_clauses().to_vec(),
            tseitin.term_to_var().clone(),
            tseitin.var_to_term().clone(),
            0, // Not used when clauses are added individually
            tseitin.num_vars(),
        );

        debug_assert!(
            self.ctx.assertions.is_empty() || !tseitin_result.clauses.is_empty(),
            "BUG: Tseitin produced 0 clauses from {} assertions in {}",
            self.ctx.assertions.len(),
            config.theory_tag
        );

        // Interrupt check before bitblasting (#3070). Wide BV multipliers
        // (64-bit) generate ~128K gates; bail out before that work if timed out.
        if self.should_abort_theory_loop() {
            if let Some((_, original)) = var_subst {
                self.ctx.assertions = original;
            }
            return Ok(SolveResult::Unknown);
        }

        // --- Phase 4: Bitblasting ---
        // Enable delayed internalization for non-incremental, non-assumption paths (#7015).
        // For expensive operations (mul/div/rem on wide BV with 2+ variable args),
        // the BvSolver allocates fresh unconstrained bits instead of building circuits.
        // After SAT solving, we check these against the model and add conflict clauses.
        // Disable delayed internalization for combined theories (array_axioms/uf_congruence)
        // until the interaction with array/UF axiom generation is verified sound.
        // Regression: QF_ABV false-UNSAT on formulas with two bvmul-computed addresses.
        let use_delayed = !config.incremental
            && assumptions.is_empty()
            && !proof_enabled
            && !config.array_axioms
            && !config.uf_congruence;
        let mut bv_solver = BvSolver::new(&self.ctx.terms);
        if use_delayed {
            bv_solver.set_delay_enabled(true);
        }
        let bv_clauses = bv_solver.bitblast_all(&self.ctx.assertions);

        if self.debug_ufbv && config.uf_congruence {
            safe_eprintln!("DEBUG: Tseitin num_vars = {}", tseitin_result.num_vars);
            safe_eprintln!(
                "DEBUG: BV num_vars (before linking) = {}",
                bv_solver.num_vars()
            );
            safe_eprintln!("DEBUG: Tseitin clauses = {}", tseitin_result.clauses.len());
            safe_eprintln!(
                "DEBUG: BV clauses (before offset) = {}",
                bv_solver.clauses().len()
            );
            for (term_id, bits) in bv_solver.iter_term_bits() {
                safe_eprintln!("DEBUG: Term {:?} has bits {:?}", term_id, bits);
            }
        }

        // --- Phase 5: Combine Tseitin + BV clauses ---
        let mut all_clauses = tseitin_result.clauses.clone();
        let var_offset = tseitin_result.num_vars as i32;
        bv_encoding::offset_and_push_clauses(bv_clauses, var_offset, &mut all_clauses);

        // Materialize BV bits for array terms (ABV/AUFBV only)
        if config.array_axioms {
            self.materialize_array_bv_terms(&mut bv_solver, assumption_roots);
            let extra = bv_solver.take_clauses();
            bv_encoding::offset_and_push_clauses(extra, var_offset, &mut all_clauses);
        }

        // --- Phases 6-7: Predicate + Bool linking (#858, #5457) ---
        let mut linking_batch = bv_encoding::build_linking_batch(
            &tseitin_result.var_to_term,
            &mut bv_solver,
            var_offset,
            &self.ctx.terms,
            None,
        );
        linking_batch.push_equivalence_clauses(&mut all_clauses);
        let extra_bv_clauses = linking_batch.take_extra_bv_clauses();
        bv_encoding::offset_and_push_clauses(extra_bv_clauses, var_offset, &mut all_clauses);

        // --- Phase 8: BV equality congruence axioms (#1708, QF_BV only) ---
        if config.bv_eq_congruence {
            all_clauses.extend(bv_encoding::generate_bv_eq_congruence_clauses(
                &self.ctx.terms,
                &self.ctx.assertions,
                &bv_solver,
                var_offset,
            ));
        }

        // --- Phase 9: Theory-specific axiom generation ---

        // Materialize BV bits for UF application arguments (#5475).
        // Complex BV sub-expressions (e.g., bvadd(x, #x01)) inside UF calls
        // are opaque to the BV bitblaster and need explicit materialization
        // before congruence axiom generation.
        if config.uf_congruence {
            self.materialize_uf_arg_bv_terms(&mut bv_solver, assumptions);
            let extra = bv_solver.take_clauses();
            bv_encoding::offset_and_push_clauses(extra, var_offset, &mut all_clauses);
        }

        let bv_num_vars = bv_solver.num_vars();
        let mut running_offset = tseitin_result.num_vars + bv_num_vars;

        // Array axiom clauses (ABV/AUFBV)
        let _array_axiom_vars = if config.array_axioms {
            let array_axiom_result = self.generate_array_bv_axioms(
                &bv_solver,
                tseitin_result.num_vars,
                running_offset,
                assumption_roots,
            );
            for clause in array_axiom_result.clauses {
                all_clauses.push(clause);
            }
            running_offset += array_axiom_result.num_vars;
            array_axiom_result.num_vars
        } else {
            0
        };

        // EUF congruence axiom clauses (UFBV/AUFBV)
        let _euf_axiom_vars = if config.uf_congruence {
            let euf_axiom_result = self.generate_euf_bv_axioms_debug(
                &bv_solver,
                tseitin_result.num_vars,
                running_offset,
                self.debug_ufbv,
                assumptions,
            );
            if self.debug_ufbv {
                safe_eprintln!("DEBUG: EUF axiom num_vars = {}", euf_axiom_result.num_vars);
                safe_eprintln!(
                    "DEBUG: EUF axiom clauses = {}",
                    euf_axiom_result.clauses.len()
                );
            }
            for clause in euf_axiom_result.clauses {
                all_clauses.push(clause);
            }
            running_offset += euf_axiom_result.num_vars;
            euf_axiom_result.num_vars
        } else {
            0
        };

        // Clone term_bits for model extraction (needed after bv_solver is consumed).
        let term_bits = bv_solver.term_to_bits().clone();
        // Alias for assumption path which references term_bits_snapshot
        let term_bits_snapshot = &term_bits;
        // Extract delayed state before dropping bv_solver (#7015).
        let mut delayed_state = bv_solver.take_delayed_state();
        // Save division caches and next_var for Phase 2 circuit building.
        // CRITICAL: Store num_vars() + 1, NOT num_vars(). num_vars() = next_var - 1,
        // so the last allocated variable IS num_vars(). Starting tmp_bv from num_vars()
        // would reuse that variable, causing variable collisions in the circuit.
        let mut delay_div_caches = if delayed_state.is_some() {
            Some((
                bv_solver.div_caches().0.clone(),
                bv_solver.div_caches().1.clone(),
                bv_solver.num_vars() + 1,
            ))
        } else {
            None
        };
        let has_delayed_ops = delayed_state.is_some();
        drop(bv_solver);

        // Non-BV-return UF congruence (#5433)
        if config.non_bv_congruence {
            let non_bv_congruence_vars = self.generate_non_bv_euf_congruence(
                &term_bits,
                &tseitin_result,
                running_offset,
                &mut all_clauses,
                assumptions,
            );
            running_offset += non_bv_congruence_vars;
        }

        let total_vars = running_offset;

        if self.debug_ufbv && config.uf_congruence {
            safe_eprintln!("DEBUG: Total vars = {}", total_vars);
            safe_eprintln!("DEBUG: Total clauses = {}", all_clauses.len());
            safe_eprintln!(
                "DEBUG: tseitin_num_vars={} bv_num_vars={} var_offset={}",
                tseitin_result.num_vars,
                bv_num_vars,
                var_offset
            );
        }

        // Interrupt check after all encoding phases, before SAT solve (#3070).
        if self.should_abort_theory_loop() {
            if let Some((_, original)) = var_subst {
                self.ctx.assertions = original;
            }
            return Ok(SolveResult::Unknown);
        }

        // --- Phase 10: SAT solving ---
        let mut solver = SatSolver::new(total_vars as usize);
        self.apply_random_seed_to_sat(&mut solver);
        self.apply_progress_to_sat(&mut solver);
        solver.set_congruence_enabled(false);
        // Disable GBCE (conditioning) for all BV solving paths (#5535, #6248).
        // Under assumptions: eliminated clauses may be needed to derive UNSAT.
        // Without assumptions: the bit-blasted clause structure can violate
        // conditioning's root-satisfied invariant, causing a debug panic in
        // the CONDITIONING phase when the solver runs as a CHC sub-solver.
        // BV instances are one-shot (fresh solver per call), so conditioning's
        // inter-solve clause DB compaction provides no benefit.
        solver.set_condition_enabled(false);
        // Adaptive reorder gate for large BV instances (#8118).
        // BV bit-blasting produces industrial-like clause structure.
        // Kissat-style VMTF queue reorder is O(n log n) and too expensive
        // when total_vars exceeds 50K (mirrors adaptive::REORDER_MAX_VARS).
        if total_vars as usize > 50_000 {
            solver.set_reorder_enabled(false);
        }

        // Wire a deadline-aware interrupt flag to the SAT solver so
        // preprocessing passes (congruence, BVE, probing) honor the DPLL
        // executor timeout (#8782). Without this, preprocessing runs
        // uninterruptibly and can consume the entire timeout budget on
        // formulas with heavy gate structure (e.g., try5_dwp_fmt: 13s in
        // congruence alone).
        //
        // Strategy: create a shared atomic flag. If a deadline exists, spawn
        // a timer thread that sets the flag when the deadline fires. The SAT
        // solver's `is_interrupted()` polls this flag during preprocessing.
        let sat_interrupt_flag = if let Some(ref flag) = self.solve_interrupt {
            // Reuse existing interrupt flag from the executor.
            solver.set_interrupt(flag.clone());
            Some(flag.clone())
        } else if self.solve_deadline.is_some() {
            // No external interrupt flag but we have a deadline: create one.
            let flag = Arc::new(AtomicBool::new(false));
            solver.set_interrupt(flag.clone());
            Some(flag)
        } else {
            None
        };
        // Spawn a deadline timer thread if needed.
        let _deadline_guard = if let (Some(deadline), Some(flag)) =
            (self.solve_deadline, sat_interrupt_flag.as_ref())
        {
            let flag = flag.clone();
            let handle = std::thread::spawn(move || {
                let now = Instant::now();
                if now < deadline {
                    std::thread::sleep(deadline - now);
                }
                flag.store(true, Ordering::Relaxed);
            });
            Some(handle)
        } else {
            None
        };

        if proof_enabled {
            solver.enable_clause_trace();
        }

        // Feed clauses to SAT solver using a reusable buffer to avoid
        // per-clause Vec allocation. For 100K+ clauses, this eliminates
        // ~200K heap allocations (one Vec per clause + one drop per clause).
        // The sort_unstable + add_clause_prenormalized path skips the
        // redundant sort/dedup inside add_clause_unscoped, saving ~15%
        // of clause-addition time. BV gate clauses are structurally unique
        // (each gate uses fresh variables), so no duplicates exist; the
        // debug_assert in add_clause_prenormalized validates this contract.
        {
            let mut lit_buf: Vec<SatLiteral> = Vec::with_capacity(8);
            for clause in &all_clauses {
                lit_buf.clear();
                lit_buf.extend(clause.literals().iter().map(|&lit| crate::cnf_lit_to_sat(lit)));
                // Sort for add_clause_prenormalized contract: Tseitin/BV
                // gate clauses have unique variables but may not be sorted.
                lit_buf.sort_unstable_by_key(|l| l.raw());
                solver.add_clause_prenormalized(&lit_buf);
            }
        }

        // When assumptions are present, use solve_with_assumptions for unsat core
        // extraction. Otherwise use the standard solve() path.
        if has_assumptions {
            solver.set_max_learned_clauses(self.learned_clause_limit);
            solver.set_max_clause_db_bytes(self.clause_db_bytes_limit);

            // Use interruptible variant to respect timeout/interrupt (#3381)
            let should_stop = self.make_should_stop();
            let assume_result =
                solver.solve_with_assumptions_interruptible(&sat_assumptions, should_stop);

            collect_sat_stats!(self, &solver);

            match assume_result.into_inner() {
                AssumeResult::Sat(model) => {
                    self.last_assumption_core = None;
                    let bv_model = Self::extract_bv_model_from_bits(
                        &model,
                        term_bits_snapshot,
                        var_offset,
                        &self.ctx.terms,
                    );
                    return self.solve_and_store_model_full(
                        SatResult::Sat(model),
                        &tseitin_result,
                        None,
                        None,
                        None,
                        None,
                        Some(bv_model),
                        None,
                        None,
                        None,
                    );
                }
                AssumeResult::Unsat(core_lits) => {
                    // Map SAT literals back to original assumption TermIds
                    let core_terms: Vec<TermId> = core_lits
                        .iter()
                        .filter_map(|&lit| {
                            assumption_to_term
                                .iter()
                                .find(|(sat_lit, _)| {
                                    sat_lit.variable() == lit.variable()
                                        && sat_lit.is_positive() == lit.is_positive()
                                })
                                .map(|(_, term)| *term)
                        })
                        .collect();
                    debug_assert!(
                        core_terms.iter().all(|ct| assumptions.contains(ct)),
                        "BUG: BV assumption core contains term not in original assumptions"
                    );
                    self.last_assumption_core = Some(core_terms);

                    // UNSAT proof handling (#340, #4176)
                    if proof_enabled {
                        self.save_bv_unsat_proof_state(
                            solver.take_clause_trace(),
                            &tseitin_result.var_to_term,
                        );
                    }

                    return self.solve_and_store_model(
                        SatResult::Unsat,
                        &tseitin_result,
                        None,
                        None,
                    );
                }
                AssumeResult::Unknown => {
                    self.last_assumption_core = None;
                    return self.solve_and_store_model(
                        SatResult::Unknown,
                        &tseitin_result,
                        None,
                        None,
                    );
                }
                #[allow(unreachable_patterns)]
                _ => unreachable!("BUG: AssumeResult variant not handled in BV assumption path"),
            }
        }

        // Standard solve path (no assumptions)
        // With delayed internalization (#7015), this becomes an iterative loop:
        // 1. Solve SAT
        // 2. If SAT, check delayed operations against model
        // 3. If violations: add conflict clauses, re-solve (up to MAX_DELAY_ITERATIONS)
        // 4. If all consistent or UNSAT: finalize
        //
        // Max iterations prevents infinite loops if cheap axioms keep failing.
        // Z3 has no explicit limit because Phase 2 always builds the full circuit,
        // guaranteeing convergence. We do the same: Phase 1 tries cheap axioms,
        // Phase 2 builds circuits.
        const MAX_DELAY_ITERATIONS: usize = 32;
        let mut delay_iteration = 0;
        let mut solve_result;

        // Enable incremental mode on the SAT solver when delayed ops exist,
        // so learned clauses survive across re-solves.
        if has_delayed_ops {
            solver.set_incremental_mode();
        }

        loop {
            let should_stop = self.make_should_stop();
            solve_result = solver.solve_interruptible(should_stop).into_inner();
            collect_sat_stats!(self, &solver);
            self.propagate_bv_unknown_reason(matches!(solve_result, SatResult::Unknown));

            // Check delayed operations if SAT and we have delayed ops (#7015)
            if let SatResult::Sat(ref model) = solve_result {
                if let Some(ref mut ds) = delayed_state {
                    if ds.has_unresolved() && delay_iteration < MAX_DELAY_ITERATIONS {
                        delay_iteration += 1;

                        // Unified check: per-op escalation from cheap axioms to full circuit.
                        // Each op gets MAX_CHEAP_TRIES attempts with cheap axioms before
                        // escalating to full circuit building. This gives cheap reasoning
                        // (zero/one/invertibility) a chance to resolve violations without
                        // building the expensive multiplication/division circuit.
                        let (cheap_clauses, needs_circuit) = ds.check(model, var_offset);
                        for clause in &cheap_clauses {
                            let lits: Vec<SatLiteral> = clause
                                .literals()
                                .iter()
                                .map(|&lit| {
                                    crate::cnf_lit_to_sat(bv_encoding::offset_cnf_lit(
                                        lit, var_offset,
                                    ))
                                })
                                .collect();
                            solver.add_clause_global(lits);
                        }

                        if !needs_circuit.is_empty() {
                            let mut tmp_bv = BvSolver::new(&self.ctx.terms);
                            tmp_bv.set_term_to_bits(ds.term_to_bits().clone());
                            if let Some((ref ucache, ref scache, ref mut next_var)) =
                                delay_div_caches
                            {
                                tmp_bv.set_div_caches(ucache.clone(), scache.clone());
                                tmp_bv.set_next_var(*next_var);
                            }
                            tmp_bv.set_delayed_ops(ds.delayed_ops().to_vec());
                            for &idx in &needs_circuit {
                                let circuit_clauses = tmp_bv.build_delayed_circuit(idx);
                                let new_bv_vars = tmp_bv.num_vars();
                                let new_total = (tseitin_result.num_vars + new_bv_vars) as usize;
                                solver.ensure_num_vars(new_total);
                                for clause in &circuit_clauses {
                                    let lits: Vec<SatLiteral> = clause
                                        .literals()
                                        .iter()
                                        .map(|&lit| {
                                            crate::cnf_lit_to_sat(bv_encoding::offset_cnf_lit(
                                                lit, var_offset,
                                            ))
                                        })
                                        .collect();
                                    solver.add_clause_global(lits);
                                }
                                let bv_extra = tmp_bv.take_clauses();
                                for clause in &bv_extra {
                                    let lits: Vec<SatLiteral> = clause
                                        .literals()
                                        .iter()
                                        .map(|&lit| {
                                            crate::cnf_lit_to_sat(bv_encoding::offset_cnf_lit(
                                                lit, var_offset,
                                            ))
                                        })
                                        .collect();
                                    solver.add_clause_global(lits);
                                }
                            }
                            // Advance next_var to prevent variable collisions
                            // on the next loop iteration (#7015 regression fix).
                            if let Some((_, _, ref mut next_var)) = delay_div_caches {
                                *next_var = tmp_bv.num_vars() + 1;
                            }
                            drop(tmp_bv);
                        }

                        // Re-solve if anything was added (cheap axioms or circuits)
                        if !cheap_clauses.is_empty() || !needs_circuit.is_empty() {
                            continue;
                        }
                    }
                }
            }

            break; // No delayed violations (or UNSAT/Unknown) — exit loop
        }

        // --- Phase 11: Model extraction ---
        if let SatResult::Sat(ref model) = solve_result {
            let sat_model: Vec<bool> = model.clone();
            // Use term_bits clone if bv_solver was dropped (non-BV congruence path),
            // otherwise get from bv_solver directly.
            let mut bv_model = Self::extract_bv_model_from_bits(
                &sat_model,
                &term_bits,
                var_offset,
                &self.ctx.terms,
            );

            // Seed bool_overrides with Tseitin SAT assignments for Bool-sorted terms (#5115).
            for (&dimacs_var, &term) in &tseitin_result.var_to_term {
                if *self.ctx.terms.sort(term) == Sort::Bool {
                    let sat_idx = (dimacs_var - 1) as usize;
                    if let Some(&val) = sat_model.get(sat_idx) {
                        bv_model.bool_overrides.entry(term).or_insert(val);
                    }
                }
            }

            // Preprocessor variable substitution recovery (#1708/#1789, QF_BV only)
            if let Some((ref var_subst, _)) = var_subst {
                let substitutions = var_subst
                    .lock()
                    .expect("variable substitution mutex poisoned during BV model recovery");
                let subs: Vec<_> = substitutions.substitutions().iter().collect();
                let mut remaining: Vec<(TermId, TermId)> =
                    subs.iter().map(|(&k, &v)| (k, v)).collect();
                let mut iterations = 0;
                const MAX_ITERATIONS: usize = 10;

                while !remaining.is_empty() && iterations < MAX_ITERATIONS {
                    iterations += 1;
                    let mut next_remaining = Vec::new();
                    for (from_var, to_var) in remaining {
                        if let Some(value) = bv_model.values.get(&to_var) {
                            bv_model.values.insert(from_var, value.clone());
                            continue;
                        }
                        if let TermData::Const(z4_core::term::Constant::BitVec { value, .. }) =
                            self.ctx.terms.get(to_var)
                        {
                            bv_model.values.insert(from_var, value.clone());
                            continue;
                        }
                        if let Some(value) =
                            Self::evaluate_bv_expr(&self.ctx.terms, to_var, &bv_model.values)
                        {
                            bv_model.values.insert(from_var, value);
                            continue;
                        }
                        // Bool-sorted recovery (#5524, #5512, #5115)
                        if *self.ctx.terms.sort(from_var) == Sort::Bool {
                            if let TermData::Const(z4_core::term::Constant::Bool(b)) =
                                self.ctx.terms.get(to_var)
                            {
                                bv_model.bool_overrides.insert(from_var, *b);
                                continue;
                            }
                            if let Some(bool_val) = Self::evaluate_bool_substitution(
                                &self.ctx.terms,
                                to_var,
                                &bv_model.values,
                                &bv_model.bool_overrides,
                            ) {
                                bv_model.bool_overrides.insert(from_var, bool_val);
                                continue;
                            }
                        }
                        next_remaining.push((from_var, to_var));
                    }
                    remaining = next_remaining;
                }
            }

            // Restore original assertions if preprocessed
            if let Some((_, original)) = var_subst {
                self.ctx.assertions = original;
            }

            // Extract array model from BV select terms (#5449)
            let array_model = if config.array_axioms {
                let am = Self::extract_array_model_from_bv_model(&self.ctx.terms, &bv_model);
                if am.array_values.is_empty() {
                    None
                } else {
                    Some(am)
                }
            } else {
                None
            };
            return self.solve_and_store_model_full(
                SatResult::Sat(sat_model),
                &tseitin_result,
                None,
                array_model,
                None,
                None,
                Some(bv_model),
                None,
                None,
                None,
            );
        }

        // --- Phase 12: Non-SAT result finalization ---
        debug_assert!(
            !matches!(solve_result, SatResult::Sat(_)),
            "BUG: BV SAT case must go through solve_and_store_model_full, not From conversion"
        );

        let clause_trace = if proof_enabled && matches!(solve_result, SatResult::Unsat) {
            solver.take_clause_trace()
        } else {
            None
        };

        if matches!(solve_result, SatResult::Unsat) {
            self.last_assumption_core = Some(vec![]);
        }

        let result = match solve_result {
            SatResult::Unsat => {
                self.finalize_bv_unsat(clause_trace, &tseitin_result.var_to_term, proof_enabled)
            }
            SatResult::Unknown => self.finalize_bv_unknown(),
            SatResult::Sat(_) => {
                unreachable!("BUG: BV SAT case handled above")
            }
            #[allow(unreachable_patterns)]
            _ => unreachable!("BUG: SatResult variant not handled in BV non-incremental path"),
        };

        // Restore original assertions if preprocessed
        if let Some((_, original)) = var_subst {
            self.ctx.assertions = original;
        }

        result
    }

    /// Finalize a BV UNSAT result: save proof state, set result, build proof.
    ///
    /// Shared by non-incremental (no-assumption) and incremental BV paths.
    /// Caller must extract `clause_trace` from the SAT solver before calling
    /// (to release the solver borrow for NLL purposes).
    pub(super) fn finalize_bv_unsat(
        &mut self,
        clause_trace: Option<ClauseTrace>,
        var_to_term: &std::collections::BTreeMap<u32, TermId>,
        proof_enabled: bool,
    ) -> Result<SolveResult> {
        if proof_enabled {
            self.save_bv_unsat_proof_state(clause_trace, var_to_term);
        }
        self.last_model = None;
        self.last_result = Some(SolveResult::Unsat);
        if proof_enabled {
            self.build_unsat_proof();
        }
        Ok(SolveResult::Unsat)
    }

    /// Finalize a BV Unknown result: map SAT-level reason, set result.
    ///
    /// Shared by non-incremental (no-assumption) and incremental BV paths.
    /// Consumes `pending_sat_unknown_reason` (set by `collect_sat_stats!`).
    pub(super) fn finalize_bv_unknown(&mut self) -> Result<SolveResult> {
        self.last_model = None;
        Self::record_sat_unknown_reason(
            &mut self.last_unknown_reason,
            self.pending_sat_unknown_reason.take(),
        );
        if self.last_unknown_reason.is_none() {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
        }
        self.last_result = Some(SolveResult::Unknown);
        Ok(SolveResult::Unknown)
    }

    /// Propagate interrupt/timeout reason to executor when SAT returns Unknown (#3381).
    ///
    /// Called after `collect_sat_stats!` which sets `pending_sat_unknown_reason`.
    /// Only checks interrupt/timeout when the SAT solver didn't provide its own
    /// reason. Shared by non-incremental and incremental BV paths (#6691).
    pub(super) fn propagate_bv_unknown_reason(&mut self, is_unknown: bool) {
        if is_unknown && self.pending_sat_unknown_reason.is_none() {
            if self
                .solve_interrupt
                .as_ref()
                .is_some_and(|f| f.load(Ordering::Relaxed))
            {
                self.last_unknown_reason = Some(UnknownReason::Interrupted);
            } else if self.solve_deadline.is_some_and(|dl| Instant::now() >= dl) {
                self.last_unknown_reason = Some(UnknownReason::Timeout);
            }
        }
    }

    /// Save BV UNSAT proof state: clause trace, var→term (DIMACS-1 offset), negations.
    ///
    /// Replaces the 3-copy pattern in BV solve paths (#6691). Builds the
    /// negation map from var_to_term on demand via `build_negation_map`.
    fn save_bv_unsat_proof_state(
        &mut self,
        clause_trace: Option<ClauseTrace>,
        var_to_term: &std::collections::BTreeMap<u32, TermId>,
    ) {
        self.last_clause_trace = clause_trace;
        self.last_var_to_term = Some(var_to_term.iter().map(|(&v, &t)| (v - 1, t)).collect());
        self.last_negations = Some(bv_encoding::build_negation_map(
            &mut self.ctx.terms,
            var_to_term,
        ));
        self.last_clausification_proofs = None;
        self.last_original_clause_theory_proofs = None;
    }

    // Array axiom generation (generate_array_bv_axioms, collect_array_terms) is in bv_axioms_array.rs.
    // EUF axiom generation (generate_euf_bv_axioms*, collect_uf_applications) is in bv_axioms_euf.rs.
}

#[cfg(test)]
mod tests;
