// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT executor - orchestrates frontend and theory solver
//!
//! Provides a high-level interface for executing SMT-LIB commands with
//! theory integration.

use hashbrown::{HashMap, HashSet};
#[cfg(test)]
use std::cell::Cell;
use std::sync::{atomic::AtomicBool, Arc};
use std::time::Instant;
use z4_core::{ClausificationProof, Proof, TheoryLemmaProof};
use z4_core::{TermId, TermStore};
use z4_frontend::{Command, CommandResult, Context, OptionValue};
use z4_sat::{ClauseTrace, SatUnknownReason};

use crate::incremental_state::IncrementalSubsystem;

use z4_proof::PartialProofCheck;

use crate::executor_types::{ExecutorError, Result, SolveResult, Statistics, UnknownReason};
use crate::quantifier_manager::QuantifierManager;
use crate::VerificationLevel;

// Combined theory solvers
pub use crate::combined_solvers::TheoryCombiner;
// Format helpers - format_sort, format_symbol now used in executor/commands.rs

// Incremental state types
use crate::incremental_state::{IncrementalBvState, IncrementalTheoryState};

/// Bounded E-matching passes per check-sat to allow instantiation chaining.
///
/// Each round builds a fresh TermIndex, so terms created by instantiation in
/// round N become matchable in round N+1. A chain of depth D (where axiom A's
/// output triggers axiom B, whose output triggers axiom C, etc.) requires D
/// rounds.
///
/// Budget 8 covers typical axiom chains in sunder's 21-axiom Seq encoding
/// (#3994). Generation-based cost filtering (eager/lazy thresholds) prevents
/// self-triggering patterns from consuming the budget.
const MAX_EMATCHING_ROUNDS: usize = 8;

/// Maximum interleaved E-matching refinement rounds after initial SAT solve.
///
/// After the initial E-matching preprocessing + SAT solve, the interleaved loop
/// re-runs E-matching with the fresh EUF model from the solve. New congruence
/// equalities discovered during solving can trigger new pattern matches that
/// weren't available during preprocessing. Each round: E-match → add instances
/// → re-solve → repeat until fixpoint or budget (#5927).
///
/// Budget 4 is conservative — enough for typical multi-step quantifier chains
/// (e.g., sunder's `f(g(a)) = b` patterns that need 2-3 rounds) without
/// excessive overhead on already-converged formulas.
const MAX_INTERLEAVED_EMATCHING_ROUNDS: usize = 4;

mod assumption_solving;
mod check_sat;
mod check_sat_assuming;
mod commands;
mod dt_axioms;
mod logic_detect;
mod mbqi;
mod mod_div_elim;
mod model;
mod optimization;
mod proof;
mod proof_farkas;
mod proof_resolution;
mod proof_rewrite;
mod proof_rewrite_division;
mod proof_rewrite_terms;
mod proof_surface_syntax;
mod quantifier_loop;
mod stats_contract;
mod theories;
use model::Model;
pub(crate) use theories::BoundRefinementReplayKey;

// NOTE: Clause Retention for Incremental Solving (Kani Fast Requirement 1.2)
//
// IMPLEMENTED: BV incremental (via solve_bv_core + BvSolveConfig::qf_bv_incremental)
// uses assumption-based clause retention.
//
// Key design:
// 1. A persistent SAT solver is maintained across check-sat calls
// 2. Each assertion gets a selector variable `s`
// 3. Clauses are added as implications: (-s ∨ clause_lits)
// 4. At check-sat time, selectors for in-scope assertions are passed as assumptions
// 5. Popped assertions have their selectors excluded, disabling their clauses
// 6. Learned clauses are retained across calls, providing the performance benefit
//
// This approach avoids the complexity of tracking global vs scoped assertions
// and syncing SMT push/pop with SAT push/pop. Instead, we let the SAT solver's
// assumption-based solving handle the scoping naturally.

/// SMT executor that coordinates frontend parsing with theory solving
pub struct Executor {
    /// Frontend context for elaboration
    pub(crate) ctx: Context,
    /// Last check-sat result
    last_result: Option<SolveResult>,
    /// Last satisfying model (if any)
    last_model: Option<Model>,
    /// Last assumptions from check-sat-assuming (for get-unsat-assumptions)
    last_assumptions: Option<Vec<TermId>>,
    /// Minimal UNSAT core from last check-sat-assuming (subset of assumptions)
    /// This is populated when using the SAT solver's assumption-based solving
    last_assumption_core: Option<Vec<TermId>>,
    /// Mapping from assertion TermId to assertion name for unsat core extraction.
    /// Populated when produce-unsat-cores redirects check-sat through
    /// check-sat-assuming with named assertions as assumptions.
    last_core_term_to_name: Option<HashMap<TermId, String>>,
    /// Last proof (for get-proof when UNSAT)
    last_proof: Option<Proof>,
    /// Last LRAT certificate serialized from the SAT clause trace.
    ///
    /// Populated opportunistically for UNSAT results when the clause trace is
    /// complete enough to replay as a standalone LRAT certificate.
    last_lrat_certificate: Option<Vec<u8>>,
    /// Optional surface-syntax overrides for proof terms during Alethe export.
    /// Keys are canonical proof terms; values are the exact source-syntax
    /// strings from parsed input assertions.
    last_proof_term_overrides: Option<HashMap<TermId, String>>,
    /// Proof-premise provenance for temporary combined-theory assertion views.
    ///
    /// When combined routes solve over a rewritten assertion window, this
    /// records which temporary assertions still correspond to original problem
    /// premises plus the original assertion stack used to recover parsed
    /// surface syntax during proof export (#6759).
    proof_problem_assertion_provenance:
        Option<theories::solve_harness::ProofProblemAssertionProvenance>,
    /// Quality metrics from last proof validation (#4420)
    last_proof_quality: Option<z4_proof::ProofQuality>,
    /// Reason for last Unknown result (for get-info :reason-unknown)
    last_unknown_reason: Option<UnknownReason>,
    /// Statistics from last check-sat call
    last_statistics: Statistics,
    /// Debug flag for QF_UFBV solving
    debug_ufbv: bool,
    /// Whether incremental mode is enabled.
    ///
    /// Enabled by push/pop and by adding assertions after a prior solve.
    /// When true, incremental solving is used which maintains a persistent SAT
    /// solver to retain learned clauses across check-sat calls.
    pub(crate) incremental_mode: bool,
    /// Persistent state for incremental BV solving with rebuild-on-pop invalidation
    incr_bv_state: Option<IncrementalBvState>,
    /// Persistent state for incremental theory solving (UF/LRA/LIA)
    pub(crate) incr_theory_state: Option<IncrementalTheoryState>,
    /// Style for counterexample generation (model minimization)
    counterexample_style: crate::CounterexampleStyle,
    /// Proof tracker for collecting proof steps during solving
    proof_tracker: crate::proof_tracker::ProofTracker,
    /// Last clause trace from SAT solver (for SAT resolution proof reconstruction)
    last_clause_trace: Option<ClauseTrace>,
    /// Last var_to_term mapping from Tseitin (for SAT proof reconstruction)
    last_var_to_term: Option<HashMap<u32, TermId>>,
    /// Last clausification proof annotations (for Alethe tautology rule steps).
    /// Parallel to Tseitin clause order — annotations[i] justifies clause[i] (#6031).
    last_clausification_proofs: Option<Vec<Option<ClausificationProof>>>,
    /// Last original-clause theory proof annotations for SAT reconstruction.
    /// Parallel to SAT original clause order, including incremental NeedLemmas.
    last_original_clause_theory_proofs: Option<Vec<Option<TheoryLemmaProof>>>,
    /// Quantifier manager for persisting generation tracking across E-matching rounds
    pub(crate) quantifier_manager: Option<QuantifierManager>,
    /// Maximum learned clauses for SAT solver (None = no limit) (#1609)
    learned_clause_limit: Option<usize>,
    /// Maximum clause DB size (bytes) for SAT solver (None = no limit) (#1609)
    clause_db_bytes_limit: Option<usize>,
    /// Interrupt flag propagated from API-level `check_sat`/`check_sat_assuming`.
    solve_interrupt: Option<Arc<AtomicBool>>,
    /// Deadline propagated from API-level timeout settings.
    solve_deadline: Option<Instant>,
    /// Re-entry guard for pivot-bounded word equation enumeration (#3826).
    /// When > 0, the pivot enumeration pre-pass in solve_strings_lia is
    /// skipped to prevent infinite recursion.
    pivot_enum_depth: u8,
    /// Result from the last proof validation run (#4393).
    /// Populated by `build_unsat_proof` after running `check_proof_partial`.
    proof_check_result: Option<PartialProofCheck>,
    /// SAT-level unknown reason pending mapping to DPLL-level (#4622).
    /// Set by `collect_sat_stats!` macro, consumed by `solve_and_store_model`.
    pending_sat_unknown_reason: Option<SatUnknownReason>,
    /// Verification level controlling runtime correctness checks (#4444).
    ///
    /// Replaces the scattered `debug_*_enabled()` env-var checks with a
    /// single structured configuration point. Consumers set this to control
    /// what verification overhead they accept.
    verification_level: VerificationLevel,
    /// When true, `finalize_sat_model_validation` skips validation and returns
    /// `Ok(SolveResult::Sat)` immediately. This is set during `check_sat_internal`
    /// when quantifier E-matching modifies the assertion set: the theory solver's
    /// model validation would see ground instances instead of the original quantified
    /// assertions, causing false violations. Validation is deferred to after the
    /// original assertions are restored (#2862).
    defer_model_validation: bool,
    /// When true, `solve_and_store_model_full` stores the SAT/theory model but
    /// skips SAT-preserving counterexample minimization until the caller
    /// restores the original assertion set. Used by standalone preprocessing
    /// lanes whose temporary reduced assertions are not the user-facing formula.
    defer_counterexample_minimization: bool,
    /// True when `finalize_sat_model_validation` actually ran and passed on the
    /// last solve call. Reset to `false` at the start of each `check_sat`.
    /// Used by the API layer to accurately report `sat_model_validated` (#5903).
    last_model_validated: bool,
    /// Validation stats from the last completed SAT validation attempt.
    /// Preserved for both validated SAT and SAT->Unknown degradation so the
    /// API layer can report why validation failed (#5777).
    pub(crate) last_validation_stats: Option<model::ValidationStats>,
    /// When true, `finalize_sat_model_validation` skips all evaluation and
    /// accepts the SAT model directly. Used for incomplete theory solvers
    /// (Seq MVP) where the model evaluator cannot independently verify
    /// seq.len, seq.unit, etc. Reset at start of each `check_sat` (#5841).
    skip_model_eval: bool,
    /// When true, `has_negated_string_equivalence_tautology` is bypassed.
    /// Set during incremental SLIA pipeline where `self.ctx.assertions` is
    /// temporarily replaced with preprocessed assertions that may falsely
    /// trigger the tautology guard (#6688).
    pub(crate) bypass_string_tautology_guard: bool,
    /// Set by the incremental macro's Unknown→Sat path when the theory
    /// returned Unknown but the model was accepted (#6688).  Used by the
    /// deferred validation in `solve_strings_lia_preprocessed` to decide
    /// whether model validation is needed.
    pub(crate) slia_accepted_unknown: bool,
    /// Temporary scope filter for array axiom generation in incremental mode (#6726).
    /// When `Some`, the fixpoint generators skip terms not reachable from current
    /// assertions. The `usize` is the TermStore length at fixpoint entry — terms
    /// created during the fixpoint (idx >= this) always pass the scope check.
    array_axiom_scope: Option<(HashSet<TermId>, usize)>,
    /// #6820: Cached store-equality tuples from the last fixpoint scan.
    /// Store equalities come from the original formula and don't change
    /// during the fixpoint, so we collect them once and reuse.
    /// Tuple: (eq_term, store_base, store_index, store_value, other_side)
    cached_store_eqs: Vec<(TermId, TermId, TermId, TermId, TermId)>,
    /// #6820: High-water mark of terms scanned for store-eq collection.
    /// Only scan terms above this index on subsequent rounds.
    store_eq_scan_hwm: usize,
    /// #6820: Cached select indices grouped by base array for the current
    /// eager array fixpoint. Reused by both store congruence passes so they
    /// do not rescan the full term store every round.
    cached_select_indices_by_array: HashMap<TermId, Vec<TermId>>,
    /// #6820: High-water mark of terms scanned for select collection.
    /// Only scan terms above this index on subsequent rounds.
    select_index_scan_hwm: usize,
    /// Cached negation map from the last proof-tracking solve, reused for
    /// incremental proof reconstruction (#6590).
    pub(crate) last_negations: Option<HashMap<TermId, TermId>>,
    /// Random seed for SAT solver VSIDS tie-breaking (#6961).
    /// When `Some(seed)`, the seed is applied to every SAT solver instance
    /// before solving. Different seeds produce different search paths.
    random_seed: Option<u64>,
    /// E-matching round limit override (#7893).
    ematching_round_limit: Option<usize>,
    /// When true, SAT solvers created during solving emit periodic progress
    /// lines to stderr (~5s interval). Propagated to DpllT and raw SAT
    /// solver instances.
    progress_enabled: bool,
    /// Test-only trace of the last seed applied to a raw SAT solver instance.
    #[cfg(test)]
    last_applied_sat_random_seed: Cell<Option<u64>>,
    /// Test-only trace of the last seed applied to a DPLL(T) solver instance.
    #[cfg(test)]
    last_applied_dpll_random_seed: Cell<Option<u64>>,
}

#[cfg(test)]
impl Executor {
    pub(crate) fn incremental_bv_state(&self) -> Option<&IncrementalBvState> {
        self.incr_bv_state.as_ref()
    }
}

/// Central registry of incremental subsystems (#5992).
///
/// Adding a new incremental subsystem requires:
/// 1. Implementing `IncrementalSubsystem` for the type
/// 2. Adding the field to this macro (and whether it's `Option<T>` or direct)
///
/// The macro dispatches push/pop/reset to all subsystems uniformly,
/// eliminating the 4×N shotgun surgery pattern.
macro_rules! for_each_incremental_subsystem {
    // Push: init-or-get for Option fields, call directly for non-Option.
    (push $self:expr, $n:expr) => {{
        let bv = $self
            .incr_bv_state
            .get_or_insert_with(IncrementalBvState::new);
        for _ in 0..$n {
            bv.push();
        }
        // NOTE: Theory state has special pre-push assertion logic handled
        // by the caller before this macro invocation. The push itself is
        // dispatched here.
        let ts = $self
            .incr_theory_state
            .get_or_insert_with(IncrementalTheoryState::new);
        for _ in 0..$n {
            ts.push();
        }
        let qm = $self
            .quantifier_manager
            .get_or_insert_with(QuantifierManager::new);
        for _ in 0..$n {
            qm.push();
        }
        for _ in 0..$n {
            $self.proof_tracker.push();
        }
    }};
    // Pop: if-let for Option fields, call directly for non-Option.
    // Returns true if all subsystems popped successfully.
    (pop $self:expr, $n:expr) => {{
        let mut ok = true;
        if let Some(ref mut s) = $self.incr_bv_state {
            for _ in 0..$n {
                ok &= s.pop();
                debug_assert!(
                    ok,
                    "BUG: IncrementalBvState::pop() underflow — more pops than pushes"
                );
            }
        }
        if let Some(ref mut s) = $self.incr_theory_state {
            for _ in 0..$n {
                let popped = s.pop();
                debug_assert!(
                    popped,
                    "BUG: IncrementalTheoryState::pop() underflow — more pops than pushes"
                );
                ok &= popped;
            }
        }
        if let Some(ref mut s) = $self.quantifier_manager {
            for _ in 0..$n {
                let popped = s.pop();
                debug_assert!(
                    popped,
                    "BUG: QuantifierManager::pop() underflow — more pops than pushes"
                );
                ok &= popped;
            }
        }
        for _ in 0..$n {
            let popped = $self.proof_tracker.pop();
            debug_assert!(
                popped,
                "BUG: ProofTracker::pop() underflow — more pops than pushes"
            );
            ok &= popped;
        }
        ok
    }};
    // Reset: if-let for Option fields, call directly for non-Option.
    (reset $self:expr) => {{
        if let Some(ref mut s) = $self.incr_bv_state {
            s.reset();
        }
        if let Some(ref mut s) = $self.incr_theory_state {
            s.reset();
        }
        if let Some(ref mut s) = $self.quantifier_manager {
            s.reset();
        }
        $self.proof_tracker.reset();
    }};
    // Drop: set Option fields to None, reset non-Option fields.
    // Used by ResetAssertions which discards all state.
    (drop $self:expr) => {{
        $self.incr_bv_state = None;
        $self.incr_theory_state = None;
        $self.quantifier_manager = None;
        $self.proof_tracker.reset();
    }};
}

mod lifecycle;

impl Executor {
    /// Execute a single command
    ///
    /// Returns output to be printed, if any.
    #[must_use = "command results must be checked — errors indicate parse/solve failures"]
    pub fn execute(&mut self, cmd: &Command) -> Result<Option<String>> {
        // Track incremental mode: enabled on first push, disabled on reset
        // Context handles assertion scoping via push/pop (truncates on pop)
        match cmd {
            Command::Push(n) => {
                self.incremental_mode = true;
                // Theory state needs pre-push assertion capture before the
                // generic push dispatch. This is the only subsystem-specific
                // logic that can't be unified into the macro (#5992).
                {
                    let assertions_before_push = self.ctx.assertions.clone();
                    let theory_state = self
                        .incr_theory_state
                        .get_or_insert_with(IncrementalTheoryState::new);
                    if theory_state.pre_push_assertions.is_empty()
                        && theory_state.encoded_assertions.is_empty()
                        && theory_state.persistent_sat.is_none()
                        && theory_state.lia_persistent_sat.is_none()
                    {
                        theory_state
                            .pre_push_assertions
                            .extend(assertions_before_push);
                    }
                }
                // Dispatch push to all subsystems (#5992)
                for_each_incremental_subsystem!(push self, *n);
            }
            Command::Pop(n) => {
                // Dispatch pop to all subsystems with underflow checks (#5992, #6230)
                let ok = for_each_incremental_subsystem!(pop self, *n);
                if !ok {
                    return Err(ExecutorError::Elaborate(
                        z4_frontend::ElaborateError::ScopeUnderflow,
                    ));
                }
            }
            Command::Reset => {
                self.incremental_mode = false;
                for_each_incremental_subsystem!(reset self);
            }
            // reset-assertions clears assertions and scopes in the frontend
            // (Context::process_command), but the executor's persistent SAT
            // solvers, incremental state, and quantifier manager also need
            // resetting — otherwise stale learned clauses, scope counters,
            // and activation-clause mappings survive into subsequent queries.
            // (#5850)
            Command::ResetAssertions => {
                // Discard all incremental state. A fresh state will be
                // created on the next push. Stay in incremental_mode per
                // SMT-LIB 2.6 §4.2.2.
                for_each_incremental_subsystem!(drop self);
            }
            // Wire :random-seed option to executor for SAT solver (#6961)
            Command::SetOption(keyword, value) => {
                let key = keyword.strip_prefix(':').unwrap_or(keyword);
                if key == "random-seed" {
                    if let z4_frontend::sexp::SExpr::Numeral(ref n) = *value {
                        if let Ok(seed) = n.parse::<u64>() {
                            self.random_seed = Some(seed);
                        }
                    }
                }
            }
            _ => {}
        }

        let result = self.ctx.process_command(cmd)?;
        if matches!(cmd, Command::Pop(_)) {
            if let Some(ref mut state) = self.incr_theory_state {
                state.retain_encoded_assertions(&self.ctx.assertions);
            }
        }
        if Self::command_invalidates_last_check_result(cmd) {
            self.invalidate_last_check_result();
        }

        match result {
            Some(CommandResult::CheckSat) => {
                let sat_result = if self.ctx.objectives().is_empty() {
                    // Route through check_sat() which calls finalize_sat_model_validation().
                    // Previously called check_sat_internal() directly, bypassing model
                    // validation — an escape hatch that violated the verification invariant.
                    // Part of #5787 (Phase 6).
                    self.check_sat()?
                } else {
                    self.optimize_check_sat()?
                };
                self.last_result = Some(sat_result);
                Ok(Some(sat_result.to_string()))
            }
            Some(CommandResult::CheckSatAssuming(assumptions)) => {
                if !self.ctx.objectives().is_empty() {
                    return Err(ExecutorError::UnsupportedOptimization(
                        "check-sat-assuming with objectives is not supported".to_string(),
                    ));
                }
                let sat_result = self.check_sat_assuming(&assumptions)?;
                self.last_result = Some(sat_result);
                Ok(Some(sat_result.to_string()))
            }
            Some(CommandResult::GetModel) => Ok(Some(self.model())),
            Some(CommandResult::GetObjectives) => Ok(Some(self.get_objectives())),
            Some(CommandResult::GetValue(term_ids)) => Ok(Some(self.values(&term_ids))),
            Some(CommandResult::GetInfo(keyword)) => Ok(Some(self.get_info(&keyword))),
            Some(CommandResult::GetOption(keyword)) => Ok(Some(self.get_option_value(&keyword))),
            Some(CommandResult::GetAssertions) => Ok(Some(self.assertions())),
            Some(CommandResult::Echo(msg)) => Ok(Some(msg)),
            Some(CommandResult::GetAssignment) => Ok(Some(self.get_assignment())),
            Some(CommandResult::GetUnsatCore) => Ok(Some(self.unsat_core())),
            Some(CommandResult::GetUnsatAssumptions) => Ok(Some(self.unsat_assumptions())),
            Some(CommandResult::GetProof) => Ok(Some(self.get_proof())),
            Some(CommandResult::Exit) => Ok(Some("exit".to_string())),
            Some(CommandResult::Simplify(term_id)) => Ok(Some(self.simplify(term_id))),
            #[allow(unreachable_patterns)]
            Some(_) => Ok(Some("unsupported".to_string())),
            None => Ok(None),
        }
    }

    /// Set the maximum number of E-matching rounds per check-sat call.
    pub fn set_ematching_round_limit(&mut self, n: usize) {
        self.ematching_round_limit = Some(n.clamp(1, 64));
    }

    /// Returns the E-matching round limit (default: `MAX_EMATCHING_ROUNDS`).
    pub fn ematching_round_limit(&self) -> usize {
        self.ematching_round_limit.unwrap_or(MAX_EMATCHING_ROUNDS)
    }

    pub(crate) fn current_random_seed(&self) -> u64 {
        match self.ctx.get_option("random-seed") {
            Some(OptionValue::Numeral(seed)) => seed.parse::<u64>().unwrap_or(0),
            Some(OptionValue::String(seed)) => seed.parse::<u64>().unwrap_or(0),
            _ => 0,
        }
    }

    pub(crate) fn record_applied_sat_random_seed_for_test(&self, seed: u64) {
        #[cfg(test)]
        self.last_applied_sat_random_seed.set(Some(seed));
        #[cfg(not(test))]
        let _ = seed;
    }

    pub(crate) fn record_applied_dpll_random_seed_for_test(&self, seed: u64) {
        #[cfg(test)]
        self.last_applied_dpll_random_seed.set(Some(seed));
        #[cfg(not(test))]
        let _ = seed;
    }

    pub(crate) fn apply_random_seed_to_sat(&self, solver: &mut z4_sat::Solver) {
        let seed = self.current_random_seed();
        self.record_applied_sat_random_seed_for_test(seed);
        solver.set_random_seed(seed);
    }

    pub(crate) fn apply_random_seed_to_dpll<T: z4_core::TheorySolver>(
        &self,
        dpll: &mut crate::DpllT<'_, T>,
    ) {
        let seed = self.current_random_seed();
        self.record_applied_dpll_random_seed_for_test(seed);
        dpll.set_random_seed(seed);
    }

    /// Apply progress setting to a raw SAT solver.
    pub(crate) fn apply_progress_to_sat(&self, solver: &mut z4_sat::Solver) {
        if self.progress_enabled {
            solver.set_progress_enabled(true);
        }
    }

    /// Apply progress setting to a DpllT solver.
    pub(crate) fn apply_progress_to_dpll<T: z4_core::TheorySolver>(
        &self,
        dpll: &mut crate::DpllT<'_, T>,
    ) {
        if self.progress_enabled {
            dpll.set_progress_enabled(true);
        }
    }

    #[cfg(test)]
    pub(crate) fn last_applied_sat_random_seed_for_test(&self) -> Option<u64> {
        self.last_applied_sat_random_seed.get()
    }

    #[cfg(test)]
    pub(crate) fn last_applied_dpll_random_seed_for_test(&self) -> Option<u64> {
        self.last_applied_dpll_random_seed.get()
    }

    // DT axiom generation functions (dt_selector_axioms, dt_acyclicity_depth_axioms,
    // dt_occurs_check_unsat_from_equalities) moved to executor/dt_axioms.rs.

    /// Execute a sequence of commands
    ///
    /// Returns outputs for each command that produces output.
    #[must_use = "command results must be checked — errors indicate parse/solve failures"]
    pub fn execute_all(&mut self, commands: &[Command]) -> Result<Vec<String>> {
        let mut outputs = Vec::new();
        for cmd in commands {
            if let Some(output) = self.execute(cmd)? {
                outputs.push(output);
            }
        }
        Ok(outputs)
    }

    // check_sat, check_sat_guarded, set_interrupt, set_solve_controls,
    // clear_solve_controls, make_should_stop, should_abort_theory_loop,
    // check_sat_internal, route_to_solver: moved to executor/check_sat.rs

    /// Get the current logic
    pub fn logic(&self) -> Option<&str> {
        self.ctx.logic()
    }

    /// Get the number of assertions
    pub fn assertion_count(&self) -> usize {
        self.ctx.assertions.len()
    }

    /// Get the last check-sat result.
    ///
    /// Read-only accessor for the result of the last solve call. The result
    /// was validated during solve (via `finalize_sat_model_validation()`).
    /// This accessor does not bypass verification — it reads an already-validated value.
    ///
    /// `pub(crate)`: External consumers use `api::Solver::last_result()` or the
    /// narrow `last_result_is_unsat()` predicate. Part of #5787 (Phase 6).
    pub(crate) fn last_result(&self) -> Option<SolveResult> {
        self.last_result
    }

    /// Returns `true` if the last check-sat call returned UNSAT.
    ///
    /// Narrow predicate for callers that only need a boolean check
    /// (e.g., proof file writing) without matching on `SolveResult` variants.
    pub fn last_result_is_unsat(&self) -> bool {
        self.last_result == Some(SolveResult::Unsat)
    }

    /// Structured reason for the last Unknown result.
    ///
    /// Returns the reason why the solver returned Unknown, if available.
    /// Returns `None` if the last result was not Unknown or if no reason was recorded.
    #[must_use]
    pub fn unknown_reason(&self) -> Option<UnknownReason> {
        match self.last_result {
            Some(SolveResult::Unknown) => self.last_unknown_reason,
            _ => None,
        }
    }

    /// True when `finalize_sat_model_validation` actually ran and passed
    /// on the last solve call (#5903).
    pub(crate) fn was_model_validated(&self) -> bool {
        self.last_model_validated
    }

    /// Get statistics from the last check-sat call
    ///
    /// Returns statistics about the solving process including:
    /// - SAT-level stats: conflicts, decisions, propagations, restarts
    /// - Theory-level stats: theory conflicts and propagations
    /// - Problem size: variables, clauses, assertions
    ///
    /// # Example
    ///
    /// ```no_run
    /// use z4_dpll::Executor;
    ///
    /// let mut exec = Executor::new();
    /// // ... setup and check_sat ...
    /// let stats = exec.statistics();
    /// println!("Conflicts: {}", stats.conflicts);
    /// println!("Decisions: {}", stats.decisions);
    /// ```
    #[must_use]
    pub fn statistics(&self) -> &Statistics {
        &self.last_statistics
    }

    /// Alias for `statistics()` (backward compat with tests).
    #[must_use]
    pub fn get_statistics(&self) -> &Statistics {
        &self.last_statistics
    }

    /// Return the reason for the last `Unknown` result, if any.
    #[must_use]
    pub fn get_reason_unknown(&self) -> Option<UnknownReason> {
        self.last_unknown_reason
    }

    // produce_assignments_enabled, produce_unsat_cores_enabled, get_assignment,
    // get_unsat_core, get_unsat_assumptions moved to executor/commands.rs
    // get_proof and produce_proofs_enabled moved to executor/proof.rs
}
