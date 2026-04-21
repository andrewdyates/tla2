// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Default for Executor {
    fn default() -> Self {
        Self::new()
    }
}

impl Executor {
    /// Commands that mutate the assertion/objective stack invalidate
    /// any cached check-sat artefacts (model/proof/unsat-assumptions).
    pub(super) fn command_invalidates_last_check_result(cmd: &Command) -> bool {
        matches!(
            cmd,
            Command::Assert(_)
                | Command::Push(_)
                | Command::Pop(_)
                | Command::Reset
                | Command::ResetAssertions
                | Command::Maximize(_)
                | Command::Minimize(_)
        )
    }

    /// Clear all query artefacts produced by the last check-sat call.
    ///
    /// This mirrors SMT-LIB solver behavior: after assertion-stack mutations,
    /// `get-model`, `get-proof`, and unsat-core/assumption queries are no
    /// longer valid until the next check-sat.
    pub(super) fn invalidate_last_check_result(&mut self) {
        self.last_result = None;
        self.last_model = None;
        self.last_assumptions = None;
        self.last_assumption_core = None;
        self.last_core_term_to_name = None;
        self.last_proof = None;
        self.last_proof_term_overrides = None;
        self.proof_problem_assertion_provenance = None;
        self.last_proof_quality = None;
        self.last_unknown_reason = None;
        self.last_clause_trace = None;
        self.last_lrat_certificate = None;
        self.last_var_to_term = None;
        self.last_clausification_proofs = None;
        self.last_original_clause_theory_proofs = None;
        self.proof_check_result = None;
        self.pending_sat_unknown_reason = None;
    }

    /// Native API assertions bypass `Command::Assert`, so they must manually
    /// invalidate stale solve artifacts.
    ///
    /// If a new assertion is added after any prior `check-sat` result, treat
    /// the session as incremental even without explicit push/pop. This keeps
    /// follow-up solves on the persistent-safe lanes used for accumulating
    /// blocking clauses and other post-solve refinement patterns.
    pub(crate) fn note_api_assertion_mutation(&mut self) {
        let had_prior_result = self.last_result.is_some();
        self.invalidate_last_check_result();
        if had_prior_result {
            self.incremental_mode = true;
        }
    }

    /// Create a new executor
    #[must_use]
    pub fn new() -> Self {
        Self {
            ctx: Context::new(),
            last_result: None,
            last_model: None,
            last_assumptions: None,
            last_assumption_core: None,
            last_core_term_to_name: None,
            last_proof: None,
            last_lrat_certificate: None,
            last_proof_term_overrides: None,
            proof_problem_assertion_provenance: None,
            last_proof_quality: None,
            last_unknown_reason: None,
            last_statistics: Statistics::default(),
            debug_ufbv: false,
            incremental_mode: false,
            incr_bv_state: None,
            incr_theory_state: None,
            counterexample_style: crate::CounterexampleStyle::default(),
            proof_tracker: crate::proof_tracker::ProofTracker::new(),
            last_clause_trace: None,
            last_var_to_term: None,
            last_clausification_proofs: None,
            last_original_clause_theory_proofs: None,
            quantifier_manager: None,
            learned_clause_limit: None,
            clause_db_bytes_limit: None,
            solve_interrupt: None,
            solve_deadline: None,
            pivot_enum_depth: 0,
            proof_check_result: None,
            pending_sat_unknown_reason: None,
            verification_level: VerificationLevel::from_state(false),
            defer_model_validation: false,
            defer_counterexample_minimization: false,
            last_model_validated: false,
            last_validation_stats: None,
            skip_model_eval: false,
            bypass_string_tautology_guard: false,
            slia_accepted_unknown: false,
            array_axiom_scope: None,
            cached_store_eqs: Vec::new(),
            store_eq_scan_hwm: 0,
            cached_select_indices_by_array: HashMap::new(),
            select_index_scan_hwm: 0,
            last_negations: None,
            random_seed: None,
            ematching_round_limit: None,
            progress_enabled: false,
            #[cfg(test)]
            last_applied_sat_random_seed: Cell::new(None),
            #[cfg(test)]
            last_applied_dpll_random_seed: Cell::new(None),
        }
    }

    /// Create a new executor with a specific verification level (#4444).
    #[must_use]
    pub fn with_verification_level(level: VerificationLevel) -> Self {
        let mut exec = Self::new();
        exec.verification_level = level;
        exec
    }

    /// Get the current verification level.
    #[must_use]
    pub fn verification_level(&self) -> VerificationLevel {
        self.verification_level
    }

    /// Set the verification level.
    pub fn set_verification_level(&mut self, level: VerificationLevel) {
        self.verification_level = level;
    }

    /// Access the internal context (for API module)
    pub fn context(&self) -> &Context {
        &self.ctx
    }

    /// Access the internal context mutably (for API module)
    pub fn context_mut(&mut self) -> &mut Context {
        &mut self.ctx
    }

    /// Result from the last internal proof validation (#4393).
    ///
    /// Returns `None` if no proof validation has been performed (e.g., last
    /// result was SAT, or proofs are not enabled). Returns `Some` with the
    /// partial check result after any UNSAT proof generation.
    pub fn proof_check_result(&self) -> Option<&PartialProofCheck> {
        self.proof_check_result.as_ref()
    }

    /// Enable debug output for QF_UFBV solving
    pub fn set_debug_ufbv(&mut self, enabled: bool) {
        self.debug_ufbv = enabled;
    }

    /// Set the counterexample style for model generation
    ///
    /// This affects how `get-model` generates values:
    /// - `Any`: Return any satisfying value (fast, current behavior)
    /// - `Minimal`: Prefer 0, ±1, powers of 2, MIN/MAX (default)
    /// - `Readable`: Prefer round numbers and simple values
    pub fn set_counterexample_style(&mut self, style: crate::CounterexampleStyle) {
        self.counterexample_style = style;
    }

    /// Get the current counterexample style.
    #[must_use]
    pub fn counterexample_style(&self) -> crate::CounterexampleStyle {
        self.counterexample_style
    }

    /// Enable or disable proof production
    ///
    /// When enabled, the solver collects proof steps during solving.
    /// After an UNSAT result, call `get_proof()` to retrieve the proof.
    ///
    /// This is required for tRust integration (proof certificates).
    pub fn set_produce_proofs(&mut self, enabled: bool) {
        if enabled {
            self.proof_tracker.enable();
        } else {
            self.proof_tracker.disable();
        }
    }

    /// Check if proof production is enabled
    #[must_use]
    pub fn is_producing_proofs(&self) -> bool {
        self.proof_tracker.is_enabled()
    }

    /// Set the maximum learned clauses limit for SAT solving (#1609)
    pub fn set_learned_clause_limit(&mut self, limit: Option<usize>) {
        self.learned_clause_limit = limit;
    }

    /// Get the current learned clause limit
    pub fn learned_clause_limit(&self) -> Option<usize> {
        self.learned_clause_limit
    }

    /// Set the maximum clause DB size (bytes) limit for SAT solving (#1609)
    pub fn set_clause_db_bytes_limit(&mut self, limit: Option<usize>) {
        self.clause_db_bytes_limit = limit;
    }

    /// Get the current clause DB size (bytes) limit
    pub fn clause_db_bytes_limit(&self) -> Option<usize> {
        self.clause_db_bytes_limit
    }

    /// Set the random seed for SAT solver VSIDS tie-breaking (#6961).
    ///
    /// Different seeds produce different variable selection orders for
    /// tied activities, leading to different search paths. Useful for
    /// catching non-deterministic solver bugs via seed perturbation.
    pub fn set_random_seed(&mut self, seed: u64) {
        self.random_seed = Some(seed);
    }

    /// Enable periodic progress line emission on SAT solvers used during solving.
    ///
    /// When enabled, all SAT solver instances created by this executor emit
    /// a compact one-line status summary to stderr approximately every 5
    /// seconds during CDCL solving. Forwarded to DpllT and raw SAT solvers.
    pub fn set_progress_enabled(&mut self, enabled: bool) {
        self.progress_enabled = enabled;
    }

    /// Get the current random seed, if set.
    #[must_use]
    pub fn random_seed(&self) -> Option<u64> {
        self.random_seed
    }

    /// Proof from the last UNSAT result.
    ///
    /// Returns None if the last result was not UNSAT or if proof production was disabled.
    #[must_use]
    pub fn last_proof(&self) -> Option<&Proof> {
        self.last_proof.as_ref()
    }

    /// Get access to the term store
    #[must_use]
    pub fn terms(&self) -> &TermStore {
        &self.ctx.terms
    }

    #[cfg(test)]
    #[must_use]
    pub(crate) fn has_proof_problem_assertion_provenance(&self) -> bool {
        self.proof_problem_assertion_provenance.is_some()
    }

    pub(super) fn produce_models_enabled(&self) -> bool {
        matches!(
            self.ctx.get_option("produce-models"),
            Some(OptionValue::Bool(true))
        )
    }

    /// Resolve the effective counterexample style from the typed API field and
    /// the SMT-LIB option. The SMT-LIB option takes precedence when explicitly set.
    pub(crate) fn effective_counterexample_style(&self) -> crate::CounterexampleStyle {
        match self.ctx.get_option("minimize-counterexamples") {
            Some(OptionValue::Bool(true)) => crate::CounterexampleStyle::Minimal,
            Some(OptionValue::Bool(false)) => crate::CounterexampleStyle::Any,
            _ => self.counterexample_style,
        }
    }

    pub(super) fn minimize_counterexamples_enabled(&self) -> bool {
        !matches!(
            self.effective_counterexample_style(),
            crate::CounterexampleStyle::Any
        )
    }

    /// Reset the executor to initial state.
    ///
    /// Aligns with the SMT-LIB `(reset)` command handler: resets all solving
    /// state, incremental state, quantifier manager, proof tracking, and
    /// interrupt/deadline. Configuration settings (debug_ufbv,
    /// counterexample_style, learned clause limits, verification_level)
    /// are preserved.
    pub fn reset(&mut self) {
        self.ctx = Context::new();
        self.last_result = None;
        self.last_model = None;
        self.last_assumptions = None;
        self.last_assumption_core = None;
        self.last_core_term_to_name = None;
        self.last_proof = None;
        self.last_proof_term_overrides = None;
        self.last_proof_quality = None;
        self.last_unknown_reason = None;
        self.pending_sat_unknown_reason = None;
        self.last_statistics = Statistics::default();
        self.last_clause_trace = None;
        self.last_var_to_term = None;
        self.last_clausification_proofs = None;
        self.last_original_clause_theory_proofs = None;
        self.proof_problem_assertion_provenance = None;
        self.last_negations = None;
        self.incremental_mode = false;
        self.pivot_enum_depth = 0;
        self.proof_check_result = None;
        self.defer_model_validation = false;
        self.defer_counterexample_minimization = false;
        self.last_model_validated = false;
        self.last_validation_stats = None;
        self.skip_model_eval = false;
        self.bypass_string_tautology_guard = false;
        self.slia_accepted_unknown = false;
        self.array_axiom_scope = None;
        self.cached_store_eqs.clear();
        self.store_eq_scan_hwm = 0;
        self.cached_select_indices_by_array.clear();
        self.select_index_scan_hwm = 0;
        self.solve_interrupt = None;
        self.solve_deadline = None;
        for_each_incremental_subsystem!(reset self);
    }
}
