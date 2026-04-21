// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Z4 DPLL(T) - Theory integration framework
//!
//! Integrates the SAT solver with theory solvers using the DPLL(T) architecture.
//!
//! # DPLL(T) Algorithm
//!
//! The DPLL(T) framework combines SAT solving with theory reasoning:
//!
//! 1. Parse SMT-LIB input and elaborate to internal representation
//! 2. Convert Boolean structure to CNF via Tseitin transformation
//! 3. Run CDCL SAT solver:
//!    - After each propagation, check theory consistency
//!    - If theory finds conflict, add theory lemma as clause
//!    - If theory propagates, add propagated literals
//! 4. When SAT solver finds SAT, verify full model with theory
//! 5. If theory rejects, add blocking clause and continue
//!
//! # Executor
//!
//! The [`Executor`] struct provides a high-level interface for executing SMT-LIB
//! commands with automatic theory selection based on the logic:
//!
//! ```
//! use z4_dpll::Executor;
//! use z4_frontend::parse;
//!
//! let input = r#"
//!     (set-logic QF_UF)
//!     (declare-const a Bool)
//!     (assert a)
//!     (check-sat)
//! "#;
//!
//! let commands = parse(input).unwrap();
//! let mut exec = Executor::new();
//! let outputs = exec.execute_all(&commands).unwrap();
//! assert_eq!(outputs, vec!["sat"]);
//! ```

#![warn(missing_docs)]
#![warn(clippy::all)]
#![cfg_attr(test, allow(clippy::large_stack_arrays))]

// Import safe_eprintln! from z4-core (non-panicking eprintln replacement)
#[macro_use]
extern crate z4_core;

#[allow(unused_macros, unused_macro_rules)]
#[macro_use]
mod pipeline_setup_macros;
#[allow(unused_macros)]
#[macro_use]
mod pipeline_split_handler_macros;
#[macro_use]
mod pipeline_incremental_macros;
#[macro_use]
mod pipeline_incremental_split_lazy_shared_macros;
#[macro_use]
mod pipeline_incremental_split_lazy_macros;
#[macro_use]
mod pipeline_incremental_split_assume_macros;
#[macro_use]
mod pipeline_incremental_split_eager_shared_macros;
#[allow(unused_macro_rules)]
#[macro_use]
mod pipeline_incremental_split_eager_macros;
#[allow(unused_macro_rules)]
#[macro_use]
mod pipeline_incremental_split_eager_persistent_macros;
#[macro_use]
mod pipeline_incremental_split_macros;

pub mod api;

/// Compile-time feature flag constants for downstream crate introspection.
pub mod feature_flags {
    /// Internal Alethe proof checker enabled.
    pub const PROOF_CHECKER: bool = cfg!(feature = "proof-checker");
}

mod assume_step_result;
pub(crate) mod bound_refinement;
pub(crate) mod cegqi;
mod clause_application;
mod combined_solvers;
mod construction;
mod diagnostic_trace;
mod dpll_error;
mod dpll_solve;
mod dpll_support;
mod dpll_tracing;
pub(crate) mod ematching;
pub mod executor;
mod executor_format;
pub(crate) mod executor_types;
pub(crate) mod extension;
pub(crate) mod features;
mod incremental_proof_cache;
mod incremental_state;
mod logic_detection;
pub(crate) mod memory;
pub(crate) mod minimize;
pub(crate) mod preprocess;
pub(crate) mod proof_tracker;
pub(crate) mod quantifier_manager;
pub(crate) mod sat_proof_manager;
pub(crate) mod skolemize;
mod solve_common;
mod solve_loop;
mod solve_step;
mod solve_step_result;
mod term_helpers;
mod theory_check;
mod theory_dispatch;
pub(crate) mod theory_inference;

#[cfg(test)]
mod executor_tests;

pub use api::{
    AssumptionSolveDetails, DatatypeConstructor, DatatypeField, DatatypeSort, FuncDecl, Logic,
    Model, ModelValue, SolveDetails, SolveResult, Solver as ApiSolver, SolverError,
    Sort as ApiSort, Term, VerificationLevel, VerificationSummary, VerifiedModel,
    VerifiedSolveResult,
};
// Crate-internal re-exports (used within z4-dpll, not exposed externally)
pub(crate) use sat_proof_manager::SatProofManager;

// Public API re-exports (used by downstream crates)
pub use assume_step_result::AssumeStepResult;
pub use dpll_error::DpllError;
pub use executor::Executor;
pub use executor_types::{
    ExecutorError, Result as ExecutorResult, StatValue, Statistics, UnknownReason,
};
pub use minimize::CounterexampleStyle;
pub use solve_step_result::SolveStepResult;
pub use z4_core::Proof;

pub(crate) use dpll_support::{
    cnf_lit_to_sat, debug_dpll_enabled, debug_sync_enabled, iter_var_to_term_sorted,
    DpllConstructionTimings, DpllEagerStats, DpllSatState, DpllTimings, PhaseTimer,
    PropositionalTheory, SplitLoopTimingStats,
};
#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
pub(crate) use theory_dispatch::{FinalCheckResult, TheoryCheck, TheoryDispatch};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
#[cfg(test)]
use z4_core::CnfLit;
#[cfg(test)]
use z4_core::TheoryPropagation;
#[cfg(test)]
use z4_core::TheoryResult;
use z4_core::{CnfClause, TermId, TermStore, TheorySolver};

use z4_sat::{
    ClauseTrace, Literal, SatUnknownReason, Solver as SatSolver, TlaTraceWriter, Variable,
};

use crate::diagnostic_trace::DpllDiagnosticWriter;

/// DPLL(T) solver combining SAT and theory reasoning
pub struct DpllT<'a, T: TheorySolver> {
    /// The underlying SAT solver
    sat: SatSolver,
    /// The theory solver
    theory: T,
    /// Term store used for debug verification (e.g., Farkas checking).
    ///
    /// This is `None` when constructed via [`DpllT::new`], and `Some` when constructed
    /// via [`DpllT::from_tseitin`].
    terms: Option<&'a TermStore>,
    /// Mapping from CNF variables to term IDs (HashMap for O(1) lookup)
    var_to_term: HashMap<u32, TermId>,
    /// Mapping from term IDs to CNF variables (HashMap for O(1) lookup)
    term_to_var: HashMap<TermId, u32>,
    /// Theory atoms to communicate to theory solver (stable order + unique)
    theory_atoms: Vec<TermId>,
    /// Membership set for O(1) theory-atom dedup and lookup.
    theory_atom_set: HashSet<TermId>,
    /// Cached: `Z4_DEBUG_DPLL` env var (checked once at construction)
    debug_dpll: bool,
    /// Cached: `Z4_DEBUG_SYNC` env var (checked once at construction)
    debug_sync: bool,
    /// Count of theory conflicts encountered during solving (#4705).
    theory_conflict_count: u64,
    /// Count of theory propagation clauses added during solving (#4705).
    theory_propagation_count: u64,
    /// Count of partial clause events where `term_to_literal` dropped terms (#5000).
    partial_clause_count: u64,
    /// Deterministic eager-extension counters for split-loop diagnostics (#6503).
    eager_stats: DpllEagerStats,
    /// Accumulated phase timing for DPLL(T) solve calls (#4802).
    timings: DpllTimings,
    /// Accumulated constructor timing for DPLL(T) setup work (#6364).
    construction_timings: DpllConstructionTimings,
    /// Optional DPLL(T) interaction diagnostic JSONL writer.
    diagnostic_trace: Option<DpllDiagnosticWriter>,
    /// Optional DPLL(T) TLA2 trace writer.
    dpll_tla_trace: Option<TlaTraceWriter>,
    /// Whether an internal model-scope `push()` is currently active on the theory solver.
    ///
    /// When `true`, the theory solver has an extra scope level from `sync_theory` that
    /// must be `pop()`-ed before returning from any solve method or mutating the
    /// scope stack via public `push()`/`pop()`/`reset_theory()`.
    ///
    /// This replaces the per-round `soft_reset()` approach: instead of clearing and
    /// re-asserting all theory atoms on every SAT model, we use `push/pop` to scope
    /// the model-level assertions, preserving learned theory state across rounds (#4520).
    model_scope_active: bool,
}

// Re-export the single source of truth for theory-atom routing from z4-core (#6881).
// Macros in pipeline_*_macros.rs use `$crate::is_theory_atom`, so this must be pub.
pub use z4_core::is_theory_atom;

impl<T: TheorySolver> DpllT<'_, T> {
    /// Safety bound for DPLL(T) theory refinement loops.
    ///
    /// If the SAT solver keeps producing models that the theory rejects
    /// (adding conflict clauses each time), the loop should eventually
    /// terminate because the finite set of theory lemmas is exhausted.
    /// This constant is a defensive upper bound: if we exceed it, something
    /// is diverging and we bail out with `Unknown` instead of hanging.
    const MAX_THEORY_REFINEMENTS: usize = 10_000;

    /// Create a new DPLL(T) solver with the given number of variables
    pub fn new(num_vars: usize, theory: T) -> Self {
        DpllT {
            sat: SatSolver::new(num_vars),
            theory,
            terms: None,
            var_to_term: HashMap::new(),
            term_to_var: HashMap::new(),
            theory_atoms: Vec::new(),
            theory_atom_set: HashSet::new(),
            debug_dpll: debug_dpll_enabled(),
            debug_sync: debug_sync_enabled(),
            theory_conflict_count: 0,
            theory_propagation_count: 0,
            partial_clause_count: 0,
            eager_stats: DpllEagerStats::default(),
            timings: DpllTimings::default(),
            construction_timings: DpllConstructionTimings::default(),
            diagnostic_trace: None,
            dpll_tla_trace: None,
            model_scope_active: false,
        }
    }

    /// Access the underlying SAT solver.
    pub fn sat_solver(&self) -> &SatSolver {
        &self.sat
    }

    /// Number of theory conflicts encountered during solving (#4705).
    #[must_use]
    pub fn num_theory_conflicts(&self) -> u64 {
        self.theory_conflict_count
    }

    /// Number of theory propagation clauses added during solving (#4705).
    #[must_use]
    pub fn num_theory_propagations(&self) -> u64 {
        self.theory_propagation_count
    }

    /// Last SAT-side `Unknown` reason reported by the underlying SAT solver.
    #[must_use]
    pub fn sat_unknown_reason(&self) -> Option<SatUnknownReason> {
        self.sat.last_unknown_reason()
    }

    /// Set the maximum learned clauses limit on the underlying SAT solver (#1609)
    pub fn set_max_learned_clauses(&mut self, limit: Option<usize>) {
        self.sat.set_max_learned_clauses(limit);
    }

    /// Set the maximum clause DB size limit (bytes) on the underlying SAT solver (#1609)
    pub fn set_max_clause_db_bytes(&mut self, limit: Option<usize>) {
        self.sat.set_max_clause_db_bytes(limit);
    }

    /// Set the SAT random seed used for tie-breaking in variable selection.
    pub fn set_random_seed(&mut self, seed: u64) {
        self.sat.set_random_seed(seed);
    }

    /// Enable periodic progress line emission on the underlying SAT solver.
    ///
    /// When enabled, the SAT solver emits a compact one-line status summary to
    /// stderr approximately every 5 seconds during CDCL solving.
    pub fn set_progress_enabled(&mut self, enabled: bool) {
        self.sat.set_progress_enabled(enabled);
    }

    /// Access the underlying SAT solver mutably
    pub fn sat_solver_mut(&mut self) -> &mut SatSolver {
        &mut self.sat
    }

    #[inline]
    fn freeze_var_if_needed(&mut self, var: Variable) {
        if !self.sat.is_frozen(var) {
            self.sat.freeze(var);
        }
    }

    fn internalize_registered_theory_atoms(&mut self) {
        let atoms = self.theory_atoms.clone();
        for atom in atoms {
            self.theory.internalize_atom(atom);
        }
    }

    /// Take the clause trace from the SAT solver (for SAT proof reconstruction)
    ///
    /// Returns the clause trace if one was being recorded, otherwise None.
    /// This consumes the trace from the SAT solver.
    pub fn take_clause_trace(&mut self) -> Option<ClauseTrace> {
        self.sat.take_clause_trace()
    }

    /// Get a reference to the var_to_term mapping
    pub fn var_to_term(&self) -> &HashMap<u32, TermId> {
        &self.var_to_term
    }

    /// Clone a point-in-time var->term mapping snapshot.
    ///
    /// This is used by proof reconstruction paths that need an owned map after
    /// the DPLL wrapper is dropped.
    #[must_use]
    pub(crate) fn clone_var_to_term_snapshot(&self) -> HashMap<u32, TermId> {
        self.var_to_term.clone()
    }

    /// Access the underlying theory solver.
    pub fn theory_solver(&self) -> &T {
        &self.theory
    }

    /// Access the underlying theory solver mutably.
    pub fn theory_solver_mut(&mut self) -> &mut T {
        &mut self.theory
    }

    /// Add a clause to the solver
    pub fn add_clause(&mut self, literals: Vec<Literal>) {
        self.sat.add_clause(literals);
    }

    /// Add a CNF clause to the solver
    pub fn add_cnf_clause(&mut self, clause: &CnfClause) {
        let lits: Vec<Literal> = clause.0.iter().copied().map(Literal::from_dimacs).collect();
        self.sat.add_clause(lits);
    }

    /// Register a theory atom
    ///
    /// Theory atoms are terms that the theory solver needs to know about.
    /// When the SAT solver assigns a value to the corresponding variable,
    /// the theory solver is informed.
    pub fn register_theory_atom(&mut self, term: TermId, var: u32) {
        self.var_to_term.insert(var, term);
        self.term_to_var.insert(term, var);
        self.freeze_var_if_needed(Variable::new(var));
        // Keep theory atom order stable by appending only newly seen terms.
        // O(1)-amortized insertion avoids the O(n^2) Vec::insert pattern in
        // incremental LIA split registration (#4468).
        if self.theory_atom_set.insert(term) {
            self.theory_atoms.push(term);
            self.theory.internalize_atom(term);
        }
        // Boost VSIDS activity for theory atoms so the DPLL solver decides them
        // before pure Boolean encoding variables (#4919, #7982). Without this,
        // all variables start at activity 0 and the decision heuristic treats
        // Tseitin encoding vars and theory atoms equally. Theory atoms should
        // be decided first because: (1) they feed the theory solver which can
        // generate conflicts and propagations that prune the search space,
        // (2) Boolean encoding vars are determined by BCP once theory atoms
        // are assigned. Z3 does this via theory_var_init_value + mk_diseq.
        //
        self.sat.bump_variable_activity(Variable::new(var));
    }

    /// Get the term ID for a SAT variable, if it exists
    pub fn term_for_var(&self, var: Variable) -> Option<TermId> {
        self.var_to_term.get(&var.id()).copied()
    }

    /// Get the SAT variable for a term ID, if it exists
    pub fn var_for_term(&self, term: TermId) -> Option<Variable> {
        self.term_to_var.get(&term).map(|&v| Variable::new(v))
    }

    /// Convert a theory literal to a SAT literal
    fn term_to_literal(&self, term: TermId, value: bool) -> Option<Literal> {
        self.var_for_term(term).map(|var| {
            if value {
                Literal::positive(var)
            } else {
                Literal::negative(var)
            }
        })
    }

    /// Convert a theory literal to a SAT literal, dynamically registering a
    /// new SAT variable if the term has no mapping yet (#6546).
    ///
    /// This is the mutable counterpart of [`term_to_literal`] for use in
    /// `check_theory_core` and other paths where `&mut self` is available.
    /// Array axiom terms generated during theory checking may not have been
    /// registered during formula preprocessing, so the lazy `step` solve
    /// mode must register them here to avoid dropping propagation clauses
    /// (the "partial clause" problem).
    pub(crate) fn term_to_literal_or_register(&mut self, term: TermId, value: bool) -> Literal {
        let var = if let Some(&var_idx) = self.term_to_var.get(&term) {
            Variable::new(var_idx)
        } else {
            let var = self.sat.new_var();
            self.register_theory_atom(term, var.id());
            var
        };
        if value {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        }
    }
}

#[cfg(test)]
mod dpll_tests;

#[cfg(kani)]
mod dpll_kani;
