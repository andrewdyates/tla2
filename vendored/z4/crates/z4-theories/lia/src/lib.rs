// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Z4 LIA - Linear Integer Arithmetic theory solver
//!
//! Implements branch-and-bound over LRA for integer arithmetic,
//! following the DPLL(T) approach where the SAT solver handles branching.
//!
//! ## Algorithm Overview
//!
//! The solver uses lazy branch-and-bound with cutting planes:
//!
//! 1. Solve the LRA (Linear Real Arithmetic) relaxation
//! 2. If UNSAT, return UNSAT (integers can't satisfy it either)
//! 3. If SAT, check if all integer variables have integer values
//! 4. If all integers are satisfied, return SAT
//! 5. Otherwise, try cutting planes (Gomory, then HNF)
//! 6. If no cuts, return a split request for branch-and-bound
//!
//! ## Cutting Planes
//!
//! - **Gomory cuts**: Derived from the simplex tableau. Fast but limited when
//!   the tableau involves slack variables (internal to simplex).
//! - **HNF cuts**: Derived from the original constraint matrix using Hermite
//!   Normal Form. Works even when Gomory cuts fail due to slack variables.
//!
//! The DPLL(T) framework handles the branching by backtracking on the conflict
//! and trying alternative Boolean assignments.

#![warn(missing_docs)]
#![warn(clippy::all)]

// Import safe_eprintln! from z4-core (non-panicking eprintln replacement)
#[macro_use]
extern crate z4_core;

mod assertion_view;
mod bounds;
mod branching;
mod check;
mod cuts;
mod dioph;
mod dioph_bridge;
mod dioph_substitution;
mod dioph_tighten;
mod enumeration;
mod gcd;
mod gcd_accumulative;
mod gcd_tableau;
mod hnf;
mod linear_collect;
mod modular;
mod modular_bounds;
mod nelson_oppen;
mod parsing;
mod state;
mod theory_impl;
mod two_var;
mod types;

pub(crate) use types::{
    gcd_of_abs, lia_debug_flags, positive_mod, CutScopeState, DirectEnumResult, IneqOp,
    LinearCoeffs, SubstitutionMap, SubstitutionTriple,
};
pub use types::{DiophState, HnfCutKey, LiaModel, LiaSolver, LiaTimings, StoredCut};

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use z4_core::FarkasAnnotation;
use z4_core::{
    propagate_tight_bound_equalities, unwrap_not, DiscoveredEquality, EqualityPropagationResult,
    Sort, SplitRequest, TheoryConflict, TheoryLit, TheoryPropagation, TheoryResult, TheorySolver,
};
use z4_lra::{Bound, GcdRowInfo, LraSolver};

impl<'a> LiaSolver<'a> {
    /// Create a new LIA solver
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        let mut lra = LraSolver::new(terms);
        lra.set_integer_mode(true);
        LiaSolver {
            terms,
            lra,
            integer_vars: HashSet::new(),
            int_constant_terms: HashMap::new(),
            asserted: Vec::new(),
            scopes: Vec::new(),
            cut_scopes: Vec::new(),
            cut_state_scopes: Vec::new(),
            gomory_iterations: 0,
            // Keep Gomory as a quick first pass; avoid burning entire checks on cycling cuts.
            max_gomory_iterations: 8,
            hnf_iterations: 0,
            max_hnf_iterations: 50, // HNF is more expensive, limit more
            seen_hnf_cuts: HashSet::new(),
            learned_cuts: Vec::new(),
            dioph_equality_key: Vec::new(),
            dioph_safe_dependent_vars: HashSet::new(),
            dioph_cached_substitutions: Vec::new(),
            dioph_cached_modular_gcds: Vec::new(),
            dioph_cached_reasons: Vec::new(),
            pending_equalities: Vec::new(),
            propagated_equality_pairs: HashSet::new(),
            shared_equalities: Vec::new(),
            skip_shared_algebraic: false,
            timeout_callback: None,
            direct_enum_witness: None,
            // #6359: Use process-level cached env vars (OnceLock) to avoid
            // syscalls on every DPLL(T) iteration.
            debug_lia: lia_debug_flags().debug_lia,
            debug_lia_branch: lia_debug_flags().debug_lia_branch,
            debug_lia_check: lia_debug_flags().debug_lia_check,
            debug_lia_nelson_oppen: lia_debug_flags().debug_lia_nelson_oppen,
            debug_patch: lia_debug_flags().debug_patch,
            debug_gcd: lia_debug_flags().debug_gcd,
            debug_gcd_tab: lia_debug_flags().debug_gcd_tab,
            debug_dioph: lia_debug_flags().debug_dioph,
            debug_hnf: lia_debug_flags().debug_hnf,
            debug_mod: lia_debug_flags().debug_mod,
            debug_enum: lia_debug_flags().debug_enum,
            assertion_view_cache: None,
            // Per-theory runtime statistics (#4706)
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
        }
    }

    /// Number of learned HNF cuts stored across soft resets.
    /// Used by combined solver tests to verify cut preservation (#3510).
    pub fn learned_cut_count(&self) -> usize {
        self.learned_cuts.len()
    }

    /// Number of seen HNF cut keys (deduplication set).
    /// Used by combined solver tests to verify cut preservation (#3510).
    pub fn seen_hnf_cut_count(&self) -> usize {
        self.seen_hnf_cuts.len()
    }

    /// Enable combined theory mode on the inner LRA solver.
    /// See [\`LraSolver::set_combined_theory_mode\`] for details.
    pub fn set_combined_theory_mode(&mut self, enabled: bool) {
        self.lra.set_combined_theory_mode(enabled);
    }

    /// Skip shared equalities in `detect_algebraic_equalities` (#6282).
    ///
    /// In AUFLIA mode, array store axioms create dense shared equality systems
    /// (e.g., `select(store(a,i,v),i) = v` for every store). Gaussian elimination
    /// on these produces O(n²) derived equalities that flood EUF with conflicts,
    /// preventing N-O convergence. Disabling shared equality processing in the
    /// algebraic detection lets the array solver handle these relationships directly.
    pub fn set_skip_shared_algebraic(&mut self, skip: bool) {
        self.skip_shared_algebraic = skip;
    }

    /// Build a fresh assertion view from current asserted literals.
    /// Returns an owned view — callers in `for` loops benefit from temporary lifetime extension.
    fn assertion_view(&self) -> assertion_view::AssertionView {
        assertion_view::AssertionView::build(self.terms, &self.asserted)
    }

    /// Invalidate the assertion view cache (called when `asserted` changes).
    fn invalidate_assertion_view(&mut self) {
        self.assertion_view_cache = None;
    }

    /// Get timing breakdown for LIA solving phases (#4794).
    pub fn timings(&self) -> &LiaTimings {
        // Stub: real timing instrumentation tracked separately.
        static DEFAULT: LiaTimings = LiaTimings {
            simplex: std::time::Duration::ZERO,
            gomory: std::time::Duration::ZERO,
            hnf: std::time::Duration::ZERO,
            dioph: std::time::Duration::ZERO,
        };
        &DEFAULT
    }

    /// Set a timeout callback for cooperative interruption.
    ///
    /// The callback is checked periodically during the branch-and-bound loop.
    /// When it returns `true`, the theory check returns `z4_core::TheoryResult::Unknown` at the
    /// next checkpoint.
    ///
    /// # Example
    /// ```
    /// # use z4_core::term::TermStore;
    /// # use z4_lia::LiaSolver;
    /// # let terms = TermStore::new();
    /// # let mut solver = LiaSolver::new(&terms);
    /// let start = std::time::Instant::now();
    /// let timeout = std::time::Duration::from_secs(5);
    /// # let timeout = std::time::Duration::from_secs(0);
    /// solver.set_timeout_callback(move || start.elapsed() >= timeout);
    /// # assert!(matches!(
    /// #     z4_core::TheorySolver::check(&mut solver),
    /// #     z4_core::TheoryResult::Unknown
    /// # ));
    /// ```
    pub fn set_timeout_callback<F: Fn() -> bool + 'static>(&mut self, callback: F) {
        self.timeout_callback = Some(Box::new(callback));
    }

    /// Check if the solver should abort due to timeout.
    fn should_timeout(&self) -> bool {
        self.timeout_callback.as_ref().is_some_and(|cb| cb())
    }

    /// Return whether this check-iteration may attempt Gomory cuts.
    ///
    /// This intentionally blocks Gomory once cube testing has been attempted.
    /// Even when cube testing fails and bounds are popped, prior relaxations of
    /// this guard caused false UNSAT regressions on modular workloads (#3073).
    fn should_try_gomory(&self, cube_tried: bool) -> bool {
        self.gomory_iterations < self.max_gomory_iterations && !cube_tried
    }

    /// Build a deterministic mapping between integer variable TermIds and
    /// contiguous indices. Sorted by TermId for reproducible behavior.
    fn build_var_index(&self) -> (HashMap<TermId, usize>, Vec<TermId>) {
        let mut term_to_idx = HashMap::new();
        let mut idx_to_term = Vec::new();
        let mut int_vars: Vec<TermId> = self.integer_vars.iter().copied().collect();
        int_vars.sort_by_key(|t| t.0);
        for (idx, term) in int_vars.into_iter().enumerate() {
            term_to_idx.insert(term, idx);
            idx_to_term.push(term);
        }
        debug_assert_eq!(
            term_to_idx.len(),
            idx_to_term.len(),
            "BUG: build_var_index bijection violated: term_to_idx has {} entries, idx_to_term has {}",
            term_to_idx.len(),
            idx_to_term.len()
        );
        debug_assert_eq!(
            idx_to_term.len(),
            self.integer_vars.len(),
            "BUG: build_var_index lost variables: {} indexed vs {} registered",
            idx_to_term.len(),
            self.integer_vars.len()
        );
        (term_to_idx, idx_to_term)
    }

    /// Register a term as an integer variable
    ///
    /// Should be called for all variables declared with Int sort.
    pub fn register_integer_var(&mut self, term: TermId) {
        self.integer_vars.insert(term);
    }

    /// Check if a rational value is an integer
    fn is_integer(val: &BigRational) -> bool {
        val.denom().is_one()
    }

    /// Detect immediate integer infeasibility from bounds alone.
    ///
    /// For integer variables, strict/real bounds can imply a tightened integer interval.
    /// Example: `x > 5` and `x < 6` with `x : Int` is immediately UNSAT.
    ///
    /// Returns a `TheoryConflict` with Farkas coefficients for interpolation.
    /// For simple bounds conflicts on a single variable, both bounds get coefficient 1.
    fn check_integer_bounds_conflict(&self) -> Option<TheoryConflict> {
        use num_rational::Rational64;

        // Sort integer vars for deterministic iteration order
        let mut int_vars: Vec<_> = self.integer_vars.iter().copied().collect();
        int_vars.sort_by_key(|t| t.0);

        for term in int_vars {
            let Some((lower, upper)) = self.lra.get_bounds(term) else {
                continue;
            };

            let lower_int = lower.as_ref().map(Self::effective_int_lower);
            let upper_int = upper.as_ref().map(Self::effective_int_upper);

            if let (Some(li), Some(ui)) = (lower_int, upper_int) {
                if li > ui {
                    let mut literals = Vec::new();
                    let mut coefficients = Vec::new();

                    if let Some(lb) = lower {
                        // Add ALL reasons from the bound
                        for (reason, reason_value) in lb.reasons.iter().zip(&lb.reason_values) {
                            if !reason.is_sentinel() {
                                literals.push(TheoryLit::new(*reason, *reason_value));
                                coefficients.push(Rational64::from(1));
                            }
                        }
                    }
                    if let Some(ub) = upper {
                        for (reason, reason_value) in ub.reasons.iter().zip(&ub.reason_values) {
                            if !reason.is_sentinel() {
                                literals.push(TheoryLit::new(*reason, *reason_value));
                                coefficients.push(Rational64::from(1));
                            }
                        }
                    }

                    debug_assert!(
                        !literals.is_empty(),
                        "BUG: check_integer_bounds_conflict: empty conflict literals for term {term:?} \
                         with integer bounds [{li}, {ui}]"
                    );
                    let farkas = FarkasAnnotation::new(coefficients);
                    return Some(TheoryConflict::with_farkas(literals, farkas));
                }
            }
        }

        None
    }

    /// Register terms from a UF-int equality for Nelson-Oppen tracking (#3581).
    ///
    /// This collects integer variables and constants from both sides of the
    /// equality without adding any constraints. Used when a negated UF-int
    /// equality is asserted (value=false) so that constants like 80 in
    /// `(not (= (inv 2) 80))` are available for tight-bound pairing.
    pub fn register_nelson_oppen_terms(&mut self, lhs: TermId, rhs: TermId) {
        self.collect_integer_vars(lhs);
        self.collect_integer_vars(rhs);
    }

    /// Extract integer variables from a term and its subterms.
    /// Also collects integer constant terms for N-O propagation (#3581).
    fn collect_integer_vars(&mut self, term: TermId) {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => {
                // Track integer constants for Nelson-Oppen propagation (#3581).
                // These allow propagate_equalities to pair derived tight bounds
                // (e.g., f(1) = 0) with existing constant terms (TermId for 0).
                self.int_constant_terms.entry(n.clone()).or_insert(term);
            }
            TermData::Var(_, _) => {
                // Check the sort of this term to see if it's an integer
                if matches!(self.terms.sort(term), Sort::Int) {
                    self.integer_vars.insert(term);
                }
            }
            TermData::App(sym, args) => {
                // Treat Int-sorted "opaque" arithmetic terms as integer variables.
                //
                // In AUFLIA/Nelson-Oppen, terms like (f x) : Int appear inside arithmetic
                // constraints (e.g., (< (f x) y)). The linear parser treats these terms as
                // atomic variables, so they must be tracked as integer vars for:
                // - direct enumeration (must not treat them as 0)
                // - integrality checks / branch-and-bound
                if matches!(self.terms.sort(term), Sort::Int) {
                    let is_atomic_var = match sym.name() {
                        // Linear arithmetic ops are decomposed into their arguments.
                        "+" | "-" => false,
                        "*" => {
                            // Match collect_linear_coeffs(): treat non-linear multiplication as
                            // an opaque variable; otherwise decompose.
                            let non_const_args = args
                                .iter()
                                .filter(|&&arg| {
                                    !matches!(
                                        self.terms.get(arg),
                                        TermData::Const(Constant::Int(_) | Constant::Rational(_))
                                    )
                                })
                                .count();
                            non_const_args > 1
                        }
                        // Everything else (UF apps, select, div/mod, etc) is opaque to linear LIA.
                        _ => true,
                    };
                    if is_atomic_var {
                        self.integer_vars.insert(term);
                    }
                }
                for &arg in args {
                    self.collect_integer_vars(arg);
                }
            }
            TermData::Let(_, body) => {
                self.collect_integer_vars(*body);
            }
            TermData::Not(inner) => {
                self.collect_integer_vars(*inner);
            }
            TermData::Ite(cond, then_branch, else_branch) => {
                self.collect_integer_vars(*cond);
                self.collect_integer_vars(*then_branch);
                self.collect_integer_vars(*else_branch);
            }
            _ => {}
        }
    }

    /// Equality-dense systems benefit from deeper HNF exploration.
    /// We treat a system as dense once equalities cover at least half of variables.
    fn is_equality_dense(num_equalities: usize, num_vars: usize) -> bool {
        num_vars > 0 && num_equalities.saturating_mul(2) >= num_vars
    }

    fn hnf_iteration_budget(num_equalities: usize, num_vars: usize) -> usize {
        if Self::is_equality_dense(num_equalities, num_vars) {
            20
        } else {
            2
        }
    }

    /// Extract the current model if satisfiable
    ///
    /// Returns None if the last check was not SAT or if integer constraints
    /// are not satisfied.
    pub fn extract_model(&self) -> Option<LiaModel> {
        let debug = self.debug_lia;

        if let Some(model) = &self.direct_enum_witness {
            return Some(model.clone());
        }

        let lra_model = self.lra.extract_model();
        let mut values = HashMap::new();

        if debug {
            safe_eprintln!(
                "[LIA] extract_model: lra_model has {} values, integer_vars has {} entries",
                lra_model.values.len(),
                self.integer_vars.len()
            );
            for &term in &self.integer_vars {
                safe_eprintln!("[LIA] integer_var: term {}", term.0);
            }
        }

        // Convert rational values to integers, checking constraints
        for (&term, val) in &lra_model.values {
            if debug {
                safe_eprintln!(
                    "[LIA] checking term {}: in integer_vars={}",
                    term.0,
                    self.integer_vars.contains(&term)
                );
            }
            if self.integer_vars.contains(&term) {
                if Self::is_integer(val) {
                    if debug {
                        safe_eprintln!("[LIA] term {} -> int value {}", term.0, val.numer());
                    }
                    values.insert(term, val.numer().clone());
                } else {
                    // Integer constraint violated
                    if debug {
                        safe_eprintln!("[LIA] term {} has non-integer value {}", term.0, val);
                    }
                    return None;
                }
            }
        }

        if debug {
            safe_eprintln!("[LIA] final model has {} values", values.len());
        }
        // Every registered integer variable that appears in the LRA model should
        // have an integer value in our extracted model. Missing variables indicate
        // a term registration or model extraction bug.
        debug_assert!(
            self.integer_vars
                .iter()
                .all(|v| !lra_model.values.contains_key(v) || values.contains_key(v)),
            "BUG: extract_model: integer variable present in LRA model but missing from LIA model"
        );
        Some(LiaModel { values })
    }

    /// Get the underlying LRA solver
    pub fn lra_solver(&self) -> &LraSolver {
        &self.lra
    }

    /// Collect bound conflicts from the underlying LRA relaxation.
    pub fn collect_all_bound_conflicts(&self, skip_first: bool) -> Vec<TheoryConflict> {
        self.lra.collect_all_bound_conflicts(skip_first)
    }

    /// Get mutable access to the underlying LRA solver
    ///
    /// Used by NIA to add tangent plane constraints directly.
    pub fn lra_solver_mut(&mut self) -> &mut LraSolver {
        &mut self.lra
    }

    /// Count integer variables that are currently fixed (lower bound == upper bound).
    ///
    /// Used by the iterative Dioph tightening loop to detect when tightening
    /// has fixed new variables, which signals that re-running the Dioph solver
    /// may discover new substitutions (Z3's continue_with_check pattern).
    fn count_fixed_integer_vars(&self) -> usize {
        let mut count = 0;
        for &term_id in &self.integer_vars {
            if let Some((Some(lb), Some(ub))) = self.lra.get_bounds(term_id) {
                if lb.value == ub.value {
                    count += 1;
                }
            }
        }
        count
    }

    /// Count the number of equality constraints in the asserted literals.
    ///
    /// Used to detect equality-dense problems where more aggressive HNF
    /// cut generation is beneficial.
    fn count_equalities(&self) -> usize {
        let mut count = 0;
        for &(literal, value) in &self.asserted {
            if !value {
                continue;
            }

            if let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) {
                if name == "=" && args.len() == 2 {
                    count += 1;
                }
            }
        }
        count
    }

    /// Compute a stable key for the currently asserted equality atoms.
    ///
    /// Used to avoid re-running Diophantine solving when only inequalities change
    /// (common during branch-and-bound).
    fn equality_key(&self) -> Vec<TermId> {
        let mut key: Vec<TermId> = Vec::new();

        for &(literal, value) in &self.asserted {
            if !value {
                continue;
            }

            if let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) {
                if name == "=" && args.len() == 2 {
                    key.push(literal);
                }
            }
        }

        key.sort_by_key(|t| t.0);
        key.dedup();
        key
    }
}

#[cfg(kani)]
mod verification;

#[cfg(test)]
mod dioph_conflict_tests;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
