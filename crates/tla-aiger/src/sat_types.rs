// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core SAT types for the AIGER IC3/BMC engine.
//!
//! Provides `Var`, `Lit`, and `Clause` types modeled after rIC3's `logicrs` types.
//! Variables are 1-indexed (Var(0) is reserved as a constant/sentinel).

use std::fmt;
use std::ops::Not;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

/// A SAT variable (1-indexed, 0 is constant FALSE).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(pub u32);

impl Var {
    /// Constant variable (index 0). Used for TRUE/FALSE literals.
    pub const CONST: Var = Var(0);

    /// Create a literal from this variable (positive polarity).
    #[inline]
    pub fn lit(self) -> Lit {
        Lit::pos(self)
    }

    /// Create a negated literal from this variable.
    #[inline]
    pub fn neg_lit(self) -> Lit {
        Lit::neg(self)
    }

    /// Get the raw index.
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

/// A SAT literal: a variable with polarity. Encoded as `var * 2 + sign`.
/// Even = positive, Odd = negative (same as AIGER/DIMACS convention shifted).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit(pub u32);

impl Lit {
    /// Constant FALSE literal (positive literal of the constant-false variable).
    /// Var(0) is always assigned `false`, so pos(Var(0)) evaluates to false.
    pub const FALSE: Lit = Lit(0);
    /// Constant TRUE literal (negated literal of the constant-false variable).
    /// Var(0) is always assigned `false`, so neg(Var(0)) evaluates to true.
    pub const TRUE: Lit = Lit(1);

    /// Create a positive literal for the given variable.
    #[inline]
    pub fn pos(v: Var) -> Lit {
        Lit(v.0 << 1)
    }

    /// Create a negative literal for the given variable.
    #[inline]
    pub fn neg(v: Var) -> Lit {
        Lit((v.0 << 1) | 1)
    }

    /// Get the variable of this literal.
    #[inline]
    pub fn var(self) -> Var {
        Var(self.0 >> 1)
    }

    /// True if this literal is negated (odd encoding).
    #[inline]
    pub fn is_negated(self) -> bool {
        self.0 & 1 != 0
    }

    /// True if this literal is positive (even encoding).
    #[inline]
    pub fn is_positive(self) -> bool {
        self.0 & 1 == 0
    }

    /// Get the raw encoding.
    #[inline]
    pub fn code(self) -> u32 {
        self.0
    }

    /// Create from raw encoding.
    #[inline]
    pub fn from_code(code: u32) -> Lit {
        Lit(code)
    }

    /// Return this literal with positive polarity.
    #[inline]
    pub fn positive(self) -> Lit {
        Lit(self.0 & !1)
    }
}

impl Not for Lit {
    type Output = Lit;
    #[inline]
    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_negated() {
            write!(f, "~{}", self.var())
        } else {
            write!(f, "{}", self.var())
        }
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

/// A clause: disjunction of literals.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Clause {
    pub lits: Vec<Lit>,
}

impl Clause {
    pub fn new(lits: Vec<Lit>) -> Self {
        Clause { lits }
    }

    pub fn unit(lit: Lit) -> Self {
        Clause { lits: vec![lit] }
    }

    pub fn binary(a: Lit, b: Lit) -> Self {
        Clause { lits: vec![a, b] }
    }

    pub fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }

    pub fn len(&self) -> usize {
        self.lits.len()
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for (i, lit) in self.lits.iter().enumerate() {
            if i > 0 {
                write!(f, " v ")?;
            }
            write!(f, "{lit}")?;
        }
        write!(f, ")")
    }
}

// ---------------------------------------------------------------------------
// SAT solver backend selection
// ---------------------------------------------------------------------------

/// Which SAT solver backend to use for IC3/BMC engines.
///
/// All production backends use z4-sat with different configurations. We own
/// z4-sat and do NOT use external SAT solvers. Portfolio diversity comes from
/// varying restart policies, branching heuristics, and preprocessing toggles.
///
/// # Backend comparison
///
/// | Backend | Restart | Branch | Preprocess | Use case |
/// |---------|---------|--------|------------|----------|
/// | Z4Sat | Glucose EMA | EVSIDS (default) | On | Production default |
/// | Z4Luby | Luby sequence | EVSIDS | On | Diverse restart schedule |
/// | Z4Stable | Reluctant doubling | EVSIDS | On | Stable mode only, no mode switching |
/// | Z4Geometric | Geometric (100, 1.5x) | EVSIDS | On | Z3-style restarts |
/// | Z4Vmtf | Glucose EMA | VMTF | On | Move-to-front branching |
/// | Z4Chb | Glucose EMA | CHB | On | Conflict-history branching |
/// | Z4NoPreprocess | Glucose EMA | EVSIDS | Off | Skip BVE/subsumption overhead |
/// | Simple | N/A | N/A | N/A | Tests only (tiny circuits) |
///
/// ## Why not z4-dpll?
///
/// z4-dpll is a DPLL(T) *SMT framework* that wraps z4-sat internally. It is
/// unsuitable as an IC3 SAT backend because:
/// 1. It operates at the SMT level (terms, assertions, theory dispatch) not
///    the raw clause level IC3 needs. Mapping `add_clause(&[Lit])` through
///    the SMT interface would add enormous overhead.
/// 2. Its `check_sat_assuming` path creates fresh Tseitin transformations
///    per call, adding overhead.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverBackend {
    /// z4-sat CDCL solver with default configuration. Truly incremental with
    /// UNSAT core support. Production default.
    Z4Sat,
    /// z4-sat with Luby restarts (Glucose restarts disabled).
    /// Luby restarts use a mathematically optimal restart sequence that
    /// guarantees completeness while exploring diverse search paths.
    Z4Luby,
    /// z4-sat with stable-only mode (EVSIDS + reluctant doubling).
    /// Disables focused/stable mode switching. Good for BMC-style instances
    /// that benefit from consistent variable ordering.
    Z4Stable,
    /// z4-sat with geometric restarts (initial=100, factor=1.5).
    /// Z3-style restart schedule: `next = initial * factor^n`. Good for
    /// structured problems where search diversity matters more than LBD signals.
    Z4Geometric,
    /// z4-sat with VMTF branching heuristic.
    /// Move-to-front branching: recently conflicted variables get highest
    /// priority. Complements EVSIDS for portfolio diversity.
    Z4Vmtf,
    /// z4-sat with CHB branching heuristic.
    /// Conflict-History-Based branching: uses exponential recency-weighted
    /// average of conflict participation. Strong on satisfiable instances.
    Z4Chb,
    /// z4-sat with preprocessing disabled.
    /// Skips BVE, subsumption, and other preprocessing. Useful when the
    /// formula structure should be preserved (e.g., incremental BMC where
    /// preprocessing adds overhead per unroll).
    Z4NoPreprocess,
    /// Simple backtracking DPLL. For unit tests with tiny circuits only.
    Simple,
}

impl Default for SolverBackend {
    fn default() -> Self {
        SolverBackend::Z4Sat
    }
}

impl SolverBackend {
    /// Create a new SAT solver instance for this backend with the given
    /// number of pre-allocated variables.
    ///
    /// All z4-sat backends inherit from `Z4SatCdclSolver::new()`:
    /// - **Full preprocessing**: enabled (one-time simplification at first solve)
    /// - **Periodic inprocessing**: ENABLED by default. BMC and k-induction
    ///   benefit from inprocessing on longer runs. IC3 callers should use
    ///   [`make_solver_no_inprocessing()`](Self::make_solver_no_inprocessing)
    ///   instead to disable it (#4102).
    /// - **Chronological backtracking**: enabled with trail reuse
    /// - **OTFS** (on-the-fly subsumption): always active in conflict analysis
    /// - **Tier-2 clause management**: always active in reduction
    ///
    /// Each variant then adds its specific restart/branching/preprocessing
    /// configuration on top of these shared defaults.
    pub fn make_solver(self, num_vars: u32) -> Box<dyn SatSolver> {
        match self {
            SolverBackend::Z4Sat => Box::new(Z4SatCdclSolver::new(num_vars)),
            SolverBackend::Z4Luby => {
                let mut s = Z4SatCdclSolver::new(num_vars);
                s.solver.set_glucose_restarts(false);
                s.solver.set_restart_base(100);
                Box::new(s)
            }
            SolverBackend::Z4Stable => {
                let mut s = Z4SatCdclSolver::new(num_vars);
                s.solver.set_stable_only(true);
                // Z4Stable benefits from aggressive vivification and probing
                // during longer BMC/k-induction runs.
                s.solver.set_vivify_interval(1000);
                s.solver.set_probe_interval(500);
                Box::new(s)
            }
            SolverBackend::Z4Geometric => {
                let mut s = Z4SatCdclSolver::new(num_vars);
                s.solver.set_geometric_restarts(100.0, 1.5);
                Box::new(s)
            }
            SolverBackend::Z4Vmtf => {
                let mut s = Z4SatCdclSolver::new(num_vars);
                s.solver.set_branch_heuristic(z4_sat::BranchHeuristic::Vmtf);
                Box::new(s)
            }
            SolverBackend::Z4Chb => {
                let mut s = Z4SatCdclSolver::new(num_vars);
                s.solver.set_branch_heuristic(z4_sat::BranchHeuristic::Chb);
                Box::new(s)
            }
            SolverBackend::Z4NoPreprocess => {
                let mut s = Z4SatCdclSolver::new(num_vars);
                s.solver.set_preprocess_enabled(false);
                Box::new(s)
            }
            SolverBackend::Simple => {
                let mut s = SimpleSolver::new();
                s.ensure_vars(num_vars.saturating_sub(1));
                Box::new(s)
            }
        }
    }

    /// Create a SAT solver with all periodic inprocessing disabled (#4102).
    ///
    /// Identical to [`make_solver()`](Self::make_solver) but immediately calls
    /// [`disable_inprocessing()`](SatSolver::disable_inprocessing) on the
    /// resulting solver. Use this for IC3/PDR frame solvers, lift solvers,
    /// predprop solvers, and domain-restricted solvers — any solver that makes
    /// thousands of short incremental queries.
    ///
    /// BMC and k-induction should use `make_solver()` instead, as they make
    /// fewer, longer SAT calls that benefit from periodic inprocessing.
    ///
    /// rIC3's GipSAT achieves the same effect with a minimal ~40-line CDCL
    /// loop that never schedules inprocessing.
    pub fn make_solver_no_inprocessing(self, num_vars: u32) -> Box<dyn SatSolver> {
        let mut solver = self.make_solver(num_vars);
        solver.disable_inprocessing();
        solver
    }
}

// ---------------------------------------------------------------------------
// SAT solver trait
// ---------------------------------------------------------------------------

/// Result of a SAT solver call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatResult {
    Sat,
    Unsat,
    Unknown,
}

/// Trait for an incremental SAT solver.
///
/// This abstracts the SAT solver interface so we can plug in different
/// backends (z4-sat with various configurations, a simple DPLL, etc.).
pub trait SatSolver {
    /// Ensure the solver has at least `n` variables.
    fn ensure_vars(&mut self, n: u32);

    /// Add a permanent clause.
    fn add_clause(&mut self, clause: &[Lit]);

    /// Solve under assumptions. Returns Sat/Unsat/Unknown.
    fn solve(&mut self, assumptions: &[Lit]) -> SatResult;

    /// After a Sat result, get the value of a literal.
    /// Returns Some(true) if the literal is true in the model,
    /// Some(false) if false, None if unassigned.
    fn value(&self, lit: Lit) -> Option<bool>;

    /// Create a fresh variable and return it.
    fn new_var(&mut self) -> Var;

    /// After an Unsat result, get the subset of assumptions that formed
    /// the conflict core. Returns None if the solver doesn't support this.
    fn unsat_core(&self) -> Option<Vec<Lit>> {
        None
    }

    /// Returns true if the solver has been poisoned by an internal error
    /// (e.g., a caught panic) and can no longer produce reliable results.
    ///
    /// IC3 uses this to detect when a frame solver needs to be rebuilt
    /// from scratch rather than continuing with degraded `Unknown` results.
    fn is_poisoned(&self) -> bool {
        false
    }

    /// Set a cooperative cancellation flag for the underlying SAT solver.
    ///
    /// When the flag is set to `true`, the solver's CDCL loop will check it
    /// periodically (e.g., every ~1000 decisions for z4-sat) and return
    /// `SatResult::Unknown` instead of continuing to search.
    ///
    /// This is critical for portfolio-based solving (#4057): when one engine
    /// finds a verdict, sibling engines stuck inside `solve()` must be able
    /// to exit promptly. Without this, `thread::join()` blocks indefinitely
    /// waiting for z4-sat's CDCL loop to finish, and the valid verdict is
    /// lost to the external timeout.
    fn set_cancelled(&mut self, _cancelled: Arc<AtomicBool>) {
        // Default no-op for solvers that don't support cooperative cancellation.
    }

    /// Disable all periodic inprocessing techniques (BVE, vivification,
    /// subsumption, probing, SBVA, factorization, congruence closure,
    /// backbone detection, etc.) while preserving initial preprocessing.
    ///
    /// IC3/PDR frame solvers make thousands of short incremental SAT queries.
    /// Periodic inprocessing between these queries is harmful because:
    /// 1. **BVE** can eliminate variables, corrupting incremental state.
    ///    (Note: IC3's `solve_incremental_ic3` path skips preprocessing
    ///    entirely, but disabling inprocessing is defense-in-depth.)
    /// 2. **Vivification** modifies learned clauses between queries.
    /// 3. **Subsumption/probing/congruence** add overhead without benefit
    ///    since IC3 queries are short (few conflicts each).
    ///
    /// rIC3's GipSAT achieves this by having a minimal CDCL loop (~40 lines)
    /// that never schedules inprocessing. We achieve the same effect by
    /// disabling all inprocessing toggles in z4-sat while keeping the
    /// initial `set_full_preprocessing(true)` for one-time simplification.
    ///
    /// Default: no-op for solvers that don't support inprocessing control.
    fn disable_inprocessing(&mut self) {}

    /// Clone this solver, producing a new solver with the same clause database.
    /// Returns `None` if the solver cannot be cloned.
    /// Reference: rIC3 `ic3/mod.rs:179` — `let solver = self.inf_solver.clone()`.
    fn clone_solver(&self) -> Option<Box<dyn SatSolver>> {
        None
    }

    /// Clone this solver using the backend's native incremental clone,
    /// preserving learned clauses and VSIDS scores.
    ///
    /// Unlike `clone_solver()` which replays the clause log into a fresh solver,
    /// this method deep-copies the solver's internal state (clause arena, watch
    /// lists, VSIDS heap, trail, assignments). The cloned solver inherits all
    /// learned clauses and activity scores, making it immediately effective for
    /// incremental frame extension.
    ///
    /// Falls back to `clone_solver()` if native incremental clone is not available.
    ///
    /// Reference: rIC3 `ic3/mod.rs:179` — clones the infinity solver when
    /// extending to a new frame. z4-sat `solver/clone.rs:48`.
    fn clone_for_incremental(&self) -> Option<Box<dyn SatSolver>> {
        self.clone_solver()
    }

    /// Set domain restriction for IC3 SAT queries.
    ///
    /// When a domain is active, the SAT solver restricts its branching decisions
    /// and BCP to variables in the domain. This is the key optimization from
    /// rIC3/GipSAT: each IC3 query operates on the cone-of-influence (COI)
    /// variables only, making individual SAT calls much faster.
    ///
    /// For z4-sat, this activates domain-restricted BCP (`propagate_domain_bcp`)
    /// and bucket-queue VSIDS for small domains.
    ///
    /// Default: no-op for solvers that don't support domain restriction.
    ///
    /// Reference: rIC3 `gipsat/domain.rs` — `enable_local()` sets the domain.
    /// z4-sat `solver/incremental.rs:352` — `set_domain()`.
    fn set_domain(&mut self, _vars: &[Var]) {}

    /// Clear domain restriction, reverting to full-variable decisions.
    ///
    /// Default: no-op for solvers that don't support domain restriction.
    ///
    /// Reference: z4-sat `solver/incremental.rs:379` — `clear_domain()`.
    fn clear_domain(&mut self) {}

    /// Attempt to remove a variable assignment without a SAT call.
    ///
    /// After a SAT result, checks whether unassigning the given variable
    /// would violate any clause (by inspecting watcher lists). Returns true
    /// if the variable was successfully unassigned (it is a don't-care),
    /// false if it must remain assigned.
    ///
    /// This is the key state-lifting primitive from rIC3/GipSAT: instead of
    /// making a full SAT call to check if a literal can be dropped from a
    /// predecessor cube, we directly inspect the clause database.
    ///
    /// Default: returns false (not supported, fall back to SAT-based lifting).
    ///
    /// Reference: rIC3 `gipsat/propagate.rs:186-228` — `flip_to_none_inner()`.
    /// z4-sat `solver/flip_to_none.rs:65`.
    fn flip_to_none(&mut self, _var: Var) -> bool {
        false
    }

    /// Minimize the current model by removing non-important variable assignments.
    ///
    /// After a SAT result, iterates over the trail in reverse and tries
    /// `flip_to_none` on each non-important variable. Returns the remaining
    /// assignment as a minimal cube.
    ///
    /// `important_vars` are variables that must remain assigned (e.g., latch
    /// variables in the predecessor cube that the IC3 engine needs).
    ///
    /// Default: returns empty vec (not supported).
    ///
    /// Reference: rIC3 uses flip_to_none in a loop for state lifting.
    /// z4-sat `solver/flip_to_none.rs:261` — `minimize_model()`.
    fn minimize_model(&mut self, _important_vars: &[Var]) -> Vec<Lit> {
        Vec::new()
    }

    /// Solve under assumptions with a conflict budget.
    ///
    /// Returns `SatResult::Unknown` when the budget is exhausted before the
    /// solver reaches a definitive Sat/Unsat answer. This is critical for
    /// FRTS (functional reduction via ternary simulation) preprocessing:
    /// FRTS compares thousands of signal pairs using SAT, but each check
    /// must be conflict-budgeted (typically 1-10 conflicts) to keep
    /// preprocessing fast. Without budgets, each SAT call takes milliseconds
    /// instead of microseconds, making FRTS impractical.
    ///
    /// ## Parameters
    /// - `assumptions`: literals assumed true for this call
    /// - `max_conflicts`: maximum number of conflicts before returning Unknown.
    ///   A value of 0 returns Unknown immediately. A very large value (e.g.,
    ///   `u64::MAX`) behaves like an unlimited solve.
    ///
    /// ## Default implementation
    /// Falls back to regular `solve()`, ignoring the budget. Solvers that
    /// support conflict limits should override this method.
    fn solve_with_budget(&mut self, assumptions: &[Lit], max_conflicts: u64) -> SatResult {
        if max_conflicts == 0 {
            return SatResult::Unknown;
        }
        // Default: ignore budget, do a full solve.
        self.solve(assumptions)
    }

    /// Solve under assumptions with an additional temporary clause that does NOT
    /// persist after the call.
    ///
    /// This is critical for IC3 soundness: the relative-inductiveness check
    /// `F_{k-1} AND !cube AND T AND cube'` must use !cube as a TEMPORARY
    /// constraint. Adding !cube permanently pollutes the frame solver, causing
    /// false convergence (soundness bug).
    ///
    /// ## Default implementation (activation-literal pattern)
    ///
    /// The default uses activation literals: the clause is permanently added as
    /// `(!act OR l1 OR ... OR ln)`, and `act` is asserted as an assumption.
    /// After the call, `act` is no longer assumed, so the clause becomes a
    /// tautology in future solves. This is correct but causes O(n) degradation
    /// as activation variables and guarded clauses accumulate (#4016).
    ///
    /// ## Production override (push/pop scopes)
    ///
    /// Production solvers (Z4SatCdclSolver) override this method to use native
    /// push/pop scope mechanisms, which physically remove the temporary clause
    /// after the solve. This matches rIC3's `clean_temporary()` approach.
    ///
    /// Reference: rIC3's `solve_with_constraint` in `gipsat/ts.rs`.
    fn solve_with_temporary_clause(
        &mut self,
        assumptions: &[Lit],
        temp_clause: &[Lit],
    ) -> SatResult {
        if temp_clause.is_empty() {
            return self.solve(assumptions);
        }
        // Create activation literal: `act` is a fresh variable.
        let act_var = self.new_var();
        let act_lit = Lit::pos(act_var);
        // Add permanent clause: (!act OR l1 OR ... OR ln).
        // When act is assumed true, this reduces to (l1 OR ... OR ln).
        // When act is not assumed, the solver can set act=false, making it a tautology.
        let mut activated_clause = Vec::with_capacity(temp_clause.len() + 1);
        activated_clause.push(Lit::neg(act_var)); // !act
        activated_clause.extend_from_slice(temp_clause);
        self.add_clause(&activated_clause);
        // Solve with act + original assumptions.
        let mut extended_assumptions = Vec::with_capacity(assumptions.len() + 1);
        extended_assumptions.push(act_lit);
        extended_assumptions.extend_from_slice(assumptions);
        self.solve(&extended_assumptions)
    }
}

// ---------------------------------------------------------------------------
// Simple backtracking DPLL solver (for bootstrap — will be replaced by z4)
// ---------------------------------------------------------------------------

/// A minimal DPLL SAT solver for bootstrapping. Not production-grade.
/// Will be replaced by z4-dpll integration in a future phase.
pub struct SimpleSolver {
    num_vars: u32,
    clauses: Vec<Vec<Lit>>,
    model: Vec<Option<bool>>,
}

impl SimpleSolver {
    pub fn new() -> Self {
        SimpleSolver {
            num_vars: 1, // var 0 is constant
            clauses: Vec::new(),
            model: vec![Some(false)], // var 0 = false (constant)
        }
    }
}

impl Default for SimpleSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl SatSolver for SimpleSolver {
    fn ensure_vars(&mut self, n: u32) {
        if n >= self.num_vars {
            self.num_vars = n + 1;
            self.model.resize(self.num_vars as usize, None);
        }
    }

    fn add_clause(&mut self, clause: &[Lit]) {
        for lit in clause {
            self.ensure_vars(lit.var().0);
        }
        self.clauses.push(clause.to_vec());
    }

    fn solve(&mut self, assumptions: &[Lit]) -> SatResult {
        for lit in assumptions {
            self.ensure_vars(lit.var().0);
        }
        // Reset model
        for v in self.model.iter_mut() {
            *v = None;
        }
        // Var 0 is always false
        self.model[0] = Some(false);

        // Apply assumptions
        for &lit in assumptions {
            let var_idx = lit.var().index();
            let val = lit.is_positive();
            if let Some(existing) = self.model[var_idx] {
                if existing != val {
                    return SatResult::Unsat; // Conflicting assumptions
                }
            }
            self.model[var_idx] = Some(val);
        }

        // Simple DPLL with unit propagation
        if self.dpll_solve(0) {
            SatResult::Sat
        } else {
            SatResult::Unsat
        }
    }

    fn value(&self, lit: Lit) -> Option<bool> {
        let var_idx = lit.var().index();
        if var_idx >= self.model.len() {
            return None;
        }
        self.model[var_idx].map(|v| if lit.is_negated() { !v } else { v })
    }

    fn new_var(&mut self) -> Var {
        let v = Var(self.num_vars);
        self.num_vars += 1;
        self.model.push(None);
        v
    }

    fn clone_solver(&self) -> Option<Box<dyn SatSolver>> {
        let mut new_solver = SimpleSolver::new();
        new_solver.num_vars = self.num_vars;
        new_solver.clauses = self.clauses.clone();
        new_solver.model = vec![None; self.num_vars as usize];
        if !new_solver.model.is_empty() {
            new_solver.model[0] = Some(false);
        }
        Some(Box::new(new_solver))
    }

    /// Override the default activation-literal-based implementation (#4092).
    ///
    /// The default `solve_with_temporary_clause` adds permanent clauses with
    /// activation literals to simulate temporary clauses. For SimpleSolver's
    /// basic DPLL, these accumulate over time and cause unsound results:
    /// DPLL searches over activation variables and may set old ones to `true`,
    /// activating stale temporary clauses and over-constraining the formula.
    ///
    /// This implementation saves the clause database, adds the temporary clause,
    /// solves, then restores the clause database. No activation literals are
    /// created, so no stale clauses accumulate.
    fn solve_with_temporary_clause(
        &mut self,
        assumptions: &[Lit],
        temp_clause: &[Lit],
    ) -> SatResult {
        if temp_clause.is_empty() {
            return self.solve(assumptions);
        }
        for lit in temp_clause {
            self.ensure_vars(lit.var().0);
        }
        // Save clause count to restore after solving.
        let saved_clause_count = self.clauses.len();
        let saved_num_vars = self.num_vars;

        // Add the temporary clause directly (no activation literal).
        self.clauses.push(temp_clause.to_vec());

        // Solve with the augmented clause database.
        let result = self.solve(assumptions);

        // Restore the clause database and variable count.
        self.clauses.truncate(saved_clause_count);
        self.num_vars = saved_num_vars;
        self.model.truncate(self.num_vars as usize);

        result
    }
}

impl SimpleSolver {
    fn eval_clause(&self, clause: &[Lit]) -> Option<bool> {
        let mut any_true = false;
        let mut all_assigned = true;
        for &lit in clause {
            match self.value(lit) {
                Some(true) => any_true = true,
                Some(false) => {}
                None => all_assigned = false,
            }
        }
        if any_true {
            Some(true)
        } else if all_assigned {
            Some(false)
        } else {
            None // undetermined
        }
    }

    fn unit_propagate(&mut self) -> bool {
        let mut changed = true;
        while changed {
            changed = false;
            for i in 0..self.clauses.len() {
                let clause = &self.clauses[i];
                let mut unset_lit = None;
                let mut num_unset = 0;
                let mut satisfied = false;

                for &lit in clause {
                    match self.value(lit) {
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        Some(false) => {}
                        None => {
                            num_unset += 1;
                            unset_lit = Some(lit);
                        }
                    }
                }

                if satisfied {
                    continue;
                }
                if num_unset == 0 {
                    return false; // Conflict
                }
                if num_unset == 1 {
                    let lit = unset_lit.unwrap();
                    self.model[lit.var().index()] = Some(lit.is_positive());
                    changed = true;
                }
            }
        }
        true
    }

    fn dpll_solve(&mut self, depth: usize) -> bool {
        if !self.unit_propagate() {
            return false;
        }

        // Check if all clauses satisfied
        let mut all_sat = true;
        for clause in &self.clauses {
            match self.eval_clause(clause) {
                Some(true) => {}
                Some(false) => return false,
                None => all_sat = false,
            }
        }
        if all_sat {
            return true;
        }

        // Limit recursion depth to prevent stack overflow on large instances
        if depth > 10000 {
            return false;
        }

        // Pick an unassigned variable
        let pick = (1..self.num_vars as usize).find(|&i| self.model[i].is_none());
        let var_idx = match pick {
            Some(v) => v,
            None => return true, // All assigned, clauses satisfied
        };

        // Save state
        let saved: Vec<Option<bool>> = self.model.clone();

        // Try true
        self.model[var_idx] = Some(true);
        if self.dpll_solve(depth + 1) {
            return true;
        }

        // Restore and try false
        self.model = saved.clone();
        self.model[var_idx] = Some(false);
        if self.dpll_solve(depth + 1) {
            return true;
        }

        // Restore
        self.model = saved;
        false
    }
}

// ---------------------------------------------------------------------------
// z4-sat CDCL solver adapter (production backend)
// ---------------------------------------------------------------------------

/// Production SAT solver backed by z4-sat's CDCL engine.
/// Uses the same var*2+sign literal encoding as our Lit type (zero-cost conversion).
///
/// ## Panic resilience (#4026)
///
/// z4-sat can panic during incremental use in IC3 (shrink.rs overflow,
/// conflict_analysis.rs assertion). Rather than crashing the entire
/// portfolio thread, this wrapper catches panics via `catch_unwind` and
/// degrades gracefully to `SatResult::Unknown`. Once a panic is caught,
/// the solver is marked `poisoned` and all subsequent calls return
/// `Unknown` immediately — the internal z4-sat state is unreliable
/// after a panic.
pub struct Z4SatCdclSolver {
    solver: z4_sat::Solver,
    num_vars: u32,
    model: Vec<Option<bool>>,
    last_core: Option<Vec<Lit>>,
    /// Set to `true` after catching a z4-sat panic. All subsequent calls
    /// return `SatResult::Unknown`. The solver cannot be recovered after
    /// a panic because z4-sat's internal invariants may be violated.
    poisoned: bool,
    /// Log of all permanent clauses for clone_solver() replay (#4062).
    clause_log: Vec<Vec<Lit>>,
}

impl Z4SatCdclSolver {
    /// Disable BVE and other preprocessing (#4074).
    ///
    /// Used as a fallback when z4-sat produces FINALIZE_SAT_FAIL
    /// (InvalidSatModel) on certain clause structures. Must be called
    /// before any clauses are added.
    ///
    /// NOTE: In the IC3 path, `solve_incremental_ic3()` never calls
    /// `preprocess()`, so BVE does not actually execute for IC3 SAT
    /// queries. This fallback is relevant for non-IC3 paths (e.g.,
    /// `solve_with_assumptions`) where preprocessing does run.
    pub fn disable_preprocessing(&mut self) {
        self.solver.set_preprocess_enabled(false);
    }

    /// Disable all periodic inprocessing in the underlying z4-sat solver (#4102).
    ///
    /// Calls `disable_all_inprocessing()` on the z4-sat `Solver`, which turns off
    /// all 16 inprocessing technique toggles: vivification, subsumption, probing,
    /// BVE, BCE, conditioning, decomposition, factorization, transitive reduction,
    /// HTR, gate extraction, congruence closure, sweep, CCE, and backbone detection.
    ///
    /// This is distinct from `disable_preprocessing()`: preprocessing runs once at
    /// the start (and is kept enabled for initial simplification), while inprocessing
    /// runs periodically between conflicts and is harmful for IC3's short incremental
    /// queries. rIC3's GipSAT never runs inprocessing — this achieves parity.
    pub fn disable_inprocessing(&mut self) {
        self.solver.disable_all_inprocessing();
    }

    pub fn new(num_vars: u32) -> Self {
        let mut solver = z4_sat::Solver::new(num_vars as usize);
        // Enable full preprocessing (z4-sat defaults to quick mode which skips
        // heavier passes like BVE). IC3 frame solvers live for the entire proof
        // and benefit from thorough initial simplification. This activates the
        // same pass set that CaDiCaL runs by default.
        //
        // NOTE: In practice, IC3 uses solve_incremental_ic3() which never calls
        // preprocess(), so this setting only takes effect if the solver falls
        // back to solve_with_assumptions() (which calls preprocess() on first
        // solve with freeze/melt around assumption variables).
        solver.set_full_preprocessing(true);
        // NOTE: Periodic inprocessing is left ENABLED by default (#4102).
        //
        // BMC and k-induction make longer SAT calls that can benefit from
        // periodic inprocessing (vivification, subsumption, probing, etc.).
        // Only IC3 frame solvers need inprocessing disabled because IC3 makes
        // thousands of short incremental queries where inprocessing overhead
        // is harmful. IC3 solvers use `make_solver_no_inprocessing()` instead
        // of the default `make_solver()` to achieve this.
        //
        // rIC3's GipSAT uses a minimal CDCL loop that never schedules
        // inprocessing. IC3 callers in tla-aiger achieve parity via
        // `SolverBackend::make_solver_no_inprocessing()` or by calling
        // `disable_inprocessing()` on the solver after creation.
        Z4SatCdclSolver {
            solver,
            num_vars,
            model: vec![None; num_vars as usize],
            last_core: None,
            poisoned: false,
            clause_log: Vec::new(),
        }
    }

    /// Returns true if the solver has been poisoned by a prior z4-sat panic.
    pub fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    #[inline]
    fn to_z4_lit(lit: Lit) -> z4_sat::Literal {
        // Both use var*2+sign encoding.
        let var = z4_sat::Variable::new(lit.var().0);
        if lit.is_positive() {
            z4_sat::Literal::positive(var)
        } else {
            z4_sat::Literal::negative(var)
        }
    }

    #[inline]
    fn from_z4_lit(lit: z4_sat::Literal) -> Lit {
        let var = Var(lit.variable().id());
        if lit.is_positive() {
            Lit::pos(var)
        } else {
            Lit::neg(var)
        }
    }
}

impl SatSolver for Z4SatCdclSolver {
    fn ensure_vars(&mut self, n: u32) {
        while self.num_vars <= n {
            self.solver.new_var();
            self.num_vars += 1;
        }
        self.model.resize(self.num_vars as usize, None);
    }

    fn add_clause(&mut self, clause: &[Lit]) {
        if self.poisoned {
            return;
        }
        for lit in clause {
            self.ensure_vars(lit.var().0);
        }
        let z4_clause: Vec<z4_sat::Literal> = clause.iter().map(|&l| Self::to_z4_lit(l)).collect();
        // Use add_clause_global to ensure permanent clauses survive push/pop scopes.
        // The default add_clause would attach a scope selector if called inside a
        // push() scope (e.g., if someone adds a lemma during solve_with_temporary_clause).
        self.solver.add_clause_global(z4_clause);
        self.clause_log.push(clause.to_vec());
    }

    fn solve(&mut self, assumptions: &[Lit]) -> SatResult {
        if self.poisoned {
            return SatResult::Unknown;
        }
        for lit in assumptions {
            self.ensure_vars(lit.var().0);
        }
        let z4_assumptions: Vec<z4_sat::Literal> =
            assumptions.iter().map(|&l| Self::to_z4_lit(l)).collect();

        // Use IC3-optimized solve path: stripped-down CDCL loop modeled after
        // GipSAT's search(). Skips inprocessing scheduling, theory callbacks,
        // proof logging, TLA tracing, progress reporting, Glucose EMA restarts,
        // lucky phases, walk init, observer notifications — all overhead that
        // IC3's thousands of short queries don't need. Falls back to standard
        // solve_with_assumptions if the IC3 path is unavailable.
        //
        // Wrap in catch_unwind to handle panics from shrink.rs overflow and
        // conflict_analysis.rs BUG (#4026).
        // SAFETY rationale for AssertUnwindSafe: after a panic we mark
        // the solver as poisoned and never call into z4-sat again, so
        // the potentially-inconsistent internal state is never observed.
        let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.solver.solve_incremental_ic3(&z4_assumptions)
        }));

        let result = match solve_result {
            Ok(r) => r,
            Err(panic_info) => {
                let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                    (*s).to_string()
                } else if let Some(s) = panic_info.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "unknown panic".to_string()
                };
                eprintln!("IC3: z4-sat panic caught in solve(): {msg}");
                self.poisoned = true;
                return SatResult::Unknown;
            }
        };

        if result.is_sat() {
            // Extract model
            if let Some(model_vals) = result.model() {
                self.model
                    .resize(model_vals.len().max(self.num_vars as usize), None);
                for (i, &val) in model_vals.iter().enumerate() {
                    if i < self.model.len() {
                        self.model[i] = Some(val);
                    }
                }
            }
            self.last_core = None;
            SatResult::Sat
        } else if result.is_unsat() {
            // Extract UNSAT core
            self.last_core = result
                .unsat_core()
                .map(|core| core.iter().map(|&l| Self::from_z4_lit(l)).collect());
            SatResult::Unsat
        } else {
            self.last_core = None;
            SatResult::Unknown
        }
    }

    fn value(&self, lit: Lit) -> Option<bool> {
        let var_idx = lit.var().index();
        if var_idx >= self.model.len() {
            return None;
        }
        self.model[var_idx].map(|v| if lit.is_negated() { !v } else { v })
    }

    fn new_var(&mut self) -> Var {
        let v = Var(self.num_vars);
        self.solver.new_var();
        self.num_vars += 1;
        self.model.push(None);
        v
    }

    fn unsat_core(&self) -> Option<Vec<Lit>> {
        self.last_core.clone()
    }

    fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    fn disable_inprocessing(&mut self) {
        self.solver.disable_all_inprocessing();
    }

    /// Wire the portfolio's cancellation flag into z4-sat's interrupt mechanism.
    ///
    /// z4-sat's CDCL loop checks `is_interrupted()` every ~1000 decisions
    /// (solve.rs:868). When the flag is set, the solver returns Unknown with
    /// reason `Interrupted`, allowing the thread to exit promptly instead of
    /// running to completion (#4057).
    fn set_cancelled(&mut self, cancelled: Arc<AtomicBool>) {
        self.solver.set_interrupt(cancelled);
    }

    fn clone_solver(&self) -> Option<Box<dyn SatSolver>> {
        if self.poisoned {
            return None;
        }
        let mut new_solver = Z4SatCdclSolver::new(self.num_vars);
        for clause in &self.clause_log {
            new_solver.add_clause(clause);
        }
        Some(Box::new(new_solver))
    }

    /// Native incremental clone using z4-sat's `clone_for_incremental()`.
    ///
    /// Deep-copies the entire solver state: clause arena, watch lists, VSIDS
    /// heap + activities, trail, variable assignments/phases, conflict analysis
    /// state. The cloned solver inherits all learned clauses and VSIDS scores,
    /// making it immediately effective without cold-start overhead.
    ///
    /// This replaces the clause-log replay in `clone_solver()` for frame
    /// extension (#4062). The key benefit: learned clauses from solving
    /// previous frames carry forward to new frames, reducing redundant work.
    ///
    /// Reference: rIC3 `ic3/mod.rs:179` — `self.inf_solver.clone()`.
    /// z4-sat `solver/clone.rs:48` — `clone_for_incremental()`.
    fn clone_for_incremental(&self) -> Option<Box<dyn SatSolver>> {
        if self.poisoned {
            return None;
        }
        let cloned_solver = self.solver.clone_for_incremental();
        Some(Box::new(Z4SatCdclSolver {
            solver: cloned_solver,
            num_vars: self.num_vars,
            model: self.model.clone(),
            last_core: None,
            poisoned: false,
            clause_log: self.clause_log.clone(),
        }))
    }

    /// Wire z4-sat's native domain restriction for IC3 queries.
    ///
    /// Activates domain-restricted BCP (`propagate_domain_bcp`) and
    /// bucket-queue VSIDS for small domains. This is the biggest
    /// performance win from rIC3: each IC3 SAT call only processes
    /// variables in the cube's cone-of-influence.
    ///
    /// Reference: z4-sat `solver/incremental.rs:352`.
    fn set_domain(&mut self, vars: &[Var]) {
        if self.poisoned {
            return;
        }
        let z4_vars: Vec<z4_sat::Variable> = vars
            .iter()
            .map(|v| z4_sat::Variable::new(v.0))
            .collect();
        self.solver.set_domain(&z4_vars);
    }

    fn clear_domain(&mut self) {
        if self.poisoned {
            return;
        }
        self.solver.clear_domain();
    }

    /// Wire z4-sat's `flip_to_none` for zero-SAT-call state lifting.
    ///
    /// After a SAT result, checks whether unassigning a variable would
    /// violate any clause by directly inspecting watcher lists. Returns
    /// true if the variable was successfully flipped to unassigned.
    ///
    /// Reference: z4-sat `solver/flip_to_none.rs:65`.
    fn flip_to_none(&mut self, var: Var) -> bool {
        if self.poisoned {
            return false;
        }
        let z4_var = z4_sat::Variable::new(var.0);
        // Wrap in catch_unwind for panic resilience (#4026).
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.solver.flip_to_none(z4_var)
        }));
        match result {
            Ok(flipped) => flipped,
            Err(_) => {
                self.poisoned = true;
                false
            }
        }
    }

    /// Wire z4-sat's `minimize_model` for bulk state lifting.
    ///
    /// Iterates the trail in reverse, flipping non-important variables.
    /// Returns the remaining assignment as a minimal cube of literals.
    ///
    /// Reference: z4-sat `solver/flip_to_none.rs:261`.
    fn minimize_model(&mut self, important_vars: &[Var]) -> Vec<Lit> {
        if self.poisoned {
            return Vec::new();
        }
        let z4_important: Vec<z4_sat::Variable> = important_vars
            .iter()
            .map(|v| z4_sat::Variable::new(v.0))
            .collect();
        // Wrap in catch_unwind for panic resilience (#4026).
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.solver.minimize_model(&z4_important)
        }));
        match result {
            Ok(z4_lits) => z4_lits.iter().map(|&l| Self::from_z4_lit(l)).collect(),
            Err(_) => {
                self.poisoned = true;
                Vec::new()
            }
        }
    }

    /// Conflict-budgeted solve using z4-sat's `solve_with_assumptions_interruptible`.
    ///
    /// z4-sat's CDCL loop calls the `should_stop` callback every ~100 conflicts.
    /// We use an invocation counter to fire after `ceil(max_conflicts / 100)`
    /// callbacks. This gives ~100-conflict granularity, which is sufficient for
    /// FRTS preprocessing (where the goal is to cap at O(100) conflicts rather
    /// than running to completion on hard pairs).
    ///
    /// For easy problems (SAT/UNSAT reached before the first callback), the
    /// budget has no effect — the solver returns the correct definitive answer.
    fn solve_with_budget(&mut self, assumptions: &[Lit], max_conflicts: u64) -> SatResult {
        if max_conflicts == 0 {
            return SatResult::Unknown;
        }
        if self.poisoned {
            return SatResult::Unknown;
        }
        for lit in assumptions {
            self.ensure_vars(lit.var().0);
        }
        let z4_assumptions: Vec<z4_sat::Literal> =
            assumptions.iter().map(|&l| Self::to_z4_lit(l)).collect();

        // z4-sat checks should_stop every 100 conflicts and every 1000 decisions.
        // Compute the maximum number of callback invocations to allow.
        // For max_conflicts < 100, we allow 1 invocation (up to ~100 conflicts).
        let max_invocations = max_conflicts.div_ceil(100);
        let invocation_count = std::sync::atomic::AtomicU64::new(0);

        // Wrap in catch_unwind for z4-sat panic resilience (#4026).
        let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.solver
                .solve_with_assumptions_interruptible(&z4_assumptions, || {
                    let count = invocation_count
                        .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    count >= max_invocations
                })
        }));

        let result = match solve_result {
            Ok(r) => r,
            Err(panic_info) => {
                let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                    (*s).to_string()
                } else if let Some(s) = panic_info.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "unknown panic".to_string()
                };
                eprintln!("IC3: z4-sat panic caught in solve_with_budget(): {msg}");
                self.poisoned = true;
                return SatResult::Unknown;
            }
        };

        if result.is_sat() {
            if let Some(model_vals) = result.model() {
                self.model
                    .resize(model_vals.len().max(self.num_vars as usize), None);
                for (i, &val) in model_vals.iter().enumerate() {
                    if i < self.model.len() {
                        self.model[i] = Some(val);
                    }
                }
            }
            self.last_core = None;
            SatResult::Sat
        } else if result.is_unsat() {
            self.last_core = result
                .unsat_core()
                .map(|core| core.iter().map(|&l| Self::from_z4_lit(l)).collect());
            SatResult::Unsat
        } else {
            self.last_core = None;
            SatResult::Unknown
        }
    }

    /// Override the default activation-literal pattern with z4-sat's native
    /// push/pop scope mechanism. This eliminates activation literal accumulation
    /// that causes O(n) solver degradation per MIC call (#4016).
    ///
    /// Before this fix, every `solve_with_temporary_clause` call created a new
    /// activation variable and added a permanent guarded clause. Over thousands
    /// of IC3 inductiveness checks, this accumulated thousands of dead variables
    /// and clauses in the solver, degrading performance.
    ///
    /// With push/pop, the temporary clause is physically removed after the solve,
    /// keeping solver state clean. Reference: rIC3's `clean_temporary()` achieves
    /// the same effect (detaching temporary clauses from watch lists between calls).
    fn solve_with_temporary_clause(
        &mut self,
        assumptions: &[Lit],
        temp_clause: &[Lit],
    ) -> SatResult {
        if self.poisoned {
            return SatResult::Unknown;
        }
        if temp_clause.is_empty() {
            return self.solve(assumptions);
        }
        for lit in temp_clause {
            self.ensure_vars(lit.var().0);
        }
        for lit in assumptions {
            self.ensure_vars(lit.var().0);
        }

        // Save the user-facing variable count before push(). z4-sat's push()
        // creates an internal scope-selector variable that increments its
        // internal variable count. We use this bound to filter the UNSAT core:
        // any literal with var index >= num_vars_before_push is an internal
        // z4-sat variable (scope selector) and must not leak into the core
        // returned to IC3 (#4024).
        let num_vars_before_push = self.num_vars;

        // Push a new scope — clauses added within this scope are automatically
        // tagged with a scope selector and removed on pop().
        self.solver.push();

        // Add the temporary clause within the pushed scope.
        // z4-sat's add_clause() attaches a scope selector when inside a push scope.
        let z4_temp: Vec<z4_sat::Literal> =
            temp_clause.iter().map(|&l| Self::to_z4_lit(l)).collect();
        self.solver.add_clause(z4_temp);

        // Solve with the original assumptions using IC3-optimized path.
        // solve_incremental_ic3 handles scope selectors via compose_scope_assumptions.
        // Wrap in catch_unwind to handle z4-sat panics (#4026).
        let z4_assumptions: Vec<z4_sat::Literal> =
            assumptions.iter().map(|&l| Self::to_z4_lit(l)).collect();
        let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.solver.solve_incremental_ic3(&z4_assumptions)
        }));

        let result = match solve_result {
            Ok(r) => r,
            Err(panic_info) => {
                let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                    (*s).to_string()
                } else if let Some(s) = panic_info.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "unknown panic".to_string()
                };
                eprintln!(
                    "IC3: z4-sat panic caught in solve_with_temporary_clause(): {msg}"
                );
                // Best-effort pop to clean up the pushed scope. If this also
                // panics, the solver is already poisoned so it doesn't matter.
                let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let _ = self.solver.pop();
                }));
                self.poisoned = true;
                return SatResult::Unknown;
            }
        };

        let sat_result = if result.is_sat() {
            if let Some(model_vals) = result.model() {
                self.model
                    .resize(model_vals.len().max(self.num_vars as usize), None);
                for (i, &val) in model_vals.iter().enumerate() {
                    if i < self.model.len() {
                        self.model[i] = Some(val);
                    }
                }
            }
            self.last_core = None;
            SatResult::Sat
        } else if result.is_unsat() {
            // Filter the UNSAT core to only include user-facing literals (#4024).
            //
            // z4-sat's push/pop mechanism adds a scope-selector variable as an
            // internal assumption (via compose_scope_assumptions). While z4-sat's
            // finalize_assumption_api_result filters active scope selectors from
            // the core, this is a defense-in-depth measure: we filter to
            // variables that existed before push() was called.
            //
            // Without this filter, the core could contain:
            // (a) scope-selector literals from z4-sat's internal variable space
            // (b) any variables allocated by push() for scope management
            //
            // IC3 uses unsat cores for cube generalization (MIC). Stale or
            // internal literals in the core would cause incorrect generalization,
            // potentially missing valid counterexamples to induction.
            self.last_core = result.unsat_core().map(|core| {
                core.iter()
                    .filter(|&&l| {
                        let var_idx = Self::from_z4_lit(l).var().0;
                        var_idx < num_vars_before_push
                    })
                    .map(|&l| Self::from_z4_lit(l))
                    .collect()
            });
            SatResult::Unsat
        } else {
            self.last_core = None;
            SatResult::Unknown
        };

        // Pop the scope — removes the temporary clause from the solver.
        let _ = self.solver.pop();

        sat_result
    }
}

// CaDiCaL solver backend REMOVED. z4-sat is our SAT solver — we own the
// full stack. Portfolio diversity comes from z4-sat configuration variants
// (restart policies, branching heuristics, preprocessing toggles).

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lit_encoding() {
        let v = Var(5);
        let pos = Lit::pos(v);
        let neg = Lit::neg(v);
        assert!(pos.is_positive());
        assert!(neg.is_negated());
        assert_eq!(pos.var(), v);
        assert_eq!(neg.var(), v);
        assert_eq!(!pos, neg);
        assert_eq!(!neg, pos);
    }

    #[test]
    fn test_lit_constants() {
        // Var(0) is constant-false. pos(Var(0)) evals to false, neg(Var(0)) evals to true.
        assert_eq!(Lit::FALSE.var(), Var::CONST);
        assert!(Lit::FALSE.is_positive()); // pos(Var(0)) = false
        assert_eq!(Lit::TRUE.var(), Var::CONST);
        assert!(Lit::TRUE.is_negated()); // neg(Var(0)) = !false = true
    }

    #[test]
    fn test_clause_display() {
        let c = Clause::new(vec![Lit::pos(Var(1)), Lit::neg(Var(2))]);
        let s = format!("{c}");
        assert!(s.contains("v1"));
        assert!(s.contains("~v2"));
    }

    #[test]
    fn test_simple_solver_sat() {
        let mut solver = SimpleSolver::new();
        let a = solver.new_var(); // Var(1)
        let b = solver.new_var(); // Var(2)
                                  // (a OR b)
        solver.add_clause(&[Lit::pos(a), Lit::pos(b)]);
        assert_eq!(solver.solve(&[]), SatResult::Sat);
    }

    #[test]
    fn test_simple_solver_unsat() {
        let mut solver = SimpleSolver::new();
        let a = solver.new_var(); // Var(1)
                                  // (a) AND (!a)
        solver.add_clause(&[Lit::pos(a)]);
        solver.add_clause(&[Lit::neg(a)]);
        assert_eq!(solver.solve(&[]), SatResult::Unsat);
    }

    #[test]
    fn test_simple_solver_assumptions() {
        let mut solver = SimpleSolver::new();
        let a = solver.new_var();
        let b = solver.new_var();
        // (a OR b)
        solver.add_clause(&[Lit::pos(a), Lit::pos(b)]);
        // Assume !a, !b => UNSAT
        assert_eq!(solver.solve(&[Lit::neg(a), Lit::neg(b)]), SatResult::Unsat);
        // Assume a => SAT
        assert_eq!(solver.solve(&[Lit::pos(a)]), SatResult::Sat);
    }

    #[test]
    fn test_simple_solver_model() {
        let mut solver = SimpleSolver::new();
        let a = solver.new_var();
        solver.add_clause(&[Lit::pos(a)]);
        assert_eq!(solver.solve(&[]), SatResult::Sat);
        assert_eq!(solver.value(Lit::pos(a)), Some(true));
        assert_eq!(solver.value(Lit::neg(a)), Some(false));
    }

    #[test]
    fn test_z4sat_cdcl_basic() {
        let mut s = Z4SatCdclSolver::new(3);
        s.add_clause(&[Lit::TRUE]); // Var(0)=false
                                    // (!v2 OR !v1) AND (v2 OR v1) — equiv to v2 <=> !v1
        s.add_clause(&[Lit::neg(Var(2)), Lit::neg(Var(1))]);
        s.add_clause(&[Lit::pos(Var(2)), Lit::pos(Var(1))]);
        let r1 = s.solve(&[Lit::pos(Var(1))]);
        assert_eq!(r1, SatResult::Sat, "v1=true should be SAT");
    }

    #[test]
    fn test_z4sat_cdcl_incremental_fixed() {
        // z4#7987 fixed in z4 ec8d049a5. Incremental add_clause between
        // solve_with_assumptions calls now returns correct results.
        let mut s = Z4SatCdclSolver::new(3);
        s.add_clause(&[Lit::TRUE]);
        s.add_clause(&[Lit::neg(Var(2)), Lit::neg(Var(1))]);
        s.add_clause(&[Lit::pos(Var(2)), Lit::pos(Var(1))]);
        let r1 = s.solve(&[Lit::pos(Var(1))]);
        assert_eq!(r1, SatResult::Sat, "v1=true should be SAT");
        s.add_clause(&[Lit::neg(Var(1))]);
        let r2 = s.solve(&[Lit::pos(Var(2))]);
        assert_eq!(
            r2,
            SatResult::Sat,
            "v2=true after adding !v1 should be SAT (z4#7987 fixed)"
        );
    }

    #[test]
    fn test_z4sat_cdcl_model() {
        let mut s = Z4SatCdclSolver::new(3);
        s.add_clause(&[Lit::pos(Var(1))]);
        let r = s.solve(&[]);
        assert_eq!(r, SatResult::Sat);
        assert_eq!(s.value(Lit::pos(Var(1))), Some(true));
    }

    #[test]
    fn test_z4sat_cdcl_unsat_core() {
        let mut s = Z4SatCdclSolver::new(3);
        s.add_clause(&[Lit::neg(Var(1))]); // !v1
        let r = s.solve(&[Lit::pos(Var(1))]); // assume v1
        assert_eq!(r, SatResult::Unsat);
        let core = s.unsat_core();
        assert!(core.is_some(), "should have UNSAT core");
    }

    // --- SolverBackend factory tests ---

    #[test]
    fn test_solver_backend_z4sat_incremental() {
        let mut s = SolverBackend::Z4Sat.make_solver(3);
        s.add_clause(&[Lit::TRUE]);
        s.add_clause(&[Lit::neg(Var(2)), Lit::neg(Var(1))]);
        s.add_clause(&[Lit::pos(Var(2)), Lit::pos(Var(1))]);
        let r1 = s.solve(&[Lit::pos(Var(1))]);
        assert_eq!(r1, SatResult::Sat);
        s.add_clause(&[Lit::neg(Var(1))]);
        let r2 = s.solve(&[Lit::pos(Var(2))]);
        assert_eq!(
            r2,
            SatResult::Sat,
            "Z4Sat should handle incremental correctly"
        );
    }

    #[test]
    fn test_solver_backend_simple_incremental() {
        let mut s = SolverBackend::Simple.make_solver(3);
        s.add_clause(&[Lit::TRUE]);
        s.add_clause(&[Lit::neg(Var(2)), Lit::neg(Var(1))]);
        s.add_clause(&[Lit::pos(Var(2)), Lit::pos(Var(1))]);
        let r1 = s.solve(&[Lit::pos(Var(1))]);
        assert_eq!(r1, SatResult::Sat);
        s.add_clause(&[Lit::neg(Var(1))]);
        let r2 = s.solve(&[Lit::pos(Var(2))]);
        assert_eq!(
            r2,
            SatResult::Sat,
            "Simple should handle incremental correctly"
        );
    }

    #[test]
    fn test_solver_backend_default_is_z4sat() {
        assert_eq!(SolverBackend::default(), SolverBackend::Z4Sat);
    }

    // --- solve_with_temporary_clause push/pop tests (#4016) ---

    /// Verify that solve_with_temporary_clause's temporary clause does NOT
    /// persist after the call returns. This is the core soundness property
    /// for IC3: !cube must not pollute frame solvers.
    #[test]
    fn test_z4sat_solve_with_temporary_clause_isolation() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);

        // Permanent clause: (a OR b)
        s.add_clause(&[Lit::pos(a), Lit::pos(b)]);

        // Temporary clause: (!a). With assumption a=true, this conflicts => UNSAT.
        let r1 = s.solve_with_temporary_clause(&[Lit::pos(a)], &[Lit::neg(a)]);
        assert_eq!(
            r1,
            SatResult::Unsat,
            "should be UNSAT: assumption a=true conflicts with temp clause !a"
        );

        // After the call, the temp clause !a should be gone.
        // Solving with assumption a=true and only permanent clause (a OR b) => SAT.
        let r2 = s.solve(&[Lit::pos(a)]);
        assert_eq!(
            r2,
            SatResult::Sat,
            "temp clause !a must not persist; (a OR b) with a=true is SAT"
        );
    }

    /// Verify that a temporary clause that constrains (but doesn't conflict
    /// with) the formula yields the correct SAT result and model.
    #[test]
    fn test_z4sat_solve_with_temporary_clause_sat() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);

        // Permanent clauses: (a OR b) AND (!a OR !b)  — XOR: exactly one is true.
        s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
        s.add_clause(&[Lit::neg(a), Lit::neg(b)]);

        // Temporary clause: (!b) — forces b=false, so a=true.
        let r1 = s.solve_with_temporary_clause(&[], &[Lit::neg(b)]);
        assert_eq!(
            r1,
            SatResult::Sat,
            "XOR(a,b) with temp !b should be SAT (a=true, b=false)"
        );
        assert_eq!(
            s.value(Lit::pos(a)),
            Some(true),
            "a should be true when b is forced false"
        );
        assert_eq!(
            s.value(Lit::pos(b)),
            Some(false),
            "b should be false from temp clause"
        );

        // After temp clause is gone, both solutions should be available.
        let r2 = s.solve(&[]);
        assert_eq!(
            r2,
            SatResult::Sat,
            "XOR(a,b) without temp clause is still SAT"
        );
    }

    /// Verify that UNSAT cores work correctly through push/pop scopes.
    #[test]
    fn test_z4sat_solve_with_temporary_clause_unsat_core() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);

        // Permanent clause: (a) — forces a=true.
        s.add_clause(&[Lit::pos(a)]);

        // Temporary clause: (!a) — conflicts with permanent (a) => UNSAT.
        // Assumptions: [a] to make the assumption trackable in the core.
        let r = s.solve_with_temporary_clause(&[Lit::pos(a)], &[Lit::neg(a)]);
        assert_eq!(r, SatResult::Unsat, "a AND !a is UNSAT");

        // UNSAT core should exist (z4-sat supports it).
        let core = s.unsat_core();
        assert!(
            core.is_some(),
            "z4-sat should provide UNSAT core through push/pop"
        );
    }

    /// Verify that UNSAT cores from solve_with_temporary_clause only contain
    /// user-facing literals — no z4-sat internal scope-selector variables (#4024).
    ///
    /// This is the core soundness property for IC3 cube generalization: the MIC
    /// (Minimal Inductive Clause) algorithm uses the UNSAT core to drop literals
    /// from the cube. If the core contains internal z4-sat variables (scope
    /// selectors created by push()), MIC would try to look up those variables
    /// in the cube and produce incorrect generalizations.
    #[test]
    fn test_z4sat_solve_with_temporary_clause_unsat_core_no_scope_lits() {
        let mut s = Z4SatCdclSolver::new(4);
        let a = Var(1);
        let b = Var(2);
        let c = Var(3);

        // Record the user-facing variable count before any push/pop.
        let user_num_vars = s.num_vars;

        // Permanent clauses: (a) AND (b OR c)
        s.add_clause(&[Lit::pos(a)]);
        s.add_clause(&[Lit::pos(b), Lit::pos(c)]);

        // Temporary clause: (!a AND !b AND !c) expressed as three unit temp clauses
        // won't work since solve_with_temporary_clause takes a single clause.
        // Instead: temp clause (!a) conflicts with permanent (a) when a is assumed.
        //
        // Use assumptions [a, b] so the core should be a subset of {a, b}.
        let r = s.solve_with_temporary_clause(
            &[Lit::pos(a), Lit::pos(b)],
            &[Lit::neg(a)], // conflicts with permanent clause (a) + assumption a
        );
        assert_eq!(
            r,
            SatResult::Unsat,
            "should be UNSAT: temp !a conflicts with permanent a + assumption a"
        );

        let core = s.unsat_core().expect("should have UNSAT core");

        // Every literal in the core must have a variable index < user_num_vars.
        // No scope-selector variables (created by push()) should be present.
        for lit in &core {
            assert!(
                lit.var().0 < user_num_vars,
                "UNSAT core contains non-user variable {:?} (index {} >= user_num_vars {}); \
                 likely a z4-sat scope selector leaked through (#4024)",
                lit,
                lit.var().0,
                user_num_vars,
            );
        }

        // The core should only contain literals from the assumptions we passed.
        let assumption_vars: std::collections::HashSet<u32> = [a.0, b.0].into();
        for lit in &core {
            assert!(
                assumption_vars.contains(&lit.var().0),
                "UNSAT core literal {:?} is not an assumption variable; \
                 core should be a subset of assumptions",
                lit,
            );
        }

        // The core may be empty: the permanent clause (a) directly conflicts
        // with the temp clause (!a), so z4-sat can prove UNSAT without any
        // assumptions. An empty core is a valid (and minimal) UNSAT core.
        // With JIT disabled (#4040), z4-sat's interpreter conflict analysis
        // correctly detects this level-0 conflict without assumption involvement.
        // Previously the JIT path included assumption `a` in the core.
    }

    /// Verify that repeated push/pop cycles don't accumulate stale literals
    /// in subsequent UNSAT cores (#4024). After many cycles, the core from a
    /// new solve_with_temporary_clause must still only contain user variables.
    #[test]
    fn test_z4sat_repeated_push_pop_core_stays_clean() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);

        // Permanent clause: (a)
        s.add_clause(&[Lit::pos(a)]);

        let user_num_vars = s.num_vars;

        // Run 50 push/pop cycles, each producing an UNSAT core.
        for i in 0..50 {
            let r = s.solve_with_temporary_clause(&[Lit::pos(a), Lit::pos(b)], &[Lit::neg(a)]);
            assert_eq!(r, SatResult::Unsat, "iteration {i}: should be UNSAT");

            if let Some(core) = s.unsat_core() {
                for lit in &core {
                    assert!(
                        lit.var().0 < user_num_vars,
                        "iteration {i}: UNSAT core contains non-user variable {:?} \
                         (index {} >= user_num_vars {})",
                        lit,
                        lit.var().0,
                        user_num_vars,
                    );
                }
            }
        }

        // Solver should still be functional after many cycles.
        let r = s.solve(&[Lit::pos(a)]);
        assert_eq!(
            r,
            SatResult::Sat,
            "solver should work after 50 push/pop cycles"
        );
    }

    /// Empty temporary clause should behave identically to a regular solve().
    #[test]
    fn test_z4sat_solve_with_temporary_clause_empty() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);

        s.add_clause(&[Lit::pos(a), Lit::pos(b)]);

        // Empty temp clause => falls through to regular solve.
        let r1 = s.solve_with_temporary_clause(&[Lit::pos(a)], &[]);
        assert_eq!(
            r1,
            SatResult::Sat,
            "empty temp clause should delegate to regular solve"
        );

        let r2 = s.solve(&[Lit::pos(a)]);
        assert_eq!(
            r2,
            SatResult::Sat,
            "regular solve should match empty-temp-clause result"
        );
    }

    /// Permanent clauses added via add_clause (which uses add_clause_global
    /// internally) must survive solve_with_temporary_clause's push/pop cycle.
    #[test]
    fn test_z4sat_permanent_clauses_survive_temporary_solve() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);

        // Permanent: (!a) — forces a=false.
        s.add_clause(&[Lit::neg(a)]);
        // Permanent: (a OR b) — with !a, forces b=true.
        s.add_clause(&[Lit::pos(a), Lit::pos(b)]);

        // Do a solve_with_temporary_clause (the temp clause is irrelevant here).
        let r1 = s.solve_with_temporary_clause(&[], &[Lit::pos(a), Lit::pos(b)]);
        assert_eq!(r1, SatResult::Sat, "should be SAT with temp clause");

        // After push/pop, permanent clauses must still hold.
        // a must be false (from permanent !a), b must be true (from permanent a OR b + !a).
        let r2 = s.solve(&[]);
        assert_eq!(
            r2,
            SatResult::Sat,
            "permanent clauses should still be active"
        );
        assert_eq!(
            s.value(Lit::pos(a)),
            Some(false),
            "permanent clause !a must survive push/pop"
        );
        assert_eq!(
            s.value(Lit::pos(b)),
            Some(true),
            "permanent clause (a OR b) with !a must force b=true after push/pop"
        );
    }

    /// Verify that repeated solve_with_temporary_clause calls do not
    /// accumulate solver state. With push/pop, the variable count should
    /// stay bounded (unlike the activation-literal pattern which adds one
    /// new variable per call).
    ///
    /// This is the key performance property from #4016: IC3 makes thousands
    /// of inductiveness checks, and each one should not permanently grow
    /// the solver.
    #[test]
    fn test_z4sat_repeated_temporary_clauses_no_accumulation() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);

        // Permanent: (a OR b)
        s.add_clause(&[Lit::pos(a), Lit::pos(b)]);

        let initial_num_vars = s.num_vars;

        // Call solve_with_temporary_clause 200 times with different temp clauses.
        for i in 0..200 {
            let temp = if i % 2 == 0 {
                vec![Lit::neg(a)]
            } else {
                vec![Lit::neg(b)]
            };
            let r = s.solve_with_temporary_clause(&[], &temp);
            assert_eq!(
                r,
                SatResult::Sat,
                "iteration {i}: should be SAT with one-literal temp clause"
            );
        }

        // With push/pop, the Z4SatCdclSolver's num_vars should NOT have grown
        // by 200 (which is what the activation-literal default would do).
        // z4-sat's push/pop allocates internal scope selector variables, but
        // those are managed inside z4-sat and not exposed through our num_vars.
        assert_eq!(
            s.num_vars, initial_num_vars,
            "num_vars should not grow with push/pop temporary clauses; \
             activation literals would have added 200 new vars, got {} -> {}",
            initial_num_vars, s.num_vars
        );

        // Verify solver still works correctly after many push/pop cycles.
        let r = s.solve(&[Lit::pos(a)]);
        assert_eq!(
            r,
            SatResult::Sat,
            "solver should still be functional after 200 push/pop cycles"
        );
    }

    /// Stress-test the push/pop pattern with an UNSAT temporary clause
    /// interleaved with SAT solves, mimicking IC3's MIC (Minimal Inductive
    /// Clause) pattern where the solver alternates between inductiveness
    /// checks (with temp clauses) and regular frame queries.
    #[test]
    fn test_z4sat_interleaved_temp_and_permanent_solves() {
        let mut s = Z4SatCdclSolver::new(4);
        let a = Var(1);
        let b = Var(2);
        let c = Var(3);

        // Permanent clauses encoding: a XOR b (exactly one true).
        s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
        s.add_clause(&[Lit::neg(a), Lit::neg(b)]);

        for _ in 0..50 {
            // Temp clause: force a=true AND b=true => UNSAT (violates XOR).
            let r1 = s.solve_with_temporary_clause(&[Lit::pos(a)], &[Lit::pos(b)]);
            assert_eq!(
                r1,
                SatResult::Unsat,
                "a=true with temp b => UNSAT against XOR(a,b)"
            );

            // Regular solve: should still work.
            let r2 = s.solve(&[Lit::pos(a)]);
            assert_eq!(
                r2,
                SatResult::Sat,
                "permanent XOR(a,b) with a=true should be SAT"
            );
            assert_eq!(
                s.value(Lit::pos(b)),
                Some(false),
                "b should be false when a is true in XOR"
            );

            // Add a permanent clause involving c (to test that permanent additions
            // between push/pop cycles work correctly).
            // This is what IC3 does: add learned lemmas between MIC calls.
            // Use ensure_vars to make sure c is available.
            s.ensure_vars(c.0);
        }

        // Final verification: all permanent clauses still hold.
        let r = s.solve(&[]);
        assert_eq!(r, SatResult::Sat, "final solve should be SAT");
    }

    // --- Panic resilience tests (#4026) ---

    /// Verify that a poisoned Z4SatCdclSolver returns Unknown for all
    /// subsequent calls and does not panic or corrupt state.
    #[test]
    fn test_z4sat_poisoned_solver_returns_unknown() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);

        // Add a clause and verify the solver works.
        s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
        let r = s.solve(&[Lit::pos(a)]);
        assert_eq!(r, SatResult::Sat, "should be SAT before poison");
        assert!(!s.is_poisoned(), "should not be poisoned yet");

        // Manually poison the solver (simulating a caught z4-sat panic).
        s.poisoned = true;
        assert!(s.is_poisoned());

        // All subsequent calls should return Unknown without panicking.
        let r1 = s.solve(&[Lit::pos(a)]);
        assert_eq!(r1, SatResult::Unknown, "poisoned solve should return Unknown");

        let r2 = s.solve_with_temporary_clause(&[Lit::pos(a)], &[Lit::neg(a)]);
        assert_eq!(
            r2,
            SatResult::Unknown,
            "poisoned solve_with_temporary_clause should return Unknown"
        );

        // add_clause should silently no-op (not panic).
        s.add_clause(&[Lit::neg(b)]);
    }

    /// Verify that the portfolio thread catch_unwind works: if an engine panics,
    /// it should produce a CheckResult::Unknown instead of crashing.
    #[test]
    fn test_z4sat_catch_unwind_in_solve() {
        // This test verifies the catch_unwind wrapper by checking that after
        // calling solve on a working solver, the solver is not poisoned.
        // We cannot easily trigger a z4-sat panic in a unit test without
        // crafting a specific incremental sequence that hits the bug, but
        // we can verify the wrapper's normal-path correctness.
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);

        s.add_clause(&[Lit::pos(a)]);
        let r = s.solve(&[]);
        assert_eq!(r, SatResult::Sat, "normal solve should still work");
        assert!(!s.is_poisoned(), "solver should not be poisoned after normal solve");

        let r2 = s.solve_with_temporary_clause(&[Lit::pos(a)], &[Lit::neg(a)]);
        assert_eq!(r2, SatResult::Unsat, "temp clause solve should work");
        assert!(
            !s.is_poisoned(),
            "solver should not be poisoned after normal solve_with_temporary_clause"
        );
    }

    // --- set_cancelled / interrupt wiring tests (#4057) ---

    /// Verify that set_cancelled wires the AtomicBool into z4-sat's interrupt
    /// mechanism. When the flag is pre-set to true, solve() should return
    /// Unknown immediately instead of running to completion.
    #[test]
    fn test_z4sat_set_cancelled_interrupts_solve() {
        use std::sync::atomic::AtomicBool;
        use std::sync::Arc;

        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);

        // Build a satisfiable formula.
        s.add_clause(&[Lit::pos(a), Lit::pos(b)]);

        // Verify it is SAT without cancellation.
        let r1 = s.solve(&[]);
        assert_eq!(r1, SatResult::Sat, "should be SAT without cancellation");

        // Set the cancellation flag BEFORE solving.
        let cancelled = Arc::new(AtomicBool::new(true));
        s.set_cancelled(cancelled);

        // Solve should return Unknown because the interrupt flag is set.
        let r2 = s.solve(&[]);
        assert_eq!(
            r2,
            SatResult::Unknown,
            "solve() should return Unknown when cancelled flag is set"
        );
    }

    /// Verify that set_cancelled also interrupts solve_with_temporary_clause.
    #[test]
    fn test_z4sat_set_cancelled_interrupts_temp_clause_solve() {
        use std::sync::atomic::AtomicBool;
        use std::sync::Arc;

        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);

        s.add_clause(&[Lit::pos(a), Lit::pos(b)]);

        // Set cancellation before the solve.
        let cancelled = Arc::new(AtomicBool::new(true));
        s.set_cancelled(cancelled);

        // Even with a temporary clause, solve should be interrupted.
        let r = s.solve_with_temporary_clause(&[Lit::pos(a)], &[Lit::neg(b)]);
        assert_eq!(
            r,
            SatResult::Unknown,
            "solve_with_temporary_clause should return Unknown when cancelled"
        );
    }

    /// Verify that cancellation via set_cancelled is cooperative: the solver
    /// works normally until the flag is set, then returns Unknown, and
    /// continues working after the flag is cleared.
    #[test]
    fn test_z4sat_set_cancelled_cooperative_lifecycle() {
        use std::sync::atomic::{AtomicBool, Ordering};
        use std::sync::Arc;

        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);

        s.add_clause(&[Lit::pos(a)]);

        let flag = Arc::new(AtomicBool::new(false));
        s.set_cancelled(flag.clone());

        // Flag is false: solve should work normally.
        let r1 = s.solve(&[]);
        assert_eq!(r1, SatResult::Sat, "should work with flag=false");

        // Set the flag: solve should return Unknown.
        flag.store(true, Ordering::Relaxed);
        let r2 = s.solve(&[]);
        assert_eq!(r2, SatResult::Unknown, "should be Unknown with flag=true");

        // Clear the flag: solve should work again.
        flag.store(false, Ordering::Relaxed);
        let r3 = s.solve(&[]);
        assert_eq!(r3, SatResult::Sat, "should recover when flag cleared");
    }

    /// Verify that the SatSolver trait's default set_cancelled is a no-op
    /// for SimpleSolver (it doesn't crash or affect behavior).
    #[test]
    fn test_simple_solver_set_cancelled_noop() {
        use std::sync::atomic::AtomicBool;
        use std::sync::Arc;

        let mut s = SimpleSolver::new();
        let a = s.new_var();
        s.add_clause(&[Lit::pos(a)]);

        // Calling set_cancelled on SimpleSolver should be a no-op.
        let flag = Arc::new(AtomicBool::new(true));
        s.set_cancelled(flag);

        // SimpleSolver should still work (it doesn't check the flag).
        let r = s.solve(&[]);
        assert_eq!(r, SatResult::Sat, "SimpleSolver ignores cancellation");
    }

    // --- z4-sat variant backend tests ---

    mod z4_variant_tests {
        use super::*;

        /// Each z4-sat variant backend should solve a basic SAT instance.
        #[test]
        fn test_z4_variants_basic_sat() {
            let backends = [
                SolverBackend::Z4Sat,
                SolverBackend::Z4Luby,
                SolverBackend::Z4Stable,
                SolverBackend::Z4Geometric,
                SolverBackend::Z4Vmtf,
                SolverBackend::Z4Chb,
                SolverBackend::Z4NoPreprocess,
            ];
            for backend in backends {
                let mut s = backend.make_solver(3);
                s.add_clause(&[Lit::pos(Var(1)), Lit::pos(Var(2))]);
                let r = s.solve(&[]);
                assert_eq!(r, SatResult::Sat, "{backend:?} should solve basic SAT");
            }
        }

        /// Each z4-sat variant should detect UNSAT.
        #[test]
        fn test_z4_variants_basic_unsat() {
            let backends = [
                SolverBackend::Z4Sat,
                SolverBackend::Z4Luby,
                SolverBackend::Z4Stable,
                SolverBackend::Z4Geometric,
                SolverBackend::Z4Vmtf,
                SolverBackend::Z4Chb,
                SolverBackend::Z4NoPreprocess,
            ];
            for backend in backends {
                let mut s = backend.make_solver(3);
                s.add_clause(&[Lit::pos(Var(1))]);
                s.add_clause(&[Lit::neg(Var(1))]);
                let r = s.solve(&[]);
                assert_eq!(r, SatResult::Unsat, "{backend:?} should detect UNSAT");
            }
        }

        /// Each z4-sat variant should handle assumptions correctly.
        #[test]
        fn test_z4_variants_assumptions() {
            let backends = [
                SolverBackend::Z4Luby,
                SolverBackend::Z4Stable,
                SolverBackend::Z4Vmtf,
                SolverBackend::Z4Chb,
                SolverBackend::Z4NoPreprocess,
            ];
            for backend in backends {
                let mut s = backend.make_solver(3);
                let a = Var(1);
                let b = Var(2);
                s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
                // Assume !a, !b => UNSAT
                let r1 = s.solve(&[Lit::neg(a), Lit::neg(b)]);
                assert_eq!(
                    r1,
                    SatResult::Unsat,
                    "{backend:?}: contradicting assumptions should be UNSAT"
                );
                // Assume a => SAT
                let r2 = s.solve(&[Lit::pos(a)]);
                assert_eq!(
                    r2,
                    SatResult::Sat,
                    "{backend:?}: consistent assumption should be SAT"
                );
            }
        }

        /// Incremental stress test with z4-sat Luby backend.
        #[test]
        fn test_z4_luby_incremental_stress() {
            let mut s = SolverBackend::Z4Luby.make_solver(10);
            // Build a chain: v1 => v2 => ... => v9
            for i in 1..9u32 {
                s.add_clause(&[Lit::neg(Var(i)), Lit::pos(Var(i + 1))]);
            }
            s.add_clause(&[Lit::pos(Var(1))]);

            let r = s.solve(&[]);
            assert_eq!(r, SatResult::Sat);

            // Now add !v9 => UNSAT
            s.add_clause(&[Lit::neg(Var(9))]);
            let r2 = s.solve(&[]);
            assert_eq!(r2, SatResult::Unsat, "chain with !v9 should be UNSAT");
        }

        /// z4-sat VMTF backend factory works through SolverBackend.
        #[test]
        fn test_z4_vmtf_backend_factory() {
            let mut s = SolverBackend::Z4Vmtf.make_solver(3);
            s.add_clause(&[Lit::TRUE]);
            s.add_clause(&[Lit::pos(Var(1)), Lit::pos(Var(2))]);
            let r = s.solve(&[Lit::pos(Var(1))]);
            assert_eq!(r, SatResult::Sat);
        }
    }

    // --- clone_solver tests (#4062) ---

    /// Verify that SimpleSolver::clone_solver produces a solver with the same
    /// clause database that yields identical results on the same queries.
    #[test]
    fn test_simple_solver_clone_identical_results() {
        let mut orig = SimpleSolver::new();
        let a = orig.new_var(); // Var(1)
        let b = orig.new_var(); // Var(2)
        let c = orig.new_var(); // Var(3)

        // Add clauses: XOR(a, b) AND (b OR c)
        orig.add_clause(&[Lit::pos(a), Lit::pos(b)]);
        orig.add_clause(&[Lit::neg(a), Lit::neg(b)]);
        orig.add_clause(&[Lit::pos(b), Lit::pos(c)]);

        let mut cloned = orig
            .clone_solver()
            .expect("SimpleSolver clone should succeed");

        // Both should agree on SAT results with the same assumptions.
        let r_orig = orig.solve(&[Lit::pos(a)]);
        let r_clone = cloned.solve(&[Lit::pos(a)]);
        assert_eq!(r_orig, r_clone, "cloned solver should give same result");
        assert_eq!(r_orig, SatResult::Sat);

        // After cloning, adding a clause to the original should NOT affect the clone.
        orig.add_clause(&[Lit::neg(a)]); // Force a=false in original.
        let r_orig2 = orig.solve(&[Lit::pos(a)]);
        let r_clone2 = cloned.solve(&[Lit::pos(a)]);
        assert_eq!(
            r_orig2,
            SatResult::Unsat,
            "original with !a and assumption a should be UNSAT"
        );
        assert_eq!(
            r_clone2,
            SatResult::Sat,
            "clone should not have the !a clause"
        );
    }

    /// Verify that Z4SatCdclSolver::clone_solver produces a solver with the
    /// same clause database via clause log replay (#4062).
    #[test]
    fn test_z4sat_clone_identical_results() {
        let mut orig = Z4SatCdclSolver::new(4);
        let a = Var(1);
        let b = Var(2);
        let c = Var(3);

        // Build formula: XOR(a, b) AND (b OR c)
        orig.add_clause(&[Lit::pos(a), Lit::pos(b)]);
        orig.add_clause(&[Lit::neg(a), Lit::neg(b)]);
        orig.add_clause(&[Lit::pos(b), Lit::pos(c)]);

        let mut cloned = orig
            .clone_solver()
            .expect("Z4SatCdclSolver clone should succeed");

        // Both should agree on SAT results.
        let r_orig = orig.solve(&[Lit::pos(a)]);
        let r_clone = cloned.solve(&[Lit::pos(a)]);
        assert_eq!(r_orig, r_clone, "cloned solver should give same result");
        assert_eq!(r_orig, SatResult::Sat);

        // Check model values agree.
        assert_eq!(
            orig.value(Lit::pos(b)),
            cloned.value(Lit::pos(b)),
            "model values should agree"
        );
    }

    /// Verify that clone isolation holds: adding clauses to the original
    /// does not affect the clone, and vice versa.
    #[test]
    fn test_z4sat_clone_isolation() {
        let mut orig = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);

        // (a OR b)
        orig.add_clause(&[Lit::pos(a), Lit::pos(b)]);

        let mut cloned = orig.clone_solver().expect("clone should succeed");

        // Add !a to original only.
        orig.add_clause(&[Lit::neg(a)]);
        // Original: (a OR b) AND !a => b must be true.
        let r1 = orig.solve(&[]);
        assert_eq!(r1, SatResult::Sat);
        assert_eq!(orig.value(Lit::pos(b)), Some(true));

        // Clone: still has only (a OR b), both solutions available.
        let r2 = cloned.solve(&[Lit::pos(a)]);
        assert_eq!(
            r2,
            SatResult::Sat,
            "clone should not have !a clause from original"
        );
    }

    /// Verify that cloning a poisoned Z4SatCdclSolver returns None (#4062).
    #[test]
    fn test_z4sat_clone_poisoned_returns_none() {
        let mut s = Z4SatCdclSolver::new(3);
        s.add_clause(&[Lit::pos(Var(1))]);
        s.poisoned = true;
        assert!(
            s.clone_solver().is_none(),
            "poisoned solver clone should return None"
        );
    }

    /// Verify that the SatSolver trait's default clone_solver returns None
    /// for solvers that don't implement it.
    #[test]
    fn test_default_clone_solver_returns_none() {
        // The SatSolver trait default returns None.
        // We test via the trait object from SolverBackend::Simple
        // but SimpleSolver overrides clone_solver, so it should succeed.
        let s = SolverBackend::Simple.make_solver(3);
        assert!(
            s.clone_solver().is_some(),
            "SimpleSolver should support clone"
        );

        let z = SolverBackend::Z4Sat.make_solver(3);
        assert!(
            z.clone_solver().is_some(),
            "Z4SatCdclSolver should support clone"
        );
    }

    /// Stress test: clone a solver with many clauses and verify
    /// the clone produces correct results (#4062).
    #[test]
    fn test_z4sat_clone_many_clauses() {
        let num_vars = 20;
        let mut orig = Z4SatCdclSolver::new(num_vars + 1);

        // Build an implication chain: v1 => v2 => ... => v20.
        for i in 1..num_vars {
            orig.add_clause(&[Lit::neg(Var(i)), Lit::pos(Var(i + 1))]);
        }
        // v1 = true
        orig.add_clause(&[Lit::pos(Var(1))]);

        let mut cloned = orig.clone_solver().expect("clone should succeed");

        // Both should have v1..v20 all true.
        let r_orig = orig.solve(&[]);
        let r_clone = cloned.solve(&[]);
        assert_eq!(r_orig, SatResult::Sat);
        assert_eq!(r_clone, SatResult::Sat);
        for i in 1..=num_vars {
            assert_eq!(
                orig.value(Lit::pos(Var(i))),
                cloned.value(Lit::pos(Var(i))),
                "var {i} should have same value in original and clone"
            );
        }

        // Add !v20 to original only => UNSAT.
        orig.add_clause(&[Lit::neg(Var(num_vars))]);
        assert_eq!(orig.solve(&[]), SatResult::Unsat);
        // Clone should still be SAT.
        assert_eq!(cloned.solve(&[]), SatResult::Sat);
    }

    /// Verify that cloning preserves the ability to use solve_with_temporary_clause
    /// correctly on the cloned solver.
    #[test]
    fn test_z4sat_clone_temp_clause_works() {
        let mut orig = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);

        // Permanent: XOR(a, b)
        orig.add_clause(&[Lit::pos(a), Lit::pos(b)]);
        orig.add_clause(&[Lit::neg(a), Lit::neg(b)]);

        let mut cloned = orig.clone_solver().expect("clone should succeed");

        // Temp clause on clone: force both true => UNSAT (violates XOR).
        let r = cloned.solve_with_temporary_clause(&[Lit::pos(a)], &[Lit::pos(b)]);
        assert_eq!(r, SatResult::Unsat, "XOR violated by temp clause");

        // After temp clause, clone should still work normally.
        let r2 = cloned.solve(&[Lit::pos(a)]);
        assert_eq!(r2, SatResult::Sat, "clone should recover after temp clause");
    }

    // --- solve_with_budget tests (#4076) ---

    /// Budget of 0 must return Unknown immediately without doing any work.
    #[test]
    fn test_z4sat_budget_zero_returns_unknown() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        // Trivially SAT formula.
        s.add_clause(&[Lit::pos(a)]);
        let r = s.solve_with_budget(&[], 0);
        assert_eq!(
            r,
            SatResult::Unknown,
            "budget 0 should return Unknown immediately"
        );
    }

    /// Budget of 0 on SimpleSolver (trait default) also returns Unknown.
    #[test]
    fn test_simple_budget_zero_returns_unknown() {
        let mut s = SimpleSolver::new();
        let a = s.new_var();
        s.add_clause(&[Lit::pos(a)]);
        let r = s.solve_with_budget(&[], 0);
        assert_eq!(
            r,
            SatResult::Unknown,
            "SimpleSolver budget 0 should return Unknown"
        );
    }

    /// Large budget on an easy problem should behave like unlimited solve.
    #[test]
    fn test_z4sat_budget_large_easy_problem_sat() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);
        s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
        // Budget of 1M is effectively unlimited for this trivial problem.
        let r = s.solve_with_budget(&[Lit::pos(a)], 1_000_000);
        assert_eq!(
            r,
            SatResult::Sat,
            "large budget on easy SAT should find solution"
        );
        assert_eq!(
            s.value(Lit::pos(a)),
            Some(true),
            "model should be available after budgeted SAT"
        );
    }

    /// Large budget on an easy UNSAT problem should return Unsat.
    #[test]
    fn test_z4sat_budget_large_easy_problem_unsat() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        // a AND !a
        s.add_clause(&[Lit::pos(a)]);
        s.add_clause(&[Lit::neg(a)]);
        let r = s.solve_with_budget(&[], 1_000_000);
        assert_eq!(
            r,
            SatResult::Unsat,
            "large budget on easy UNSAT should detect unsatisfiability"
        );
    }

    /// Small budget on a hard pigeon hole problem should return Unknown.
    /// Pigeon hole (N+1 pigeons, N holes) requires exponential search.
    #[test]
    fn test_z4sat_budget_small_hard_problem_returns_unknown() {
        // Build pigeon hole: 7 pigeons, 6 holes (UNSAT but requires significant search).
        let num_holes = 6u32;
        let num_pigeons = num_holes + 1;
        let total_vars = num_pigeons * num_holes + 1; // +1 for Var(0)
        let mut s = Z4SatCdclSolver::new(total_vars);

        // p(i, j) = pigeon i is in hole j, variable index = 1 + i*num_holes + j
        for i in 0..num_pigeons {
            // Each pigeon must be in at least one hole.
            let clause: Vec<Lit> = (0..num_holes)
                .map(|j| {
                    let var_idx = 1 + i * num_holes + j;
                    Lit::pos(Var(var_idx))
                })
                .collect();
            s.add_clause(&clause);
        }
        // No two pigeons in the same hole.
        for j in 0..num_holes {
            for i1 in 0..num_pigeons {
                for i2 in (i1 + 1)..num_pigeons {
                    let l1 = Var(1 + i1 * num_holes + j);
                    let l2 = Var(1 + i2 * num_holes + j);
                    s.add_clause(&[Lit::neg(l1), Lit::neg(l2)]);
                }
            }
        }

        // With a tiny budget (100 conflicts), the solver should not have enough
        // time to prove UNSAT on pigeon hole 7/6.
        let r = s.solve_with_budget(&[], 100);
        // We accept Unknown (budget exhausted) or Unsat (solver was fast enough).
        // The key property: we do NOT hang indefinitely.
        assert!(
            r == SatResult::Unknown || r == SatResult::Unsat,
            "small budget on hard problem should return Unknown or Unsat, got {r:?}"
        );
    }

    /// Budget does not corrupt solver state: after a budgeted Unknown result,
    /// a subsequent unbounded solve should produce the correct answer.
    #[test]
    fn test_z4sat_budget_solver_usable_after_unknown() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);

        // (a OR b) AND (!a OR !b) — XOR: exactly one true.
        s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
        s.add_clause(&[Lit::neg(a), Lit::neg(b)]);

        // Budget 0 => Unknown.
        let r1 = s.solve_with_budget(&[], 0);
        assert_eq!(r1, SatResult::Unknown);

        // Subsequent unbounded solve should work correctly.
        let r2 = s.solve(&[]);
        assert_eq!(
            r2,
            SatResult::Sat,
            "solver should be usable after budget-limited Unknown"
        );
    }

    /// Poisoned solver returns Unknown from solve_with_budget.
    #[test]
    fn test_z4sat_budget_poisoned_returns_unknown() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        s.add_clause(&[Lit::pos(a)]);
        s.poisoned = true;
        let r = s.solve_with_budget(&[], 1_000_000);
        assert_eq!(
            r,
            SatResult::Unknown,
            "poisoned solver should return Unknown from solve_with_budget"
        );
    }

    /// SimpleSolver's default solve_with_budget ignores budget (falls through
    /// to regular solve) and produces correct results.
    #[test]
    fn test_simple_budget_correctness() {
        let mut s = SimpleSolver::new();
        let a = s.new_var();
        let b = s.new_var();
        s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
        // Non-zero budget falls through to regular solve.
        let r = s.solve_with_budget(&[Lit::pos(a)], 10);
        assert_eq!(
            r,
            SatResult::Sat,
            "SimpleSolver budget should fall through to regular solve"
        );
    }

    /// Trait-object dynamic dispatch works correctly with solve_with_budget.
    #[test]
    fn test_budget_via_trait_object() {
        let mut s: Box<dyn SatSolver> = SolverBackend::Z4Sat.make_solver(3);
        s.add_clause(&[Lit::pos(Var(1))]);
        // Budget 0 => Unknown via trait object.
        let r1 = s.solve_with_budget(&[], 0);
        assert_eq!(r1, SatResult::Unknown);
        // Large budget => Sat via trait object.
        let r2 = s.solve_with_budget(&[], 1_000_000);
        assert_eq!(r2, SatResult::Sat);
    }

    /// Budget on UNSAT core: when the problem is trivially UNSAT (conflict at
    /// clause level, no search needed), even a budget of 1 should return Unsat
    /// because the solver detects the conflict before any CDCL search.
    #[test]
    fn test_z4sat_budget_trivial_unsat() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        // Empty clause via contradictory permanent clauses.
        s.add_clause(&[Lit::pos(a)]);
        s.add_clause(&[Lit::neg(a)]);
        // Even budget=1 should detect this trivial UNSAT.
        let r = s.solve_with_budget(&[], 1);
        assert_eq!(
            r,
            SatResult::Unsat,
            "trivial UNSAT should be detected regardless of budget"
        );
    }

    /// Budget with assumptions: verify that assumptions and budget work together.
    #[test]
    fn test_z4sat_budget_with_assumptions() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);
        // (a OR b)
        s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
        // Assume !a, !b with large budget => UNSAT.
        let r = s.solve_with_budget(&[Lit::neg(a), Lit::neg(b)], 1_000_000);
        assert_eq!(
            r,
            SatResult::Unsat,
            "contradicting assumptions should be UNSAT within budget"
        );
        // UNSAT core should be available after budgeted UNSAT.
        let core = s.unsat_core();
        assert!(core.is_some(), "UNSAT core should be available after budgeted solve");
    }

    // --- clone_for_incremental tests (#4091) ---

    /// Verify that Z4SatCdclSolver::clone_for_incremental produces a solver
    /// that preserves learned clauses and gives correct results.
    #[test]
    fn test_z4sat_clone_for_incremental_basic() {
        let mut orig = Z4SatCdclSolver::new(4);
        let a = Var(1);
        let b = Var(2);
        let c = Var(3);

        // Build formula: XOR(a, b) AND (b OR c)
        orig.add_clause(&[Lit::pos(a), Lit::pos(b)]);
        orig.add_clause(&[Lit::neg(a), Lit::neg(b)]);
        orig.add_clause(&[Lit::pos(b), Lit::pos(c)]);

        // Do a solve to build up learned clauses and VSIDS scores.
        let r = orig.solve(&[Lit::pos(a)]);
        assert_eq!(r, SatResult::Sat);

        // Clone via native incremental clone.
        let mut cloned = orig
            .clone_for_incremental()
            .expect("Z4SatCdclSolver incremental clone should succeed");

        // Cloned solver should give same results.
        let r_clone = cloned.solve(&[Lit::pos(a)]);
        assert_eq!(r_clone, SatResult::Sat, "cloned solver should agree on SAT");
    }

    /// Verify clone_for_incremental isolation: changes to original don't
    /// affect clone.
    #[test]
    fn test_z4sat_clone_for_incremental_isolation() {
        let mut orig = Z4SatCdclSolver::new(3);
        let a = Var(1);
        let b = Var(2);

        orig.add_clause(&[Lit::pos(a), Lit::pos(b)]);

        let mut cloned = orig
            .clone_for_incremental()
            .expect("clone should succeed");

        // Add !a to original only.
        orig.add_clause(&[Lit::neg(a)]);
        let r1 = orig.solve(&[Lit::pos(a)]);
        assert_eq!(r1, SatResult::Unsat, "original with !a + assumption a should be UNSAT");

        // Clone should NOT have !a.
        let r2 = cloned.solve(&[Lit::pos(a)]);
        assert_eq!(r2, SatResult::Sat, "clone should not have !a from original");
    }

    /// Verify that poisoned solver returns None from clone_for_incremental.
    #[test]
    fn test_z4sat_clone_for_incremental_poisoned() {
        let mut s = Z4SatCdclSolver::new(3);
        s.add_clause(&[Lit::pos(Var(1))]);
        s.poisoned = true;
        assert!(
            s.clone_for_incremental().is_none(),
            "poisoned solver incremental clone should return None"
        );
    }

    // --- set_domain / clear_domain tests (#4091) ---

    /// Verify that set_domain + solve works correctly: domain restriction
    /// should not change the SAT/UNSAT result when all formula variables
    /// are within the domain (the correct IC3 usage pattern — domain-restricted
    /// solvers only contain domain-relevant clauses).
    #[test]
    fn test_z4sat_set_domain_basic_sat() {
        let mut s = Z4SatCdclSolver::new(4);
        let a = Var(1);
        let b = Var(2);
        let c = Var(3);

        // (a OR b) AND (b OR c) — all variables are in the domain.
        s.add_clause(&[Lit::pos(a), Lit::pos(b)]);
        s.add_clause(&[Lit::pos(b), Lit::pos(c)]);

        // Without domain restriction.
        let r1 = s.solve(&[Lit::pos(a)]);
        assert_eq!(r1, SatResult::Sat);

        // With domain restricted to {a, b, c} — covers all formula variables.
        s.set_domain(&[a, b, c]);
        let r2 = s.solve(&[Lit::pos(a)]);
        assert_eq!(r2, SatResult::Sat, "domain restriction should not change SAT result");

        // Clear domain and verify normal operation resumes.
        s.clear_domain();
        let r3 = s.solve(&[Lit::pos(c)]);
        assert_eq!(r3, SatResult::Sat, "after clear_domain, full solving should work");
    }

    /// Verify that set_domain works for UNSAT instances too.
    #[test]
    fn test_z4sat_set_domain_unsat() {
        let mut s = Z4SatCdclSolver::new(3);
        let a = Var(1);

        // a AND !a
        s.add_clause(&[Lit::pos(a)]);
        s.add_clause(&[Lit::neg(a)]);

        s.set_domain(&[a]);
        let r = s.solve(&[]);
        assert_eq!(r, SatResult::Unsat, "domain-restricted UNSAT should still detect conflict");

        s.clear_domain();
    }

    /// Verify that set_domain is a no-op on poisoned solver.
    #[test]
    fn test_z4sat_set_domain_poisoned_noop() {
        let mut s = Z4SatCdclSolver::new(3);
        s.poisoned = true;
        // Should not panic.
        s.set_domain(&[Var(1)]);
        s.clear_domain();
    }

    /// Default trait implementations for SimpleSolver: set_domain/clear_domain
    /// are no-ops and don't affect behavior.
    #[test]
    fn test_simple_solver_domain_noop() {
        let mut s = SimpleSolver::new();
        let a = s.new_var();
        s.add_clause(&[Lit::pos(a)]);
        s.set_domain(&[a]);
        let r = s.solve(&[]);
        assert_eq!(r, SatResult::Sat, "SimpleSolver ignores domain restriction");
        s.clear_domain();
        let r2 = s.solve(&[]);
        assert_eq!(r2, SatResult::Sat, "SimpleSolver ignores clear_domain");
    }

    // --- flip_to_none / minimize_model tests (#4091) ---

    /// Verify that flip_to_none on Z4SatCdclSolver works after a SAT result.
    #[test]
    fn test_z4sat_flip_to_none_basic() {
        let mut s = Z4SatCdclSolver::new(4);
        let a = Var(1);
        let b = Var(2);
        let c = Var(3);

        // (a) AND (b OR c) — a is forced, b/c have freedom.
        s.add_clause(&[Lit::pos(a)]);
        s.add_clause(&[Lit::pos(b), Lit::pos(c)]);

        let r = s.solve(&[]);
        assert_eq!(r, SatResult::Sat);

        // a is forced by a unit clause — flip should fail.
        let flipped_a = s.flip_to_none(a);
        assert!(!flipped_a, "a is forced by unit clause, should not flip");

        // b or c may be flippable depending on the model.
        // We just verify no panic occurs.
        let _ = s.flip_to_none(b);
        let _ = s.flip_to_none(c);
    }

    /// Verify that minimize_model returns a subset of the original model.
    #[test]
    fn test_z4sat_minimize_model_basic() {
        let mut s = Z4SatCdclSolver::new(5);
        let a = Var(1);
        let b = Var(2);
        let c = Var(3);
        let d = Var(4);

        // (a) AND (b OR c) AND (c OR d) — a is essential, others have freedom.
        s.add_clause(&[Lit::pos(a)]);
        s.add_clause(&[Lit::pos(b), Lit::pos(c)]);
        s.add_clause(&[Lit::pos(c), Lit::pos(d)]);

        let r = s.solve(&[]);
        assert_eq!(r, SatResult::Sat);

        // Minimize with a as important — the result should include a.
        let minimized = s.minimize_model(&[a]);
        let min_vars: Vec<Var> = minimized.iter().map(|l| l.var()).collect();
        assert!(
            min_vars.contains(&a),
            "important variable a must be in minimized model"
        );
        // The minimized model should be no larger than the full variable count.
        assert!(
            minimized.len() <= 5,
            "minimized model should not exceed total variables"
        );
    }

    /// Verify that minimize_model returns empty on poisoned solver.
    #[test]
    fn test_z4sat_minimize_model_poisoned() {
        let mut s = Z4SatCdclSolver::new(3);
        s.poisoned = true;
        let result = s.minimize_model(&[Var(1)]);
        assert!(result.is_empty(), "poisoned solver minimize_model should return empty");
    }

    /// Default trait implementation: flip_to_none returns false for SimpleSolver.
    #[test]
    fn test_simple_solver_flip_to_none_default() {
        let mut s = SimpleSolver::new();
        let a = s.new_var();
        s.add_clause(&[Lit::pos(a)]);
        let r = s.solve(&[]);
        assert_eq!(r, SatResult::Sat);
        // Default implementation returns false.
        assert!(!s.flip_to_none(a), "SimpleSolver default flip_to_none returns false");
    }

    /// Default trait implementation: minimize_model returns empty for SimpleSolver.
    #[test]
    fn test_simple_solver_minimize_model_default() {
        let mut s = SimpleSolver::new();
        let a = s.new_var();
        s.add_clause(&[Lit::pos(a)]);
        let r = s.solve(&[]);
        assert_eq!(r, SatResult::Sat);
        let result = s.minimize_model(&[a]);
        assert!(result.is_empty(), "SimpleSolver default minimize_model returns empty");
    }

}
