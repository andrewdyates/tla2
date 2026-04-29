// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core SAT types for the AIGER IC3/BMC engine.
//!
//! Provides `Var`, `Lit`, and `Clause` types modeled after rIC3's `logicrs` types.
//! Variables are 1-indexed (Var(0) is reserved as a constant/sentinel).

mod simple_solver;
mod z4_solver;

#[cfg(test)]
mod tests;

pub use simple_solver::SimpleSolver;
pub use z4_solver::Z4SatCdclSolver;

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

    /// Create a SAT solver in IC3/PDR mode (#4306 Patch B, z4#8569).
    ///
    /// Identical to [`make_solver()`](Self::make_solver) but immediately calls
    /// [`set_ic3_mode()`](SatSolver::set_ic3_mode) on the resulting solver.
    /// This is a strict superset of
    /// [`make_solver_no_inprocessing()`](Self::make_solver_no_inprocessing):
    /// in addition to disabling all periodic inprocessing, it also disables
    /// preprocessing, LRAT proof logging, chronological backtracking, cold
    /// restarts, rephase, flip search; locks the branching heuristic to
    /// stable-mode VSIDS; keeps the bucket queue permanently active for
    /// domain-restricted queries; and enables the fast incremental reset
    /// path (O(new_clauses) per solve vs O(num_vars)).
    ///
    /// Use this for IC3/PDR **frame solvers** (including the inf solver),
    /// lift solvers, and predprop solvers — any solver that makes thousands
    /// of short incremental queries under the IC3 driver. The mode persists
    /// across all subsequent `solve()` calls.
    ///
    /// BMC and k-induction should continue to use `make_solver()` (they
    /// make fewer, longer SAT calls that benefit from periodic inprocessing
    /// and do not share the IC3 query shape).
    ///
    /// Reference: rIC3's GipSAT ships a ~2,449-LOC SAT core with zero
    /// inprocessing, zero proofs, and a minimal per-solve reset; this
    /// configures z4-sat to match that shape.
    pub fn make_solver_ic3_mode(self, num_vars: u32) -> Box<dyn SatSolver> {
        let mut solver = self.make_solver(num_vars);
        solver.set_ic3_mode();
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

    /// Configure this solver for IC3/PDR workloads (#4306 Patch B, z4#8569).
    ///
    /// IC3 makes thousands of short incremental SAT queries per second, each
    /// with 5-50 domain variables in a system with hundreds-to-thousands of
    /// variables. Individual queries are often 0-5 conflicts, so per-call
    /// fixed costs dominate.
    ///
    /// `set_ic3_mode()` is a single entry point that disables every feature
    /// unnecessary for IC3 queries:
    ///
    /// - All inprocessing techniques (same as `disable_inprocessing()`).
    /// - Preprocessing — IC3 queries are too small to benefit.
    /// - LRAT proof logging — IC3 doesn't need proof certificates.
    /// - Chronological backtracking — non-chrono BT is optimal for the
    ///   shallow decision trees in IC3 queries.
    /// - Cold restarts — IC3 uses its own Luby restart scheme.
    /// - Rephase, flip search, lucky phases — IC3 uses forced phases from
    ///   PDR cube polarity.
    /// - Bucket queue stays permanently active (no 10-restart fallback to
    ///   heap) for domain-restricted queries. O(1) VSIDS for short queries.
    ///
    /// Additionally, incremental reset becomes O(new_clauses) instead of
    /// O(num_vars) — skipping ~80 cold scheduling state resets that IC3
    /// never reads.
    ///
    /// This is a strict superset of `disable_inprocessing()` and is the
    /// recommended configuration for all IC3/PDR frame solvers.
    ///
    /// Reference: rIC3 GipSAT achieves <10us/query with zero inprocessing,
    /// zero proofs, and minimal per-solve reset. z4-sat
    /// `solver/incremental.rs::set_ic3_mode`.
    ///
    /// Default: no-op for solvers that don't support this mode.
    fn set_ic3_mode(&mut self) {}

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
