// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Z4-sat CDCL solver wrapper for IC3/BMC engines.
//!
//! Wraps the z4-sat `Solver` with panic resilience, UNSAT core extraction,
//! push/pop scope management, and IC3-specific optimizations (domain restriction,
//! flip-to-none state lifting, conflict-budgeted solving).

use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use super::{Lit, SatResult, SatSolver, Var};

/// z4-sat CDCL solver with panic resilience and IC3-optimized solving.
///
/// z4-sat may panic on certain clause structures (see shrink.rs overflow,
/// conflict_analysis.rs assertion). Rather than crashing the entire
/// portfolio thread, this wrapper catches panics via `catch_unwind` and
/// degrades gracefully to `SatResult::Unknown`. Once a panic is caught,
/// the solver is marked `poisoned` and all subsequent calls return
/// `Unknown` immediately — the internal z4-sat state is unreliable
/// after a panic.
pub struct Z4SatCdclSolver {
    pub(crate) solver: z4_sat::Solver,
    pub(crate) num_vars: u32,
    model: Vec<Option<bool>>,
    last_core: Option<Vec<Lit>>,
    /// Set to `true` after catching a z4-sat panic. All subsequent calls
    /// return `SatResult::Unknown`. The solver cannot be recovered after
    /// a panic because z4-sat's internal invariants may be violated.
    pub(crate) poisoned: bool,
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

    /// Enable full IC3/PDR mode in the underlying z4-sat solver (#4306 Patch B,
    /// z4#8569).
    ///
    /// This is a strict superset of `disable_inprocessing()`: in addition to
    /// disabling all 16 inprocessing techniques, it also disables preprocessing,
    /// LRAT proof logging, chronological backtracking, cold restarts, rephase,
    /// and flip search; locks the branching heuristic to stable-mode VSIDS; and
    /// keeps the bucket queue permanently active for O(1) variable selection on
    /// short domain-restricted queries.
    ///
    /// The big win for cal14-style benchmarks is the per-query incremental
    /// reset: with ic3_mode on, `reset_search_state_incremental()` skips ~80
    /// cold scheduling state resets per solve call (EMA counters, tick
    /// watermarks, effort demotion, etc.) that the IC3 CDCL loop never reads.
    /// Per z4#8569, this saves ~5-10us per query — small per call but
    /// multiplicative across thousands of incremental queries.
    ///
    /// Must be called before `solve()` to take effect. Idempotent.
    fn set_ic3_mode(&mut self) {
        self.solver.set_ic3_mode();
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
