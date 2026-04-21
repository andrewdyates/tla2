// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! k-Induction engine for AIGER safety checking.
//!
//! Uses a single SAT solver instance (mirroring rIC3's efficient approach):
//! - Transition clauses are loaded incrementally for each unrolled step.
//! - `!bad` at depths 0..k-1 is asserted permanently (for the induction check).
//! - The init constraints are used as **assumptions** for the base case check.
//! - The induction step check uses the bad literal at depth k as an assumption.
//!
//! Algorithm (following rIC3's `kind.rs`):
//! 1. Unroll transition to step k.
//! 2. **Induction step first** (k > 0): Assert `!bad` at 0..k-1 permanently.
//!    Check if `bad@k` is satisfiable (without init). If UNSAT → SAFE.
//! 3. **Base case**: Check if `bad@k` is reachable from init by adding init
//!    constraints as assumptions. If SAT → UNSAFE.
//! 4. Increment k and repeat.
//!
//! Checking induction BEFORE base is key: an induction success (UNSAT) is
//! conclusive and avoids wasting time on base case checks that can't prove safety.
//!
//! Reference: rIC3 `src/kind.rs` (298 lines), adapted for our SAT types.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use crate::check_result::CheckResult;
use crate::sat_types::{Lit, SatResult, SatSolver, SolverBackend, Var};
use crate::transys::{Transys, VarRenamer};

/// Configuration for the k-induction engine.
#[derive(Debug, Clone)]
pub struct KindConfig {
    /// Enable simple-path constraint in the inductive step solver.
    ///
    /// The simple-path constraint asserts that all states in the induction
    /// trace are pairwise distinct (no two time steps visit the same state).
    /// This strengthens the induction hypothesis, helping k-induction prove
    /// properties that are not directly k-inductive but become so when
    /// restricted to simple (non-looping) paths.
    ///
    /// Reference: rIC3 `kind.rs` with `--simple-path` flag.
    /// rIC3's default portfolio uses `kind --step 1 --simple-path`.
    pub simple_path: bool,

    /// Skip the base case (BMC) check. When true, only the induction step
    /// is checked. This is useful when BMC is already running in the portfolio
    /// and we only need the induction proof.
    ///
    /// Reference: rIC3 `kind.rs` `--skip-bmc` flag.
    pub skip_bmc: bool,
}

impl Default for KindConfig {
    fn default() -> Self {
        KindConfig {
            simple_path: false,
            skip_bmc: false,
        }
    }
}

/// k-Induction engine.
///
/// Uses a single SAT solver for both base and step checks. Init constraints
/// are added as assumptions for the base case, while `!bad` at earlier depths
/// is asserted permanently for the induction step.
///
/// This mirrors rIC3's efficient single-solver design, halving memory usage
/// compared to the two-solver approach.
pub struct KindEngine {
    ts: Transys,
    /// Single solver for both base and step checks.
    solver: Box<dyn SatSolver>,
    renamer: VarRenamer,
    /// How far we've unrolled the transition relation.
    unrolled_depth: usize,
    /// How far we've asserted `!bad` (for induction step).
    bad_asserted_depth: usize,
    /// Bad literal in base encoding.
    bad_base: Lit,
    /// Init constraint literals (used as assumptions for base case).
    init_assumption_lits: Vec<Lit>,
    /// Cancellation flag.
    cancelled: Arc<AtomicBool>,
    /// Configuration.
    config: KindConfig,
}

impl KindEngine {
    pub fn new(ts: Transys) -> Self {
        Self::with_config(ts, KindConfig::default())
    }

    /// Create a k-induction engine with the simple-path constraint enabled.
    ///
    /// This is rIC3's default k-induction mode (`--simple-path`).
    pub fn new_simple_path(ts: Transys) -> Self {
        Self::with_config(
            ts,
            KindConfig {
                simple_path: true,
                skip_bmc: false,
            },
        )
    }

    /// Create a k-induction engine with a specific configuration.
    pub fn with_config(ts: Transys, config: KindConfig) -> Self {
        Self::with_config_and_backend(ts, config, SolverBackend::Z4Sat)
    }

    /// Create a k-induction engine with a specific configuration and solver backend.
    ///
    /// This allows the portfolio to spawn k-induction engines backed by different
    /// z4-sat configurations (Luby restarts, stable mode, VMTF branching, etc.)
    /// for diversity. Mirrors the backend selection pattern established for BMC.
    pub fn with_config_and_backend(
        ts: Transys,
        config: KindConfig,
        backend: SolverBackend,
    ) -> Self {
        let mut solver: Box<dyn SatSolver> = backend.make_solver(ts.max_var + 1);
        let mut renamer = VarRenamer::new(&ts);

        // Constrain Var(0) = false (AIGER convention: literal 0 = constant FALSE).
        solver.add_clause(&[Lit::TRUE]);

        // Initialize with trans at step 0
        renamer.ensure_step(0);
        solver.ensure_vars(renamer.max_allocated());
        ts.load_trans_renamed(solver.as_mut(), &|lit| renamer.rename_lit(lit, 0));

        let bad_base = ts.get_bad_lit(solver.as_mut());

        // Collect init constraint literals for assumption-based base case.
        // We load init as permanent clauses AND collect them as assumption lits.
        // For the base case: assumptions include init lits + bad@k.
        // For the step case: no init assumptions, just bad@k.
        let mut init_assumption_lits = Vec::new();
        for clause in &ts.init_clauses {
            // Only unit clauses can be used directly as assumptions.
            // Non-unit init clauses are added permanently (they're always needed).
            if clause.lits.len() == 1 {
                init_assumption_lits.push(clause.lits[0]);
            } else {
                solver.add_clause(&clause.lits);
            }
        }

        KindEngine {
            ts,
            solver,
            renamer,
            unrolled_depth: 0,
            bad_asserted_depth: 0,
            bad_base,
            init_assumption_lits,
            cancelled: Arc::new(AtomicBool::new(false)),
            config,
        }
    }

    /// Set the cancellation flag.
    ///
    /// Propagates the flag to the SAT solver so z4-sat's CDCL loop can exit
    /// promptly when cancelled (#4057).
    pub fn set_cancelled(&mut self, cancelled: Arc<AtomicBool>) {
        self.solver.set_cancelled(cancelled.clone());
        self.cancelled = cancelled;
    }

    /// Run k-induction up to `max_k` steps.
    ///
    /// Uses rIC3's induction-first strategy:
    /// 1. Unroll to depth k.
    /// 2. Check induction step (no init, !bad@0..k-1, bad@k?) — UNSAT → SAFE.
    /// 3. Check base case (init + bad@k?) — SAT → UNSAFE.
    /// 4. Repeat with k+1.
    pub fn check(&mut self, max_k: usize) -> CheckResult {
        for k in 0..=max_k {
            if self.cancelled.load(Ordering::Relaxed) {
                return CheckResult::Unknown {
                    reason: "cancelled".into(),
                };
            }

            // Unroll transition to step k
            if k > 0 {
                self.unroll_to(k);
                // Add simple-path constraints if enabled
                self.add_simple_path_constraint(k);
            }

            // Induction step check (for k > 0):
            // Assert !bad at steps 0..k-1, check if bad@k is satisfiable
            // WITHOUT init constraints. UNSAT → property is k-inductive → SAFE.
            if k > 0 {
                self.assert_no_bad_up_to(k - 1);

                let bad_at_k = self.renamer.rename_lit(self.bad_base, k);
                match self.solver.solve(&[bad_at_k]) {
                    SatResult::Unsat => {
                        if self.config.simple_path {
                            // SOUNDNESS GUARD (#4039): When simple-path is
                            // enabled, the step solver's UNSAT may be due to
                            // the simple-path constraints exhausting the
                            // constrained state space, NOT because the property
                            // is truly k-inductive. This caused a false UNSAT
                            // on microban_24 where the base solver uses a
                            // separate instance without simple-path constraints
                            // and may not have explored all reachable depths.
                            //
                            // Conservative fix: treat simple-path step UNSAT as
                            // Unknown rather than Safe. IC3 and standard
                            // k-induction in the portfolio can still prove Safe
                            // properties.
                            return CheckResult::Unknown {
                                reason: format!(
                                    "simple-path step UNSAT at k={k} \
                                     (may be state-space exhaustion, not k-inductiveness)"
                                ),
                            };
                        }
                        // Standard k-induction (no simple-path): step UNSAT
                        // means the property is genuinely k-inductive.
                        return CheckResult::Safe;
                    }
                    SatResult::Sat => {
                        // Induction step fails — continue to larger k
                    }
                    SatResult::Unknown => {
                        return CheckResult::Unknown {
                            reason: format!("step solver unknown at k={k}"),
                        };
                    }
                }
            }

            // Base case: is bad reachable at step k from init?
            // Use init constraints as assumptions alongside bad@k.
            if !self.config.skip_bmc {
                let bad_at_k = self.renamer.rename_lit(self.bad_base, k);
                let mut assumptions = self.init_assumption_lits.clone();
                assumptions.push(bad_at_k);

                match self.solver.solve(&assumptions) {
                    SatResult::Sat => {
                        let trace = self.extract_trace(k);
                        // Verify witness by simulating the circuit (#4103).
                        // If the trace doesn't actually reach a bad state,
                        // the SAT solver returned a spurious result.
                        if let Err(reason) = self.ts.verify_witness(&trace) {
                            eprintln!(
                                "k-ind: spurious SAT at k={k} (witness verification \
                                 failed: {reason}). Ignoring and continuing search.",
                            );
                            // Continue to next k instead of reporting UNSAFE
                        } else {
                            return CheckResult::Unsafe { depth: k, trace };
                        }
                    }
                    SatResult::Unsat => {
                        // Not reachable at step k, continue
                    }
                    SatResult::Unknown => {
                        return CheckResult::Unknown {
                            reason: format!("base solver unknown at k={k}"),
                        };
                    }
                }
            }
        }

        CheckResult::Unknown {
            reason: format!("k-induction reached bound {max_k}"),
        }
    }

    /// Unroll the transition relation to step k.
    fn unroll_to(&mut self, k: usize) {
        while self.unrolled_depth < k {
            let next_k = self.unrolled_depth + 1;
            self.renamer.ensure_step(next_k);
            self.solver.ensure_vars(self.renamer.max_allocated());

            let renamer = &self.renamer;
            self.ts
                .load_trans_renamed(self.solver.as_mut(), &|lit| renamer.rename_lit(lit, next_k));

            // Wire latches from step next_k-1 to step next_k
            for &latch_var in &self.ts.latch_vars {
                let next_lit = self.ts.next_state[&latch_var];
                let next_at_prev = self.renamer.rename_lit(next_lit, next_k - 1);
                let curr_at_k = Lit::pos(self.renamer.rename_var(latch_var, next_k));
                self.solver.add_clause(&[!curr_at_k, next_at_prev]);
                self.solver.add_clause(&[curr_at_k, !next_at_prev]);
            }

            self.unrolled_depth = next_k;
        }
    }

    /// Assert !bad at all steps from bad_asserted_depth+1 up to k (inclusive).
    /// These are permanent clauses for the induction step.
    fn assert_no_bad_up_to(&mut self, k: usize) {
        while self.bad_asserted_depth < k {
            let next_depth = self.bad_asserted_depth + 1;
            // We assert !bad at depth `bad_asserted_depth` (which is the step
            // we haven't asserted yet). But we need to be careful: at depth 0,
            // we haven't asserted anything yet.
            let bad_at_depth = self.renamer.rename_lit(self.bad_base, self.bad_asserted_depth);
            self.solver.add_clause(&[!bad_at_depth]);
            self.bad_asserted_depth = next_depth;
        }
        // Also assert at depth k itself if not yet done
        if self.bad_asserted_depth <= k {
            let bad_at_k = self.renamer.rename_lit(self.bad_base, k);
            self.solver.add_clause(&[!bad_at_k]);
            self.bad_asserted_depth = k + 1;
        }
    }

    /// Add simple-path constraint between step `new_step` and all previous steps.
    ///
    /// For each pair (i, new_step) with i < new_step, asserts that the latch
    /// states at steps i and new_step are pairwise distinct. Encoded as:
    ///   OR over all latches L: (L@i XOR L@new_step)
    /// which is equivalent to:
    ///   OR over all latches L: (L@i != L@new_step)
    ///
    /// This means at least one latch must differ between any two time steps,
    /// preventing the induction trace from revisiting states. This strengthens
    /// the induction hypothesis and helps prove properties that are not directly
    /// k-inductive but become so on simple paths.
    ///
    /// Reference: rIC3 uses `enable_simple_path()` on TransysUnroll, which adds
    /// XOR-difference disjunctions for each pair of steps.
    fn add_simple_path_constraint(&mut self, new_step: usize) {
        if !self.config.simple_path || self.ts.latch_vars.is_empty() {
            return;
        }

        for earlier_step in 0..new_step {
            // Build: OR_{latch L} (L@earlier XOR L@new_step)
            // XOR(a, b) = (a AND !b) OR (!a AND b)
            // To encode this in CNF without auxiliary variables for each latch,
            // we use the Tseitin-like approach: introduce a fresh diff variable
            // for each latch and assert the disjunction of diffs.
            //
            // For each latch L:
            //   diff_L <=> (L@earlier XOR L@new_step)
            //   Tseitin:
            //     diff_L -> (L@earlier XOR L@new_step):
            //       (!diff_L OR L@earlier OR L@new_step) AND (!diff_L OR !L@earlier OR !L@new_step)
            //     (L@earlier XOR L@new_step) -> diff_L:
            //       (diff_L OR L@earlier OR !L@new_step) AND (diff_L OR !L@earlier OR L@new_step)
            //
            // Then assert: OR_{latch L} diff_L

            let mut diff_lits = Vec::with_capacity(self.ts.latch_vars.len());

            for &latch_var in &self.ts.latch_vars {
                let l_earlier = Lit::pos(self.renamer.rename_var(latch_var, earlier_step));
                let l_new = Lit::pos(self.renamer.rename_var(latch_var, new_step));

                let diff_var = self.solver.new_var();
                let diff = Lit::pos(diff_var);

                // diff -> XOR(l_earlier, l_new):
                // !diff OR l_earlier OR l_new
                self.solver.add_clause(&[!diff, l_earlier, l_new]);
                // !diff OR !l_earlier OR !l_new
                self.solver.add_clause(&[!diff, !l_earlier, !l_new]);

                // XOR(l_earlier, l_new) -> diff:
                // diff OR l_earlier OR !l_new
                self.solver.add_clause(&[diff, l_earlier, !l_new]);
                // diff OR !l_earlier OR l_new
                self.solver.add_clause(&[diff, !l_earlier, l_new]);

                diff_lits.push(diff);
            }

            // At least one latch must differ: OR(diff_0, diff_1, ..., diff_n)
            self.solver.add_clause(&diff_lits);
        }
    }

    /// Extract a counterexample trace from the solver (named string keys).
    fn extract_trace(&self, depth: usize) -> Vec<rustc_hash::FxHashMap<String, bool>> {
        let mut trace = Vec::with_capacity(depth + 1);
        for k in 0..=depth {
            let mut step = rustc_hash::FxHashMap::default();
            for (idx, &latch_var) in self.ts.latch_vars.iter().enumerate() {
                let renamed = self.renamer.rename_var(latch_var, k);
                let val = self.solver.value(Lit::pos(renamed)).unwrap_or(false);
                step.insert(format!("l{idx}"), val);
            }
            for (idx, &input_var) in self.ts.input_vars.iter().enumerate() {
                let renamed = self.renamer.rename_var(input_var, k);
                let val = self.solver.value(Lit::pos(renamed)).unwrap_or(false);
                step.insert(format!("i{idx}"), val);
            }
            trace.push(step);
        }
        trace
    }

    /// Extract a literal-level witness trace from the solver.
    ///
    /// Each time step is a vector of literals over the original (base)
    /// latch and input variables. Call this after `check()` returns
    /// `CheckResult::Unsafe` to get the raw witness.
    pub fn extract_lit_trace(&self, depth: usize) -> Vec<Vec<Lit>> {
        let mut trace = Vec::with_capacity(depth + 1);
        for k in 0..=depth {
            let mut step_lits = Vec::new();
            for &latch_var in &self.ts.latch_vars {
                let renamed = self.renamer.rename_var(latch_var, k);
                match self.solver.value(Lit::pos(renamed)) {
                    Some(true) => step_lits.push(Lit::pos(latch_var)),
                    Some(false) => step_lits.push(Lit::neg(latch_var)),
                    None => {}
                }
            }
            for &input_var in &self.ts.input_vars {
                let renamed = self.renamer.rename_var(input_var, k);
                match self.solver.value(Lit::pos(renamed)) {
                    Some(true) => step_lits.push(Lit::pos(input_var)),
                    Some(false) => step_lits.push(Lit::neg(input_var)),
                    None => {}
                }
            }
            trace.push(step_lits);
        }
        trace
    }
}

// ---------------------------------------------------------------------------
// Strengthened k-Induction
// ---------------------------------------------------------------------------

/// Strengthened k-induction engine with auxiliary invariant discovery.
///
/// Extends standard k-induction with:
/// 1. Single-literal invariant discovery (stuck-at-constant latches from init + BMC).
/// 2. Counterexample-guided strengthening (CEGS): when the inductive step fails,
///    analyze the model to find invariants that block the spurious counterexample.
/// 3. Two-literal (pair) invariant discovery for harder properties.
///
/// Uses two solvers: a BMC solver for invariant validation, and the main step
/// solver for k-induction with invariants as strengthening constraints.
pub struct KindStrengthenedEngine {
    ts: Transys,
    step_solver: Box<dyn SatSolver>,
    bmc_solver: Box<dyn SatSolver>,
    renamer: VarRenamer,
    bmc_renamer: VarRenamer,
    step_unrolled_depth: usize,
    bmc_unrolled_depth: usize,
    bad_asserted_depth: usize,
    bad_base: Lit,
    bmc_bad_base: Lit,
    init_assumption_lits: Vec<Lit>,
    /// Discovered invariant literals over base (time-0) variables.
    invariant_lits: Vec<Lit>,
    /// Discovered pair invariants: each entry is (!l_i, !l_j) meaning
    /// "l_i AND l_j is unreachable". Asserted as clause [!l_i, !l_j] at each depth.
    pair_invariants: Vec<(Lit, Lit)>,
    invariants_asserted_depth: usize,
    cancelled: Arc<AtomicBool>,
}

impl KindStrengthenedEngine {
    pub fn new(ts: Transys) -> Self {
        Self::with_backend(ts, SolverBackend::Z4Sat)
    }

    pub fn with_backend(ts: Transys, backend: SolverBackend) -> Self {
        // Step solver setup
        let mut step_solver: Box<dyn SatSolver> = backend.make_solver(ts.max_var + 1);
        let mut renamer = VarRenamer::new(&ts);
        step_solver.add_clause(&[Lit::TRUE]);
        renamer.ensure_step(0);
        step_solver.ensure_vars(renamer.max_allocated());
        ts.load_trans_renamed(step_solver.as_mut(), &|lit| renamer.rename_lit(lit, 0));
        let bad_base = ts.get_bad_lit(step_solver.as_mut());

        // BMC solver setup
        let mut bmc_solver: Box<dyn SatSolver> = backend.make_solver(ts.max_var + 1);
        let mut bmc_renamer = VarRenamer::new(&ts);
        bmc_solver.add_clause(&[Lit::TRUE]);
        bmc_renamer.ensure_step(0);
        bmc_solver.ensure_vars(bmc_renamer.max_allocated());
        ts.load_trans_renamed(bmc_solver.as_mut(), &|lit| bmc_renamer.rename_lit(lit, 0));
        let bmc_bad_base = ts.get_bad_lit(bmc_solver.as_mut());

        let mut init_assumption_lits = Vec::new();
        for clause in &ts.init_clauses {
            if clause.lits.len() == 1 {
                init_assumption_lits.push(clause.lits[0]);
            } else {
                bmc_solver.add_clause(&clause.lits);
            }
        }

        KindStrengthenedEngine {
            ts,
            step_solver,
            bmc_solver,
            renamer,
            bmc_renamer,
            step_unrolled_depth: 0,
            bmc_unrolled_depth: 0,
            bad_asserted_depth: 0,
            bad_base,
            bmc_bad_base,
            init_assumption_lits,
            invariant_lits: Vec::new(),
            pair_invariants: Vec::new(),
            invariants_asserted_depth: 0,
            cancelled: Arc::new(AtomicBool::new(false)),
        }
    }

    pub fn set_cancelled(&mut self, cancelled: Arc<AtomicBool>) {
        self.step_solver.set_cancelled(cancelled.clone());
        self.bmc_solver.set_cancelled(cancelled.clone());
        self.cancelled = cancelled;
    }

    /// Run strengthened k-induction up to `max_k` steps.
    pub fn check(&mut self, max_k: usize) -> CheckResult {
        self.discover_init_invariants();

        for k in 0..=max_k {
            if self.cancelled.load(Ordering::Relaxed) {
                return CheckResult::Unknown {
                    reason: "cancelled".into(),
                };
            }

            if k > 0 {
                self.step_unroll_to(k);
            }
            self.assert_invariants_up_to(k);

            // Induction step check
            if k > 0 {
                self.step_assert_no_bad_up_to(k - 1);
                let bad_at_k = self.renamer.rename_lit(self.bad_base, k);
                match self.step_solver.solve(&[bad_at_k]) {
                    SatResult::Unsat => return CheckResult::Safe,
                    SatResult::Sat => {
                        let inv_count_before = self.invariant_lits.len();
                        let pair_count_before = self.pair_invariants.len();
                        let new_invs = self.ceg_strengthen(k);
                        if new_invs > 0 {
                            // Assert newly discovered invariants at all depths
                            // 0..=k. The previous assert_invariants_up_to(k) already
                            // advanced invariants_asserted_depth, so we must directly
                            // add the new invariants at depths that were already covered.
                            for d in 0..=k {
                                for &inv_lit in &self.invariant_lits[inv_count_before..] {
                                    let renamed = self.renamer.rename_lit(inv_lit, d);
                                    self.step_solver.add_clause(&[renamed]);
                                }
                                for &(l_i, l_j) in &self.pair_invariants[pair_count_before..] {
                                    let li_at_d = self.renamer.rename_lit(l_i, d);
                                    let lj_at_d = self.renamer.rename_lit(l_j, d);
                                    self.step_solver.add_clause(&[!li_at_d, !lj_at_d]);
                                }
                            }
                            let bad_retry = self.renamer.rename_lit(self.bad_base, k);
                            if matches!(self.step_solver.solve(&[bad_retry]), SatResult::Unsat) {
                                return CheckResult::Safe;
                            }
                        }
                    }
                    SatResult::Unknown => {
                        return CheckResult::Unknown {
                            reason: format!("step solver unknown at k={k}"),
                        };
                    }
                }
            }

            // Base case check
            self.bmc_unroll_to(k);
            let bmc_bad_at_k = self.bmc_renamer.rename_lit(self.bmc_bad_base, k);
            let mut assumptions = self.init_assumption_lits.clone();
            assumptions.push(bmc_bad_at_k);

            match self.bmc_solver.solve(&assumptions) {
                SatResult::Sat => {
                    let trace = self.bmc_extract_trace(k);
                    if let Err(reason) = self.ts.verify_witness(&trace) {
                        eprintln!(
                            "kind-str: spurious SAT at k={k} ({reason}). Continuing.",
                        );
                    } else {
                        return CheckResult::Unsafe { depth: k, trace };
                    }
                }
                SatResult::Unsat => {}
                SatResult::Unknown => {
                    return CheckResult::Unknown {
                        reason: format!("base solver unknown at k={k}"),
                    };
                }
            }
        }

        CheckResult::Unknown {
            reason: format!(
                "strengthened k-induction reached bound {max_k} ({} invariants)",
                self.invariant_lits.len()
            ),
        }
    }

    /// Discover invariants from initial state analysis and short BMC.
    fn discover_init_invariants(&mut self) {
        let mut init_vals: rustc_hash::FxHashMap<Var, bool> = rustc_hash::FxHashMap::default();
        for clause in &self.ts.init_clauses {
            if clause.lits.len() == 1 {
                let lit = clause.lits[0];
                init_vals.insert(lit.var(), !lit.is_negated());
            }
        }

        // Stuck-at-constant latches
        for &latch_var in &self.ts.latch_vars {
            if let Some(&next_lit) = self.ts.next_state.get(&latch_var) {
                if next_lit == Lit::FALSE && init_vals.get(&latch_var) == Some(&false) {
                    self.invariant_lits.push(Lit::neg(latch_var));
                } else if next_lit == Lit::TRUE && init_vals.get(&latch_var) == Some(&true) {
                    self.invariant_lits.push(Lit::pos(latch_var));
                }
            }
        }

        // BMC-based invariant discovery: check if each latch can flip within
        // a few steps from init.
        let discovery_depth = 5.min(self.ts.num_latches);
        self.bmc_unroll_to(discovery_depth);

        for &latch_var in &self.ts.latch_vars {
            if self.cancelled.load(Ordering::Relaxed) {
                break;
            }
            if self.invariant_lits.iter().any(|l| l.var() == latch_var) {
                continue;
            }
            if let Some(&init_val) = init_vals.get(&latch_var) {
                let opposite = if init_val {
                    Lit::neg(latch_var)
                } else {
                    Lit::pos(latch_var)
                };
                let mut can_flip = false;
                for d in 0..=discovery_depth {
                    let opp_at_d = self.bmc_renamer.rename_lit(opposite, d);
                    let mut assumptions = self.init_assumption_lits.clone();
                    assumptions.push(opp_at_d);
                    match self.bmc_solver.solve_with_budget(&assumptions, 500) {
                        SatResult::Sat => {
                            can_flip = true;
                            break;
                        }
                        SatResult::Unsat => {}
                        SatResult::Unknown => {
                            can_flip = true;
                            break;
                        }
                    }
                }
                if !can_flip {
                    let inv = if init_val {
                        Lit::pos(latch_var)
                    } else {
                        Lit::neg(latch_var)
                    };
                    self.invariant_lits.push(inv);
                }
            }
        }
    }

    /// Counterexample-guided strengthening: analyze the induction failure
    /// model and discover invariants that block spurious counterexamples.
    fn ceg_strengthen(&mut self, k: usize) -> usize {
        let mut new_count = 0;

        // Extract latch values from the counterexample's first state.
        let mut cex_s0_lits: Vec<Lit> = Vec::new();
        for &latch_var in &self.ts.latch_vars {
            let renamed = self.renamer.rename_var(latch_var, 0);
            match self.step_solver.value(Lit::pos(renamed)) {
                Some(true) => cex_s0_lits.push(Lit::pos(latch_var)),
                Some(false) => cex_s0_lits.push(Lit::neg(latch_var)),
                None => {}
            }
        }

        let check_depth = (k + 2).min(self.bmc_unrolled_depth).min(20);

        for &cex_lit in &cex_s0_lits {
            if self.cancelled.load(Ordering::Relaxed) {
                break;
            }
            if self.invariant_lits.contains(&!cex_lit) {
                continue;
            }

            let mut reachable = false;
            for d in 0..=check_depth {
                if d > self.bmc_unrolled_depth {
                    break;
                }
                let lit_at_d = self.bmc_renamer.rename_lit(cex_lit, d);
                let mut assumptions = self.init_assumption_lits.clone();
                assumptions.push(lit_at_d);
                match self.bmc_solver.solve_with_budget(&assumptions, 1000) {
                    SatResult::Sat => {
                        reachable = true;
                        break;
                    }
                    SatResult::Unsat => {}
                    SatResult::Unknown => {
                        reachable = true;
                        break;
                    }
                }
            }

            if !reachable {
                let inv = !cex_lit;
                if !self.invariant_lits.contains(&inv) {
                    self.invariant_lits.push(inv);
                    new_count += 1;
                }
            }
        }

        // Try pair invariants if single-literal strengthening didn't help.
        if cex_s0_lits.len() <= 100 && new_count == 0 {
            new_count += self.discover_pair_invariants(&cex_s0_lits, check_depth);
        }

        new_count
    }

    /// Discover two-literal invariants from a counterexample.
    fn discover_pair_invariants(&mut self, cex_lits: &[Lit], check_depth: usize) -> usize {
        let mut new_count = 0;
        let unconstrained: Vec<Lit> = cex_lits
            .iter()
            .filter(|&&l| {
                !self.invariant_lits.contains(&l) && !self.invariant_lits.contains(&!l)
            })
            .copied()
            .collect();

        let limit = unconstrained.len().min(30);
        for i in 0..limit {
            if self.cancelled.load(Ordering::Relaxed) {
                break;
            }
            for j in (i + 1)..limit {
                let l_i = unconstrained[i];
                let l_j = unconstrained[j];
                let mut reachable = false;
                for d in 0..=check_depth.min(10) {
                    if d > self.bmc_unrolled_depth {
                        break;
                    }
                    let li_at_d = self.bmc_renamer.rename_lit(l_i, d);
                    let lj_at_d = self.bmc_renamer.rename_lit(l_j, d);
                    let mut assumptions = self.init_assumption_lits.clone();
                    assumptions.push(li_at_d);
                    assumptions.push(lj_at_d);
                    match self.bmc_solver.solve_with_budget(&assumptions, 200) {
                        SatResult::Sat => {
                            reachable = true;
                            break;
                        }
                        SatResult::Unsat => {}
                        SatResult::Unknown => {
                            reachable = true;
                            break;
                        }
                    }
                }
                if !reachable {
                    // Track the pair invariant for future depth assertions.
                    // Store as (l_i, l_j) — the clause is [!l_i, !l_j].
                    self.pair_invariants.push((l_i, l_j));
                    new_count += 1;
                }
            }
        }
        new_count
    }

    fn step_unroll_to(&mut self, k: usize) {
        while self.step_unrolled_depth < k {
            let next_k = self.step_unrolled_depth + 1;
            self.renamer.ensure_step(next_k);
            self.step_solver.ensure_vars(self.renamer.max_allocated());
            let renamer = &self.renamer;
            self.ts.load_trans_renamed(self.step_solver.as_mut(), &|lit| {
                renamer.rename_lit(lit, next_k)
            });
            for &latch_var in &self.ts.latch_vars {
                let next_lit = self.ts.next_state[&latch_var];
                let next_at_prev = self.renamer.rename_lit(next_lit, next_k - 1);
                let curr_at_k = Lit::pos(self.renamer.rename_var(latch_var, next_k));
                self.step_solver.add_clause(&[!curr_at_k, next_at_prev]);
                self.step_solver.add_clause(&[curr_at_k, !next_at_prev]);
            }
            self.step_unrolled_depth = next_k;
        }
    }

    fn bmc_unroll_to(&mut self, k: usize) {
        while self.bmc_unrolled_depth < k {
            let next_k = self.bmc_unrolled_depth + 1;
            self.bmc_renamer.ensure_step(next_k);
            self.bmc_solver.ensure_vars(self.bmc_renamer.max_allocated());
            let renamer = &self.bmc_renamer;
            self.ts.load_trans_renamed(self.bmc_solver.as_mut(), &|lit| {
                renamer.rename_lit(lit, next_k)
            });
            for &latch_var in &self.ts.latch_vars {
                let next_lit = self.ts.next_state[&latch_var];
                let next_at_prev = self.bmc_renamer.rename_lit(next_lit, next_k - 1);
                let curr_at_k = Lit::pos(self.bmc_renamer.rename_var(latch_var, next_k));
                self.bmc_solver.add_clause(&[!curr_at_k, next_at_prev]);
                self.bmc_solver.add_clause(&[curr_at_k, !next_at_prev]);
            }
            self.bmc_unrolled_depth = next_k;
        }
    }

    fn step_assert_no_bad_up_to(&mut self, k: usize) {
        while self.bad_asserted_depth < k {
            let bad_at_d = self.renamer.rename_lit(self.bad_base, self.bad_asserted_depth);
            self.step_solver.add_clause(&[!bad_at_d]);
            self.bad_asserted_depth += 1;
        }
        if self.bad_asserted_depth <= k {
            let bad_at_k = self.renamer.rename_lit(self.bad_base, k);
            self.step_solver.add_clause(&[!bad_at_k]);
            self.bad_asserted_depth = k + 1;
        }
    }

    fn assert_invariants_up_to(&mut self, k: usize) {
        for d in self.invariants_asserted_depth..=k {
            for &inv_lit in &self.invariant_lits {
                let renamed = self.renamer.rename_lit(inv_lit, d);
                self.step_solver.add_clause(&[renamed]);
            }
            for &(l_i, l_j) in &self.pair_invariants {
                let li_at_d = self.renamer.rename_lit(l_i, d);
                let lj_at_d = self.renamer.rename_lit(l_j, d);
                self.step_solver.add_clause(&[!li_at_d, !lj_at_d]);
            }
        }
        if k >= self.invariants_asserted_depth {
            self.invariants_asserted_depth = k + 1;
        }
    }

    fn bmc_extract_trace(&self, depth: usize) -> Vec<rustc_hash::FxHashMap<String, bool>> {
        let mut trace = Vec::with_capacity(depth + 1);
        for k in 0..=depth {
            let mut step = rustc_hash::FxHashMap::default();
            for (idx, &latch_var) in self.ts.latch_vars.iter().enumerate() {
                let renamed = self.bmc_renamer.rename_var(latch_var, k);
                let val = self.bmc_solver.value(Lit::pos(renamed)).unwrap_or(false);
                step.insert(format!("l{idx}"), val);
            }
            for (idx, &input_var) in self.ts.input_vars.iter().enumerate() {
                let renamed = self.bmc_renamer.rename_var(input_var, k);
                let val = self.bmc_solver.value(Lit::pos(renamed)).unwrap_or(false);
                step.insert(format!("i{idx}"), val);
            }
            trace.push(step);
        }
        trace
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_aag;
    use crate::sat_types::Var;

    #[test]
    fn test_kind_trivially_unsafe() {
        // output=1 => bad at step 0
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new(ts);
        let result = kind.check(10);
        assert!(matches!(result, CheckResult::Unsafe { depth: 0, .. }));
    }

    #[test]
    fn test_kind_toggle_unsafe() {
        // Toggle: latch toggles, bad = latch. Reachable at step 1.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new(ts);
        let result = kind.check(10);
        assert!(matches!(result, CheckResult::Unsafe { depth: 1, .. }));
    }

    #[test]
    fn test_kind_latch_stays_zero_safe() {
        // Latch with next=0. Bad = latch.
        // Property: latch is always 0. This is 0-inductive (base: init forces 0,
        // step: next=0 means if !bad now, !bad next).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new(ts);
        let result = kind.check(10);
        assert!(
            matches!(result, CheckResult::Safe),
            "expected Safe, got {result:?}"
        );
    }

    #[test]
    fn test_kind_cancellation() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new(ts);
        let cancel = Arc::new(AtomicBool::new(true));
        kind.set_cancelled(cancel);
        let result = kind.check(100);
        assert!(matches!(result, CheckResult::Unknown { .. }));
    }

    // ----------- Simple-path constraint tests -----------

    #[test]
    fn test_kind_simple_path_trivially_unsafe() {
        // output=1 => bad at step 0
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new_simple_path(ts);
        let result = kind.check(10);
        assert!(matches!(result, CheckResult::Unsafe { depth: 0, .. }));
    }

    #[test]
    fn test_kind_simple_path_toggle_unsafe() {
        // Toggle: latch toggles, bad = latch. Reachable at step 1.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new_simple_path(ts);
        let result = kind.check(10);
        assert!(matches!(result, CheckResult::Unsafe { depth: 1, .. }));
    }

    #[test]
    fn test_kind_simple_path_latch_stays_zero_returns_unknown() {
        // Latch with next=0. Bad = latch. This property holds, but with the
        // #4039 soundness guard, simple-path k-induction returns Unknown
        // instead of Safe (to avoid false UNSAT on constrained circuits).
        // Standard k-induction and IC3 can still prove this safe.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new_simple_path(ts);
        let result = kind.check(10);
        assert!(
            matches!(result, CheckResult::Unknown { .. }),
            "expected Unknown (soundness guard), got {result:?}"
        );
    }

    #[test]
    fn test_kind_simple_path_two_step_shift_returns_unknown() {
        // 2-stage shift register: l0 toggles, l1 = delayed copy of l0.
        // bad = l0 AND l1 is never reachable (they alternate).
        // With the #4039 soundness guard, simple-path returns Unknown
        // instead of Safe. Standard k-induction or IC3 proves this safe.
        let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 2 4\n";
        let circuit = parse_aag(aag).unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new_simple_path(ts);
        let result = kind.check(20);
        assert!(
            matches!(result, CheckResult::Unknown { .. }),
            "expected Unknown (soundness guard), got {result:?}"
        );
    }

    #[test]
    fn test_kind_simple_path_cancellation() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind = KindEngine::new_simple_path(ts);
        let cancel = Arc::new(AtomicBool::new(true));
        kind.set_cancelled(cancel);
        let result = kind.check(100);
        assert!(matches!(result, CheckResult::Unknown { .. }));
    }

    // ----------- Backend selection tests -----------

    #[test]
    fn test_kind_with_config_and_backend_z4sat() {
        // Verify that explicit z4-sat backend matches the default constructor.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        let mut kind =
            KindEngine::with_config_and_backend(ts, KindConfig::default(), SolverBackend::Z4Sat);
        let result = kind.check(10);
        assert!(
            matches!(result, CheckResult::Safe),
            "expected Safe, got {result:?}"
        );
    }

    // ----------- z4-sat variant backend tests -----------

    mod z4_variant_kind_tests {
        use super::*;

        #[test]
        fn test_kind_z4_luby_trivially_unsafe() {
            let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut kind = KindEngine::with_config_and_backend(
                ts,
                KindConfig::default(),
                SolverBackend::Z4Luby,
            );
            let result = kind.check(10);
            assert!(matches!(result, CheckResult::Unsafe { depth: 0, .. }));
        }

        #[test]
        fn test_kind_z4_stable_toggle_unsafe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut kind = KindEngine::with_config_and_backend(
                ts,
                KindConfig::default(),
                SolverBackend::Z4Stable,
            );
            let result = kind.check(10);
            assert!(matches!(result, CheckResult::Unsafe { depth: 1, .. }));
        }

        #[test]
        fn test_kind_z4_vmtf_proves_safe() {
            // Latch with next=0, bad=latch. k-induction proves safe.
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut kind = KindEngine::with_config_and_backend(
                ts,
                KindConfig::default(),
                SolverBackend::Z4Vmtf,
            );
            let result = kind.check(10);
            assert!(
                matches!(result, CheckResult::Safe),
                "z4-sat VMTF k-induction should prove Safe, got {result:?}"
            );
        }

        #[test]
        fn test_kind_z4_luby_skip_bmc() {
            // skip-bmc mode with z4-sat Luby: should prove safe (stuck-at-zero).
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut kind = KindEngine::with_config_and_backend(
                ts,
                KindConfig {
                    simple_path: false,
                    skip_bmc: true,
                },
                SolverBackend::Z4Luby,
            );
            let result = kind.check(10);
            assert!(
                matches!(result, CheckResult::Safe),
                "z4-sat Luby kind-skip-bmc should prove Safe, got {result:?}"
            );
        }

        #[test]
        fn test_kind_z4_chb_cancellation() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut kind = KindEngine::with_config_and_backend(
                ts,
                KindConfig::default(),
                SolverBackend::Z4Chb,
            );
            let cancel = Arc::new(AtomicBool::new(true));
            kind.set_cancelled(cancel);
            let result = kind.check(100);
            assert!(matches!(result, CheckResult::Unknown { .. }));
        }

        /// z4-sat variant and default k-induction should agree on results.
        #[test]
        fn test_kind_z4_variant_default_agreement() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);

            let mut default_kind = KindEngine::new(ts.clone());
            let default_result = default_kind.check(10);

            let mut luby_kind = KindEngine::with_config_and_backend(
                ts,
                KindConfig::default(),
                SolverBackend::Z4Luby,
            );
            let luby_result = luby_kind.check(10);

            assert!(
                matches!(default_result, CheckResult::Safe),
                "z4 default result: {default_result:?}"
            );
            assert!(
                matches!(luby_result, CheckResult::Safe),
                "z4 Luby result: {luby_result:?}"
            );
        }
    }

    // ----------- Strengthened k-induction tests -----------

    mod strengthened_kind_tests {
        use super::*;
        use crate::sat_types::Var;

        #[test]
        fn test_strengthened_trivially_unsafe() {
            let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::new(ts);
            let result = engine.check(10);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 0, .. }),
                "expected Unsafe at depth 0, got {result:?}"
            );
        }

        #[test]
        fn test_strengthened_toggle_unsafe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::new(ts);
            let result = engine.check(10);
            assert!(
                matches!(result, CheckResult::Unsafe { depth: 1, .. }),
                "expected Unsafe at depth 1, got {result:?}"
            );
        }

        #[test]
        fn test_strengthened_latch_stays_zero_safe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::new(ts);
            let result = engine.check(10);
            assert!(
                matches!(result, CheckResult::Safe),
                "expected Safe, got {result:?}"
            );
        }

        #[test]
        fn test_strengthened_two_step_shift_safe() {
            // 2-stage shift register: l0 toggles, l1 = delayed copy of l0.
            // bad = l0 AND l1. Never reachable: l0 and l1 alternate phases.
            // Standard k-induction can't prove this, but strengthened should.
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 2 4\n";
            let circuit = parse_aag(aag).unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::new(ts);
            let result = engine.check(20);
            assert!(
                matches!(result, CheckResult::Safe),
                "strengthened kind should prove two-step shift Safe, got {result:?}"
            );
        }

        #[test]
        fn test_strengthened_cancellation() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::new(ts);
            let cancel = Arc::new(AtomicBool::new(true));
            engine.set_cancelled(cancel);
            let result = engine.check(100);
            assert!(matches!(result, CheckResult::Unknown { .. }));
        }

        #[test]
        fn test_strengthened_discovers_stuck_at_zero_invariant() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::new(ts);
            engine.discover_init_invariants();
            assert!(
                !engine.invariant_lits.is_empty(),
                "should discover at least one invariant"
            );
            assert!(
                engine.invariant_lits.contains(&Lit::neg(Var(1))),
                "should discover Var(1)=0 invariant, found: {:?}",
                engine.invariant_lits
            );
        }

        #[test]
        fn test_strengthened_z4_luby_backend() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::with_backend(ts, SolverBackend::Z4Luby);
            let result = engine.check(10);
            assert!(
                matches!(result, CheckResult::Safe),
                "z4-luby strengthened kind should prove Safe, got {result:?}"
            );
        }

        /// Verify that the init invariant discovery phase finds stuck-at
        /// invariants and that they are persisted as pair_invariants or
        /// invariant_lits (not lost after assertion).
        #[test]
        fn test_strengthened_invariant_persistence_after_check() {
            // Latch with next=0, bad = latch. The stuck-at-zero invariant
            // is discovered during init analysis and persists through check.
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let mut engine = KindStrengthenedEngine::new(ts);
            let result = engine.check(10);
            assert!(
                matches!(result, CheckResult::Safe),
                "expected Safe, got {result:?}"
            );
            // Invariants discovered during init phase should still be tracked.
            assert!(
                !engine.invariant_lits.is_empty(),
                "invariant_lits should persist after check()"
            );
        }

        /// Verify pair_invariants field is accessible and initialized empty.
        #[test]
        fn test_strengthened_pair_invariants_initialized_empty() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let ts = Transys::from_aiger(&circuit);
            let engine = KindStrengthenedEngine::new(ts);
            assert!(
                engine.pair_invariants.is_empty(),
                "pair_invariants should be empty before check()"
            );
        }
    }
}
