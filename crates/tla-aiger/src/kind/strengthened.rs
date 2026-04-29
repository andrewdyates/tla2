// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strengthened k-induction engine with auxiliary invariant discovery.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use crate::check_result::CheckResult;
use crate::sat_types::{Lit, SatResult, SatSolver, SolverBackend, Var};
use crate::transys::{Transys, VarRenamer};

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
    pub(crate) invariant_lits: Vec<Lit>,
    /// Discovered pair invariants: each entry is (!l_i, !l_j) meaning
    /// "l_i AND l_j is unreachable". Asserted as clause [!l_i, !l_j] at each depth.
    pub(crate) pair_invariants: Vec<(Lit, Lit)>,
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
                        eprintln!("kind-str: spurious SAT at k={k} ({reason}). Continuing.",);
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
    pub(crate) fn discover_init_invariants(&mut self) {
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
            .filter(|&&l| !self.invariant_lits.contains(&l) && !self.invariant_lits.contains(&!l))
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
                    // Store as (l_i, l_j) -- the clause is [!l_i, !l_j].
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
            self.ts
                .load_trans_renamed(self.step_solver.as_mut(), &|lit| {
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
            self.bmc_solver
                .ensure_vars(self.bmc_renamer.max_allocated());
            let renamer = &self.bmc_renamer;
            self.ts
                .load_trans_renamed(self.bmc_solver.as_mut(), &|lit| {
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
            let bad_at_d = self
                .renamer
                .rename_lit(self.bad_base, self.bad_asserted_depth);
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
