// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IC3 frame propagation: propagate lemmas forward, push_lemma, infinity frame
//! promotion, and core extraction helpers.

use super::config::consecution_verify_interval_full;
use super::engine::Ic3Engine;
use super::frame::Lemma;
use crate::sat_types::{Lit, SatResult, SatSolver, Var};

impl Ic3Engine {
    /// Push a generalized lemma to higher frames.
    pub(super) fn push_lemma(&mut self, frame: usize, cube: Vec<Lit>) -> (usize, Vec<Lit>) {
        let depth = self.frames.depth();
        for f in (frame + 1)..=depth {
            if f > self.solvers.len() {
                break;
            }
            if self.cube_sat_consistent_with_init(&cube) {
                return (f, cube);
            }
            let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();
            let assumptions = self.prime_cube(&cube);

            // Domain-restricted consecution (#4059, #4091).
            // `build_consecution_domain_solver` gates at >= 20 latches (reverted from 2).
            let is_ind = if let Some(mut domain_solver) =
                self.build_consecution_domain_solver(f, &cube)
            {
                domain_solver.set_cancelled(self.cancelled.clone());
                let domain_result = domain_solver
                    .solve_with_temporary_clause(&assumptions, &neg_cube);
                if domain_result == SatResult::Unsat {
                    true
                } else {
                    let solver_idx = f - 1;
                    if self.solvers[solver_idx].is_poisoned() {
                        if self.solver_rebuild_budget_exceeded(solver_idx) {
                            return (f, cube); // Conservative: stop pushing (#4105)
                        }
                        self.rebuild_solver_at(solver_idx);
                    }
                    // Set domain on the full frame solver for the fallback path.
                    let domain = self
                        .domain_computer
                        .compute_domain(&cube, &self.next_vars);
                    let domain_vars: Vec<Var> = (0..=self.max_var)
                        .filter(|&i| domain.contains(Var(i)))
                        .map(Var)
                        .collect();
                    self.solvers[solver_idx].set_domain(&domain_vars);
                    let result = self.solvers[solver_idx]
                        .solve_with_temporary_clause(&assumptions, &neg_cube)
                        == SatResult::Unsat;
                    self.solvers[solver_idx].clear_domain();
                    result
                }
            } else {
                let solver_idx = f - 1;
                if self.solvers[solver_idx].is_poisoned() {
                    if self.solver_rebuild_budget_exceeded(solver_idx) {
                        return (f, cube); // Conservative: stop pushing (#4105)
                    }
                    self.rebuild_solver_at(solver_idx);
                }
                self.solvers[solver_idx]
                    .solve_with_temporary_clause(&assumptions, &neg_cube)
                    == SatResult::Unsat
            };

            if !is_ind {
                return (f, cube);
            }
        }
        (depth + 1, cube)
    }

    /// Check if a cube is blocked at a frame and return the inductive core.
    pub(super) fn propagation_blocked(&mut self, frame: usize, cube: &[Lit]) -> Option<Vec<Lit>> {
        if frame == 0 {
            return None;
        }
        let solver_idx = frame - 1;
        if solver_idx >= self.solvers.len() {
            return None;
        }
        let assumptions = self.prime_cube(cube);

        // Domain-restricted consecution (#4059, #4091).
        // `build_consecution_domain_solver` gates at >= 20 latches (reverted from 2).
        if let Some(mut domain_solver) =
            self.build_consecution_domain_solver(frame, cube)
        {
            let domain = self
                .domain_computer
                .compute_domain(cube, &self.next_vars);
            self.domain_stats
                .record(domain.len(), self.max_var as usize + 1, true);

            domain_solver.set_cancelled(self.cancelled.clone());
            let domain_result = domain_solver.solve(&assumptions);
            if domain_result == SatResult::Unsat {
                let core = self.core_from_solver(domain_solver.as_ref(), cube);
                return Some(core);
            }
        } else {
            self.domain_stats
                .record(0, self.max_var as usize + 1, false);
        }

        if self.solvers[solver_idx].is_poisoned() {
            if self.solver_rebuild_budget_exceeded(solver_idx) {
                return None; // Conservative: treat as not blocked (#4105)
            }
            self.rebuild_solver_at(solver_idx);
        }
        let result = self.solvers[solver_idx].solve(&assumptions);
        match result {
            SatResult::Unsat => {
                let core = self.core_from_solver(self.solvers[solver_idx].as_ref(), cube);
                Some(core)
            }
            SatResult::Unknown => {
                if self.solver_rebuild_budget_exceeded(solver_idx) {
                    return None; // Conservative: treat as not blocked (#4105)
                }
                self.rebuild_solver_at(solver_idx);
                if self.solvers[solver_idx].solve(&assumptions) == SatResult::Unsat {
                    let core = self.core_from_solver(self.solvers[solver_idx].as_ref(), cube);
                    Some(core)
                } else {
                    None
                }
            }
            SatResult::Sat => None,
        }
    }

    /// Extract inductive core from a solver after an UNSAT result.
    pub(super) fn core_from_solver(&self, solver: &dyn SatSolver, cube: &[Lit]) -> Vec<Lit> {
        let Some(core) = solver.unsat_core() else {
            return cube.to_vec();
        };
        if core.is_empty() {
            return cube.to_vec();
        }
        let mut core_latch_vars = rustc_hash::FxHashSet::default();
        for &core_lit in &core {
            if let Some(&latch_var) = self.reverse_next.get(&core_lit.var()) {
                core_latch_vars.insert(latch_var);
            }
        }
        let reduced: Vec<Lit> = cube
            .iter()
            .filter(|lit| core_latch_vars.contains(&lit.var()))
            .copied()
            .collect();
        if reduced.is_empty() {
            return cube.to_vec();
        }
        if self.cube_sat_consistent_with_init(&reduced) {
            cube.to_vec()
        } else {
            reduced
        }
    }

    /// Propagate lemmas forward through frames with Counter-To-Propagation (CTP).
    pub(super) fn propagate(&mut self) -> bool {
        let depth = self.frames.depth();
        if depth < 2 {
            return false;
        }
        for k in 1..depth - 1 {
            self.frames.frames[k].lemmas.sort_by_key(|l| l.lits.len());
            let lemmas: Vec<Lemma> = self.frames.frames[k].lemmas.clone();
            let orig_count = lemmas.len();
            let mut pushed_indices = rustc_hash::FxHashSet::default();
            for (idx, lemma) in lemmas.iter().enumerate() {
                let cube: Vec<Lit> = lemma.lits.iter().map(|l| !*l).collect();
                let ctp_max = if self.config.ctp {
                    self.config.ctp_max
                } else {
                    1
                };
                let mut succeeded = false;
                for _ctp_attempt in 0..ctp_max {
                    if let Some(core_cube) = self.propagation_blocked(k + 1, &cube) {
                        if self.cube_sat_consistent_with_init(&core_cube) {
                            break;
                        }
                        self.consecution_verify_counter += 1;
                        let verify_interval = consecution_verify_interval_full(
                            self.ts.trans_clauses.len(),
                            self.ts.constraint_lits.len(),
                            self.ts.latch_vars.len(),
                        );
                        if self.ts.latch_vars.len() <= 60
                            && !self.crosscheck_disabled
                            && self.consecution_verify_counter % verify_interval == 0
                            && !self.verify_consecution_independent(k + 1, &core_cube, false)
                        {
                            break;
                        }
                        let core_lemma = Lemma::from_blocked_cube(&core_cube);
                        self.frames.add_lemma(k + 1, core_lemma.clone());
                        if k + 1 < self.solvers.len() {
                            self.solvers[k + 1].add_clause(&core_lemma.lits);
                        }
                        pushed_indices.insert(idx);
                        succeeded = true;
                        break;
                    }
                    if !self.config.ctp || k == 0 {
                        break;
                    }
                    let pred = self.extract_full_state_from_solver(self.solvers[k].as_ref());
                    if self.cube_consistent_with_init(&pred) {
                        break;
                    }
                    let mut tb_limit = self.config.ctg_limit;
                    if !self.trivial_block(k, pred, &mut tb_limit) {
                        break;
                    }
                }
                if !succeeded {
                    // Lemma stays at frame k.
                }
            }
            if !pushed_indices.is_empty() {
                let new_lemmas: Vec<Lemma> = self.frames.frames[k]
                    .lemmas
                    .iter()
                    .filter(|l| !lemmas.contains(l))
                    .cloned()
                    .collect();
                let mut kept: Vec<Lemma> = lemmas
                    .into_iter()
                    .enumerate()
                    .filter(|(i, _)| !pushed_indices.contains(i))
                    .map(|(_, l)| l)
                    .collect();
                kept.extend(new_lemmas);
                self.frames.frames[k].lemmas = kept;
            }
            if self.frames.frames[k].lemmas.is_empty() && orig_count > 0 {
                eprintln!(
                    "IC3 propagate: frame {k} empty (had {orig_count} lemma(s), all pushed to {})",
                    k + 1
                );
                if cfg!(debug_assertions) || std::env::var("IC3_VERIFY_CONVERGENCE").is_ok() {
                    eprintln!("IC3: verifying convergence at frame {k}...");
                    let f_k_lemmas: Vec<_> = self.frames.frames[k].lemmas.clone();
                    let f_k1_lemmas: Vec<_> = self.frames.frames[k + 1].lemmas.clone();
                    eprintln!(
                        "IC3 convergence check: frame[{k}] has {} lemmas, frame[{}] has {} lemmas",
                        f_k_lemmas.len(),
                        k + 1,
                        f_k1_lemmas.len(),
                    );
                }
                return true;
            }
        }
        self.earliest_changed_frame = depth;

        if self.config.inf_frame {
            self.propagate_to_inf();

            if !self.inf_lemmas.is_empty() && depth >= 3 {
                for k in 1..depth - 1 {
                    if self.frames.frames[k].lemmas.is_empty()
                        && self.frames.frames[k + 1].lemmas.is_empty()
                    {
                        return true;
                    }
                }
            }
        }

        false
    }

    /// Try to push top-frame lemmas to the infinity frame.
    pub(super) fn propagate_to_inf(&mut self) {
        let depth = self.frames.depth();
        if depth == 0 {
            return;
        }
        let top = depth - 1;
        let lemmas: Vec<Lemma> = self.frames.frames[top].lemmas.clone();
        let mut promoted_indices = rustc_hash::FxHashSet::default();
        for (idx, lemma) in lemmas.iter().enumerate() {
            let cube: Vec<Lit> = lemma.lits.iter().map(|l| !*l).collect();
            if self.cube_sat_consistent_with_init(&cube) {
                continue;
            }
            let neg_cube: Vec<Lit> = cube.iter().map(|l| !*l).collect();
            let assumptions = self.prime_cube(&cube);
            if self
                .inf_solver
                .solve_with_temporary_clause(&assumptions, &neg_cube)
                == SatResult::Unsat
            {
                self.inf_solver.add_clause(&lemma.lits);
                self.inf_lemmas.push(lemma.clone());
                for s in &mut self.solvers {
                    s.add_clause(&lemma.lits);
                }
                promoted_indices.insert(idx);
            }
        }
        if !promoted_indices.is_empty() {
            self.frames.frames[top].lemmas = lemmas
                .into_iter()
                .enumerate()
                .filter(|(i, _)| !promoted_indices.contains(i))
                .map(|(_, l)| l)
                .collect();
        }
    }
}
