// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Simple backtracking DPLL solver for bootstrapping and tests.

use super::{Lit, SatResult, SatSolver, Var};

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

        // Pick first unassigned variable
        let pick = (1..self.num_vars as usize).find(|&i| self.model[i].is_none());

        if let Some(var_idx) = pick {
            // Save model state
            let saved = self.model.clone();

            // Try true
            self.model[var_idx] = Some(true);
            if self.dpll_solve(depth + 1) {
                return true;
            }

            // Restore and try false
            self.model = saved;
            self.model[var_idx] = Some(false);
            if self.dpll_solve(depth + 1) {
                return true;
            }

            // Restore
            self.model[var_idx] = None;
            false
        } else {
            true
        }
    }
}
