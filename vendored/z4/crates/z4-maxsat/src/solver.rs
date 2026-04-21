// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MAX-SAT Solver Implementation
//!
//! This module implements a MAX-SAT solver using iterative SAT solving with
//! relaxation variables and cardinality constraints.
//!
//! ## Algorithm
//!
//! Uses binary search on the violation bound:
//! 1. Add relaxation variables to soft clauses
//! 2. Binary search for the minimum k such that at-most-k violations is satisfiable
//! 3. Encode at-most-k using direct or sequential counter encoding
//! 4. For weighted instances, process weight strata from highest to lowest

use z4_sat::{Literal, SatResult, SignedClause, Solver as SatSolver, Variable};

/// Weight type for soft clauses
pub(crate) type Weight = u64;
type StratumBound = (Vec<u32>, usize);

/// Result of MAX-SAT solving
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MaxSatResult {
    /// Found optimal solution
    Optimal {
        /// The satisfying assignment (variable -> value)
        model: Vec<bool>,
        /// Total cost (sum of weights of unsatisfied soft clauses)
        cost: u64,
    },
    /// Hard clauses are unsatisfiable
    Unsatisfiable,
    /// Unknown result (timeout, resource limit)
    Unknown,
}

/// Statistics for MAX-SAT solving
#[derive(Debug, Clone, Default)]
pub struct MaxSatStats {
    /// Number of SAT solver calls
    pub sat_calls: u64,
    /// Number of cardinality constraints added
    pub cardinality_constraints: u64,
}

/// A soft clause with its relaxation variable
#[derive(Debug, Clone)]
struct SoftClause {
    /// Original clause literals (converted to Literal at the API boundary)
    clause: Vec<Literal>,
    /// Weight of this clause
    weight: Weight,
    /// Relaxation variable (when true, clause is "satisfied" by relaxation)
    relax_var: u32,
}

/// MAX-SAT Solver
///
/// Supports weighted partial MAX-SAT:
/// - Hard clauses must be satisfied
/// - Soft clauses have weights; goal is to minimize total weight of unsatisfied soft clauses
pub struct MaxSatSolver {
    /// Hard clauses (converted to Literal at the API boundary)
    hard_clauses: Vec<Vec<Literal>>,
    /// Soft clauses with weights
    soft_clauses: Vec<SoftClause>,
    /// Next available variable
    next_var: u32,
    /// Statistics
    stats: MaxSatStats,
}

impl MaxSatSolver {
    /// Create a new MAX-SAT solver
    pub fn new() -> Self {
        Self {
            hard_clauses: Vec::new(),
            soft_clauses: Vec::new(),
            next_var: 1,
            stats: MaxSatStats::default(),
        }
    }

    /// Track variable indices and convert a signed clause to internal literals.
    fn track_and_convert(&mut self, clause: &SignedClause) -> Vec<Literal> {
        for &lit in clause {
            let var = lit.unsigned_abs();
            if var >= self.next_var {
                self.next_var = var + 1;
            }
        }
        clause.iter().map(|&l| Literal::from(l)).collect()
    }

    /// Add a hard clause (must be satisfied)
    pub fn add_hard_clause(&mut self, clause: SignedClause) {
        let lits = self.track_and_convert(&clause);
        self.hard_clauses.push(lits);
    }

    /// Add a soft clause with weight
    ///
    /// Note: relaxation variables are allocated lazily in solve() to avoid
    /// collisions with user variables added after soft clauses.
    pub fn add_soft_clause(&mut self, clause: SignedClause, weight: Weight) {
        let lits = self.track_and_convert(&clause);
        self.soft_clauses.push(SoftClause {
            clause: lits,
            weight,
            relax_var: 0,
        });
    }

    /// Get solver statistics
    pub fn stats(&self) -> &MaxSatStats {
        &self.stats
    }

    /// Solve the MAX-SAT instance
    ///
    /// Returns the optimal solution or UNSAT if hard clauses are unsatisfiable.
    pub fn solve(&mut self) -> MaxSatResult {
        // Handle empty instance
        if self.hard_clauses.is_empty() && self.soft_clauses.is_empty() {
            return MaxSatResult::Optimal {
                model: vec![],
                cost: 0,
            };
        }

        // Allocate relaxation variables AFTER all user variables
        // This ensures no collisions between user vars and relax vars
        for soft in &mut self.soft_clauses {
            soft.relax_var = self.next_var;
            self.next_var += 1;
        }

        // First check if hard clauses alone are satisfiable
        if !self.check_hard_clauses() {
            return MaxSatResult::Unsatisfiable;
        }

        // If no soft clauses, just solve hard clauses
        if self.soft_clauses.is_empty() {
            return self.solve_hard_only();
        }

        // For unweighted MAX-SAT, use binary search on violation count
        // For weighted MAX-SAT with diverse weights, use stratification
        if self.all_unit_weights() {
            self.solve_binary_search()
        } else {
            self.solve_stratified()
        }
    }

    /// Check if all soft clauses have weight 1
    fn all_unit_weights(&self) -> bool {
        self.soft_clauses.iter().all(|s| s.weight == 1)
    }

    /// Build a SAT solver with all hard clauses loaded.
    ///
    /// `total_vars` specifies the variable count (including any extra variables
    /// for cardinality encoding).
    fn build_base_solver(&self, total_vars: usize) -> SatSolver {
        let mut solver = SatSolver::new(total_vars);
        for clause in &self.hard_clauses {
            solver.add_clause(clause.clone());
        }
        solver
    }

    /// Build a SAT solver containing only the hard clauses.
    fn build_hard_solver(&self) -> SatSolver {
        self.build_base_solver(self.next_var as usize)
    }

    /// Estimate extra variables needed for a cardinality encoding of at-most-k
    /// over `n` relaxation variables.
    fn cardinality_extra_vars(n: usize, k: usize) -> usize {
        if k > 0 && k < n {
            n * (k + 1) + 100
        } else {
            100
        }
    }

    /// Build a SAT solver with hard clauses and relaxed soft clauses.
    ///
    /// Each soft clause gets its relaxation variable appended, so the solver
    /// can "satisfy" soft clauses by setting the relaxation variable to true.
    /// `extra_vars` reserves space for cardinality encoding auxiliary variables.
    fn build_relaxed_solver(&self, extra_vars: usize) -> SatSolver {
        let mut solver = self.build_base_solver((self.next_var as usize) + extra_vars);
        for soft in &self.soft_clauses {
            let mut lits = soft.clause.clone();
            lits.push(Literal::positive(Variable::new(soft.relax_var)));
            solver.add_clause(lits);
        }
        solver
    }

    /// Check if hard clauses are satisfiable
    fn check_hard_clauses(&mut self) -> bool {
        if self.hard_clauses.is_empty() {
            return true;
        }

        self.stats.sat_calls += 1;
        self.build_hard_solver().solve().is_sat()
    }

    /// Solve when there are only hard clauses
    fn solve_hard_only(&mut self) -> MaxSatResult {
        self.stats.sat_calls += 1;
        match self.build_hard_solver().solve().into_inner() {
            SatResult::Sat(model) => MaxSatResult::Optimal { model, cost: 0 },
            SatResult::Unsat => MaxSatResult::Unsatisfiable,
            SatResult::Unknown => MaxSatResult::Unknown,
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }
    }

    /// Binary search algorithm for unweighted MAX-SAT
    fn solve_binary_search(&mut self) -> MaxSatResult {
        let n = self.soft_clauses.len();

        // Binary search for optimal k (minimum violations)
        let mut lo = 0;
        let mut hi = n;
        let mut best_model: Option<Vec<bool>> = None;

        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if let Some(model) = self.try_solve_with_bound(mid) {
                // Found solution with cost <= mid
                best_model = Some(model);
                hi = mid;
            } else {
                // Need more than mid violations
                lo = mid + 1;
            }
        }

        // Final verification at lo
        if best_model.is_none() {
            if let Some(model) = self.try_solve_with_bound(lo) {
                best_model = Some(model);
            }
        }

        match best_model {
            Some(model) => {
                // Compute actual cost from model
                let cost = self.compute_cost(&model);
                MaxSatResult::Optimal { cost, model }
            }
            None => MaxSatResult::Unsatisfiable,
        }
    }

    /// Try to solve with at most k soft clause violations
    fn try_solve_with_bound(&mut self, k: usize) -> Option<Vec<bool>> {
        let relax_vars: Vec<u32> = self.soft_clauses.iter().map(|s| s.relax_var).collect();
        let extra_vars = Self::cardinality_extra_vars(relax_vars.len(), k);

        let mut solver = self.build_relaxed_solver(extra_vars);
        Self::add_at_most_k_clauses(&mut solver, &relax_vars, k, self.next_var);

        self.stats.sat_calls += 1;
        self.stats.cardinality_constraints += 1;

        solver.solve().into_model()
    }

    /// Stratified algorithm for weighted MAX-SAT
    fn solve_stratified(&mut self) -> MaxSatResult {
        // Group soft clauses by weight
        let mut weights: Vec<Weight> = self.soft_clauses.iter().map(|s| s.weight).collect();
        weights.sort_unstable();
        weights.dedup();
        weights.reverse(); // Process highest weight first

        // Process each weight stratum to find minimum violations.
        // Lower-weight strata are conditioned on previously fixed higher-weight bounds.
        let mut stratum_bounds: Vec<StratumBound> = Vec::new();
        for &weight in &weights {
            // Get soft clauses with this weight
            let stratum_indices: Vec<usize> = self
                .soft_clauses
                .iter()
                .enumerate()
                .filter(|(_, s)| s.weight == weight)
                .map(|(i, _)| i)
                .collect();

            let stratum_relax_vars: Vec<u32> = stratum_indices
                .iter()
                .map(|&i| self.soft_clauses[i].relax_var)
                .collect();
            let min_violations =
                self.find_min_violations_for_stratum(&stratum_indices, &stratum_bounds);
            stratum_bounds.push((stratum_relax_vars, min_violations));
        }

        // Final solve to get a model
        let n = self.soft_clauses.len();
        let extra_vars = n * (n + 1) + 1000;
        let mut solver = self.build_relaxed_solver(extra_vars);

        stratum_bounds
            .iter()
            .fold(self.next_var, |next_aux, (relax_vars, bound)| {
                Self::add_at_most_k_clauses(&mut solver, relax_vars, *bound, next_aux)
            });

        self.stats.sat_calls += 1;
        self.stats.cardinality_constraints += stratum_bounds.len() as u64;

        match solver.solve().into_inner() {
            SatResult::Sat(model) => {
                let cost = self.compute_cost(&model);
                MaxSatResult::Optimal { model, cost }
            }
            SatResult::Unsat => MaxSatResult::Unsatisfiable,
            SatResult::Unknown => MaxSatResult::Unknown,
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }
    }

    /// Find minimum violations for a stratum of soft clauses
    fn find_min_violations_for_stratum(
        &mut self,
        stratum_indices: &[usize],
        prior_bounds: &[StratumBound],
    ) -> usize {
        // Binary search for minimum violations in this stratum
        let n = stratum_indices.len();
        let mut lo = 0;
        let mut hi = n;

        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if self.can_solve_stratum_with_bound(stratum_indices, mid, prior_bounds) {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }

        lo
    }

    /// Check if stratum can be solved with at most k violations
    fn can_solve_stratum_with_bound(
        &mut self,
        stratum_indices: &[usize],
        k: usize,
        prior_bounds: &[StratumBound],
    ) -> bool {
        let relax_vars: Vec<u32> = stratum_indices
            .iter()
            .map(|&i| self.soft_clauses[i].relax_var)
            .collect();

        let n = self.soft_clauses.len();
        let extra_vars = n * (n + 1) + 100;
        let mut solver = self.build_relaxed_solver(extra_vars);

        // Apply already-fixed higher-priority strata bounds first.
        let aux_var =
            prior_bounds
                .iter()
                .fold(self.next_var, |next_aux, (bound_relax_vars, bound_k)| {
                    Self::add_at_most_k_clauses(&mut solver, bound_relax_vars, *bound_k, next_aux)
                });

        // Add at-most-k constraint for current stratum relaxation variables
        Self::add_at_most_k_clauses(&mut solver, &relax_vars, k, aux_var);

        self.stats.sat_calls += 1;
        self.stats.cardinality_constraints += prior_bounds.len() as u64 + 1;

        solver.solve().is_sat()
    }

    /// Add at-most-k constraint clauses
    /// Returns the next available auxiliary variable
    fn add_at_most_k_clauses(solver: &mut SatSolver, vars: &[u32], k: usize, next_aux: u32) -> u32 {
        let n = vars.len();

        if k >= n {
            return next_aux; // Trivially satisfied
        }

        if k == 0 {
            // All must be false
            for &var in vars {
                solver.add_clause(vec![Literal::negative(Variable::new(var))]);
            }
            return next_aux;
        }

        // Use direct encoding for small cases
        if n <= 6 || k == 1 {
            Self::add_at_most_k_direct(solver, vars, k);
            return next_aux;
        }

        // Sequential counter encoding for larger cases
        Self::add_at_most_k_sequential(solver, vars, k, next_aux)
    }

    /// Direct encoding for at-most-k: add one clause per (k+1)-subset of `vars`.
    fn add_at_most_k_direct(solver: &mut SatSolver, vars: &[u32], k: usize) {
        let n = vars.len();
        let r = k + 1;
        if r > n {
            return;
        }

        // Generate all r-subsets of 0..n using iterative combination enumeration.
        // Each subset produces a clause: at least one variable in the subset must be false.
        let mut indices: Vec<usize> = (0..r).collect();
        loop {
            let clause: Vec<Literal> = indices
                .iter()
                .map(|&i| Literal::negative(Variable::new(vars[i])))
                .collect();
            solver.add_clause(clause);

            // Advance to next combination (lexicographic order)
            let Some(pos) = (0..r).rev().find(|&i| indices[i] != i + n - r) else {
                break;
            };
            indices[pos] += 1;
            for j in (pos + 1)..r {
                indices[j] = indices[j - 1] + 1;
            }
        }
    }

    /// Sequential counter encoding for at-most-k
    fn add_at_most_k_sequential(
        solver: &mut SatSolver,
        vars: &[u32],
        k: usize,
        mut next_aux: u32,
    ) -> u32 {
        let n = vars.len();

        // Create counter variables: r[i][j] means "sum of first i+1 vars >= j+1"
        // We need r[i][j] for i in 0..n, j in 0..k
        let mut r: Vec<Vec<u32>> = Vec::with_capacity(n);
        for _ in 0..n {
            let row: Vec<u32> = (0..k)
                .map(|_| {
                    let v = next_aux;
                    next_aux += 1;
                    v
                })
                .collect();
            r.push(row);
        }

        // Base case: r[0][0] <=> vars[0]
        // vars[0] -> r[0][0]
        solver.add_clause(vec![
            Literal::negative(Variable::new(vars[0])),
            Literal::positive(Variable::new(r[0][0])),
        ]);
        // r[0][0] -> vars[0]
        solver.add_clause(vec![
            Literal::negative(Variable::new(r[0][0])),
            Literal::positive(Variable::new(vars[0])),
        ]);
        // r[0][j] = false for j > 0 (can't have sum >= 2 with one var)
        for &r0j in r[0].iter().skip(1) {
            solver.add_clause(vec![Literal::negative(Variable::new(r0j))]);
        }

        // Inductive case
        for i in 1..n {
            // r[i][0] <=> r[i-1][0] OR vars[i]
            // r[i-1][0] -> r[i][0]
            solver.add_clause(vec![
                Literal::negative(Variable::new(r[i - 1][0])),
                Literal::positive(Variable::new(r[i][0])),
            ]);
            // vars[i] -> r[i][0]
            solver.add_clause(vec![
                Literal::negative(Variable::new(vars[i])),
                Literal::positive(Variable::new(r[i][0])),
            ]);
            // r[i][0] -> r[i-1][0] OR vars[i]
            solver.add_clause(vec![
                Literal::negative(Variable::new(r[i][0])),
                Literal::positive(Variable::new(r[i - 1][0])),
                Literal::positive(Variable::new(vars[i])),
            ]);

            for j in 1..k {
                // r[i][j] <=> r[i-1][j] OR (vars[i] AND r[i-1][j-1])

                // r[i-1][j] -> r[i][j]
                solver.add_clause(vec![
                    Literal::negative(Variable::new(r[i - 1][j])),
                    Literal::positive(Variable::new(r[i][j])),
                ]);
                // vars[i] AND r[i-1][j-1] -> r[i][j]
                solver.add_clause(vec![
                    Literal::negative(Variable::new(vars[i])),
                    Literal::negative(Variable::new(r[i - 1][j - 1])),
                    Literal::positive(Variable::new(r[i][j])),
                ]);
                // r[i][j] -> r[i-1][j] OR vars[i]
                solver.add_clause(vec![
                    Literal::negative(Variable::new(r[i][j])),
                    Literal::positive(Variable::new(r[i - 1][j])),
                    Literal::positive(Variable::new(vars[i])),
                ]);
                // r[i][j] -> r[i-1][j] OR r[i-1][j-1]
                solver.add_clause(vec![
                    Literal::negative(Variable::new(r[i][j])),
                    Literal::positive(Variable::new(r[i - 1][j])),
                    Literal::positive(Variable::new(r[i - 1][j - 1])),
                ]);
            }

            // Block sum >= k+1: NOT (vars[i] AND r[i-1][k-1])
            // Equivalently: !vars[i] OR !r[i-1][k-1]
            solver.add_clause(vec![
                Literal::negative(Variable::new(vars[i])),
                Literal::negative(Variable::new(r[i - 1][k - 1])),
            ]);
        }

        next_aux
    }

    /// Compute cost (weight of unsatisfied soft clauses)
    fn compute_cost(&self, model: &[bool]) -> u64 {
        let mut cost = 0;

        for soft in &self.soft_clauses {
            let satisfied = soft.clause.iter().any(|&lit| {
                let var = lit.variable().index();
                let polarity = lit.is_positive();
                var < model.len() && model[var] == polarity
            });

            if !satisfied {
                cost += soft.weight;
            }
        }

        cost
    }
}

impl Default for MaxSatSolver {
    fn default() -> Self {
        Self::new()
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "solver_tests.rs"]
mod tests;
