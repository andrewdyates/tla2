// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ALL-SAT Solver Implementation
//!
//! This module implements solution enumeration using iterative SAT solving
//! with blocking clauses.

use z4_sat::{Literal, SignedClause, Solver as SatSolver, Variable};

/// A satisfying assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Solution {
    /// Assignment: index is variable number, value is true/false.
    /// Index 0 is unused (variables are 1-indexed).
    pub assignment: Vec<bool>,
}

impl Solution {
    /// Get the value of a variable in this solution.
    pub fn get(&self, var: u32) -> Option<bool> {
        self.assignment.get(var as usize).copied()
    }

    /// Check if a variable is true in this solution.
    pub fn is_true(&self, var: u32) -> bool {
        self.get(var).unwrap_or(false)
    }

    /// Check if a literal is satisfied by this solution.
    pub fn satisfies(&self, lit: i32) -> bool {
        let var = lit.unsigned_abs() as usize;
        let polarity = lit > 0;
        self.assignment.get(var).copied().unwrap_or(false) == polarity
    }

    /// Convert to a vector of literals representing this assignment.
    /// Returns positive literal if var=true, negative if var=false.
    pub fn to_literals(&self, vars: &[u32]) -> Vec<i32> {
        vars.iter()
            .map(|&v| {
                if self.is_true(v) {
                    v as i32
                } else {
                    -(v as i32)
                }
            })
            .collect()
    }
}

/// Configuration for ALL-SAT enumeration.
#[derive(Debug, Clone, Default)]
pub struct AllSatConfig {
    /// Maximum number of solutions to enumerate (None = unlimited).
    pub max_solutions: Option<usize>,

    /// Variables to project onto (None = all variables).
    /// When set, blocking clauses only reference these variables,
    /// effectively finding all distinct assignments to projected vars.
    pub projection: Option<Vec<u32>>,
}

/// Statistics for ALL-SAT solving.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct AllSatStats {
    /// Number of SAT solver calls.
    pub sat_calls: u64,
    /// Number of solutions found.
    pub solutions_found: u64,
    /// Number of blocking clauses added.
    pub blocking_clauses: u64,
}

/// ALL-SAT Solver
///
/// Enumerates all satisfying assignments to a Boolean formula.
pub struct AllSatSolver {
    /// Clauses of the formula (converted to Literal at the API boundary).
    clauses: Vec<Vec<Literal>>,
    /// Maximum variable seen.
    max_var: u32,
    /// Statistics.
    stats: AllSatStats,
}

impl AllSatSolver {
    /// Create a new ALL-SAT solver.
    pub fn new() -> Self {
        Self {
            clauses: Vec::new(),
            max_var: 0,
            stats: AllSatStats::default(),
        }
    }

    /// Add a clause to the formula.
    ///
    /// Literals use signed integer encoding: positive = positive literal,
    /// negative = negated literal. E.g., `vec![1, -2]` means x1 OR NOT x2.
    pub fn add_clause(&mut self, clause: SignedClause) {
        for &lit in &clause {
            let var = lit.unsigned_abs();
            self.max_var = self.max_var.max(var);
        }
        let lits = clause.iter().map(|&l| Literal::from(l)).collect();
        self.clauses.push(lits);
    }

    /// Get the number of variables.
    pub fn num_vars(&self) -> u32 {
        self.max_var
    }

    /// Get solver statistics.
    pub fn stats(&self) -> &AllSatStats {
        &self.stats
    }

    /// Create an iterator over all solutions.
    pub fn iter(&mut self) -> AllSatIterator<'_> {
        self.iter_with_config(AllSatConfig::default())
    }

    /// Create an iterator with custom configuration.
    pub fn iter_with_config(&mut self, config: AllSatConfig) -> AllSatIterator<'_> {
        AllSatIterator::new(self, config)
    }

    /// Enumerate all solutions (convenience method).
    pub fn enumerate(&mut self) -> Vec<Solution> {
        self.iter().collect()
    }

    /// Enumerate solutions with custom configuration (convenience method).
    pub fn enumerate_with_config(&mut self, config: AllSatConfig) -> Vec<Solution> {
        self.iter_with_config(config).collect()
    }

    /// Count the number of solutions without storing them.
    pub fn count(&mut self) -> u64 {
        self.count_with_config(AllSatConfig::default())
    }

    /// Count with custom configuration.
    pub fn count_with_config(&mut self, config: AllSatConfig) -> u64 {
        let mut count = 0;
        for _ in self.iter_with_config(config) {
            count += 1;
        }
        count
    }

    /// Check if the formula is satisfiable.
    pub fn is_sat(&mut self) -> bool {
        let config = AllSatConfig {
            max_solutions: Some(1),
            ..Default::default()
        };
        self.count_with_config(config) > 0
    }

    /// Check if the formula has exactly one solution.
    pub fn has_unique_solution(&mut self) -> bool {
        let config = AllSatConfig {
            max_solutions: Some(2),
            ..Default::default()
        };
        self.count_with_config(config) == 1
    }

    /// Build a fresh SAT solver with the current clauses plus blocking clauses.
    fn build_solver(&self, blocking_clauses: &[Vec<Literal>]) -> SatSolver {
        let mut solver = SatSolver::new((self.max_var + 1) as usize);

        for clause in &self.clauses {
            solver.add_clause(clause.clone());
        }

        for clause in blocking_clauses {
            solver.add_clause(clause.clone());
        }

        solver
    }
}

impl Default for AllSatSolver {
    fn default() -> Self {
        Self::new()
    }
}

/// Iterator over all solutions.
pub struct AllSatIterator<'a> {
    solver: &'a mut AllSatSolver,
    config: AllSatConfig,
    blocking_clauses: Vec<Vec<Literal>>,
    solutions_returned: usize,
    exhausted: bool,
}

impl<'a> AllSatIterator<'a> {
    fn new(solver: &'a mut AllSatSolver, config: AllSatConfig) -> Self {
        Self {
            solver,
            config,
            blocking_clauses: Vec::new(),
            solutions_returned: 0,
            exhausted: false,
        }
    }

    /// Create a blocking clause that excludes the given solution.
    fn make_blocking_clause(&self, solution: &Solution) -> Vec<Literal> {
        let vars: Vec<u32> = if let Some(ref proj) = self.config.projection {
            proj.clone()
        } else {
            (1..=self.solver.max_var).collect()
        };

        // Blocking clause: at least one variable must differ
        // If var=true in solution, add negated literal; if false, add positive literal
        vars.iter()
            .map(|&v| {
                let var = Variable::new(v);
                if solution.is_true(v) {
                    Literal::negative(var)
                } else {
                    Literal::positive(var)
                }
            })
            .collect()
    }
}

impl Iterator for AllSatIterator<'_> {
    type Item = Solution;

    fn next(&mut self) -> Option<Self::Item> {
        // Check if we've reached the limit
        if self.exhausted {
            return None;
        }

        if let Some(max) = self.config.max_solutions {
            if self.solutions_returned >= max {
                return None;
            }
        }

        // Build solver and solve
        let mut sat_solver = self.solver.build_solver(&self.blocking_clauses);
        self.solver.stats.sat_calls += 1;

        if let Some(model) = sat_solver.solve().into_model() {
            let solution = Solution { assignment: model };

            // Create blocking clause
            let blocking = self.make_blocking_clause(&solution);
            self.blocking_clauses.push(blocking);
            self.solver.stats.blocking_clauses += 1;
            self.solver.stats.solutions_found += 1;
            self.solutions_returned += 1;

            Some(solution)
        } else {
            self.exhausted = true;
            None
        }
    }
}

#[cfg(test)]
#[path = "solver_tests.rs"]
mod tests;
