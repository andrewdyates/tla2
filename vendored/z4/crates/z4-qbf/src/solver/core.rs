// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl QbfSolver {
    /// Create a new QBF solver for the given formula
    pub fn new(formula: QbfFormula) -> Self {
        let num_vars = formula.num_vars;

        // Build decision order from quantifier prefix
        let mut decision_order = Vec::with_capacity(num_vars);
        for block in &formula.prefix {
            for &var in &block.variables {
                decision_order.push(var);
            }
        }

        // Add any unquantified variables (implicitly existential at outermost)
        let quantified: HashSet<u32> = decision_order.iter().copied().collect();
        for v in 1..=num_vars as u32 {
            if !quantified.contains(&v) {
                decision_order.insert(0, v); // Add at front (outermost)
            }
        }

        // Initialize watch lists: 2 entries per variable (positive and negative)
        let watches = vec![Vec::new(); num_vars * 2 + 2];

        let mut solver = Self {
            formula,
            assignments: vec![Assignment::Unassigned; num_vars],
            levels: vec![0; num_vars],
            reasons: vec![Reason::Decision; num_vars],
            trail: Vec::with_capacity(num_vars),
            trail_lim: Vec::new(),
            decision_level: 0,
            learned: Vec::new(),
            cubes: Vec::new(),
            decision_order,
            activity: vec![0.0; num_vars],
            var_inc: 1.0,
            var_decay: 0.95,
            conflicts: 0,
            propagations: 0,
            decisions: 0,
            watches,
            qhead: 0,
            clause_used: Vec::new(),
            cube_used: Vec::new(),
            next_reduce: REDUCE_DB_INIT,
            reductions: 0,
            clauses_deleted: 0,
            cubes_deleted: 0,
        };

        // Initialize watches for all original clauses
        solver.init_watches();
        solver
    }

    /// Solve the QBF formula
    pub fn solve(&mut self) -> QbfResult {
        self.solve_with_limit(1_000_000)
    }

    /// Solve with iteration limit (for debugging)
    pub fn solve_with_limit(&mut self, max_iterations: u64) -> QbfResult {
        // Apply initial universal reduction
        self.apply_universal_reduction();

        // Check for empty clause (immediate UNSAT)
        if self.has_empty_clause() {
            return QbfResult::Unsat(Certificate::None);
        }

        let mut iterations: u64 = 0;
        loop {
            iterations += 1;
            if iterations > max_iterations {
                return QbfResult::Unknown;
            }

            // Unit propagation
            match self.propagate() {
                PropResult::Ok => {}
                PropResult::Conflict(clause_idx) => {
                    self.conflicts += 1;

                    if self.decision_level == 0 {
                        // Conflict at level 0 - UNSAT
                        return QbfResult::Unsat(self.build_herbrand_certificate());
                    }

                    // Analyze conflict and learn
                    let (learned_clause, backtrack_level) = self.analyze_conflict(clause_idx);
                    self.bump_clause_activity(&learned_clause);
                    self.var_decay_activity();

                    // Backtrack
                    self.backtrack(backtrack_level);

                    // Add learned clause, reduce DB if due
                    self.add_learned_clause(learned_clause);
                    self.maybe_reduce_db();

                    // Continue to propagate the learned clause before deciding
                    continue;
                }
            }

            // Check if all variables assigned
            if self.all_assigned() {
                // Check if formula is satisfied
                if self.is_satisfied() {
                    return QbfResult::Sat(self.build_skolem_certificate());
                } else {
                    // Should not happen with correct propagation
                    return QbfResult::Unknown;
                }
            }

            // Check for partial solution (all clauses satisfied but not all vars assigned)
            // This is a "solution" state where we can learn a cube
            if self.is_satisfied() {
                // All clauses satisfied - existential player wins for this universal path
                // Learn a cube to block this universal search path
                if let Some(cube_result) = self.learn_cube_from_solution() {
                    match cube_result {
                        CubeResult::Learned(backtrack_level) => {
                            self.backtrack(backtrack_level);
                            continue;
                        }
                        CubeResult::Solved => {
                            // All universal paths lead to SAT
                            return QbfResult::Sat(self.build_skolem_certificate());
                        }
                    }
                }
            }

            // Make a decision
            match self.decide() {
                Some(_) => {
                    self.decisions += 1;
                }
                None => {
                    // No more decisions possible but not all assigned?
                    // This shouldn't happen
                    return QbfResult::Unknown;
                }
            }
        }
    }

    /// Apply universal reduction to all clauses
    fn apply_universal_reduction(&mut self) {
        let reduced: Vec<Vec<Literal>> = self
            .formula
            .clauses
            .iter()
            .map(|c| self.formula.universal_reduce(c))
            .collect();
        self.formula.clauses = reduced;
    }

    /// Check if any clause is empty
    fn has_empty_clause(&self) -> bool {
        self.formula.clauses.iter().any(Vec::is_empty) || self.learned.iter().any(Vec::is_empty)
    }

    /// Build Skolem certificate for SAT result
    fn build_skolem_certificate(&self) -> Certificate {
        let mut functions = Vec::new();
        for &var in &self.decision_order {
            if self.formula.is_existential(var) {
                let value = self.value(var).to_bool().unwrap_or(false);
                functions.push(SkolemFunction {
                    variable: var,
                    value,
                });
            }
        }
        Certificate::Skolem(functions)
    }

    /// Build Herbrand certificate for UNSAT result
    fn build_herbrand_certificate(&self) -> Certificate {
        let mut functions = Vec::new();
        for &var in &self.decision_order {
            if self.formula.is_universal(var) {
                let value = self.value(var).to_bool().unwrap_or(false);
                functions.push(HerbrandFunction {
                    variable: var,
                    value,
                });
            }
        }
        Certificate::Herbrand(functions)
    }

    /// Get statistics
    pub fn stats(&self) -> QbfStats {
        let active_clauses = self.learned.iter().filter(|c| !c.is_empty()).count();
        let active_cubes = self.cubes.iter().filter(|c| !c.is_empty()).count();
        QbfStats {
            conflicts: self.conflicts,
            propagations: self.propagations,
            decisions: self.decisions,
            learned_clauses: active_clauses as u64,
            learned_cubes: active_cubes as u64,
            reductions: self.reductions,
            clauses_deleted: self.clauses_deleted,
            cubes_deleted: self.cubes_deleted,
        }
    }
}
