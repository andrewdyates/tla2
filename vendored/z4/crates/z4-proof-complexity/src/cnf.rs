// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CNF formula representation and XOR encoding utilities.

use z4_sat::Literal;

use crate::{Lit, Var};

/// A CNF formula represented as a list of clauses.
#[derive(Debug, Clone)]
pub struct Cnf {
    /// Number of variables
    num_vars: u32,
    /// Clauses (each clause is a list of literals)
    clauses: Vec<Vec<Literal>>,
}

impl Cnf {
    /// Create a new CNF with reserved capacity.
    pub fn new_with_capacity(num_vars: u32, clause_capacity: usize) -> Self {
        Self {
            num_vars,
            clauses: Vec::with_capacity(clause_capacity),
        }
    }

    /// Add a clause to the formula.
    pub fn add_clause(&mut self, literals: &[Literal]) {
        self.clauses.push(literals.to_vec());
    }

    /// Number of variables.
    pub fn num_vars(&self) -> usize {
        self.num_vars as usize
    }

    /// Number of clauses.
    pub fn num_clauses(&self) -> usize {
        self.clauses.len()
    }

    /// Iterate over clauses.
    pub fn clauses(&self) -> impl Iterator<Item = &Vec<Literal>> {
        self.clauses.iter()
    }

    /// Convert to a solver with adaptive inprocessing gating.
    ///
    /// Extracts syntactic features from the clause database and applies
    /// instance-driven adjustments to the inprocessing profile before
    /// returning the solver. This matches the adaptive gating applied
    /// by the DIMACS entry point in `z4-sat`.
    pub fn into_solver(self) -> z4_sat::Solver {
        let features =
            z4_sat::SatFeatures::extract(self.num_vars as usize, &self.clauses);
        let class = z4_sat::InstanceClass::classify(&features);

        let mut solver = z4_sat::Solver::new(self.num_vars as usize);

        // Apply adaptive inprocessing adjustments.
        let mut profile = solver.inprocessing_feature_profile();
        if z4_sat::adjust_features_for_instance(&features, &class, &mut profile) {
            solver.set_condition_enabled(profile.condition);
            solver.set_symmetry_enabled(profile.symmetry);
            solver.set_bce_enabled(profile.bce);
        }
        if z4_sat::should_disable_reorder(&features, &class) {
            solver.set_reorder_enabled(false);
        }

        for clause in self.clauses {
            solver.add_clause(clause);
        }
        solver
    }
}

pub(crate) fn xor_clause_count(num_vars: usize, parity: bool) -> usize {
    if num_vars == 0 {
        usize::from(parity)
    } else {
        1usize << (num_vars - 1)
    }
}

pub(crate) fn add_xor_equals_clauses(vars: &[Var], parity: bool, cnf: &mut Cnf) {
    if vars.is_empty() {
        if parity {
            cnf.add_clause(&[]); // UNSAT
        }
        return;
    }

    let num_vars = vars.len();
    for mask in 0..(1u64 << num_vars) {
        let assignment_is_odd = mask.count_ones() % 2 == 1;
        if assignment_is_odd != parity {
            // This assignment should be forbidden
            // Clause: at least one literal must be flipped
            let clause: Vec<Lit> = vars
                .iter()
                .enumerate()
                .map(|(idx, &var)| {
                    if (mask >> idx) & 1 == 1 {
                        Lit::negative(var)
                    } else {
                        Lit::positive(var)
                    }
                })
                .collect();
            cnf.add_clause(&clause);
        }
    }
}
