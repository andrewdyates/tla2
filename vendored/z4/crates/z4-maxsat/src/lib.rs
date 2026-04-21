#![forbid(unsafe_code)]
#![warn(missing_docs)]
// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Maximum Satisfiability (MAX-SAT) solver
//!
//! MAX-SAT finds an assignment that maximizes the number (or weight) of
//! satisfied clauses in a CNF formula.
//!
//! ## Problem Variants
//!
//! - **Unweighted MAX-SAT**: Maximize the count of satisfied clauses
//! - **Weighted MAX-SAT**: Maximize the sum of weights of satisfied clauses
//! - **Partial MAX-SAT**: Some clauses are "hard" (must be satisfied), others are "soft"
//! - **Weighted Partial MAX-SAT**: Combination of weighted and partial
//!
//! ## Example
//!
//! ```
//! use z4_maxsat::{MaxSatSolver, MaxSatResult};
//!
//! let mut solver = MaxSatSolver::new();
//!
//! // Add soft clauses (can be violated at a cost)
//! solver.add_soft_clause(vec![1], 1);   // prefer x1 = true
//! solver.add_soft_clause(vec![-1], 1);  // prefer x1 = false (conflicts!)
//! solver.add_soft_clause(vec![2], 1);   // prefer x2 = true
//!
//! let result = solver.solve();
//! match result {
//!     MaxSatResult::Optimal { model, cost } => {
//!         // Cost = 1 (one soft clause violated)
//!         assert_eq!(cost, 1);
//!     }
//!     _ => panic!("Expected optimal solution"),
//! }
//! ```
//!
//! ## Algorithm
//!
//! This implementation uses a core-guided approach based on OLL (Optimized
//! Linear Search) and MSU3 algorithms. The key ideas:
//!
//! 1. Add relaxation variables to soft clauses
//! 2. Find UNSAT cores when hard constraints conflict
//! 3. Add cardinality constraints to limit violations
//! 4. Iterate until optimal
//!
//! ## References
//!
//! - Morgado et al., "Iterative and core-guided MaxSAT solving: A survey and assessment"
//! - Fu & Malik, "On solving the partial MAX-SAT problem"
//! - Martins et al., "Incremental Cardinality Constraints for MaxSAT"

mod solver;

pub use solver::{MaxSatResult, MaxSatSolver, MaxSatStats};
pub use z4_sat::SignedClause;
