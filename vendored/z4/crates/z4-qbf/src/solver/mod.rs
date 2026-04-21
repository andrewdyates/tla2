// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QCDCL Solver
//!
//! Quantified Conflict-Driven Clause Learning algorithm for QBF.
//!
//! ## Algorithm Overview
//!
//! QCDCL extends CDCL for quantified formulas:
//!
//! 1. **Quantifier-aware propagation**: A clause can only propagate an existential
//!    literal. Universal literals cannot be forced because the adversary controls them.
//!
//! 2. **Universal reduction**: Universal literals at the "tail" of a clause
//!    (with level >= max existential level) can be removed.
//!
//! 3. **Two-sided learning**: Learn clauses on existential conflicts,
//!    learn cubes on universal "wins".
//!
//! ## Current Implementation Status
//!
//! **Implemented:**
//! - Basic QCDCL with quantifier-aware unit propagation
//! - Universal reduction (Q-resolution)
//! - Universally-blocked clause detection
//! - Tautology detection (clauses with x ∨ ¬x)
//! - Q-resolution based 1-UIP conflict analysis
//! - VSIDS-style activity-based decision heuristic
//! - Two-watched literals for efficient propagation
//! - Cube learning for solution states (existential wins)
//! - Cube propagation for blocking universal search paths
//! - Certificate generation (constant Skolem/Herbrand functions)
//!
//! **Not Yet Implemented (Future Work):**
//! - Dependency learning (DepQBF-style)
//! - Long-distance resolution
//!
//! ## References
//! - Zhang & Malik, "Conflict Driven Learning in a Quantified Boolean Satisfiability Solver"
//! - Lonsing & Biere, "DepQBF: A Dependency-Aware QBF Solver"

use crate::formula::QbfFormula;
use std::collections::HashSet;
use z4_sat::{Literal, Variable};

mod core;
mod database;
mod propagate;
mod search;
mod state;
#[cfg(test)]
mod tests;

/// Result of QBF solving
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QbfResult {
    /// Formula is satisfiable (true for all universal assignments)
    Sat(Certificate),
    /// Formula is unsatisfiable (false for some universal assignment)
    Unsat(Certificate),
    /// Unknown result (timeout, resource limit)
    Unknown,
}

/// Certificate for QBF result
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Certificate {
    /// Skolem functions mapping existential vars to boolean functions of outer universals
    Skolem(Vec<SkolemFunction>),
    /// Herbrand functions mapping universal vars to boolean functions of outer existentials
    Herbrand(Vec<HerbrandFunction>),
    /// No certificate (for simple true/false results)
    None,
}

/// A Skolem function for an existential variable
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SkolemFunction {
    /// The existential variable
    pub variable: u32,
    /// The function as a truth table (indexed by universal variable assignments)
    /// For now, just store a constant value
    pub value: bool,
}

/// A Herbrand function for a universal variable
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HerbrandFunction {
    /// The universal variable
    pub variable: u32,
    /// The counterexample value
    pub value: bool,
}

/// Assignment state for a variable
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Assignment {
    /// Variable is unassigned
    Unassigned,
    /// Variable is assigned true
    True,
    /// Variable is assigned false
    False,
}

impl Assignment {
    fn to_bool(self) -> Option<bool> {
        match self {
            Self::True => Some(true),
            Self::False => Some(false),
            Self::Unassigned => None,
        }
    }

    fn is_assigned(self) -> bool {
        self != Self::Unassigned
    }
}

/// Reason for an assignment
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reason {
    /// Decision (no reason)
    Decision,
    /// Propagated from clause (index into original or learned clauses)
    Propagated(usize),
    /// Propagated from a learned cube (index into `cubes`)
    CubePropagated(usize),
}

/// QCDCL Solver
pub struct QbfSolver {
    /// The formula
    formula: QbfFormula,
    /// Variable assignments (0-indexed)
    assignments: Vec<Assignment>,
    /// Decision level for each variable (0-indexed)
    levels: Vec<u32>,
    /// Reason for each assignment (0-indexed)
    reasons: Vec<Reason>,
    /// Assignment trail (in order of assignment)
    trail: Vec<Literal>,
    /// Decision level boundaries in trail
    trail_lim: Vec<usize>,
    /// Current decision level
    decision_level: u32,
    /// Learned clauses (disjunctions - block existential search paths)
    learned: Vec<Vec<Literal>>,
    /// Learned cubes (conjunctions - block universal search paths)
    /// A cube represents a winning strategy for the existential player
    cubes: Vec<Vec<Literal>>,
    /// Variables in quantifier order for decisions
    decision_order: Vec<u32>,
    /// Variable activity for VSIDS-style decisions (0-indexed by var-1)
    activity: Vec<f64>,
    /// VSIDS increment amount
    var_inc: f64,
    /// VSIDS decay factor (smaller => faster decay)
    var_decay: f64,
    /// Number of conflicts
    conflicts: u64,
    /// Number of propagations
    propagations: u64,
    /// Number of decisions
    decisions: u64,
    /// Two-watched literal data: watches[lit_idx] = list of (clause_idx, other_watch)
    /// lit_idx = var * 2 + (1 if negative else 0)
    watches: Vec<Vec<WatchInfo>>,
    /// Position in trail for propagation queue
    qhead: usize,
    /// "Used" flag for each learned clause (set during conflict analysis)
    clause_used: Vec<bool>,
    /// "Used" flag for each learned cube
    cube_used: Vec<bool>,
    /// Next conflict count at which to reduce the clause database
    next_reduce: u64,
    /// Number of clause reductions performed
    reductions: u64,
    /// Number of learned clauses deleted by reduction
    clauses_deleted: u64,
    /// Number of learned cubes deleted by reduction
    cubes_deleted: u64,
}

/// Watch information for a clause
#[derive(Debug, Clone, Copy)]
struct WatchInfo {
    /// Clause index (high bit indicates learned clause)
    clause_idx: usize,
    /// The other watched literal (for quick filtering)
    blocker: Literal,
}

/// Bit flag to distinguish learned clauses in watch lists
const LEARNED_CLAUSE_BIT: usize = 1 << (usize::BITS - 1);

/// Conflict count before first clause database reduction
const REDUCE_DB_INIT: u64 = 2000;

/// Conflicts between reductions
const REDUCE_DB_INC: u64 = 300;

/// Minimum clause length to consider for deletion (short clauses are protected)
const REDUCE_PROTECT_LEN: usize = 3;

/// Result of propagation
enum PropResult {
    Ok,
    Conflict(usize),
}

/// Result of cube learning
enum CubeResult {
    /// Learned a cube, backtrack to this level
    Learned(u32),
    /// Formula is solved (SAT for all universal paths)
    Solved,
}

/// Status of a clause during propagation
enum ClauseStatus {
    Satisfied,
    Falsified,
    /// Only universal literals remain unassigned - UNSAT player wins
    UniversallyBlocked,
    Unit(Literal),
    Unresolved,
}

/// QBF solver statistics
#[derive(Debug, Clone, Default)]
pub struct QbfStats {
    /// Number of conflicts
    pub conflicts: u64,
    /// Number of propagations
    pub propagations: u64,
    /// Number of decisions
    pub decisions: u64,
    /// Number of active (non-deleted) learned clauses
    pub learned_clauses: u64,
    /// Number of active (non-deleted) learned cubes
    pub learned_cubes: u64,
    /// Number of clause database reductions performed
    pub reductions: u64,
    /// Total learned clauses deleted by reduction
    pub clauses_deleted: u64,
    /// Total learned cubes deleted by reduction
    pub cubes_deleted: u64,
}
