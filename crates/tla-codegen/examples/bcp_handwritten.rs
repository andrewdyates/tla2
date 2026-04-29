// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Hand-written BCP (Boolean Constraint Propagation) state machine.
//!
//! This is a hand-optimized Rust implementation of the same BCP spec
//! (specs/z4/BCP.tla) for benchmarking against the auto-generated version.
//!
//! Key optimizations over the generated code:
//! - Uses `[Assign; 3]` array instead of `TlaFunc<i64, String>` for assignment
//! - Uses an enum `Assign` instead of `String` for variable values
//! - Uses `Vec<TrailEntry>` with a struct instead of `Vec<(i64, String, TlaSet<i64>)>`
//! - Uses `&[&[i32]]` for clauses instead of `TlaSet<TlaSet<i64>>`
//! - Avoids BTreeSet overhead entirely

#![allow(unused)]

use tla_runtime::prelude::*;

/// Variable assignment: TRUE, FALSE, or UNSET
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Assign {
    True,
    False,
    Unset,
}

/// Trail entry: which variable was set to what value, and why
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TrailEntry {
    pub var: usize, // 0-indexed variable
    pub value: Assign,
    pub reason: Vec<i32>, // clause that forced it, or empty for decisions
}

/// Hand-optimized BCP state
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HandBCPState {
    pub assignment: [Assign; 3], // 3 variables
    pub trail: Vec<TrailEntry>,
    pub conflict: bool,
    pub propagating: bool,
}

/// Clause database: 4 clauses over 3 variables
/// C1: {1, 2}, C2: {-1, 3}, C3: {-2, -3}, C4: {1, -2, 3}
const CLAUSES: &[&[i32]] = &[&[1, 2], &[-1, 3], &[-2, -3], &[1, -2, 3]];

const NUM_VARS: usize = 3;

/// Hand-written BCP state machine
pub struct HandBCP;

impl HandBCP {
    #[inline]
    fn var_idx(lit: i32) -> usize {
        (lit.unsigned_abs() as usize) - 1
    }

    #[inline]
    fn lit_true(assignment: &[Assign; 3], lit: i32) -> bool {
        let v = Self::var_idx(lit);
        if lit > 0 {
            assignment[v] == Assign::True
        } else {
            assignment[v] == Assign::False
        }
    }

    #[inline]
    fn lit_false(assignment: &[Assign; 3], lit: i32) -> bool {
        let v = Self::var_idx(lit);
        if lit > 0 {
            assignment[v] == Assign::False
        } else {
            assignment[v] == Assign::True
        }
    }

    #[inline]
    fn lit_unset(assignment: &[Assign; 3], lit: i32) -> bool {
        assignment[Self::var_idx(lit)] == Assign::Unset
    }

    #[inline]
    fn clause_sat(assignment: &[Assign; 3], clause: &[i32]) -> bool {
        clause.iter().any(|&lit| Self::lit_true(assignment, lit))
    }

    #[inline]
    fn clause_conflict(assignment: &[Assign; 3], clause: &[i32]) -> bool {
        clause.iter().all(|&lit| Self::lit_false(assignment, lit))
    }

    fn clause_unit(assignment: &[Assign; 3], clause: &[i32]) -> Option<i32> {
        if Self::clause_sat(assignment, clause) {
            return None;
        }
        let mut unset_lit = None;
        for &lit in clause {
            if Self::lit_unset(assignment, lit) {
                if unset_lit.is_some() {
                    return None; // more than one unset
                }
                unset_lit = Some(lit);
            }
        }
        unset_lit // Some(lit) if exactly one unset, None if zero unset
    }

    #[inline]
    fn lit_value(lit: i32) -> Assign {
        if lit > 0 {
            Assign::True
        } else {
            Assign::False
        }
    }
}

impl StateMachine for HandBCP {
    type State = HandBCPState;

    fn init(&self) -> Vec<Self::State> {
        vec![HandBCPState {
            assignment: [Assign::Unset; 3],
            trail: Vec::new(),
            conflict: false,
            propagating: true,
        }]
    }

    fn next(&self, state: &Self::State) -> Vec<Self::State> {
        let mut next_states = Vec::new();

        // Action 1: Propagate
        if state.propagating && !state.conflict {
            for clause in CLAUSES {
                if let Some(lit) = Self::clause_unit(&state.assignment, clause) {
                    let v = Self::var_idx(lit);
                    let val = Self::lit_value(lit);
                    let mut new_assign = state.assignment;
                    new_assign[v] = val;
                    let mut new_trail = state.trail.clone();
                    new_trail.push(TrailEntry {
                        var: v,
                        value: val,
                        reason: clause.to_vec(),
                    });
                    next_states.push(HandBCPState {
                        assignment: new_assign,
                        trail: new_trail,
                        conflict: false,
                        propagating: true,
                    });
                }
            }
        }

        // Action 2: DetectConflict
        if state.propagating && !state.conflict {
            if CLAUSES
                .iter()
                .any(|c| Self::clause_conflict(&state.assignment, c))
            {
                next_states.push(HandBCPState {
                    assignment: state.assignment,
                    trail: state.trail.clone(),
                    conflict: true,
                    propagating: false,
                });
            }
        }

        // Action 3: Quiesce
        if state.propagating && !state.conflict {
            let has_unit = CLAUSES
                .iter()
                .any(|c| Self::clause_unit(&state.assignment, c).is_some());
            let has_conflict = CLAUSES
                .iter()
                .any(|c| Self::clause_conflict(&state.assignment, c));
            if !has_unit && !has_conflict {
                next_states.push(HandBCPState {
                    assignment: state.assignment,
                    trail: state.trail.clone(),
                    conflict: state.conflict,
                    propagating: false,
                });
            }
        }

        // Action 4: Decide
        if !state.propagating && !state.conflict {
            for v in 0..NUM_VARS {
                if state.assignment[v] == Assign::Unset {
                    for &val in &[Assign::True, Assign::False] {
                        let mut new_assign = state.assignment;
                        new_assign[v] = val;
                        let mut new_trail = state.trail.clone();
                        new_trail.push(TrailEntry {
                            var: v,
                            value: val,
                            reason: Vec::new(),
                        });
                        next_states.push(HandBCPState {
                            assignment: new_assign,
                            trail: new_trail,
                            conflict: false,
                            propagating: true,
                        });
                    }
                }
            }
        }

        // Action 5: Done (stuttering)
        if state.conflict
            || (!state.propagating && state.assignment.iter().all(|a| *a != Assign::Unset))
        {
            next_states.push(state.clone());
        }

        next_states
    }

    fn check_invariant(&self, state: &Self::State) -> Option<bool> {
        // TrailConsistent
        for entry in &state.trail {
            if state.assignment[entry.var] != entry.value {
                return Some(false);
            }
        }
        // NoSpuriousConflict
        if state.conflict
            && !CLAUSES
                .iter()
                .any(|c| Self::clause_conflict(&state.assignment, c))
        {
            return Some(false);
        }
        // PropagationSound
        for entry in &state.trail {
            if !entry.reason.is_empty() {
                let reason = &entry.reason;
                if !reason.iter().any(|&lit| {
                    Self::var_idx(lit) == entry.var && Self::lit_value(lit) == entry.value
                }) {
                    return Some(false);
                }
            }
        }
        Some(true)
    }
}

fn main() {
    println!("BCP (Boolean Constraint Propagation) — hand-optimized Rust implementation");
    println!("Comparison target for the auto-generated version (bcp_generated).");
    println!();
    println!("This example is a benchmark target. Run with:");
    println!("  cargo bench -p tla-codegen --bench bcp_benchmark");
}
