// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CHC (Constrained Horn Clause) translation for IC3/PDR verification
//!
//! This module translates TLA+ specs to CHC problems for IC3/PDR-based
//! safety verification using the z4-chc crate.
//!
//! # Background
//!
//! IC3/PDR (Property-Directed Reachability) can prove safety properties
//! for infinite-state systems by finding inductive invariants, unlike
//! explicit-state model checking which requires finite enumeration.
//!
//! # CHC Encoding
//!
//! For a TLA+ spec with Init, Next, and Invariant:
//! ```text
//! Clause 1 (Initiation):   Init(vars) => Inv(vars)
//! Clause 2 (Consecution):  Inv(vars) ∧ Next(vars,vars') => Inv(vars')
//! Clause 3 (Query):        Inv(vars) ∧ ¬Safety(vars) => false
//! ```
//!
//! If PDR finds an interpretation for Inv satisfying all clauses, the
//! spec is proven safe for all reachable states.
//!
//! # Example
//!
//! ```no_run
//! use tla_z4::chc::{ChcTranslator, PdrCheckResult};
//! use tla_z4::TlaSort;
//!
//! let mut trans = ChcTranslator::new(&[("count", TlaSort::Int)]).unwrap();
//!
//! // Build Init, Next, Safety expressions and translate them
//! // ...
//!
//! match trans.solve_pdr_default() {
//!     Ok(PdrCheckResult::Safe { invariant }) => println!("Safe: {}", invariant),
//!     Ok(PdrCheckResult::Unsafe { trace }) => println!("Counterexample found"),
//!     Ok(PdrCheckResult::Unknown { reason }) => println!("Unknown: {}", reason),
//!     Err(e) => eprintln!("Error: {}", e),
//! }
//! ```
//!
//! # Current Scope
//!
//! - Scalar Bool/Int/String state variables
//! - Finite-domain function-valued state variables expanded into predicate arguments
//! - Record-valued state variables expanded into per-field predicate arguments
//! - Init → initiation clause
//! - Next → consecution clause (with primed variable handling)
//! - Safety → query clause
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

mod builder;
mod result;
mod support;
mod translation;

#[cfg(test)]
mod tests;

pub use result::{PdrCheckResult, PdrState};

use std::collections::HashMap;

use z4_chc::{ChcProblem, ChcVar, PredicateId};

use crate::TlaSort;

/// Expanded representation of a finite-domain function-valued state variable.
#[derive(Debug, Clone)]
pub struct ChcFuncVarInfo {
    /// Domain elements encoded as string keys.
    pub domain_keys: Vec<String>,
    /// Sort of the function range.
    pub range_sort: TlaSort,
    /// Current-state variables for each function element.
    pub element_vars: HashMap<String, ChcVar>,
    /// Next-state variables for each function element.
    pub element_next_vars: HashMap<String, ChcVar>,
}

/// Expanded representation of a record-valued state variable.
#[derive(Debug, Clone)]
pub struct ChcRecordVarInfo {
    /// Record field names and sorts in canonical name order.
    pub field_sorts: Vec<(String, TlaSort)>,
    /// Current-state variables for each record field.
    pub field_vars: HashMap<String, ChcVar>,
    /// Next-state variables for each record field.
    pub field_next_vars: HashMap<String, ChcVar>,
}

/// CHC translator for IC3/PDR verification
///
/// Translates TLA+ Init/Next/Safety to a CHC problem that can be
/// solved with z4-chc's PDR solver.
pub struct ChcTranslator {
    /// The CHC problem being built
    problem: ChcProblem,
    /// Invariant predicate ID
    inv_pred: PredicateId,
    /// State variable mapping: TLA+ name -> ChcVar (current state)
    vars: HashMap<String, ChcVar>,
    /// State variable mapping: TLA+ name -> ChcVar (next state, primed)
    next_vars: HashMap<String, ChcVar>,
    /// Expanded function-valued state variables: TLA+ name -> per-key vars
    func_vars: HashMap<String, ChcFuncVarInfo>,
    /// Expanded record-valued state variables: TLA+ name -> per-field vars
    record_vars: HashMap<String, ChcRecordVarInfo>,
    /// Flattened invariant predicate arguments for current state
    pred_vars: Vec<ChcVar>,
    /// Flattened invariant predicate arguments for next state
    pred_next_vars: Vec<ChcVar>,
    /// Variable sorts for type checking
    var_sorts: HashMap<String, TlaSort>,
    /// Interned atoms for strings and model values lowered to CHC Ints
    atom_intern: HashMap<String, i64>,
    /// Whether primed variables are allowed in the current translation context
    allow_primed: bool,
    /// Whether scalar lookups should resolve to next-state variables
    use_primed_vars: bool,
}
