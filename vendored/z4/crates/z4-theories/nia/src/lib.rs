#![forbid(unsafe_code)]

//! Z4 NIA - Non-linear Integer Arithmetic theory solver
//!
//! Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//!
//! Implements model-based incremental linearization for non-linear arithmetic,
//! following the DPLL(T) approach where the SAT solver handles branching.
//!
//! ## Algorithm Overview
//!
//! The solver uses a combination of techniques:
//!
//! 1. **Monomial tracking**: Map nonlinear terms like `x*y` to auxiliary variables
//! 2. **Sign lemmas**: Infer sign of product from signs of factors
//! 3. **Tangent plane lemmas**: Linear approximations at the current model point
//! 4. **Delegate to LIA**: Linear constraints are handled by the LIA solver
//!
//! ## Key Insight
//!
//! QF_NIA is undecidable (Hilbert's 10th Problem), but model-based refinement
//! works well on practical problems. The solver iteratively refines bounds using
//! lemmas derived from the current model, converging to a solution or UNSAT.
//!
//! ## Reference
//!
//! Based on Z3's NLA solver (`reference/z3/src/math/lp/nla_*.cpp`).

#![warn(missing_docs)]
#![warn(clippy::all)]
#![allow(clippy::type_complexity)]

// Import safe_eprintln! from z4-core (non-panicking eprintln replacement)
#[macro_use]
extern crate z4_core;

mod monomial;
mod sign_check;
mod sign_lemmas;
mod tangent_add;
mod tangent_lemmas;
mod theory_impl;

#[cfg(not(kani))]
use hashbrown::HashMap;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::{Symbol, TermData, TermId, TermStore};
use z4_core::{Sort, TheoryLit, TheoryPropagation, TheoryResult, TheorySolver};
use z4_lia::LiaSolver;
use z4_lra::GomoryCut;

pub use monomial::Monomial;

/// Model extracted from NIA solver with variable assignments
#[derive(Debug, Clone)]
pub struct NiaModel {
    /// Variable assignments: term_id -> integer value
    pub values: HashMap<TermId, BigInt>,
}

use z4_core::nonlinear::SignConstraint;

/// NIA theory solver using model-based incremental linearization
pub struct NiaSolver<'a> {
    /// Reference to the term store for parsing expressions
    terms: &'a TermStore,
    /// Underlying LIA solver for linear constraints
    lia: LiaSolver<'a>,
    /// Tracked monomials: sorted var list -> Monomial info
    monomials: HashMap<Vec<TermId>, Monomial>,
    /// Auxiliary variable to monomial mapping (reverse index)
    aux_to_monomial: HashMap<TermId, Vec<TermId>>,
    /// Sign constraints on monomials: monomial key -> (constraint, assertion term)
    sign_constraints: HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>>,
    /// Sign constraints on variables: var -> (constraint, assertion term)
    var_sign_constraints: HashMap<TermId, Vec<(SignConstraint, TermId)>>,
    /// Saved sign constraint snapshots for push/pop scoping.
    /// Each entry saves the sign constraint maps at the time of push().
    sign_constraint_snapshots: Vec<(
        HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>>,
        HashMap<TermId, Vec<(SignConstraint, TermId)>>,
    )>,
    /// Trail for monomial push/pop scoping (#3735).
    /// Each entry records (vars_key, aux_var) pairs inserted during that scope level.
    /// On pop, these entries are removed from `monomials` and `aux_to_monomial`.
    monomial_trail: Vec<Vec<(Vec<TermId>, TermId)>>,
    /// Asserted atoms for conflict generation
    asserted: Vec<(TermId, bool)>,
    /// Scope markers for push/pop
    scopes: Vec<usize>,
    /// Debug flag
    debug: bool,
    // Per-theory runtime statistics (#4706)
    check_count: u64,
    conflict_count: u64,
    propagation_count: u64,
}

impl<'a> NiaSolver<'a> {
    /// Create a new NIA solver
    pub fn new(terms: &'a TermStore) -> Self {
        let debug =
            std::env::var("Z4_DEBUG_NIA").is_ok() || std::env::var("Z4_DEBUG_THEORY").is_ok();
        Self {
            terms,
            lia: LiaSolver::new(terms),
            monomials: HashMap::new(),
            aux_to_monomial: HashMap::new(),
            sign_constraints: HashMap::new(),
            var_sign_constraints: HashMap::new(),
            sign_constraint_snapshots: Vec::new(),
            monomial_trail: Vec::new(),
            asserted: Vec::new(),
            scopes: Vec::new(),
            debug,
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
        }
    }

    /// Register a monomial term and return its auxiliary variable
    pub fn register_monomial(&mut self, vars: Vec<TermId>, aux_var: TermId) {
        let mon = Monomial::new(vars.clone(), aux_var);
        // #3735: Record insertion on the monomial trail for push/pop scoping.
        if let Some(scope) = self.monomial_trail.last_mut() {
            scope.push((vars.clone(), aux_var));
        }
        self.aux_to_monomial.insert(aux_var, vars.clone());
        self.monomials.insert(vars, mon);
    }

    /// Get the value of a variable from the current LIA model
    pub(crate) fn var_value(&self, var: TermId) -> Option<BigRational> {
        // Use direct LRA access to get current value
        // (extract_model() returns None when integer variables have non-integer values)
        self.lia.lra_solver().get_value(var)
    }

    /// LIA timing breakdown from the underlying solver (#4794).
    pub fn lia_timings(&self) -> &z4_lia::LiaTimings {
        self.lia.timings()
    }

    /// Extract a model from the solver
    pub fn extract_model(&self) -> Option<NiaModel> {
        self.lia.extract_model().map(|lia_model| NiaModel {
            values: lia_model.values,
        })
    }

    /// Get the auxiliary variable for a monomial (if registered)
    pub fn get_monomial_aux(&self, vars: &[TermId]) -> Option<TermId> {
        self.monomials.get(vars).map(|m| m.aux_var)
    }

    /// All registered monomials, sorted by variable list for deterministic iteration.
    pub fn monomials_sorted(&self) -> Vec<&Monomial> {
        let mut ms: Vec<&Monomial> = self.monomials.values().collect();
        ms.sort_unstable_by(|a, b| a.vars.cmp(&b.vars));
        ms
    }

    /// Passthrough: get the underlying LRA solver (via LIA) for bound
    /// conflict collection in the split-loop pipeline.
    pub fn lra_solver(&self) -> &z4_lra::LraSolver {
        self.lia.lra_solver()
    }

    /// Passthrough: replay learned cuts into the underlying LIA solver
    /// after asserting new literals in a fresh theory instance.
    pub fn replay_learned_cuts(&mut self) {
        self.lia.replay_learned_cuts();
    }

    /// Passthrough: take learned state from the underlying LIA solver for
    /// cross-iteration persistence in the split-loop pipeline.
    pub fn take_learned_state(
        &mut self,
    ) -> (
        Vec<z4_lia::StoredCut>,
        hashbrown::HashSet<z4_lia::HnfCutKey>,
    ) {
        self.lia.take_learned_state()
    }

    /// Passthrough: import previously learned state into the underlying LIA solver.
    pub fn import_learned_state(
        &mut self,
        cuts: Vec<z4_lia::StoredCut>,
        seen: hashbrown::HashSet<z4_lia::HnfCutKey>,
    ) {
        self.lia.import_learned_state(cuts, seen);
    }

    /// Passthrough: take Diophantine solver state from the underlying LIA solver.
    pub fn take_dioph_state(&mut self) -> z4_lia::DiophState {
        self.lia.take_dioph_state()
    }

    /// Passthrough: import Diophantine solver state into the underlying LIA solver.
    pub fn import_dioph_state(&mut self, state: z4_lia::DiophState) {
        self.lia.import_dioph_state(state);
    }
}

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;
