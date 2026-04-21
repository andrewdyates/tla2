#![forbid(unsafe_code)]

//! Z4 NRA - Non-linear Real Arithmetic theory solver
//!
//! Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//!
//! Implements model-based incremental linearization for nonlinear real arithmetic,
//! following the DPLL(T) approach where the SAT solver handles branching.
//!
//! ## Algorithm Overview
//!
//! 1. **Monomial tracking**: Map nonlinear terms like `x*y` to auxiliary variables
//! 2. **Sign lemmas**: Infer sign of product from signs of factors
//! 3. **Tangent plane lemmas**: Linear approximations at the current model point
//! 4. **Delegate to LRA**: Linear constraints are handled by the LRA solver
//!
//! Based on Z3's NLA solver (`reference/z3/src/math/lp/nla_*.cpp`).
//!
//! Check loop + refinement: see `check_loop.rs`

#![warn(missing_docs)]
#![warn(clippy::all)]
#![allow(clippy::type_complexity)]

mod check_loop;
mod monomial;
mod patch;
mod sign;
mod tangent;
mod theory_impl;
mod verification;

#[cfg(not(kani))]
use hashbrown::HashMap;
use num_rational::BigRational;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use z4_core::{TheoryLit, TheoryPropagation, TheoryResult, TheorySolver};

use monomial::Monomial;
use sign::SignConstraint;

/// A purified division: `(/ num denom)` → fresh LRA variable `div_term`,
/// with side constraint `denom * div_term = num`.
#[derive(Debug, Clone)]
struct DivPurification {
    /// The original `(/ num denom)` term (has an LRA variable via `intern_var`)
    div_term: TermId,
    /// The numerator term
    numerator: TermId,
    /// The denominator term
    denominator: TermId,
}

/// Red zone: if remaining stack is below this threshold, grow before entering
/// the NRA check loop. The NRA check loop (via LRA simplex + monomial
/// refinement) needs significant stack in debug. A 4 MiB red zone triggers
/// growth when a default 8 MiB test thread has less than 4 MiB remaining.
const NRA_STACK_RED_ZONE: usize = 4 * 1024 * 1024;

/// Size of the new stack segment allocated when the red zone is reached.
/// 16 MiB to provide ample room for NRA check iterations in debug mode.
const NRA_STACK_SIZE: usize = 16 * 1024 * 1024;

/// Guard the NRA entrypoint against stack overflow on small thread stacks.
fn maybe_grow_nra_stack<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(NRA_STACK_RED_ZONE, NRA_STACK_SIZE, f)
}

pub use z4_lra::LraModel;

/// NRA theory solver using model-based incremental linearization
pub struct NraSolver<'a> {
    /// Reference to the term store
    terms: &'a TermStore,
    /// Underlying LRA solver for linear constraints
    pub(crate) lra: z4_lra::LraSolver,
    /// Tracked monomials: sorted var list -> Monomial info
    pub(crate) monomials: HashMap<Vec<TermId>, Monomial>,
    /// Auxiliary variable to monomial mapping (reverse index)
    aux_to_monomial: HashMap<TermId, Vec<TermId>>,
    /// Sign constraints on monomials
    sign_constraints: HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>>,
    /// Sign constraints on variables
    var_sign_constraints: HashMap<TermId, Vec<(SignConstraint, TermId)>>,
    /// Saved sign constraint snapshots for push/pop
    sign_constraint_snapshots: Vec<(
        HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>>,
        HashMap<TermId, Vec<(SignConstraint, TermId)>>,
    )>,
    /// Division purifications: `(/ num denom)` → side constraint `denom * div = num`.
    /// Tracked separately from monomials because the numerator may be a constant
    /// with no LRA variable (#6811).
    div_purifications: Vec<DivPurification>,
    /// Asserted atoms for conflict generation
    asserted: Vec<(TermId, bool)>,
    /// Scope markers for push/pop: (asserted_len, div_purifications_len)
    scopes: Vec<(usize, usize)>,
    /// Debug flag
    pub(crate) debug: bool,
    check_count: u64,
    conflict_count: u64,
    propagation_count: u64,
    tangent_lemma_count: u64,
    patch_count: u64,
    sign_cut_count: u64,
    /// Number of tentative LRA scopes active (sign-cut + patch scopes).
    /// The sign-cut path (lib.rs:322) and try_tentative_patch (patch.rs:245)
    /// each push one scope. undo_tentative_patch() must pop ALL of them
    /// to avoid leaking model-dependent bounds into future queries.
    tentative_depth: u32,
}

impl<'a> NraSolver<'a> {
    /// Create a new NRA solver
    pub fn new(terms: &'a TermStore) -> Self {
        let debug =
            std::env::var("Z4_DEBUG_NRA").is_ok() || std::env::var("Z4_DEBUG_THEORY").is_ok();
        let mut lra = z4_lra::LraSolver::new(terms);
        // NRA handles nonlinear multiplication — tell LRA not to flag it as unsupported.
        lra.set_combined_theory_mode(true);
        Self {
            terms,
            lra,
            monomials: HashMap::new(),
            aux_to_monomial: HashMap::new(),
            sign_constraints: HashMap::new(),
            var_sign_constraints: HashMap::new(),
            sign_constraint_snapshots: Vec::new(),
            div_purifications: Vec::new(),
            asserted: Vec::new(),
            scopes: Vec::new(),
            debug,
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            tangent_lemma_count: 0,
            patch_count: 0,
            sign_cut_count: 0,
            tentative_depth: 0,
        }
    }

    /// Get the value of a variable from the current LRA model
    pub(crate) fn var_value(&self, var: TermId) -> Option<BigRational> {
        self.lra.get_value(var)
    }

    /// Register a monomial
    fn register_monomial(&mut self, vars: Vec<TermId>, aux_var: TermId) {
        if self.debug {
            tracing::debug!(
                "[NRA] register_monomial: vars={:?}, aux_var={:?}",
                vars,
                aux_var
            );
        }
        let mon = Monomial::new(vars.clone(), aux_var);
        self.aux_to_monomial.insert(aux_var, vars.clone());
        self.monomials.insert(vars, mon);
    }

    /// Recursively scan a term for nonlinear subterms and register them
    fn collect_nonlinear_terms(&mut self, term: TermId) {
        match self.terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                match name.as_str() {
                    "*" => {
                        let mut var_args = Vec::new();
                        for &arg in args {
                            let is_const = self.terms.extract_integer_constant(arg).is_some()
                                || matches!(
                                    self.terms.get(arg),
                                    TermData::Const(Constant::Rational(_))
                                );
                            if !is_const {
                                var_args.push(arg);
                            }
                        }

                        if var_args.len() >= 2 {
                            var_args.sort_by_key(|t| t.0);
                            if !self.monomials.contains_key(&var_args) {
                                self.register_monomial(var_args, term);
                            }
                        }
                    }
                    "/" if args.len() == 2 => {
                        // Division purification (#6811): (/ num denom) with symbolic
                        // denominator → track for refinement via denom * div = num.
                        let num = args[0];
                        let denom = args[1];
                        let denom_is_const = self.terms.extract_integer_constant(denom).is_some()
                            || matches!(
                                self.terms.get(denom),
                                TermData::Const(Constant::Rational(_))
                            );
                        if !denom_is_const
                            && !self.div_purifications.iter().any(|p| p.div_term == term)
                        {
                            self.div_purifications.push(DivPurification {
                                div_term: term,
                                numerator: num,
                                denominator: denom,
                            });
                        }
                    }
                    _ => {}
                }
                for &arg in args {
                    self.collect_nonlinear_terms(arg);
                }
            }
            TermData::Not(inner) => self.collect_nonlinear_terms(*inner),
            TermData::Ite(c, t, e) => {
                self.collect_nonlinear_terms(*c);
                self.collect_nonlinear_terms(*t);
                self.collect_nonlinear_terms(*e);
            }
            TermData::Let(_, body) => self.collect_nonlinear_terms(*body),
            _ => {}
        }
    }

    /// Extract a model from the solver, returning an LRA-compatible model.
    pub fn extract_model(&self) -> LraModel {
        self.lra.extract_model()
    }

    /// Access the underlying LRA solver for value queries in combined theory adapters.
    pub fn lra(&self) -> &z4_lra::LraSolver {
        &self.lra
    }
}
