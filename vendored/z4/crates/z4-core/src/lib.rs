// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! Z4 Core - Common types and traits for the Z4 SMT solver
//!
//! This crate provides the foundational types shared across all Z4 components:
//! - Term representation (hash-consed DAG)
//! - Sort system (type checking)
//! - Theory trait (interface for theory solvers)
//! - Proof types (resolution proofs, theory lemmas)
//! - Tseitin transformation (Boolean to CNF)
//!
//! # Type Hierarchy
//!
//! Z4 has multiple Sort types at different layers. This crate provides the
//! canonical internal representation:
//!
//! ```text
//! z4_core::Sort (canonical internal representation)
//!     ↕ From impls
//! z4_chc::ChcSort (CHC expression types — bidirectional From<CoreSort>)
//!
//! z4_dpll::api::Sort (re-export of z4_core::Sort — same type)
//!
//! z4_frontend::Sort (parser AST — separate, string-based, no From conversion)
//! ```
//!
//! When consuming Z4:
//! - Use `z4::Sort` (re-exported from z4-dpll) for the native Rust API
//! - `z4_core::Sort` is the internal canonical type
//! - `z4_frontend::Sort` is only for parsing SMT-LIB files
//!
//! Bidirectional `From` implementations exist between `z4_core::Sort` and
//! `z4_chc::ChcSort`. The dpll Sort is a direct re-export (same type).

#![warn(missing_docs)]
#![warn(clippy::all)]

pub(crate) mod alethe;
pub mod kani_compat;
pub(crate) mod math;
pub mod nonlinear;
pub mod panic_utils;
pub(crate) mod proof;
pub mod proof_validation;
pub(crate) mod smtlib;
pub(crate) mod sort;
pub mod term;
pub(crate) mod theory;
pub(crate) mod tseitin;
pub mod verification;

pub use math::extended_gcd_bigint;
pub use proof::{
    AletheRule, BvGateType, CuttingPlaneAnnotation, FarkasAnnotation, FpOp, LiaAnnotation, Proof,
    ProofId, ProofStep, TheoryLemmaKind, TheoryLemmaProof,
};
pub use smtlib::{escape_string_contents, quote_symbol, string_literal, unescape_string_contents};
pub use sort::{ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
pub use term::{Constant, RationalWrapper, Symbol, TermData, TermId, TermStore};
pub use theory::{
    assert_conflict_soundness, BoundRefinementRequest, DiscoveredEquality, DisequalitySplitRequest,
    EqualityPropagationResult, ExpressionSplitRequest, ModelEqualityRequest, SplitRequest,
    StringLemma, StringLemmaKind, TheoryConflict, TheoryLemma, TheoryLit, TheoryPropagation,
    TheoryResult, TheorySolver,
};
pub use tseitin::{
    ClausificationProof, CnfClause, CnfLit, Tseitin, TseitinEncodedAssertion, TseitinResult,
    TseitinState,
};
pub use verification::{
    VerificationBoundary, VerificationEvidenceKind, VerificationFailure, VerificationVerdict,
};

pub use panic_utils::{catch_z4_panics, is_z4_panic_reason, panic_payload_to_string};

/// Write to stderr without panicking on broken pipe.
///
/// Unlike `eprintln!`, this macro silently ignores write errors (e.g., broken
/// pipe when stderr is redirected). This is important for solver diagnostics
/// that should never cause a panic.
#[macro_export]
macro_rules! safe_eprintln {
    ($($arg:tt)*) => {{
        use std::io::Write;
        let _ = writeln!(std::io::stderr(), $($arg)*);
    }};
}

/// Create a cached environment-variable-based boolean flag.
///
/// The flag value is read once from the environment on first access and
/// cached for the process lifetime via `OnceLock`. Uses `var_os().is_some()`
/// for consistency: the flag is active when the env var is present,
/// regardless of its value or UTF-8 validity.
///
/// # Usage
///
/// ```rust
/// use z4_core::cached_env_flag;
///
/// // Private function (default)
/// cached_env_flag!(debug_foo, "Z4_DEBUG_FOO");
///
/// // With explicit visibility
/// cached_env_flag!(pub(crate) debug_bar, "Z4_DEBUG_BAR");
///
/// let _: fn() -> bool = debug_foo;
/// let _: fn() -> bool = debug_bar;
/// ```
///
/// Centralizes the pattern previously duplicated across z4-dpll and z4-chc
/// (see issue #3908).
#[macro_export]
macro_rules! cached_env_flag {
    ($vis:vis $name:ident, $env_var:literal) => {
        #[inline]
        $vis fn $name() -> bool {
            static CACHE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            *CACHE.get_or_init(|| std::env::var_os($env_var).is_some())
        }
    };
}

/// Unwrap a `Not` wrapper from a literal, flipping the boolean value.
///
/// Theory solvers receive literals as `(TermId, bool)` pairs where the term
/// may be `Not(inner)`. This strips one layer of negation and flips the value,
/// returning the inner atom and its effective polarity.
pub fn unwrap_not(terms: &TermStore, literal: TermId, value: bool) -> (TermId, bool) {
    match terms.get(literal) {
        TermData::Not(inner) => (*inner, !value),
        _ => (literal, value),
    }
}

/// Determine whether a term is a theory atom (as opposed to propositional structure).
///
/// Theory atoms are Bool-sorted terms that represent atomic predicates from a
/// Decode the canonical Bool-equality biconditional introduced by `TermStore::mk_eq`.
///
/// Bool-sorted equalities are normalized in `z4-core` to `ite(lhs, rhs, not(rhs))`
/// (#3421). Consumers that need equality semantics on the canonicalized term
/// can use this helper to recover the original `(lhs, rhs)` pair.
pub fn decode_bool_biconditional_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::Ite(lhs, rhs, else_term) if terms.sort(term) == &Sort::Bool => {
            match terms.get(*else_term) {
                TermData::Not(inner) if *inner == *rhs => Some((*lhs, *rhs)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Determine whether a term should be communicated to the theory solver.
///
/// DPLL(T) theory solvers should only see *atomic* Boolean predicates (e.g., `x <= 5`,
/// `f(a) = b`, `select(a,i) = v`) and should not be asked to interpret Boolean structure
/// like `and/or/xor/=>/ite`.
///
/// This is the single source of truth for theory-atom routing, used by both
/// z4-dpll and z4-chc. See #6881 for the consolidation rationale.
pub fn is_theory_atom(terms: &TermStore, term: TermId) -> bool {
    if terms.sort(term) != &Sort::Bool {
        return false;
    }

    match terms.get(term) {
        TermData::Const(Constant::Bool(_)) => false,
        TermData::Const(_) => false,
        TermData::Var(_, _) => false,
        TermData::Not(_) => false,
        TermData::Ite(_, _, _) => decode_bool_biconditional_eq(terms, term).is_some(),
        TermData::Let(_, _) => false,
        TermData::App(Symbol::Named(name), _args) => match name.as_str() {
            "and" | "or" | "xor" | "=>" => false,
            "=" => true,
            _ => true,
        },
        TermData::App(_, _) => true,
        // Quantifiers are theory literals (handled by E-matching)
        TermData::Forall(..) | TermData::Exists(..) => true,
    }
}

/// Propagate pairwise equalities for variables with identical tight bounds.
///
/// Given a list of `(term, value, reasons)` triples where each variable has
/// tight bounds (lower == upper, non-strict), groups variables by value and
/// propagates equalities between all pairs in each group. Used by both LRA
/// and LIA Nelson-Oppen equality propagation.
///
/// Deduplicates against `propagated_pairs` to avoid re-propagating equalities
/// that were already sent in prior calls (e.g., after push/pop).
pub fn propagate_tight_bound_equalities(
    tight_bound_vars: Vec<(TermId, num_rational::BigRational, Vec<TheoryLit>)>,
    propagated_pairs: &mut kani_compat::DetHashSet<(TermId, TermId)>,
) -> Vec<DiscoveredEquality> {
    use kani_compat::DetHashMap as HashMap;

    // Group variables by their value
    let mut vars_by_value: HashMap<num_rational::BigRational, Vec<(TermId, Vec<TheoryLit>)>> =
        HashMap::new();
    for (term, value, reasons) in tight_bound_vars {
        vars_by_value
            .entry(value)
            .or_insert_with(Vec::new)
            .push((term, reasons));
    }

    // Sort groups by value for deterministic iteration (#2681)
    let mut sorted_groups: Vec<_> = vars_by_value.iter().collect();
    sorted_groups.sort_by(|(a, _), (b, _)| a.cmp(b));

    let mut equalities = Vec::new();

    for (_value, vars) in sorted_groups {
        if vars.len() < 2 {
            continue;
        }

        // Propagate pairwise equalities between all variables with same value
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                let (lhs, lhs_reasons) = &vars[i];
                let (rhs, rhs_reasons) = &vars[j];

                // Canonicalize the pair to avoid duplicate propagations
                let pair = if lhs.0 < rhs.0 {
                    (*lhs, *rhs)
                } else {
                    (*rhs, *lhs)
                };

                if !propagated_pairs.contains(&pair) {
                    propagated_pairs.insert(pair);

                    // Combine reasons from both variables
                    let mut combined_reasons = lhs_reasons.clone();
                    for r in rhs_reasons {
                        if !combined_reasons.contains(r) {
                            combined_reasons.push(*r);
                        }
                    }

                    equalities.push(DiscoveredEquality::new(*lhs, *rhs, combined_reasons));
                }
            }
        }
    }

    equalities
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
