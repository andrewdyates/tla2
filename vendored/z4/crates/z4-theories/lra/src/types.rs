// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Type definitions and utility functions for LRA solver.

#[cfg(not(kani))]
use hashbrown::HashMap;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use smallvec::SmallVec;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::TermId;

use crate::rational::Rational;

/// Cached `BigRational::one()` to avoid heap allocation per call.
/// Used as default Farkas scale in 11+ call sites.
pub(crate) fn big_rational_one() -> &'static BigRational {
    use std::sync::OnceLock;
    static ONE: OnceLock<BigRational> = OnceLock::new();
    ONE.get_or_init(|| BigRational::one())
}

pub(crate) fn add_sparse_term(coeffs: &mut Vec<(u32, BigRational)>, var: u32, coeff: BigRational) {
    if coeff.is_zero() {
        return;
    }
    match coeffs.binary_search_by_key(&var, |(existing_var, _)| *existing_var) {
        Ok(idx) => {
            coeffs[idx].1 += coeff;
            if coeffs[idx].1.is_zero() {
                coeffs.remove(idx);
            }
        }
        Err(idx) => coeffs.insert(idx, (var, coeff)),
    }
}

/// Normalize and merge sparse coefficient list (BigRational version for tests).
#[cfg(test)]
pub(crate) fn normalize_sparse_coeffs(
    mut coeffs: Vec<(u32, BigRational)>,
) -> Vec<(u32, BigRational)> {
    coeffs.retain(|(_, coeff)| !coeff.is_zero());
    coeffs.sort_unstable_by_key(|(var, _)| *var);

    let mut merged: Vec<(u32, BigRational)> = Vec::with_capacity(coeffs.len());
    for (var, coeff) in coeffs {
        if let Some((last_var, last_coeff)) = merged.last_mut() {
            if *last_var == var {
                *last_coeff += coeff;
                if last_coeff.is_zero() {
                    merged.pop();
                }
                continue;
            }
        }
        merged.push((var, coeff));
    }
    merged
}

/// Normalize and merge sparse coefficient list using fast Rational.
pub(crate) fn normalize_sparse_coeffs_rat(
    mut coeffs: Vec<(u32, Rational)>,
) -> Vec<(u32, Rational)> {
    coeffs.retain(|(_, coeff)| !coeff.is_zero());
    coeffs.sort_unstable_by_key(|(var, _)| *var);

    let mut merged: Vec<(u32, Rational)> = Vec::with_capacity(coeffs.len());
    for (var, coeff) in coeffs {
        if let Some((last_var, last_coeff)) = merged.last_mut() {
            if *last_var == var {
                *last_coeff += coeff;
                if last_coeff.is_zero() {
                    merged.pop();
                }
                continue;
            }
        }
        merged.push((var, coeff));
    }
    merged
}

/// Add a term to sparse coefficient list using fast Rational.
pub(crate) fn add_sparse_term_rat(coeffs: &mut Vec<(u32, Rational)>, var: u32, coeff: Rational) {
    if coeff.is_zero() {
        return;
    }
    match coeffs.binary_search_by_key(&var, |(existing_var, _)| *existing_var) {
        Ok(idx) => {
            coeffs[idx].1 += coeff;
            if coeffs[idx].1.is_zero() {
                coeffs.remove(idx);
            }
        }
        Err(idx) => coeffs.insert(idx, (var, coeff)),
    }
}

/// Bound type for a variable
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BoundType {
    /// Lower bound: x >= c
    Lower,
    /// Upper bound: x <= c
    Upper,
}

/// Heap key for greatest-error pivot selection (#4919 Phase 1).
///
/// Keyed by (violation_magnitude_f64, var_id). Rust's BinaryHeap is a max-heap,
/// so the variable with the largest bound violation is extracted first.
/// Uses `f64::total_cmp` for deterministic total ordering (NaN sorts last).
///
/// Reference: Z3 `select_greatest_error_var()` in `theory_arith_core.h:2270-2300`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ErrorKey(pub(crate) f64, pub(crate) u32);

impl PartialEq for ErrorKey {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == std::cmp::Ordering::Equal && self.1 == other.1
    }
}
impl Eq for ErrorKey {}

impl PartialOrd for ErrorKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ErrorKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Primary: largest error first (max-heap naturally returns this)
        // Secondary: smallest var index first (determinism tiebreaker)
        self.0
            .total_cmp(&other.0)
            .then_with(|| other.1.cmp(&self.1))
    }
}

/// Eager explanation data captured at bound derivation time (#6617).
///
/// Equivalent to Z3's `m_explain_bound` closure in `implied_bound.h:36`.
/// When called to produce reasons, iterates over `contributing_vars` and
/// fetches each variable's current direct bound reason. Never recurses
/// into the depth-limited `collect_row_reasons_recursive` walker.
///
/// Reference: Z3 `limit_j` (bound_analyzer_on_row.h:298-321) captures
/// the row by value and fetches bound witnesses at explanation time.
#[derive(Debug, Clone)]
pub(crate) struct BoundExplanation {
    /// Variables whose bounds contributed to this derivation, with the
    /// direction of bound used (true = upper, false = lower).
    /// Excludes the target variable itself.
    /// Z3 equivalent: the loop body in `limit_j` (bound_analyzer_on_row.h:308-316).
    pub(crate) contributing_vars: SmallVec<[(u32, bool); 8]>,
}

/// An implied bound derived from a tableau row during `compute_implied_bounds`.
///
/// Stores the bound value, strictness flag, and eagerly-captured explanation
/// data for flat (non-recursive) reason collection (#6617).
///
/// Reference: Z3 stores a lazy explanation closure on `implied_bound`
/// (`reference/z3/src/math/lp/implied_bound.h:36`). Z4 captures the same
/// data eagerly in `BoundExplanation` at derivation time.
#[derive(Debug, Clone)]
pub(crate) struct ImpliedBound {
    /// The bound value
    pub(crate) value: Rational,
    /// Whether the bound is strict
    pub(crate) strict: bool,
    /// The tableau row index from which this bound was derived.
    /// Used for lazy reason collection in `collect_row_reasons_recursive`.
    /// `usize::MAX` is the sentinel for direct bounds (which use `Bound.reason_pairs()`).
    pub(crate) row_idx: usize,
    /// Eager explanation data captured at derivation time (#6617).
    /// `None` for direct bounds (sentinel row_idx = usize::MAX) and for
    /// legacy implied bounds created before this field was added.
    /// When present, `collect_reasons_from_explanation` uses this instead
    /// of the depth-limited recursive walker.
    pub(crate) explanation: Option<BoundExplanation>,
}

/// One finite endpoint of an expression interval.
///
/// The numeric value alone is insufficient for strict propagation because an
/// open endpoint at zero proves a strict sign while a closed endpoint at zero
/// does not (`#6582`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct IntervalEndpoint {
    /// Endpoint value.
    pub(crate) value: BigRational,
    /// Whether the endpoint is open.
    pub(crate) strict: bool,
}

impl IntervalEndpoint {
    pub(crate) fn new(value: BigRational, strict: bool) -> Self {
        Self { value, strict }
    }
}

/// Finite lower/upper bounds for a linear expression.
///
/// `None` means the corresponding side is unbounded.
pub(crate) type ExprInterval = (Option<IntervalEndpoint>, Option<IntervalEndpoint>);

/// A bound with its value and the atoms that established it
#[derive(Debug, Clone)]
pub struct Bound {
    /// The bound value (fast-path i64 with BigRational fallback).
    pub value: Rational,
    /// The atom terms that established this bound.
    /// Multiple reasons can exist when bounds are derived from the LIA solver's
    /// Diophantine analysis, which combines information from multiple constraints.
    pub reasons: Vec<TermId>,
    /// The Boolean values of each reason in the current assignment.
    ///
    /// When the SAT layer assigns an atom `t` to `false`, the theory asserts the
    /// negation of `t` (e.g. `!(x <= 5)` becomes `x > 5`). For conflict clauses
    /// to be sound, we must preserve that polarity.
    pub reason_values: Vec<bool>,
    /// Farkas scaling factors for each reason atom.
    ///
    /// When an atom like `5x <= c` is normalized to a per-variable bound `x <= c/5`,
    /// the Farkas coefficient must account for this normalization. The scale factor
    /// is `1/|coeff|` where `coeff` is the original variable coefficient in the atom.
    /// For atoms that directly constrain a single variable with coefficient 1,
    /// the scale is 1. Parallel to `reasons` — one entry per reason.
    pub reason_scales: Vec<BigRational>,
    /// Whether the bound is strict (< or >) vs non-strict (<= or >=)
    pub strict: bool,
}

impl Bound {
    /// Create a bound with reason tracking and debug invariant checks.
    pub fn new(
        value: Rational,
        reasons: Vec<TermId>,
        reason_values: Vec<bool>,
        reason_scales: Vec<BigRational>,
        strict: bool,
    ) -> Self {
        debug_assert_eq!(
            reasons.len(),
            reason_values.len(),
            "reasons/values mismatch"
        );
        debug_assert!(
            reason_scales.len() <= reasons.len(),
            "more scales than reasons"
        );
        Self {
            value,
            reasons,
            reason_values,
            reason_scales,
            strict,
        }
    }

    /// Create a bound with no reason tracking (tests only).
    ///
    /// Production code must always provide reasons to prevent sentinel-only
    /// bounds that degrade to Unknown or produce unsound conflicts (#4919).
    #[cfg(test)]
    pub fn without_reasons(value: Rational, strict: bool) -> Self {
        Self {
            value,
            reasons: Vec::new(),
            reason_values: Vec::new(),
            reason_scales: Vec::new(),
            strict,
        }
    }

    /// Iterate over `(term, value)` pairs for reason atoms.
    ///
    /// Convenience accessor that zips the parallel `reasons` and
    /// `reason_values` vectors.
    pub fn reason_pairs(&self) -> impl Iterator<Item = (TermId, bool)> + '_ {
        self.reasons
            .iter()
            .copied()
            .zip(self.reason_values.iter().copied())
    }

    /// Convert to InfRational target for simplex assignment.
    pub(crate) fn as_inf(&self, bound_type: BoundType) -> InfRational {
        // value is already Rational -- no conversion needed.
        let x = self.value.clone();
        if self.strict {
            let eps = match bound_type {
                BoundType::Lower => Rational::one(),
                BoundType::Upper => -Rational::one(),
            };
            InfRational::new_rat(x, eps)
        } else {
            InfRational::from_rat(x)
        }
    }

    /// Approximate the bound value as f64, avoiding BigRational allocation.
    /// Used for heuristic heap keys (#6617).
    #[inline]
    pub(crate) fn value_approx_f64(&self) -> f64 {
        self.value.approx_f64()
    }

    /// Convert bound value to BigRational (for cold-path arithmetic).
    /// Hot-path comparisons should use `self.value` directly (Rational).
    #[inline]
    pub fn value_big(&self) -> BigRational {
        self.value.to_big()
    }
}

pub(crate) use crate::infrational::InfRational;

/// Status of a variable in the simplex tableau
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarStatus {
    /// Non-basic variable: can be pivoted with a basic variable
    NonBasic,
    /// Basic variable: defined by a row in the tableau
    Basic(usize), // row index
}

// TableauRow is defined in crate::tableau (extracted for code health, #5970).
// Re-exported here so existing `use types::TableauRow` imports continue to work.
pub(crate) use crate::tableau::TableauRow;

/// Information about an LRA variable
#[derive(Debug, Clone, Default)]
pub(crate) struct VarInfo {
    /// Current value assignment
    /// Current value assignment (infinitesimal-extended for strict bounds)
    pub(crate) value: InfRational,
    /// Lower bound (if any)
    pub(crate) lower: Option<Bound>,
    /// Upper bound (if any)
    pub(crate) upper: Option<Bound>,
    /// Status in tableau
    pub(crate) status: Option<VarStatus>,
}

// Re-exported here so existing `use types::LinearExpr` imports continue to work.
pub use crate::linear_expr::LinearExpr;

/// Model extracted from LRA solver with variable assignments
#[derive(Debug, Clone)]
pub struct LraModel {
    /// Variable assignments: term_id -> rational value
    pub values: HashMap<TermId, BigRational>,
}

/// Optimization direction for linear objective optimization
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptimizationSense {
    /// Minimize the objective
    Minimize,
    /// Maximize the objective
    Maximize,
}

/// Result of an optimization query
#[derive(Debug, Clone)]
pub enum OptimizationResult {
    /// Optimal value found (the constraints are satisfiable and the objective has a finite optimum)
    Optimal(BigRational),
    /// The objective is unbounded in the requested direction
    Unbounded,
    /// The constraints are infeasible
    Infeasible,
    /// Optimization could not be completed (e.g., iteration limit reached)
    Unknown,
}

/// Cached information about a parsed atom
#[derive(Clone)]
pub(crate) struct ParsedAtomInfo {
    /// The normalized linear expression (expr such that "expr op 0" is the constraint)
    pub(crate) expr: LinearExpr,
    /// Is this a <= constraint (vs >=)?
    pub(crate) is_le: bool,
    /// Is this a strict comparison (< or >)?
    pub(crate) strict: bool,
    /// Is this an equality atom (= symbol)?
    pub(crate) is_eq: bool,
    /// Is this a distinct atom (distinct symbol)?
    /// When true, semantics are inverted: value=true means disequality, value=false means equality
    pub(crate) is_distinct: bool,
    /// Whether parsing this atom triggered unsupported sub-expressions (#6167).
    /// Cached alongside the parse result so register_atom() → check() cache hits
    /// preserve the unsupported status.
    pub(crate) has_unsupported: bool,
    /// Precomputed slack variable for compound atoms (coeffs.len() > 1).
    /// Set during register_atom to avoid per-assertion Vec alloc + sort in assert_literal.
    pub(crate) compound_slack: Option<u32>,
}

/// A reference to a registered theory atom for bound propagation.
///
/// Stores the information needed to check if a variable's current bounds
/// imply the truth value of this atom. Used by same-variable chain
/// propagation (Z3 Component 3).
///
/// Reference: Z3 `theory_lra.cpp:2924-2984`
#[derive(Debug, Clone)]
pub(crate) struct AtomRef {
    /// The original theory atom term
    pub(crate) term: TermId,
    /// The bound value `k` where the atom is `var <= k` or `var >= k`
    pub(crate) bound_value: BigRational,
    /// true for `var <= k` (upper bound atom), false for `var >= k` (lower bound atom)
    pub(crate) is_upper: bool,
    /// true for strict comparisons (< or >)
    pub(crate) strict: bool,
}

/// A Gomory cutting plane
#[derive(Debug, Clone)]
pub struct GomoryCut {
    /// Coefficients: (internal_var_id, coefficient)
    pub coeffs: Vec<(u32, BigRational)>,
    /// The bound value (RHS of the inequality)
    pub bound: BigRational,
    /// True for >= constraint (lower bound), false for <= (upper bound)
    pub is_lower: bool,
    /// Active bound literals that justify the cut (keeps branch-local cuts scoped).
    pub reasons: Vec<(TermId, bool)>,
    /// Basic variable whose tableau row generated this cut (LIA safety check).
    pub source_term: Option<TermId>,
}

impl GomoryCut {
    /// Returns true if all coefficients and the bound fit in machine integers.
    ///
    /// Small cuts are numerically stable and can be added permanently.
    /// Big cuts should be tested tentatively via push/pop before committing.
    /// Reference: Z3 gomory.cpp:489-491 `is_small_cut`
    pub fn is_small(&self) -> bool {
        use num_traits::ToPrimitive;
        let fits = |r: &BigRational| r.numer().to_i64().is_some() && r.denom().to_i64().is_some();
        self.coeffs.iter().all(|(_, c)| fits(c)) && fits(&self.bound)
    }
}

/// Row information for GCD test
///
/// Contains the coefficients and constant of a tableau row:
/// basic_var = Σ(coeff * var) + constant
///
/// Used by LIA to perform GCD tests on rows where the basic variable
/// has a non-integer value.
#[derive(Debug, Clone)]
pub struct GcdRowInfo {
    /// The basic variable for this row (internal var ID)
    pub basic_var: u32,
    /// The corresponding term ID (if mapped)
    pub basic_term: Option<TermId>,
    /// Sparse coefficients: (internal_var_id, coefficient)
    pub coeffs: Vec<(u32, BigRational)>,
    /// Constant term
    pub constant: BigRational,
    /// Lower bound on basic_var (if any)
    pub lower_bound: Option<BigRational>,
    /// Upper bound on basic_var (if any)
    pub upper_bound: Option<BigRational>,
    /// Whether variable is fixed (lower == upper)
    pub is_fixed: bool,
    /// Whether variable is bounded on both sides
    pub is_bounded: bool,
}

/// Compute the fractional part of a rational number
/// frac(x) = x - floor(x), always in [0, 1)
pub(crate) fn fractional_part(val: &BigRational) -> BigRational {
    let numer = val.numer();
    let denom = val.denom();

    // floor(n/d) for positive d
    let floor_val = if numer.is_negative() {
        // For negative numbers: floor(n/d) = (n - d + 1) / d for d > 0
        (numer - denom + BigInt::one()) / denom
    } else {
        numer / denom
    };

    val - BigRational::from(floor_val)
}
