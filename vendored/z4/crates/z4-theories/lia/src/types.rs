// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIA type definitions and utility functions.
//!
//! Extracted from `lib.rs` for code health (#5970).

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::sync::OnceLock;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{TermId, TermStore};
use z4_core::{DiscoveredEquality, TheoryLit};
use z4_lra::LraSolver;

use crate::assertion_view;

/// #6359: Cached debug flags for LIA solver.
///
/// Environment variables are read once per process via OnceLock, not per
/// solver construction. In DPLL(T) loops where LiaSolver is created fresh
/// on each iteration, this eliminates ~13 syscalls per iteration.
pub(crate) struct LiaDebugFlags {
    pub(crate) debug_lia: bool,
    pub(crate) debug_lia_branch: bool,
    pub(crate) debug_lia_check: bool,
    pub(crate) debug_lia_nelson_oppen: bool,
    pub(crate) debug_patch: bool,
    pub(crate) debug_gcd: bool,
    pub(crate) debug_gcd_tab: bool,
    pub(crate) debug_dioph: bool,
    pub(crate) debug_hnf: bool,
    pub(crate) debug_mod: bool,
    pub(crate) debug_enum: bool,
}

static LIA_DEBUG_FLAGS: OnceLock<LiaDebugFlags> = OnceLock::new();

pub(crate) fn lia_debug_flags() -> &'static LiaDebugFlags {
    LIA_DEBUG_FLAGS.get_or_init(|| LiaDebugFlags {
        debug_lia: std::env::var("Z4_DEBUG_LIA").is_ok()
            || std::env::var("Z4_DEBUG_THEORY").is_ok(),
        debug_lia_branch: std::env::var("Z4_DEBUG_LIA_BRANCH").is_ok(),
        debug_lia_check: std::env::var("Z4_DEBUG_LIA_CHECK").is_ok()
            || std::env::var("Z4_DEBUG_THEORY").is_ok(),
        debug_lia_nelson_oppen: std::env::var("Z4_DEBUG_LIA_NELSON_OPPEN").is_ok()
            || std::env::var("Z4_DEBUG_THEORY").is_ok(),
        debug_patch: std::env::var("Z4_DEBUG_PATCH").is_ok(),
        debug_gcd: std::env::var("Z4_DEBUG_GCD").is_ok(),
        debug_gcd_tab: std::env::var("Z4_DEBUG_GCD_TAB").is_ok(),
        debug_dioph: std::env::var("Z4_DEBUG_DIOPH").is_ok(),
        debug_hnf: std::env::var("Z4_DEBUG_HNF").is_ok(),
        debug_mod: std::env::var("Z4_DEBUG_MOD").is_ok(),
        debug_enum: std::env::var_os("Z4_DEBUG_ENUM").is_some(),
    })
}

/// Borrowed view into a substitution map: TermId → (coefficient pairs, constant).
pub(crate) type SubstitutionMap<'a> = HashMap<TermId, (&'a [(TermId, BigInt)], &'a BigInt)>;

/// A variable-elimination substitution triple: `(var, coefficients, constant)`.
///
/// Represents the expression `var = constant + Σ(coeff * dep_var)`.
/// Used by the Diophantine solver and RREF enumeration engine.
///
/// Generic over `K` (variable key: `TermId` or `usize`) and `V` (numeric
/// type: `BigInt` or `BigRational`).
pub(crate) type SubstitutionTriple<K, V> = (K, Vec<(K, V)>, V);

/// Timing breakdown for LIA solving phases (#4794).
#[derive(Clone, Debug, Default)]
pub struct LiaTimings {
    /// Time spent in LRA simplex.
    pub simplex: std::time::Duration,
    /// Time spent in Gomory cuts.
    pub gomory: std::time::Duration,
    /// Time spent in HNF cuts.
    pub hnf: std::time::Duration,
    /// Time spent in Diophantine solving.
    pub dioph: std::time::Duration,
}

/// Non-negative remainder: `a mod m` with result in `[0, m)`.
///
/// Rust's `%` operator preserves the sign of the dividend, so `-3 % 5 == -3`.
/// This function returns the canonical non-negative representative instead:
/// `positive_mod(-3, 5) == 2`.
pub(crate) fn positive_mod(a: &BigInt, m: &BigInt) -> BigInt {
    debug_assert!(
        m > &BigInt::zero(),
        "BUG: positive_mod called with non-positive modulus {m} (a={a})",
    );
    let r = a % m;
    let result = if r < BigInt::zero() { r + m } else { r };
    debug_assert!(
        result >= BigInt::zero() && result < *m,
        "BUG: positive_mod({a}, {m}) produced out-of-range result {result}",
    );
    result
}

/// Compute the GCD of absolute values yielded by an iterator.
///
/// Returns `BigInt::zero()` for an empty iterator (the identity for GCD).
/// Short-circuits when GCD drops to 1 (it can never decrease further).
pub(crate) fn gcd_of_abs(values: impl Iterator<Item = BigInt>) -> BigInt {
    let mut result = BigInt::zero();
    for v in values {
        let abs_v = v.abs();
        if result.is_zero() {
            result = abs_v;
        } else {
            result = result.gcd(&abs_v);
        }
        if result.is_one() {
            break;
        }
    }
    debug_assert!(
        !result.is_negative(),
        "BUG: gcd_of_abs produced negative result {result}"
    );
    result
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum IneqOp {
    Ge,
    Le,
    Gt,
    Lt,
}

/// Model extracted from LIA solver with variable assignments
#[derive(Debug, Clone)]
pub struct LiaModel {
    /// Variable assignments: term_id -> integer value
    pub values: HashMap<TermId, BigInt>,
}

/// Result from direct lattice enumeration.
///
/// Used to distinguish between UNSAT (with conflict), SAT (with witness model stored
/// in `direct_enum_witness`), and "no conclusion" (requires fallback to branch-and-bound).
#[derive(Debug)]
pub(crate) enum DirectEnumResult {
    /// Enumeration proved UNSAT within bounded search
    Unsat(Vec<TheoryLit>),
    /// Found a satisfying integer assignment (stored in `direct_enum_witness`)
    SatWitness,
    /// Could not reach conclusion (too many solutions, unbounded, etc.)
    NoConclusion,
}

/// A stored HNF cut using TermIds (stable across LRA resets)
#[derive(Clone)]
pub struct StoredCut {
    /// Coefficients: term_id -> coefficient
    pub(crate) coeffs: Vec<(TermId, BigRational)>,
    /// The bound value
    pub(crate) bound: BigRational,
    /// True if lower bound (>= bound), false if upper bound (<= bound)
    pub(crate) is_lower: bool,
    /// Reason atoms (equality TermIds) that derived this cut (#5388).
    /// Used for proper conflict explanation during replay.
    pub(crate) reasons: Vec<(TermId, bool)>,
}

/// Linear expression coefficients for Nelson-Oppen propagation.
/// Represents: Σ(coeff * var) + constant
pub(crate) struct LinearCoeffs {
    pub(crate) vars: HashMap<TermId, BigRational>,
    pub(crate) constant: BigRational,
}

/// Saved cut-related state for push/pop scoping (#3685).
///
/// On `push()`, the current gomory/HNF iteration counters and seen-cut set
/// are snapshotted. On `pop()`, they are restored so that the outer scope
/// resumes with the exact cut state it had before the inner scope.
#[derive(Clone, Default)]
pub(crate) struct CutScopeState {
    pub(crate) gomory_iterations: usize,
    pub(crate) hnf_iterations: usize,
    pub(crate) seen_hnf_cuts: HashSet<HnfCutKey>,
    /// Saved length of `shared_equalities` at push time (#3581).
    pub(crate) shared_eq_mark: usize,
}

/// LIA theory solver using Gomory cuts, HNF cuts, and branch-and-bound over LRA
pub struct LiaSolver<'a> {
    /// Reference to the term store for parsing expressions
    pub(crate) terms: &'a TermStore,
    /// Underlying LRA solver for the relaxation
    pub(crate) lra: LraSolver,
    /// Set of term IDs known to be integer variables
    pub(crate) integer_vars: HashSet<TermId>,
    /// Map from integer values to constant term IDs (#3581).
    /// Used by Nelson-Oppen propagation to create equalities between
    /// variables with derived tight bounds and constant terms. For example,
    /// when Gaussian elimination derives f(1) = 0, this map provides the
    /// TermId for constant 0 so that the equality f(1) = 0 can be propagated.
    pub(crate) int_constant_terms: HashMap<BigInt, TermId>,
    /// Asserted atoms for conflict generation
    pub(crate) asserted: Vec<(TermId, bool)>,
    /// Scope markers for push/pop
    pub(crate) scopes: Vec<usize>,
    /// Scope markers for learned cut truncation on pop.
    pub(crate) cut_scopes: Vec<usize>,
    /// Saved cut state per scope level for proper restore on pop (#3685).
    pub(crate) cut_state_scopes: Vec<CutScopeState>,
    /// Number of Gomory cut iterations attempted
    pub(crate) gomory_iterations: usize,
    /// Maximum Gomory cut iterations before falling back to split
    pub(crate) max_gomory_iterations: usize,
    /// Number of HNF cut iterations attempted
    pub(crate) hnf_iterations: usize,
    /// Maximum HNF cut iterations
    pub(crate) max_hnf_iterations: usize,
    /// Deduplicate HNF cuts across the solve (cuts are globally valid).
    pub(crate) seen_hnf_cuts: HashSet<HnfCutKey>,
    /// Stored cuts using TermIds for replay after LRA reset.
    /// These are derived from equality constraints and should be valid
    /// across different SAT models with the same base constraints.
    pub(crate) learned_cuts: Vec<StoredCut>,
    /// Cached set of asserted equality atoms (used to avoid re-running Diophantine
    /// solving when only inequalities change due to branching).
    /// Diophantine solving is skipped if this matches the current equality atoms.
    pub(crate) dioph_equality_key: Vec<TermId>,
    /// Integer variables that are provably dependent on other integer variables
    /// via unit-coefficient equalities (safe substitutions).
    ///
    /// These are typically poor branching candidates because their integrality
    /// is implied by other variables.
    pub(crate) dioph_safe_dependent_vars: HashSet<TermId>,
    /// Cached substitutions from Diophantine solver for bound propagation.
    /// Format: (substituted_term, [(dep_term, coeff)...], constant)
    /// Meaning: substituted_term = constant + Σ(coeff * dep_term)
    pub(crate) dioph_cached_substitutions: Vec<SubstitutionTriple<TermId, BigInt>>,
    /// Modular constraints from Dioph substitutions including free parameters.
    /// Format: (term_id, gcd, residue) meaning `term ≡ residue (mod gcd)`.
    /// Populated by expanding substitutions WITH free fresh parameters,
    /// preserving GCD information that the filtered substitutions lose.
    pub(crate) dioph_cached_modular_gcds: Vec<(TermId, BigInt, BigInt)>,
    /// Equality literals that justify cached substitutions.
    /// These are reused as reasons for propagated bounds.
    pub(crate) dioph_cached_reasons: Vec<(TermId, bool)>,
    /// Discovered equalities for Nelson-Oppen propagation.
    /// These are collected during check() when we detect tight bounds.
    pub(crate) pending_equalities: Vec<DiscoveredEquality>,
    /// Track which equality pairs have been propagated to avoid duplicates.
    /// Stores (min(lhs, rhs), max(lhs, rhs)) for canonical ordering.
    pub(crate) propagated_equality_pairs: HashSet<(TermId, TermId)>,
    /// Shared equalities received via `assert_shared_equality` (#3581).
    /// These are (lhs, rhs, reason_lits) tuples from EUF that need to be
    /// processed by `detect_algebraic_equalities` alongside assertion-view
    /// equalities. Without this, variables introduced only via shared
    /// equalities (e.g., UF terms f(0), f(1)) have no tight bounds and
    /// are invisible to the algebraic equality detection phase.
    pub(crate) shared_equalities: Vec<(TermId, TermId, Vec<TheoryLit>)>,
    /// When true, `detect_algebraic_equalities` skips shared equalities (#6282).
    /// Set in AUFLIA mode where array store axioms create dense shared equality
    /// systems that overwhelm Gaussian elimination with O(n²) derived equalities.
    pub(crate) skip_shared_algebraic: bool,
    /// Optional timeout callback for cooperative interruption.
    /// When the callback returns true, the solver will return Unknown at the next check point.
    pub(crate) timeout_callback: Option<Box<dyn Fn() -> bool>>,
    /// When direct enumeration finds a satisfying integer assignment, store it here so
    /// `check()` can return SAT without branch-and-bound and `extract_model()` can succeed.
    pub(crate) direct_enum_witness: Option<LiaModel>,
    // Cached env vars (#2673)
    pub(crate) debug_lia: bool,
    pub(crate) debug_lia_branch: bool,
    pub(crate) debug_lia_check: bool,
    pub(crate) debug_lia_nelson_oppen: bool,
    pub(crate) debug_patch: bool,
    pub(crate) debug_gcd: bool,
    pub(crate) debug_gcd_tab: bool,
    pub(crate) debug_dioph: bool,
    pub(crate) debug_hnf: bool,
    pub(crate) debug_mod: bool,
    pub(crate) debug_enum: bool,
    /// Cached assertion classification (see assertion_view.rs, #4742).
    pub(crate) assertion_view_cache: Option<assertion_view::AssertionView>,
    // Per-theory runtime statistics (#4706)
    pub(crate) check_count: u64,
    pub(crate) conflict_count: u64,
    pub(crate) propagation_count: u64,
}

/// Key for deduplicating HNF cuts (uses TermIds for stability across theory instances)
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HnfCutKey {
    /// Coefficients
    pub(crate) coeffs: Vec<(TermId, BigInt)>,
    /// Bound
    pub(crate) bound: BigInt,
}

/// Diophantine solver state for external storage.
///
/// Stores the results of Diophantine analysis so they can be preserved across
/// solver recreations during branch-and-bound. Since equalities don't change
/// during branching, the analysis can be reused.
#[derive(Default)]
pub struct DiophState {
    /// List of asserted equality atoms (used to detect when re-analysis is needed)
    pub equality_key: Vec<TermId>,
    /// Variables that are poor branching candidates (dependent on others via
    /// unit-coefficient equalities)
    pub safe_dependent_vars: HashSet<TermId>,
    /// Variable elimination expressions for bound propagation.
    /// Format: (substituted_term, [(dep_term, coeff)...], constant)
    pub cached_substitutions: Vec<SubstitutionTriple<TermId, BigInt>>,
    /// Modular constraints from fully-expanded substitutions (including free params).
    /// Format: (term_id, gcd, residue) meaning `term ≡ residue (mod gcd)`.
    pub cached_modular_gcds: Vec<(TermId, BigInt, BigInt)>,
    /// Equality literals justifying the substitutions (for conflict analysis)
    pub cached_reasons: Vec<(TermId, bool)>,
}
