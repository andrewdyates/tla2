// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::proof::FarkasAnnotation;
use crate::term::TermId;
use num_bigint::BigInt;
use num_rational::BigRational;

/// A signed theory literal (term + Boolean value).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TheoryLit {
    /// The term representing the (Boolean) atom.
    pub term: TermId,
    /// The Boolean value of the atom.
    pub value: bool,
}

impl TheoryLit {
    /// Create a new signed theory literal.
    #[must_use]
    pub fn new(term: TermId, value: bool) -> Self {
        Self { term, value }
    }
}

/// A theory clause that should be added permanently to the SAT solver.
///
/// Unlike [`TheoryConflict`], these literals already represent the clause
/// polarity that should be asserted. For example, the ROW2 axiom
/// `i = j OR select(store(a, i, v), j) = select(a, j)` is encoded directly as
/// two positive clause literals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TheoryLemma {
    /// The literals of the clause in SAT polarity.
    pub clause: Vec<TheoryLit>,
}

impl TheoryLemma {
    /// Create a new theory lemma clause.
    #[must_use]
    pub fn new(clause: Vec<TheoryLit>) -> Self {
        Self { clause }
    }
}

/// A request from a theory solver to split on an integer variable.
///
/// Used for branch-and-bound in LIA: when the LRA relaxation gives x = 2.5,
/// the solver requests a split to force (x <= 2) OR (x >= 3).
#[derive(Debug, Clone)]
pub struct SplitRequest {
    /// The integer variable to split on
    pub variable: TermId,
    /// The non-integer value from the LRA relaxation
    pub value: BigRational,
    /// Floor of the value (lower bound in the split)
    pub floor: BigInt,
    /// Ceiling of the value (upper bound in the split)
    pub ceil: BigInt,
}

/// Request for the DPLL executor to create and assert a tighter bound atom.
///
/// Produced when implied-bound analysis derives a bound that no existing
/// unassigned Boolean atom represents. The executor creates the atom after
/// releasing the theory's immutable `TermStore` borrow, then adds the
/// implication clause `reason -> atom`.
///
/// Reference: Z3 `theory_lra::refine_bound()` in `reference/z3/src/smt/theory_lra.cpp`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundRefinementRequest {
    /// Left-hand arithmetic term to refine.
    pub variable: TermId,
    /// Optional right-hand arithmetic term for relative refinements.
    ///
    /// When present, the refined atom is `variable <= rhs_term + bound_value`
    /// or `variable >= rhs_term + bound_value` depending on `is_upper`.
    /// When absent, the refinement is against a numeric constant.
    pub rhs_term: Option<TermId>,
    /// Derived bound value before Int floor/ceil canonicalization.
    pub bound_value: BigRational,
    /// `true` for an upper-bound refinement, `false` for a lower-bound refinement.
    ///
    /// With `rhs_term == None`, this is `variable <= bound_value` or
    /// `variable >= bound_value`. With `rhs_term == Some(rhs)`, it is
    /// `variable <= rhs + bound_value` or `variable >= rhs + bound_value`.
    pub is_upper: bool,
    /// Whether the variable is Int-sorted.
    pub is_integer: bool,
    /// Antecedent literals justifying the implied bound.
    pub reason: Vec<TheoryLit>,
}

/// A request from a theory solver to split on a disequality.
///
/// Used when a disequality `x != c` is violated by the current model (x = c)
/// but the variable has slack (can take other values). The DPLL(T) layer
/// should create atoms `x < c` and `x > c` and add a clause to exclude `x = c`
/// only when the disequality is active.
///
/// When `disequality_term` is Some, the clause polarity depends on `is_distinct`:
/// - For `distinct` terms (is_distinct=true): `~term OR (x < c) OR (x > c)`
///   Forces split when distinct is asserted true (disequality holds)
/// - For `=` terms (is_distinct=false): `term OR (x < c) OR (x > c)`
///   Forces split when equality is asserted false (disequality holds)
///
/// When `disequality_term` is None (legacy behavior), the clause is:
///   `(x < c) OR (x > c)` (unconditional - may cause soundness issues!)
#[derive(Debug, Clone)]
pub struct DisequalitySplitRequest {
    /// The variable/expression that must be different from the excluded value
    pub variable: TermId,
    /// The value that is excluded by the disequality
    pub excluded_value: BigRational,
    /// The original equality/distinct term that triggered the disequality.
    /// When present, this is used to make the split conditional.
    pub disequality_term: Option<TermId>,
    /// Whether the disequality_term is a `distinct` term (true) or `=` term (false).
    /// This determines the polarity of the conditional clause literal.
    pub is_distinct: bool,
}

/// A request from a theory solver to split on a multi-variable expression.
///
/// Used when a multi-variable disequality `E != F` (or `E - F != 0`) is violated.
/// Single-value enumeration doesn't work for these - we need to split on
/// `E < F OR E > F` directly. The DPLL(T) layer should parse the disequality
/// term to extract LHS and RHS, then create atoms for the comparison.
#[derive(Debug, Clone)]
pub struct ExpressionSplitRequest {
    /// The disequality term that was violated (the `distinct` or negated `=` term).
    /// The SMT layer should extract LHS and RHS from this term.
    pub disequality_term: TermId,
}

/// A request from a combined theory solver to speculatively assume a model equality.
///
/// Used for Nelson-Oppen theory combination with non-convex theories (#4906).
/// When the arithmetic model implies `lhs = rhs` (both evaluate to the same value),
/// the DPLL(T) layer should create an `(= lhs rhs)` atom, set its SAT variable's
/// phase to `true`, and continue solving. The equality becomes a normal CDCL decision
/// that is retracted on conflict — unlike `assert_shared_equality` which is permanent.
///
/// Reference: Z3 `smt_context.cpp:4576-4632` (`assume_eq` + `try_true_first`).
#[derive(Debug, Clone)]
pub struct ModelEqualityRequest {
    /// Left-hand side of the model equality.
    pub lhs: TermId,
    /// Right-hand side of the model equality.
    pub rhs: TermId,
    /// Reason literals justifying why the model implies this equality.
    /// Used for conflict analysis if the equality leads to a contradiction.
    pub reason: Vec<TheoryLit>,
}

/// A lemma request from the string theory solver.
///
/// Describes a split that needs new terms created (skolems, concat applications)
/// and a disjunctive clause added to the SAT solver. The executor creates the
/// actual terms and clause because the theory solver only holds `&TermStore`
/// (immutable) and cannot create new terms.
///
/// Reference: CVC5 `core_solver.cpp:731-852` (`getConclusion`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StringLemma {
    /// The kind of split lemma.
    pub kind: StringLemmaKind,
    /// First component (the term being split).
    pub x: TermId,
    /// Second component or constant (depends on kind).
    pub y: TermId,
    /// Character offset into the constant `y` (for ConstSplit with partial
    /// constant consumption). When non-zero, the executor extracts the
    /// character at position `char_offset` instead of position 0.
    /// Default: 0 (first character).
    pub char_offset: usize,
    /// NF explanation (antecedent) for context-dependent lemmas.
    ///
    /// ConstSplit and VarSplit lemmas are NOT universally valid — they depend
    /// on the NF comparison context (which character position the variable
    /// falls at). Including the reason as negated guard literals in the clause
    /// makes the lemma universally valid: `¬(reason) ∨ conclusion`.
    ///
    /// EmptySplit and LengthSplit are universally valid and have empty reasons.
    ///
    /// Without guards, stale ConstSplit clauses persist after DPLL backtracking
    /// and force variables to wrong characters, causing false UNSAT (#4094).
    ///
    /// Reference: CVC5 `sendInference(ant, conc, ...)` where `ant` is the
    /// NF explanation.
    pub reason: Vec<TheoryLit>,
}

/// Kind of string split lemma.
///
/// Maps to CVC5's `processSimpleNEq` Cases 6-9.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum StringLemmaKind {
    /// Case 6: `len(x) = len(y) OR len(x) != len(y)`.
    /// Both components are non-constant variables with unknown length relationship.
    LengthSplit,
    /// Case 8 (prerequisite): `x = "" OR x != ""`.
    /// A non-constant component might be empty; determine before const-split.
    EmptySplit,
    /// Case 8: `x = firstChar(y) ++ k` where `y` is the constant.
    /// A non-constant variable vs a string constant; peel first character.
    ConstSplit,
    /// Case 9: `(x = y ++ k) OR (y = x ++ k)`.
    /// Both non-constant, lengths disequal; variable-variable split.
    VarSplit,
    /// Positive `str.contains(x, y)` reduction: `x = sk1 ++ y ++ sk2`.
    /// When `str.contains(x, y)` is asserted true but arguments are not
    /// ground-resolvable, decompose `x` into prefix + `y` + suffix.
    /// Reference: CVC5 `extf_solver.cpp:181-202`
    ContainsPositive,
    /// On-demand `str.substr(s, n, m)` reduction.
    ///
    /// The executor lowers `x = str.substr(s, n, m)` into the same skolemized
    /// word-equation + arithmetic axiom used by eager preregistration, but
    /// only when the string core requests it at runtime. `x` is the substr
    /// application term; `y` is unused.
    SubstrReduction,
    /// Length-aware constant unification (#4055): `x = prefix(y, char_offset)`.
    /// When a variable `x` has a known length `n` (via N-O bridge) and is
    /// compared against a constant `y` with `len(y) >= n`, directly assert
    /// `x = y[0..n]`. The `char_offset` field carries `n` (the prefix length).
    /// This replaces character-by-character ConstSplit for the common case
    /// of dual-concat NF comparisons (e.g., prefix+suffix decompositions).
    ConstUnify,
    /// Disequality equality split: `x = y OR x != y`.
    /// Emitted by `process_simple_deq` when two NF components have equal
    /// lengths but unknown equality status. Forces the SAT solver to decide
    /// whether the components are equal (disequality may still hold via other
    /// components) or disequal (directly satisfying the disequality).
    /// Reference: CVC5 `core_solver.cpp:2280-2300` (DEQ_STRINGS_EQ).
    EqualitySplit,
    /// Disequality empty split: `x = "" OR x != ""`.
    /// Emitted by `process_deq_disl` when one NF component is constant and
    /// the other is a non-constant that may be empty. Forces the SAT solver
    /// to decide whether the non-constant is empty before decomposition.
    /// Reference: CVC5 `core_solver.cpp:2157-2167` (DEQ_DISL_EMP_SPLIT).
    DeqEmptySplit,
    /// Disequality first-char equality split: `x = c OR x != c`.
    /// Emitted when a non-constant has length 1 and the other side is a
    /// constant `c` (its first character). Splits on character equality.
    /// Reference: CVC5 `core_solver.cpp:2192-2198` (DEQ_DISL_FIRST_CHAR_EQ_SPLIT).
    DeqFirstCharEqSplit,
}

/// A theory conflict with optional Farkas coefficients.
///
/// This struct bundles the conflicting literals with their Farkas coefficients
/// for arithmetic theories (LRA/LIA). The coefficients are essential for
/// Craig interpolation in CHC solving.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct TheoryConflict {
    /// The conflicting literals (bounds that cannot all hold)
    pub literals: Vec<TheoryLit>,
    /// Optional Farkas coefficients for interpolation
    /// Present when the conflict comes from LRA/LIA with proof production enabled
    pub farkas: Option<FarkasAnnotation>,
}

impl TheoryConflict {
    /// Create a conflict without Farkas coefficients
    #[must_use]
    pub fn new(literals: Vec<TheoryLit>) -> Self {
        Self {
            literals,
            farkas: None,
        }
    }

    /// Create a conflict with Farkas coefficients
    #[must_use]
    pub fn with_farkas(literals: Vec<TheoryLit>, farkas: FarkasAnnotation) -> Self {
        Self {
            literals,
            farkas: Some(farkas),
        }
    }
}

/// Result of a theory check
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum TheoryResult {
    /// The current assignment is satisfiable
    Sat,
    /// The current assignment is unsatisfiable, with a conflicting set of signed literals.
    ///
    /// The returned set represents assignments that cannot all hold simultaneously.
    /// The DPLL(T) layer negates these literals to produce a blocking clause.
    Unsat(Vec<TheoryLit>),
    /// Unknown (theory solver could not determine)
    Unknown,
    /// Theory needs to split on an integer variable for branch-and-bound.
    ///
    /// The DPLL layer should create atoms `var <= floor` and `var >= ceil`,
    /// add the clause `(var <= floor) OR (var >= ceil)`, and continue solving.
    NeedSplit(SplitRequest),
    /// Theory needs to split on a disequality.
    ///
    /// The DPLL layer should create atoms `var < value` and `var > value`,
    /// add the clause `(var < value) OR (var > value)`, and continue solving.
    NeedDisequalitySplit(DisequalitySplitRequest),
    /// Theory needs to split on a multi-variable expression disequality.
    ///
    /// Used when `E != F` is violated but single-value enumeration would be infinite.
    /// The DPLL layer should parse the disequality term to get LHS and RHS,
    /// then create atoms `LHS < RHS` and `LHS > RHS`, add the clause
    /// `(LHS < RHS) OR (LHS > RHS)`, and continue solving.
    NeedExpressionSplit(ExpressionSplitRequest),
    /// Unsatisfiable with optional Farkas coefficients for interpolation.
    ///
    /// This variant is used by arithmetic theories (LRA/LIA) when proof production
    /// is enabled. The Farkas coefficients provide a certificate of infeasibility
    /// that can be used for Craig interpolation in CHC solving.
    UnsatWithFarkas(TheoryConflict),
    /// String theory needs a split lemma added to the SAT solver.
    ///
    /// The executor creates new terms (skolems, concat applications) from the
    /// symbolic description and adds the resulting clause. The theory solver
    /// cannot create these directly because it only holds `&TermStore`.
    NeedStringLemma(StringLemma),
    /// Theory needs multiple permanent clauses injected without restarting SAT.
    ///
    /// The executor adds each clause to the current SAT state and continues
    /// propagation from the existing trail. This is used by array ROW2 batching
    /// to avoid one solver restart per discovered axiom (#6546).
    NeedLemmas(Vec<TheoryLemma>),
    /// Theory combination needs a speculative model equality (#4906).
    ///
    /// The DPLL layer should create an `(= lhs rhs)` atom with a SAT variable,
    /// set its phase to `true`, and continue solving. The equality becomes a
    /// retractable CDCL decision — if it leads to conflict, the solver backtracks.
    ///
    /// Reference: Z3 `assume_eq` + `try_true_first` (smt_context.cpp:4576-4632).
    NeedModelEquality(ModelEqualityRequest),
    /// Batch variant of [`NeedModelEquality`]: request multiple speculative
    /// model equalities in one pipeline restart instead of one-per-restart.
    ///
    /// This avoids O(N) pipeline restarts when the N-O fixpoint discovers N
    /// unresolved index pairs simultaneously (#6303).
    NeedModelEqualities(Vec<ModelEqualityRequest>),
}

/// A propagated literal from a theory solver
#[derive(Debug, Clone)]
pub struct TheoryPropagation {
    /// The propagated literal
    pub literal: TheoryLit,
    /// The reason (antecedents) for the propagation
    pub reason: Vec<TheoryLit>,
}

/// An equality discovered by a theory solver during Nelson-Oppen combination.
///
/// When a theory determines that two terms must be equal (e.g., LIA determines
/// that `x = 5` and `y = 5`, so `x = y`), it reports this equality for propagation
/// to other theories.
#[derive(Debug, Clone)]
pub struct DiscoveredEquality {
    /// Left-hand side of the equality
    pub lhs: TermId,
    /// Right-hand side of the equality
    pub rhs: TermId,
    /// The reason (antecedent literals) that justify this equality
    pub reason: Vec<TheoryLit>,
}

impl DiscoveredEquality {
    /// Create a new discovered equality with a reason.
    #[must_use]
    pub fn new(lhs: TermId, rhs: TermId, reason: Vec<TheoryLit>) -> Self {
        Self { lhs, rhs, reason }
    }
}

/// Result of equality propagation for Nelson-Oppen theory combination.
///
/// Currently equality-only: disequality propagation is not implemented.
/// When a concrete producer/consumer pair exists, reintroduce a disequality
/// channel (see Z3's `propagate_th_diseqs` for reference architecture).
#[derive(Debug, Clone, Default)]
pub struct EqualityPropagationResult {
    /// Equalities discovered by this theory (e.g., x = y from LIA bounds)
    pub equalities: Vec<DiscoveredEquality>,
    /// A conflict discovered during equality propagation
    pub conflict: Option<Vec<TheoryLit>>,
}
