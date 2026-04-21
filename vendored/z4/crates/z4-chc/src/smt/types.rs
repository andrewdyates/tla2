// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Type definitions for the SMT backend.

use crate::ChcExpr;
use num_rational::BigRational;
use rustc_hash::FxHashMap;
use z4_core::{FarkasAnnotation, TermId};

/// Result of model verification against a CHC expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ModelVerifyResult {
    /// Expression evaluates to `true` under the model.
    Valid,
    /// Expression evaluates to `false` under the model — a definite bug.
    Invalid,
    /// Expression cannot be fully evaluated (predicates, arrays, missing vars).
    /// The model may or may not satisfy the expression.
    Indeterminate,
}

/// Partition origin for a constraint in Craig interpolation.
///
/// When computing interpolants from `A ∧ B` being UNSAT, we need to know
/// which partition each conflict literal originated from. This is critical
/// for correct B-pure classification: a constraint is B-pure only if it
/// came from the B partition AND mentions only shared variables.
///
/// Reference: Z3 Spacer's `spacer_unsat_core_plugin.cpp:94-214`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Partition {
    /// Constraint came from the A partition (transition constraints).
    A,
    /// Constraint came from the B partition (bad state constraints).
    B,
    /// Constraint came from both partitions.
    #[default]
    AB,
    /// Constraint was introduced by branch-and-bound case splitting (`NeedSplit`).
    ///
    /// These atoms (e.g., `x <= floor`, `x >= ceil`) are not derived from
    /// specific A/B constraints and should be excluded from interpolation
    /// to avoid polluting the proof structure (matching Z3's treatment of
    /// DPLL hypotheses as A-side).
    ///
    /// Note: Disequality and expression splits (`NeedDisequalitySplit`,
    /// `NeedExpressionSplit`) inherit `A/B/AB` from their triggering guard
    /// atom and are NOT classified as `Split`.
    ///
    /// See designs/2026-01-28-split-atom-coloring.md for rationale.
    Split,
}

/// UNSAT core - the subset of constraints that caused unsatisfiability
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub struct UnsatCoreDiagnostics {
    /// Number of DPLL(T) refinement iterations executed.
    pub dt_iterations: u64,
    /// Count of plain theory UNSAT conflicts (without Farkas certificate).
    pub theory_unsat_count: u64,
    /// Count of theory UNSAT conflicts with concrete Farkas coefficients.
    pub theory_farkas_count: u64,
    /// Count of theory UNSAT conflicts where Farkas data was missing (`None`).
    pub theory_farkas_none_count: u64,
    /// Number of theory-requested split clauses added during solving.
    pub split_count: u64,
    /// Activation assumptions from the SAT UNSAT core that map to Farkas conflicts.
    pub activation_core_conflicts: u64,
    /// Total Farkas conflicts collected before activation-core filtering.
    pub total_farkas_conflicts: u64,
}

#[derive(Debug, Clone, Default)]
pub struct UnsatCore {
    /// Conjuncts from the original query that are sufficient for UNSAT.
    ///
    /// This is currently populated only for conjunction-shaped queries where
    /// we solve under assumptions and extract an UNSAT core over those assumptions.
    pub conjuncts: Vec<ChcExpr>,

    /// Arithmetic Farkas conflicts observed while solving under assumptions.
    ///
    /// These are collected opportunistically when the arithmetic theory returns
    /// `TheoryResult::UnsatWithFarkas`. They can be used by PDR to attempt
    /// proof-based interpolation even when the background contains Boolean structure.
    pub farkas_conflicts: Vec<FarkasConflict>,

    /// Solver-level diagnostics for UNSAT-core extraction.
    ///
    /// Populated by `check_sat_with_assumption_conjuncts` when DPLL(T)-under-assumptions
    /// is used. Defaults to zeros in simpler UNSAT-core paths.
    pub diagnostics: UnsatCoreDiagnostics,
}

/// A Farkas certificate from an arithmetic theory conflict.
///
/// When LRA/LIA proves UNSAT through linear arithmetic, the Farkas lemma provides
/// non-negative coefficients such that the linear combination of constraints
/// yields a contradiction (e.g., 0 >= 1). This certificate can be used for
/// Craig interpolation in CHC solving.
#[derive(Debug, Clone)]
pub struct FarkasConflict {
    /// The conflicting constraint terms (TermIds in the SmtContext's term store).
    ///
    /// These are the theory literals that participated in the conflict. Each term
    /// is a comparison atom (e.g., `x <= 5`, `y >= 3`).
    pub conflict_terms: Vec<TermId>,

    /// Whether each conflict term was asserted positively (true) or negatively (false).
    pub polarities: Vec<bool>,

    /// Farkas coefficients for interpolation.
    ///
    /// Each coefficient corresponds to the conflict term at the same index.
    /// The coefficients are non-negative and their linear combination proves UNSAT.
    pub farkas: FarkasAnnotation,

    /// Partition origin for each conflict term (#982).
    ///
    /// Used for Craig interpolation to determine which constraints came from
    /// the A partition vs the B partition. When empty, interpolation falls back
    /// to variable-based classification.
    pub origins: Vec<Partition>,
}

/// Result of an SMT satisfiability check
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use = "SMT results must be checked — ignoring Sat/Unsat loses correctness"]
pub enum SmtResult {
    /// Formula is satisfiable, with a model mapping variable names to values
    Sat(FxHashMap<String, SmtValue>),
    /// Formula is unsatisfiable, optionally with an UNSAT core
    Unsat,
    /// Formula is unsatisfiable with an UNSAT core for interpolation
    UnsatWithCore(UnsatCore),
    /// Formula is unsatisfiable with a Farkas certificate from arithmetic theory.
    ///
    /// This variant is returned when LIA/LRA directly proves UNSAT through linear
    /// arithmetic conflict. The certificate can be used for Craig interpolation.
    UnsatWithFarkas(FarkasConflict),
    /// Solver couldn't determine satisfiability
    Unknown,
}

impl SmtResult {
    /// Returns `true` if this result is any UNSAT variant (plain, with core, or with Farkas certificate).
    #[inline]
    pub fn is_unsat(&self) -> bool {
        matches!(
            self,
            Self::Unsat | Self::UnsatWithCore(_) | Self::UnsatWithFarkas(_)
        )
    }

    /// Returns `true` if this result is SAT (carries a model).
    #[inline]
    pub fn is_sat(&self) -> bool {
        matches!(self, Self::Sat(_))
    }

    /// Returns `true` if the solver returned Unknown.
    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }

    /// Returns a reference to the SAT model, if this result is SAT.
    #[inline]
    pub fn model(&self) -> Option<&FxHashMap<String, SmtValue>> {
        match self {
            Self::Sat(m) => Some(m),
            _ => None,
        }
    }

    /// Consumes this result and returns the SAT model, if SAT.
    #[inline]
    pub fn into_model(self) -> Option<FxHashMap<String, SmtValue>> {
        match self {
            Self::Sat(m) => Some(m),
            _ => None,
        }
    }

    /// Extracts Farkas conflicts from an UNSAT result, consuming self.
    ///
    /// Returns the clause-local Farkas certificates carried by `UnsatWithFarkas`
    /// or `UnsatWithCore` variants. Returns an empty vec for plain `Unsat`, `Sat`,
    /// and `Unknown`. Used by PDR blocking to preserve clause-local proof data
    /// for interpolation (#6484).
    #[inline]
    pub fn into_farkas_conflicts(self) -> Vec<FarkasConflict> {
        match self {
            Self::UnsatWithFarkas(conflict) => vec![conflict],
            Self::UnsatWithCore(core) => core.farkas_conflicts,
            _ => vec![],
        }
    }
}

/// A value in an SMT model
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SmtValue {
    /// Boolean value
    Bool(bool),
    /// Integer value
    Int(i64),
    /// Real (rational) value
    Real(BigRational),
    /// Bitvector value (value, width)
    BitVec(u128, u32),
    /// Opaque symbolic model value that could not be concretized.
    ///
    /// This preserves solver-generated placeholders such as `@arr33` and
    /// sort-qualified anti-unification names instead of fabricating concrete
    /// zeros that can cause false-SAT during witness verification.
    Opaque(String),
    /// Constant array: all indices map to the same default value.
    /// Represents `((as const (Array K V)) default)`.
    ConstArray(Box<Self>),
    /// Array with explicit point overrides on a default.
    /// `default` is the value for all indices not in `entries`.
    /// Each entry is `(index_value, element_value)`.
    ArrayMap {
        default: Box<Self>,
        entries: Vec<(Self, Self)>,
    },
    /// Datatype constructor application: (ctor_name, field_values).
    /// Nullary: `Datatype("Green", vec![])`.
    /// Non-nullary: `Datatype("mkpair", vec![Int(42), Bool(true)])`.
    Datatype(String, Vec<Self>),
}

#[derive(Debug, Clone, Copy)]
pub(super) enum DiseqGuardKind {
    Distinct,
    Eq,
}
