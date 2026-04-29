// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use serde::{Deserialize, Serialize};

/// A single MCC property from an examination XML file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Property {
    /// Property identifier (e.g., "ModelName-UpperBounds-00").
    pub(crate) id: String,
    /// The parsed formula content.
    pub(crate) formula: Formula,
}

/// Parsed formula content from MCC property XML.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum Formula {
    /// UpperBounds: compute max sum of tokens across these places.
    PlaceBound(Vec<String>),
    /// Reachability formula: EF(φ) or AG(φ) over state predicates.
    Reachability(ReachabilityFormula),
    /// CTL formula (CTLCardinality / CTLFireability examinations).
    Ctl(CtlFormula),
    /// LTL formula (LTLCardinality / LTLFireability examinations).
    Ltl(LtlFormula),
}

/// Top-level reachability quantifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum PathQuantifier {
    /// `<exists-path><finally>` — true if any reachable state satisfies φ.
    EF,
    /// `<all-paths><globally>` — true if all reachable states satisfy φ.
    AG,
}

/// A reachability property: path quantifier + state predicate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ReachabilityFormula {
    pub(crate) quantifier: PathQuantifier,
    pub(crate) predicate: StatePredicate,
}

/// Boolean state predicate over markings and transition enablement.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum StatePredicate {
    /// Boolean conjunction.
    And(Vec<StatePredicate>),
    /// Boolean disjunction.
    Or(Vec<StatePredicate>),
    /// Boolean negation.
    Not(Box<StatePredicate>),
    /// `<integer-le>`: left ≤ right.
    IntLe(IntExpr, IntExpr),
    /// `<is-fireable>`: at least one of the named transitions is enabled.
    IsFireable(Vec<String>),
    /// Constant true.
    True,
    /// Constant false.
    False,
}

/// Integer expression in cardinality formulas.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum IntExpr {
    /// Constant integer value.
    Constant(u64),
    /// Sum of tokens across named places.
    TokensCount(Vec<String>),
}

/// CTL formula with path quantifiers at each temporal operator.
///
/// In MCC CTL XML, every temporal operator is wrapped in `<exists-path>` or
/// `<all-paths>`, forming combinations like EX, AX, EF, AF, EG, AG, EU, AU.
/// Path quantifiers nest arbitrarily deep within boolean connectives.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum CtlFormula {
    /// Atomic state predicate (leaf).
    Atom(StatePredicate),
    /// Boolean negation.
    Not(Box<CtlFormula>),
    /// Boolean conjunction.
    And(Vec<CtlFormula>),
    /// Boolean disjunction.
    Or(Vec<CtlFormula>),
    /// EX(φ) — some successor satisfies φ.
    EX(Box<CtlFormula>),
    /// AX(φ) — all successors satisfy φ.
    AX(Box<CtlFormula>),
    /// EF(φ) — some path reaches φ.
    EF(Box<CtlFormula>),
    /// AF(φ) — all paths reach φ.
    AF(Box<CtlFormula>),
    /// EG(φ) — some infinite path stays in φ.
    EG(Box<CtlFormula>),
    /// AG(φ) — all paths stay in φ.
    AG(Box<CtlFormula>),
    /// E[φ U ψ] — some path has φ until ψ.
    EU(Box<CtlFormula>, Box<CtlFormula>),
    /// A[φ U ψ] — all paths have φ until ψ.
    AU(Box<CtlFormula>, Box<CtlFormula>),
}

/// LTL formula (path formula, no explicit path quantifiers).
///
/// In MCC LTL XML, the root is `<all-paths>` wrapping a single path formula.
/// Temporal operators (X, F, G, U) appear without path quantifiers.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum LtlFormula {
    /// Atomic state predicate (leaf).
    Atom(StatePredicate),
    /// Boolean negation.
    Not(Box<LtlFormula>),
    /// Boolean conjunction.
    And(Vec<LtlFormula>),
    /// Boolean disjunction.
    Or(Vec<LtlFormula>),
    /// X(φ) — next state satisfies φ.
    Next(Box<LtlFormula>),
    /// F(φ) — eventually φ.
    Finally(Box<LtlFormula>),
    /// G(φ) — always φ.
    Globally(Box<LtlFormula>),
    /// φ U ψ — φ holds until ψ.
    Until(Box<LtlFormula>, Box<LtlFormula>),
}
