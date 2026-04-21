// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cached asserted-literal classification for LIA (#4742).

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use num_bigint::BigInt;
use num_traits::One;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{Symbol, TermData, TermId, TermStore};
use z4_core::TheoryLit;

/// Integer bounds and source literals for a single term.
#[derive(Clone, Debug, Default)]
pub(crate) struct TermBounds {
    /// Tightest asserted lower bound (integer-adjusted for strict atoms).
    pub(crate) lower: Option<BigInt>,
    /// Tightest asserted upper bound (integer-adjusted for strict atoms).
    pub(crate) upper: Option<BigInt>,
    /// Positive asserted inequality literals that produced bounds.
    pub(crate) reason_lits: Vec<TheoryLit>,
}

/// Pre-classified asserted literals shared by LIA submodules.
#[derive(Clone, Debug, Default)]
pub(crate) struct AssertionView {
    /// Positive equality literals (`(= lhs rhs)` asserted true).
    pub(crate) positive_equalities: Vec<TermId>,
    /// Negative equality literals (`(= lhs rhs)` asserted false / disequalities).
    pub(crate) negative_equalities: Vec<TermId>,
    /// Inequality literals (`>=`, `<=`, `>`, `<`) with asserted polarity.
    pub(crate) inequalities: Vec<(TermId, bool)>,
    /// Stable, deduplicated key for positive equalities.
    pub(crate) equality_key: Vec<TermId>,
    /// Integer bounds derived from positive asserted inequalities.
    pub(crate) bounds_by_term: HashMap<TermId, TermBounds>,
}

impl AssertionView {
    /// Build a new view from asserted literals.
    pub(crate) fn build(terms: &TermStore, asserted: &[(TermId, bool)]) -> Self {
        let mut view = Self::default();
        let mut seen_reasons: HashMap<TermId, HashSet<TheoryLit>> = HashMap::new();

        for &(literal, value) in asserted {
            let TermData::App(Symbol::Named(name), args) = terms.get(literal) else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }

            match name.as_str() {
                "=" => {
                    if value {
                        view.positive_equalities.push(literal);
                    } else {
                        view.negative_equalities.push(literal);
                    }
                }
                ">=" | "<=" | ">" | "<" => {
                    view.inequalities.push((literal, value));
                    if value {
                        Self::record_integer_bound(
                            &mut view.bounds_by_term,
                            &mut seen_reasons,
                            terms,
                            literal,
                            name.as_str(),
                            args[0],
                            args[1],
                        );
                    }
                }
                _ => {}
            }
        }

        view.equality_key = view.positive_equalities.clone();
        view.equality_key.sort_by_key(|term| term.0);
        view.equality_key.dedup();
        view
    }

    fn record_integer_bound(
        bounds_by_term: &mut HashMap<TermId, TermBounds>,
        seen_reasons: &mut HashMap<TermId, HashSet<TheoryLit>>,
        terms: &TermStore,
        literal: TermId,
        op: &str,
        lhs: TermId,
        rhs: TermId,
    ) {
        let (target, constant, target_on_left) =
            if let Some(c) = terms.extract_integer_constant(rhs) {
                (lhs, c, true)
            } else if let Some(c) = terms.extract_integer_constant(lhs) {
                (rhs, c, false)
            } else {
                return;
            };

        let mut lower: Option<BigInt> = None;
        let mut upper: Option<BigInt> = None;
        match (op, target_on_left) {
            (">=", true) | ("<=", false) => lower = Some(constant),
            (">", true) | ("<", false) => lower = Some(&constant + BigInt::one()),
            ("<=", true) | (">=", false) => upper = Some(constant),
            ("<", true) | (">", false) => upper = Some(&constant - BigInt::one()),
            _ => {}
        }

        let bounds = bounds_by_term.entry(target).or_default();
        if let Some(candidate) = lower {
            bounds.lower = Some(
                bounds
                    .lower
                    .as_ref()
                    .map_or(candidate.clone(), |current| current.max(&candidate).clone()),
            );
        }
        if let Some(candidate) = upper {
            bounds.upper = Some(
                bounds
                    .upper
                    .as_ref()
                    .map_or(candidate.clone(), |current| current.min(&candidate).clone()),
            );
        }

        let reason = TheoryLit::new(literal, true);
        if seen_reasons.entry(target).or_default().insert(reason) {
            bounds.reason_lits.push(reason);
        }
    }
}

#[cfg(test)]
#[path = "assertion_view_tests.rs"]
mod tests;
