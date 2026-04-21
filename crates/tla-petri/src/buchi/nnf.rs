// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! LTL Negative Normal Form (NNF) representation and conversion.

use crate::property_xml::{LtlFormula, StatePredicate};

/// LTL formula in Negative Normal Form (negations pushed to atoms).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum LtlNnf {
    /// Positive atom (state predicate holds).
    Atom(usize),
    /// Negated atom (state predicate does NOT hold).
    NegAtom(usize),
    And(Vec<LtlNnf>),
    Or(Vec<LtlNnf>),
    Next(Box<LtlNnf>),
    Until(Box<LtlNnf>, Box<LtlNnf>),
    Release(Box<LtlNnf>, Box<LtlNnf>),
    /// Constant true.
    True,
    /// Constant false.
    False,
}

/// Negate an LTL formula and produce NNF.
pub(super) fn negate(formula: &LtlNnf) -> LtlNnf {
    match formula {
        LtlNnf::Atom(id) => LtlNnf::NegAtom(*id),
        LtlNnf::NegAtom(id) => LtlNnf::Atom(*id),
        LtlNnf::True => LtlNnf::False,
        LtlNnf::False => LtlNnf::True,
        LtlNnf::And(children) => LtlNnf::Or(children.iter().map(negate).collect()),
        LtlNnf::Or(children) => LtlNnf::And(children.iter().map(negate).collect()),
        LtlNnf::Next(inner) => LtlNnf::Next(Box::new(negate(inner))),
        LtlNnf::Until(a, b) => {
            // ¬(a U b) = (¬a) R (¬b)
            LtlNnf::Release(Box::new(negate(a)), Box::new(negate(b)))
        }
        LtlNnf::Release(a, b) => {
            // ¬(a R b) = (¬a) U (¬b)
            LtlNnf::Until(Box::new(negate(a)), Box::new(negate(b)))
        }
    }
}

/// Convert an LtlFormula to NNF, extracting atomic predicates.
///
/// Returns the NNF formula and the list of extracted atoms.
pub(crate) fn to_nnf(formula: &LtlFormula, atoms: &mut Vec<StatePredicate>) -> LtlNnf {
    match formula {
        LtlFormula::Atom(pred) => match pred {
            StatePredicate::True => LtlNnf::True,
            StatePredicate::False => LtlNnf::False,
            _ => {
                let id = atoms.len();
                atoms.push(pred.clone());
                LtlNnf::Atom(id)
            }
        },
        LtlFormula::Not(inner) => {
            let inner_nnf = to_nnf(inner, atoms);
            negate(&inner_nnf)
        }
        LtlFormula::And(children) => {
            LtlNnf::And(children.iter().map(|c| to_nnf(c, atoms)).collect())
        }
        LtlFormula::Or(children) => LtlNnf::Or(children.iter().map(|c| to_nnf(c, atoms)).collect()),
        LtlFormula::Next(inner) => LtlNnf::Next(Box::new(to_nnf(inner, atoms))),
        LtlFormula::Finally(inner) => {
            // F(φ) = True U φ
            let inner_nnf = to_nnf(inner, atoms);
            LtlNnf::Until(Box::new(LtlNnf::True), Box::new(inner_nnf))
        }
        LtlFormula::Globally(inner) => {
            // G(φ) = False R φ
            let inner_nnf = to_nnf(inner, atoms);
            LtlNnf::Release(Box::new(LtlNnf::False), Box::new(inner_nnf))
        }
        LtlFormula::Until(a, b) => {
            let a_nnf = to_nnf(a, atoms);
            let b_nnf = to_nnf(b, atoms);
            LtlNnf::Until(Box::new(a_nnf), Box::new(b_nnf))
        }
    }
}

#[cfg(test)]
#[path = "nnf_tests.rs"]
mod nnf_tests;
