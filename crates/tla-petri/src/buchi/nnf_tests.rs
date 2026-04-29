// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{negate, to_nnf, LtlNnf};
use crate::property_xml::{IntExpr, LtlFormula, StatePredicate};

fn tokens_at_least(place: &str, value: u64) -> StatePredicate {
    StatePredicate::IntLe(
        IntExpr::Constant(value),
        IntExpr::TokensCount(vec![place.to_string()]),
    )
}

fn atom_formula(place: &str, value: u64) -> LtlFormula {
    LtlFormula::Atom(tokens_at_least(place, value))
}

fn assert_atom_is_tokens_at_least(atom: &StatePredicate, place: &str, value: u64) {
    let StatePredicate::IntLe(IntExpr::Constant(bound), IntExpr::TokensCount(places)) = atom else {
        panic!("expected integer bound atom");
    };
    assert_eq!(*bound, value);
    assert_eq!(places, &[place.to_string()]);
}

#[test]
fn test_nnf_atom_true_collapses() {
    let formula = LtlFormula::Atom(StatePredicate::True);
    let mut atoms = Vec::new();

    let nnf = to_nnf(&formula, &mut atoms);

    assert_eq!(nnf, LtlNnf::True);
    assert!(
        atoms.is_empty(),
        "True constant should not enter atom table"
    );
}

#[test]
fn test_nnf_atom_false_collapses() {
    let formula = LtlFormula::Atom(StatePredicate::False);
    let mut atoms = Vec::new();

    let nnf = to_nnf(&formula, &mut atoms);

    assert_eq!(nnf, LtlNnf::False);
    assert!(
        atoms.is_empty(),
        "False constant should not enter atom table"
    );
}

#[test]
fn test_nnf_not_atom_true_becomes_false() {
    let formula = LtlFormula::Not(Box::new(LtlFormula::Atom(StatePredicate::True)));
    let mut atoms = Vec::new();

    let nnf = to_nnf(&formula, &mut atoms);

    assert_eq!(nnf, LtlNnf::False);
    assert!(atoms.is_empty());
}

#[test]
fn test_nnf_globally_atom_false_collapses() {
    // G(False) = False R False. Both False constants should be NNF False.
    let formula = LtlFormula::Globally(Box::new(LtlFormula::Atom(StatePredicate::False)));
    let mut atoms = Vec::new();

    let nnf = to_nnf(&formula, &mut atoms);

    assert_eq!(
        nnf,
        LtlNnf::Release(Box::new(LtlNnf::False), Box::new(LtlNnf::False))
    );
    assert!(atoms.is_empty());
}

fn assert_negations_pushed(formula: &LtlNnf) {
    match formula {
        LtlNnf::Atom(_) | LtlNnf::NegAtom(_) | LtlNnf::True | LtlNnf::False => {}
        LtlNnf::And(children) | LtlNnf::Or(children) => {
            for child in children {
                assert_negations_pushed(child);
            }
        }
        LtlNnf::Next(inner) => assert_negations_pushed(inner),
        LtlNnf::Until(left, right) | LtlNnf::Release(left, right) => {
            assert_negations_pushed(left);
            assert_negations_pushed(right);
        }
    }
}

#[test]
fn test_nnf_double_negation() {
    let formula = LtlFormula::Not(Box::new(LtlFormula::Not(Box::new(atom_formula("p0", 1)))));
    let mut atoms = Vec::new();

    let nnf = to_nnf(&formula, &mut atoms);

    assert_eq!(nnf, LtlNnf::Atom(0));
    assert_eq!(atoms.len(), 1);
    assert_atom_is_tokens_at_least(&atoms[0], "p0", 1);
}

#[test]
fn test_nnf_finally() {
    let formula = LtlFormula::Finally(Box::new(atom_formula("p0", 1)));
    let mut atoms = Vec::new();

    let nnf = to_nnf(&formula, &mut atoms);

    assert_eq!(
        nnf,
        LtlNnf::Until(Box::new(LtlNnf::True), Box::new(LtlNnf::Atom(0)))
    );
    assert_eq!(atoms.len(), 1);
}

#[test]
fn test_nnf_globally() {
    let formula = LtlFormula::Globally(Box::new(atom_formula("p1", 2)));
    let mut atoms = Vec::new();

    let nnf = to_nnf(&formula, &mut atoms);

    assert_eq!(
        nnf,
        LtlNnf::Release(Box::new(LtlNnf::False), Box::new(LtlNnf::Atom(0)))
    );
    assert_eq!(atoms.len(), 1);
    assert_atom_is_tokens_at_least(&atoms[0], "p1", 2);
}

#[test]
fn test_nnf_negate_until() {
    let nnf = negate(&LtlNnf::Until(
        Box::new(LtlNnf::Atom(0)),
        Box::new(LtlNnf::Atom(1)),
    ));

    assert_eq!(
        nnf,
        LtlNnf::Release(Box::new(LtlNnf::NegAtom(0)), Box::new(LtlNnf::NegAtom(1)))
    );
}

#[test]
fn test_nnf_negate_release() {
    let nnf = negate(&LtlNnf::Release(
        Box::new(LtlNnf::Atom(0)),
        Box::new(LtlNnf::NegAtom(1)),
    ));

    assert_eq!(
        nnf,
        LtlNnf::Until(Box::new(LtlNnf::NegAtom(0)), Box::new(LtlNnf::Atom(1)))
    );
}

#[test]
fn test_nnf_negate_next() {
    let nnf = negate(&LtlNnf::Next(Box::new(LtlNnf::Atom(0))));

    assert_eq!(nnf, LtlNnf::Next(Box::new(LtlNnf::NegAtom(0))));
}

#[test]
fn test_nnf_and_demorgan() {
    let nnf = negate(&LtlNnf::And(vec![LtlNnf::Atom(0), LtlNnf::NegAtom(1)]));

    assert_eq!(nnf, LtlNnf::Or(vec![LtlNnf::NegAtom(0), LtlNnf::Atom(1)]));
}

#[test]
fn test_nnf_complex_nested_pushes_all_negations_to_atoms() {
    let formula = LtlFormula::Not(Box::new(LtlFormula::And(vec![
        LtlFormula::Finally(Box::new(atom_formula("p0", 1))),
        LtlFormula::Or(vec![
            LtlFormula::Globally(Box::new(atom_formula("p1", 1))),
            LtlFormula::Next(Box::new(LtlFormula::Not(Box::new(atom_formula("p2", 1))))),
        ]),
    ])));
    let mut atoms = Vec::new();

    let nnf = to_nnf(&formula, &mut atoms);

    assert_eq!(atoms.len(), 3);
    assert_negations_pushed(&nnf);
}
