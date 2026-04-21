// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Axiom verification for the certificate checker.

use crate::types::{ArithmeticAxiom, Axiom, Formula, SetAxiom, Term, VerificationError};

/// Verify that a formula correctly instantiates the given axiom.
pub(crate) fn verify_axiom(axiom: &Axiom, formula: &Formula) -> Result<(), VerificationError> {
    match axiom {
        Axiom::ExcludedMiddle(p) => {
            let expected = Formula::Or(
                Box::new(p.clone()),
                Box::new(Formula::Not(Box::new(p.clone()))),
            );
            check_axiom_match(formula, &expected, "Excluded middle formula mismatch")
        }
        Axiom::Identity(p) => {
            let expected = Formula::Implies(Box::new(p.clone()), Box::new(p.clone()));
            check_axiom_match(formula, &expected, "Identity formula mismatch")
        }
        Axiom::Weakening => verify_weakening(formula),
        Axiom::EqualityRefl => verify_equality_refl(formula),
        Axiom::EqualitySym => verify_equality_sym(formula),
        Axiom::EqualityTrans => verify_equality_trans(formula),
        Axiom::Arithmetic(arith) => verify_arithmetic_axiom(arith, formula),
        Axiom::SetTheory(set) => verify_set_axiom(set, formula),
    }
}

fn check_axiom_match(
    formula: &Formula,
    expected: &Formula,
    msg: &str,
) -> Result<(), VerificationError> {
    if formula == expected {
        Ok(())
    } else {
        Err(VerificationError::InvalidAxiom(msg.to_string()))
    }
}

fn verify_weakening(formula: &Formula) -> Result<(), VerificationError> {
    // P → (Q → P) for some P, Q
    if let Formula::Implies(p, inner) = formula {
        if let Formula::Implies(_, p2) = inner.as_ref() {
            if p.as_ref() == p2.as_ref() {
                return Ok(());
            }
        }
    }
    Err(VerificationError::InvalidAxiom(
        "Weakening axiom mismatch".to_string(),
    ))
}

fn verify_equality_refl(formula: &Formula) -> Result<(), VerificationError> {
    // a = a
    if let Formula::Eq(a, b) = formula {
        if a == b {
            return Ok(());
        }
    }
    Err(VerificationError::InvalidAxiom(
        "Equality reflexivity mismatch".to_string(),
    ))
}

fn verify_equality_sym(formula: &Formula) -> Result<(), VerificationError> {
    // (a = b) → (b = a)
    if let Formula::Implies(ante, cons) = formula {
        if let (Formula::Eq(a1, b1), Formula::Eq(a2, b2)) = (ante.as_ref(), cons.as_ref()) {
            if a1 == b2 && b1 == a2 {
                return Ok(());
            }
        }
    }
    Err(VerificationError::InvalidAxiom(
        "Equality symmetry mismatch".to_string(),
    ))
}

fn verify_equality_trans(formula: &Formula) -> Result<(), VerificationError> {
    // (a = b ∧ b = c) → (a = c)
    if let Formula::Implies(ante, cons) = formula {
        if let Formula::And(eq1, eq2) = ante.as_ref() {
            if let (Formula::Eq(a, b1), Formula::Eq(b2, c), Formula::Eq(a2, c2)) =
                (eq1.as_ref(), eq2.as_ref(), cons.as_ref())
            {
                if b1 == b2 && a == a2 && c == c2 {
                    return Ok(());
                }
            }
        }
    }
    Err(VerificationError::InvalidAxiom(
        "Equality transitivity mismatch".to_string(),
    ))
}

fn verify_arithmetic_axiom(
    axiom: &ArithmeticAxiom,
    formula: &Formula,
) -> Result<(), VerificationError> {
    match axiom {
        ArithmeticAxiom::AddZero => verify_add_zero(formula),
        ArithmeticAxiom::AddComm => verify_add_comm(formula),
        ArithmeticAxiom::AddAssoc => verify_add_assoc(formula),
        ArithmeticAxiom::MulOne => verify_mul_one(formula),
        ArithmeticAxiom::MulZero => verify_mul_zero(formula),
    }
}

fn verify_add_zero(formula: &Formula) -> Result<(), VerificationError> {
    // 0 + a = a
    if let Formula::Eq(Term::App(op, args), rhs) = formula {
        if op == "+" && args.len() == 2 && args[0] == Term::Int(0) && &args[1] == rhs {
            return Ok(());
        }
    }
    Err(VerificationError::InvalidAxiom(
        "AddZero axiom mismatch".to_string(),
    ))
}

fn verify_add_comm(formula: &Formula) -> Result<(), VerificationError> {
    // a + b = b + a
    if let Formula::Eq(lhs, rhs) = formula {
        if let (Term::App(op1, args1), Term::App(op2, args2)) = (lhs, rhs) {
            if op1 == "+"
                && op2 == "+"
                && args1.len() == 2
                && args2.len() == 2
                && args1[0] == args2[1]
                && args1[1] == args2[0]
            {
                return Ok(());
            }
        }
    }
    Err(VerificationError::InvalidAxiom(
        "AddComm axiom mismatch".to_string(),
    ))
}

fn verify_add_assoc(formula: &Formula) -> Result<(), VerificationError> {
    // (a + b) + c = a + (b + c)
    if let Formula::Eq(lhs, rhs) = formula {
        if let (Term::App(op1, args1), Term::App(op2, args2)) = (lhs, rhs) {
            if op1 == "+" && op2 == "+" && args1.len() == 2 && args2.len() == 2 {
                if let (Term::App(inner_op1, inner_args1), Term::App(inner_op2, inner_args2)) =
                    (&args1[0], &args2[1])
                {
                    if inner_op1 == "+"
                        && inner_op2 == "+"
                        && inner_args1.len() == 2
                        && inner_args2.len() == 2
                        && inner_args1[0] == args2[0]
                        && inner_args1[1] == inner_args2[0]
                        && args1[1] == inner_args2[1]
                    {
                        return Ok(());
                    }
                }
            }
        }
    }
    Err(VerificationError::InvalidAxiom(
        "AddAssoc axiom mismatch".to_string(),
    ))
}

fn verify_mul_one(formula: &Formula) -> Result<(), VerificationError> {
    // a * 1 = a
    if let Formula::Eq(Term::App(op, args), rhs) = formula {
        if op == "*" && args.len() == 2 && args[1] == Term::Int(1) && &args[0] == rhs {
            return Ok(());
        }
    }
    Err(VerificationError::InvalidAxiom(
        "MulOne axiom mismatch".to_string(),
    ))
}

fn verify_mul_zero(formula: &Formula) -> Result<(), VerificationError> {
    // a * 0 = 0
    if let Formula::Eq(Term::App(op, args), rhs) = formula {
        if op == "*" && args.len() == 2 && args[1] == Term::Int(0) && rhs == &Term::Int(0) {
            return Ok(());
        }
    }
    Err(VerificationError::InvalidAxiom(
        "MulZero axiom mismatch".to_string(),
    ))
}

fn verify_set_axiom(axiom: &SetAxiom, formula: &Formula) -> Result<(), VerificationError> {
    match axiom {
        SetAxiom::EmptySet => verify_empty_set(formula),
        SetAxiom::Singleton => verify_singleton(formula),
        SetAxiom::Union => verify_binary_set_op(formula, "∪", true, "Union"),
        SetAxiom::Intersection => verify_binary_set_op(formula, "∩", false, "Intersection"),
    }
}

fn verify_empty_set(formula: &Formula) -> Result<(), VerificationError> {
    // x ∈ {} ↔ FALSE
    if let Formula::Equiv(lhs, rhs) = formula {
        if let Formula::Predicate(pred, args) = lhs.as_ref() {
            if pred == "∈" && args.len() == 2 {
                if let Term::Const(set_name) = &args[1] {
                    if set_name == "{}" && rhs.as_ref() == &Formula::Bool(false) {
                        return Ok(());
                    }
                }
            }
        }
    }
    Err(VerificationError::InvalidAxiom(
        "EmptySet axiom mismatch".to_string(),
    ))
}

fn verify_singleton(formula: &Formula) -> Result<(), VerificationError> {
    // x ∈ {a} ↔ x = a
    if let Formula::Equiv(lhs, rhs) = formula {
        if let Formula::Predicate(pred, args) = lhs.as_ref() {
            if pred == "∈" && args.len() == 2 {
                if let Formula::Eq(x, a) = rhs.as_ref() {
                    if &args[0] == x {
                        if let Term::App(set_op, set_args) = &args[1] {
                            if set_op == "singleton" && set_args.len() == 1 && &set_args[0] == a {
                                return Ok(());
                            }
                        }
                    }
                }
            }
        }
    }
    Err(VerificationError::InvalidAxiom(
        "Singleton axiom mismatch".to_string(),
    ))
}

/// Verify a binary set operation axiom (Union or Intersection).
///
/// Union:        x ∈ S ∪ T ↔ x ∈ S ∨ x ∈ T
/// Intersection: x ∈ S ∩ T ↔ x ∈ S ∧ x ∈ T
fn verify_binary_set_op(
    formula: &Formula,
    set_op: &str,
    is_disjunction: bool,
    name: &str,
) -> Result<(), VerificationError> {
    if let Formula::Equiv(lhs, rhs) = formula {
        if let Formula::Predicate(pred, args) = lhs.as_ref() {
            if pred == "∈" && args.len() == 2 {
                if let Term::App(op, op_args) = &args[1] {
                    if op == set_op && op_args.len() == 2 {
                        let (in_s, in_t) = match (is_disjunction, rhs.as_ref()) {
                            (true, Formula::Or(s, t)) => (s.as_ref(), t.as_ref()),
                            (false, Formula::And(s, t)) => (s.as_ref(), t.as_ref()),
                            _ => {
                                return Err(VerificationError::InvalidAxiom(format!(
                                    "{} axiom mismatch",
                                    name
                                )));
                            }
                        };
                        if check_membership_pair(&args[0], op_args, in_s, in_t) {
                            return Ok(());
                        }
                    }
                }
            }
        }
    }
    Err(VerificationError::InvalidAxiom(format!(
        "{} axiom mismatch",
        name
    )))
}

/// Check that in_s is `x ∈ S` and in_t is `x ∈ T`.
fn check_membership_pair(x: &Term, set_operands: &[Term], in_s: &Formula, in_t: &Formula) -> bool {
    if let (Formula::Predicate(p1, a1), Formula::Predicate(p2, a2)) = (in_s, in_t) {
        p1 == "∈"
            && p2 == "∈"
            && a1.len() == 2
            && a2.len() == 2
            && a1[0] == *x
            && a2[0] == *x
            && a1[1] == set_operands[0]
            && a2[1] == set_operands[1]
    } else {
        false
    }
}
