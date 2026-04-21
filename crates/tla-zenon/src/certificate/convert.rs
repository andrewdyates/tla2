// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Conversion between Zenon formula/term types and certificate types.

use crate::formula::{Formula as ZenonFormula, Term as ZenonTerm};
use tla_cert::{Formula as CertFormula, Term as CertTerm};

/// Convert a Zenon term to a certificate term.
pub fn convert_term(term: &ZenonTerm) -> CertTerm {
    match term {
        ZenonTerm::Var(name) => CertTerm::Var(name.clone()),
        ZenonTerm::Const(name) => CertTerm::Const(name.clone()),
        ZenonTerm::App(name, args) => {
            CertTerm::App(name.clone(), args.iter().map(convert_term).collect())
        }
    }
}

/// Convert a Zenon formula to a certificate formula.
pub fn convert_formula(formula: &ZenonFormula) -> CertFormula {
    match formula {
        ZenonFormula::True => CertFormula::Bool(true),
        ZenonFormula::False => CertFormula::Bool(false),
        ZenonFormula::Atom(name) => CertFormula::Predicate(name.clone(), vec![]),
        ZenonFormula::Pred(name, args) => {
            CertFormula::Predicate(name.clone(), args.iter().map(convert_term).collect())
        }
        ZenonFormula::Eq(t1, t2) => CertFormula::Eq(convert_term(t1), convert_term(t2)),
        ZenonFormula::Not(f) => CertFormula::Not(Box::new(convert_formula(f))),
        ZenonFormula::And(f1, f2) => {
            CertFormula::And(Box::new(convert_formula(f1)), Box::new(convert_formula(f2)))
        }
        ZenonFormula::Or(f1, f2) => {
            CertFormula::Or(Box::new(convert_formula(f1)), Box::new(convert_formula(f2)))
        }
        ZenonFormula::Implies(f1, f2) => {
            CertFormula::Implies(Box::new(convert_formula(f1)), Box::new(convert_formula(f2)))
        }
        ZenonFormula::Equiv(f1, f2) => {
            CertFormula::Equiv(Box::new(convert_formula(f1)), Box::new(convert_formula(f2)))
        }
        ZenonFormula::Forall(var, body) => {
            CertFormula::Forall(var.clone(), Box::new(convert_formula(body)))
        }
        ZenonFormula::Exists(var, body) => {
            CertFormula::Exists(var.clone(), Box::new(convert_formula(body)))
        }
    }
}
