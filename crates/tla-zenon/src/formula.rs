// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! First-order logic formulas and terms.
//!
//! This module defines the representation for FOL formulas used in tableau proving.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::Arc;

/// A first-order term (variables, constants, function applications).
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// Variable: x, y, z
    Var(String),
    /// Constant: c, d (including Skolem constants)
    Const(String),
    /// Function application: f(t1, t2, ...)
    App(String, Vec<Term>),
}

impl Term {
    /// Create a variable term.
    pub fn var(name: impl Into<String>) -> Self {
        Term::Var(name.into())
    }

    /// Create a constant term.
    pub fn constant(name: impl Into<String>) -> Self {
        Term::Const(name.into())
    }

    /// Create a function application.
    pub fn app(name: impl Into<String>, args: Vec<Term>) -> Self {
        Term::App(name.into(), args)
    }

    /// Get free variables in this term.
    pub fn free_vars(&self) -> HashSet<String> {
        match self {
            Term::Var(x) => {
                let mut set = HashSet::new();
                set.insert(x.clone());
                set
            }
            Term::Const(_) => HashSet::new(),
            Term::App(_, args) => args.iter().flat_map(|t| t.free_vars()).collect(),
        }
    }

    /// Apply a substitution to this term.
    pub fn substitute(&self, subst: &Subst) -> Term {
        match self {
            Term::Var(x) => {
                if let Some(t) = subst.get(x) {
                    t.clone()
                } else {
                    self.clone()
                }
            }
            Term::Const(_) => self.clone(),
            Term::App(f, args) => Term::App(
                f.clone(),
                args.iter().map(|t| t.substitute(subst)).collect(),
            ),
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(x) => write!(f, "{}", x),
            Term::Const(c) => write!(f, "{}", c),
            Term::App(name, args) if args.is_empty() => write!(f, "{}", name),
            Term::App(name, args) => {
                write!(f, "{}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

/// A substitution mapping variables to terms.
pub type Subst = HashMap<String, Term>;

/// A first-order logic formula.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Formula {
    /// True constant
    True,
    /// False constant
    False,
    /// Propositional variable or predicate with 0 args: P
    Atom(String),
    /// Predicate application: P(t1, t2, ...)
    Pred(String, Vec<Term>),
    /// Equality: t1 = t2
    Eq(Term, Term),
    /// Negation: ¬P
    Not(Arc<Formula>),
    /// Conjunction: P ∧ Q
    And(Arc<Formula>, Arc<Formula>),
    /// Disjunction: P ∨ Q
    Or(Arc<Formula>, Arc<Formula>),
    /// Implication: P → Q
    Implies(Arc<Formula>, Arc<Formula>),
    /// Equivalence: P ↔ Q
    Equiv(Arc<Formula>, Arc<Formula>),
    /// Universal quantification: ∀x. P
    Forall(String, Arc<Formula>),
    /// Existential quantification: ∃x. P
    Exists(String, Arc<Formula>),
}

impl Formula {
    /// Create an atomic formula (propositional variable).
    pub fn atom(name: impl Into<String>) -> Self {
        Formula::Atom(name.into())
    }

    /// Alias for atom - creates a propositional variable.
    pub fn var(name: impl Into<String>) -> Self {
        Formula::atom(name)
    }

    /// Create a predicate application.
    pub fn pred(name: impl Into<String>, args: Vec<Term>) -> Self {
        Formula::Pred(name.into(), args)
    }

    /// Create an equality formula.
    pub fn eq(t1: Term, t2: Term) -> Self {
        Formula::Eq(t1, t2)
    }

    /// Create a negation.
    #[allow(clippy::should_implement_trait)]
    pub fn not(f: Formula) -> Self {
        Formula::Not(Arc::new(f))
    }

    /// Create a conjunction.
    pub fn and(f1: Formula, f2: Formula) -> Self {
        Formula::And(Arc::new(f1), Arc::new(f2))
    }

    /// Create a disjunction.
    pub fn or(f1: Formula, f2: Formula) -> Self {
        Formula::Or(Arc::new(f1), Arc::new(f2))
    }

    /// Create an implication.
    pub fn implies(f1: Formula, f2: Formula) -> Self {
        Formula::Implies(Arc::new(f1), Arc::new(f2))
    }

    /// Create an equivalence.
    pub fn equiv(f1: Formula, f2: Formula) -> Self {
        Formula::Equiv(Arc::new(f1), Arc::new(f2))
    }

    /// Create a universal quantification.
    pub fn forall(var: impl Into<String>, body: Formula) -> Self {
        Formula::Forall(var.into(), Arc::new(body))
    }

    /// Create an existential quantification.
    pub fn exists(var: impl Into<String>, body: Formula) -> Self {
        Formula::Exists(var.into(), Arc::new(body))
    }

    /// Get the negation of this formula (pushes negation or removes double negation).
    pub fn negate(&self) -> Formula {
        match self {
            Formula::Not(inner) => (**inner).clone(),
            _ => Formula::Not(Arc::new(self.clone())),
        }
    }

    /// Get free variables in this formula.
    pub fn free_vars(&self) -> HashSet<String> {
        match self {
            Formula::True | Formula::False => HashSet::new(),
            Formula::Atom(_) => HashSet::new(),
            Formula::Pred(_, args) => args.iter().flat_map(|t| t.free_vars()).collect(),
            Formula::Eq(t1, t2) => {
                let mut vars = t1.free_vars();
                vars.extend(t2.free_vars());
                vars
            }
            Formula::Not(f) => f.free_vars(),
            Formula::And(f1, f2)
            | Formula::Or(f1, f2)
            | Formula::Implies(f1, f2)
            | Formula::Equiv(f1, f2) => {
                let mut vars = f1.free_vars();
                vars.extend(f2.free_vars());
                vars
            }
            Formula::Forall(x, body) | Formula::Exists(x, body) => {
                let mut vars = body.free_vars();
                vars.remove(x);
                vars
            }
        }
    }

    /// Apply a substitution to this formula.
    pub fn substitute(&self, subst: &Subst) -> Formula {
        match self {
            Formula::True => Formula::True,
            Formula::False => Formula::False,
            Formula::Atom(name) => Formula::Atom(name.clone()),
            Formula::Pred(name, args) => Formula::Pred(
                name.clone(),
                args.iter().map(|t| t.substitute(subst)).collect(),
            ),
            Formula::Eq(t1, t2) => Formula::Eq(t1.substitute(subst), t2.substitute(subst)),
            Formula::Not(f) => Formula::not(f.substitute(subst)),
            Formula::And(f1, f2) => Formula::and(f1.substitute(subst), f2.substitute(subst)),
            Formula::Or(f1, f2) => Formula::or(f1.substitute(subst), f2.substitute(subst)),
            Formula::Implies(f1, f2) => {
                Formula::implies(f1.substitute(subst), f2.substitute(subst))
            }
            Formula::Equiv(f1, f2) => Formula::equiv(f1.substitute(subst), f2.substitute(subst)),
            Formula::Forall(x, body) => {
                // Avoid variable capture
                let mut new_subst = subst.clone();
                new_subst.remove(x);
                Formula::forall(x.clone(), body.substitute(&new_subst))
            }
            Formula::Exists(x, body) => {
                let mut new_subst = subst.clone();
                new_subst.remove(x);
                Formula::exists(x.clone(), body.substitute(&new_subst))
            }
        }
    }

    /// Check if this formula is an atomic formula (atom, pred, eq, or their negations).
    pub fn is_literal(&self) -> bool {
        match self {
            Formula::True
            | Formula::False
            | Formula::Atom(_)
            | Formula::Pred(_, _)
            | Formula::Eq(_, _) => true,
            Formula::Not(inner) => {
                matches!(
                    **inner,
                    Formula::Atom(_)
                        | Formula::Pred(_, _)
                        | Formula::Eq(_, _)
                        | Formula::True
                        | Formula::False
                )
            }
            _ => false,
        }
    }

    /// Check if two formulas are contradictory (one is the negation of the other).
    pub fn contradicts(&self, other: &Formula) -> bool {
        match (self, other) {
            (Formula::Not(f1), f2) if **f1 == *f2 => true,
            (f1, Formula::Not(f2)) if *f1 == **f2 => true,
            (Formula::True, Formula::False) | (Formula::False, Formula::True) => true,
            _ => false,
        }
    }
}

impl fmt::Debug for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::True => write!(f, "⊤"),
            Formula::False => write!(f, "⊥"),
            Formula::Atom(name) => write!(f, "{}", name),
            Formula::Pred(name, args) if args.is_empty() => write!(f, "{}", name),
            Formula::Pred(name, args) => {
                write!(f, "{}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}", arg)?;
                }
                write!(f, ")")
            }
            Formula::Eq(t1, t2) => write!(f, "{:?} = {:?}", t1, t2),
            Formula::Not(inner) => write!(f, "¬{:?}", inner),
            Formula::And(f1, f2) => write!(f, "({:?} ∧ {:?})", f1, f2),
            Formula::Or(f1, f2) => write!(f, "({:?} ∨ {:?})", f1, f2),
            Formula::Implies(f1, f2) => write!(f, "({:?} → {:?})", f1, f2),
            Formula::Equiv(f1, f2) => write!(f, "({:?} ↔ {:?})", f1, f2),
            Formula::Forall(x, body) => write!(f, "∀{}. {:?}", x, body),
            Formula::Exists(x, body) => write!(f, "∃{}. {:?}", x, body),
        }
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_formula_construction() {
        let p = Formula::atom("P");
        let q = Formula::atom("Q");

        let and = Formula::and(p.clone(), q.clone());
        assert!(matches!(and, Formula::And(_, _)));

        let or = Formula::or(p.clone(), q.clone());
        assert!(matches!(or, Formula::Or(_, _)));

        let not_p = Formula::not(p.clone());
        assert!(matches!(not_p, Formula::Not(_)));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_formula_negate() {
        let p = Formula::atom("P");
        let not_p = p.negate();

        // ¬P
        assert!(matches!(not_p, Formula::Not(_)));

        // ¬¬P = P
        let not_not_p = not_p.negate();
        assert_eq!(not_not_p, p);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_formula_free_vars() {
        let x = Term::var("x");
        let y = Term::var("y");

        // P(x, y) has free vars {x, y}
        let pred = Formula::pred("P", vec![x.clone(), y.clone()]);
        let free = pred.free_vars();
        assert!(free.contains("x"));
        assert!(free.contains("y"));

        // ∀x. P(x, y) has free var {y}
        let forall = Formula::forall("x", pred);
        let free2 = forall.free_vars();
        assert!(!free2.contains("x"));
        assert!(free2.contains("y"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_formula_substitute() {
        let x = Term::var("x");
        let c = Term::constant("c");

        // P(x) with x := c gives P(c)
        let pred = Formula::pred("P", vec![x]);
        let mut subst = Subst::new();
        subst.insert("x".to_string(), c);

        let result = pred.substitute(&subst);
        if let Formula::Pred(_, args) = result {
            assert_eq!(args.len(), 1);
            assert!(matches!(&args[0], Term::Const(name) if name == "c"));
        } else {
            panic!("Expected Pred");
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_is_literal() {
        assert!(Formula::atom("P").is_literal());
        assert!(Formula::True.is_literal());
        assert!(Formula::False.is_literal());
        assert!(Formula::not(Formula::atom("P")).is_literal());

        let p = Formula::atom("P");
        let q = Formula::atom("Q");
        assert!(!Formula::and(p.clone(), q.clone()).is_literal());
        assert!(!Formula::or(p, q).is_literal());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_contradicts() {
        let p = Formula::atom("P");
        let not_p = Formula::not(p.clone());

        assert!(p.contradicts(&not_p));
        assert!(not_p.contradicts(&p));
        assert!(Formula::True.contradicts(&Formula::False));
        assert!(Formula::False.contradicts(&Formula::True));

        let q = Formula::atom("Q");
        assert!(!p.contradicts(&q));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_term_free_vars() {
        let x = Term::var("x");
        let c = Term::constant("c");
        let f = Term::app("f", vec![x.clone(), c.clone()]);

        assert_eq!(x.free_vars(), HashSet::from(["x".to_string()]));
        assert!(c.free_vars().is_empty());
        assert_eq!(f.free_vars(), HashSet::from(["x".to_string()]));
    }
}
