// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tableau decomposition rules.
//!
//! This module implements the alpha, beta, gamma, and delta rules for tableau proving.

use crate::formula::{Formula, Subst, Term};
use crate::proof::ProofRule;

/// The result of applying a tableau rule.
#[derive(Clone, Debug)]
pub enum RuleResult {
    /// Alpha rule: single branch extension with new formulas.
    Alpha {
        rule: ProofRule,
        conclusions: Vec<Formula>,
    },
    /// Beta rule: branch splits into two.
    Beta {
        rule: ProofRule,
        left: Vec<Formula>,
        right: Vec<Formula>,
    },
    /// Gamma rule: universal instantiation (can be applied multiple times).
    Gamma {
        rule: ProofRule,
        conclusions: Vec<Formula>,
        /// The instantiated variable.
        var: String,
        /// The term used for instantiation.
        term: Term,
    },
    /// Delta rule: existential witness with fresh constant.
    Delta {
        rule: ProofRule,
        conclusions: Vec<Formula>,
        /// The fresh constant introduced.
        witness: String,
    },
    /// No rule applicable.
    None,
}

/// Apply an alpha rule if possible.
///
/// Alpha rules decompose conjunctions and produce a single successor.
pub fn try_alpha(formula: &Formula) -> Option<RuleResult> {
    match formula {
        // α₁: A ∧ B → {A, B}
        Formula::And(a, b) => Some(RuleResult::Alpha {
            rule: ProofRule::AndElim(formula.clone()),
            conclusions: vec![(**a).clone(), (**b).clone()],
        }),

        // α₂: ¬(A ∨ B) → {¬A, ¬B}
        Formula::Not(inner) if matches!(**inner, Formula::Or(_, _)) => {
            if let Formula::Or(a, b) = &**inner {
                Some(RuleResult::Alpha {
                    rule: ProofRule::NotOr(formula.clone()),
                    conclusions: vec![Formula::not((**a).clone()), Formula::not((**b).clone())],
                })
            } else {
                None
            }
        }

        // α₃: ¬(A → B) → {A, ¬B}
        Formula::Not(inner) if matches!(**inner, Formula::Implies(_, _)) => {
            if let Formula::Implies(a, b) = &**inner {
                Some(RuleResult::Alpha {
                    rule: ProofRule::NotImplies(formula.clone()),
                    conclusions: vec![(**a).clone(), Formula::not((**b).clone())],
                })
            } else {
                None
            }
        }

        // α₄: ¬¬A → {A}
        Formula::Not(inner) if matches!(**inner, Formula::Not(_)) => {
            if let Formula::Not(a) = &**inner {
                Some(RuleResult::Alpha {
                    rule: ProofRule::NotNot(formula.clone()),
                    conclusions: vec![(**a).clone()],
                })
            } else {
                None
            }
        }

        // α₅: A ↔ B → {A → B, B → A}
        Formula::Equiv(a, b) => Some(RuleResult::Alpha {
            rule: ProofRule::EquivElim(formula.clone()),
            conclusions: vec![
                Formula::implies((**a).clone(), (**b).clone()),
                Formula::implies((**b).clone(), (**a).clone()),
            ],
        }),

        // ¬⊥ → ⊤ (treated as alpha producing no new formulas needed)
        Formula::Not(inner) if matches!(**inner, Formula::False) => Some(RuleResult::Alpha {
            rule: ProofRule::TrueIntro,
            conclusions: vec![Formula::True],
        }),

        _ => None,
    }
}

/// Apply a beta rule if possible.
///
/// Beta rules decompose disjunctions and produce two branches.
pub fn try_beta(formula: &Formula) -> Option<RuleResult> {
    match formula {
        // β₁: A ∨ B → {A} | {B}
        Formula::Or(a, b) => Some(RuleResult::Beta {
            rule: ProofRule::OrElim(formula.clone()),
            left: vec![(**a).clone()],
            right: vec![(**b).clone()],
        }),

        // β₂: ¬(A ∧ B) → {¬A} | {¬B}
        Formula::Not(inner) if matches!(**inner, Formula::And(_, _)) => {
            if let Formula::And(a, b) = &**inner {
                Some(RuleResult::Beta {
                    rule: ProofRule::NotAnd(formula.clone()),
                    left: vec![Formula::not((**a).clone())],
                    right: vec![Formula::not((**b).clone())],
                })
            } else {
                None
            }
        }

        // β₃: A → B → {¬A} | {B}
        Formula::Implies(a, b) => Some(RuleResult::Beta {
            rule: ProofRule::ImpliesElim(formula.clone()),
            left: vec![Formula::not((**a).clone())],
            right: vec![(**b).clone()],
        }),

        // β₄: ¬(A ↔ B) → {A, ¬B} | {¬A, B}
        Formula::Not(inner) if matches!(**inner, Formula::Equiv(_, _)) => {
            if let Formula::Equiv(a, b) = &**inner {
                Some(RuleResult::Beta {
                    rule: ProofRule::NotEquiv(formula.clone()),
                    left: vec![(**a).clone(), Formula::not((**b).clone())],
                    right: vec![Formula::not((**a).clone()), (**b).clone()],
                })
            } else {
                None
            }
        }

        _ => None,
    }
}

/// Apply a gamma rule (universal instantiation).
///
/// Gamma rules instantiate universally quantified formulas.
/// The term to instantiate with must be provided.
pub fn try_gamma(formula: &Formula, term: &Term) -> Option<RuleResult> {
    match formula {
        // γ: ∀x.P(x) → P(t)
        Formula::Forall(x, body) => {
            let mut subst = Subst::new();
            subst.insert(x.clone(), term.clone());
            let instantiated = body.substitute(&subst);

            Some(RuleResult::Gamma {
                rule: ProofRule::ForallElim(formula.clone(), term.clone()),
                conclusions: vec![instantiated],
                var: x.clone(),
                term: term.clone(),
            })
        }

        // ¬∃x.P(x) ≡ ∀x.¬P(x), then instantiate
        Formula::Not(inner) if matches!(**inner, Formula::Exists(_, _)) => {
            if let Formula::Exists(x, body) = &**inner {
                let mut subst = Subst::new();
                subst.insert(x.clone(), term.clone());
                let instantiated = Formula::not(body.substitute(&subst));

                Some(RuleResult::Gamma {
                    rule: ProofRule::NotExists(formula.clone(), x.clone()),
                    conclusions: vec![instantiated],
                    var: x.clone(),
                    term: term.clone(),
                })
            } else {
                None
            }
        }

        _ => None,
    }
}

/// Apply a delta rule (existential witness).
///
/// Delta rules introduce fresh constants for existentially quantified formulas.
pub fn try_delta(formula: &Formula, fresh_const: &str) -> Option<RuleResult> {
    match formula {
        // δ: ∃x.P(x) → P(c) for fresh c
        Formula::Exists(x, body) => {
            let mut subst = Subst::new();
            subst.insert(x.clone(), Term::constant(fresh_const));
            let instantiated = body.substitute(&subst);

            Some(RuleResult::Delta {
                rule: ProofRule::ExistsElim(formula.clone(), x.clone()),
                conclusions: vec![instantiated],
                witness: fresh_const.to_string(),
            })
        }

        // ¬∀x.P(x) ≡ ∃x.¬P(x), then witness
        Formula::Not(inner) if matches!(**inner, Formula::Forall(_, _)) => {
            if let Formula::Forall(x, body) = &**inner {
                let mut subst = Subst::new();
                subst.insert(x.clone(), Term::constant(fresh_const));
                let instantiated = Formula::not(body.substitute(&subst));

                Some(RuleResult::Delta {
                    rule: ProofRule::NotForall(formula.clone(), x.clone()),
                    conclusions: vec![instantiated],
                    witness: fresh_const.to_string(),
                })
            } else {
                None
            }
        }

        _ => None,
    }
}

/// Check if a formula is immediately closable (True or contains False).
pub fn is_trivially_closed(formula: &Formula) -> Option<ProofRule> {
    match formula {
        Formula::True => Some(ProofRule::TrueIntro),
        Formula::Not(inner) if matches!(**inner, Formula::False) => Some(ProofRule::TrueIntro),
        _ => None,
    }
}

/// Check if a formula makes the branch immediately contradictory.
pub fn is_contradiction(formula: &Formula) -> Option<ProofRule> {
    match formula {
        Formula::False => Some(ProofRule::FalseElim),
        Formula::Not(inner) if matches!(**inner, Formula::True) => Some(ProofRule::FalseElim),
        _ => None,
    }
}

/// Classify a formula by the type of rule that can be applied.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum FormulaKind {
    /// Literal (atom, negated atom, equality) - no decomposition.
    Literal,
    /// Alpha formula - decompose without branching.
    Alpha,
    /// Beta formula - decompose with branching.
    Beta,
    /// Gamma formula - universal quantifier.
    Gamma,
    /// Delta formula - existential quantifier.
    Delta,
    /// True - trivially valid.
    TrueConst,
    /// False - contradiction.
    FalseConst,
}

/// Classify a formula for rule selection.
pub fn classify(formula: &Formula) -> FormulaKind {
    match formula {
        Formula::True => FormulaKind::TrueConst,
        Formula::False => FormulaKind::FalseConst,
        Formula::Atom(_) | Formula::Pred(_, _) | Formula::Eq(_, _) => FormulaKind::Literal,

        Formula::Not(inner) => match &**inner {
            Formula::True => FormulaKind::FalseConst,
            Formula::False => FormulaKind::TrueConst,
            Formula::Atom(_) | Formula::Pred(_, _) | Formula::Eq(_, _) => FormulaKind::Literal,
            Formula::Not(_) => FormulaKind::Alpha,
            Formula::And(_, _) => FormulaKind::Beta,
            Formula::Or(_, _) => FormulaKind::Alpha,
            Formula::Implies(_, _) => FormulaKind::Alpha,
            Formula::Equiv(_, _) => FormulaKind::Beta,
            Formula::Forall(_, _) => FormulaKind::Delta,
            Formula::Exists(_, _) => FormulaKind::Gamma,
        },

        Formula::And(_, _) => FormulaKind::Alpha,
        Formula::Or(_, _) => FormulaKind::Beta,
        Formula::Implies(_, _) => FormulaKind::Beta,
        Formula::Equiv(_, _) => FormulaKind::Alpha,
        Formula::Forall(_, _) => FormulaKind::Gamma,
        Formula::Exists(_, _) => FormulaKind::Delta,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_alpha_and() {
        let a = Formula::atom("A");
        let b = Formula::atom("B");
        let conj = Formula::and(a.clone(), b.clone());

        let result = try_alpha(&conj);
        assert!(
            matches!(result, Some(RuleResult::Alpha { conclusions, .. }) if conclusions.len() == 2)
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_alpha_not_or() {
        let a = Formula::atom("A");
        let b = Formula::atom("B");
        let not_or = Formula::not(Formula::or(a.clone(), b.clone()));

        let result = try_alpha(&not_or);
        assert!(
            matches!(result, Some(RuleResult::Alpha { ref conclusions, .. }) if conclusions.len() == 2)
        );

        if let Some(RuleResult::Alpha { conclusions, .. }) = result {
            // Should be ¬A and ¬B
            assert!(matches!(&conclusions[0], Formula::Not(_)));
            assert!(matches!(&conclusions[1], Formula::Not(_)));
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_alpha_double_neg() {
        let a = Formula::atom("A");
        let not_not_a = Formula::not(Formula::not(a.clone()));

        let result = try_alpha(&not_not_a);
        assert!(
            matches!(result, Some(RuleResult::Alpha { ref conclusions, .. }) if conclusions.len() == 1)
        );

        if let Some(RuleResult::Alpha { conclusions, .. }) = result {
            assert_eq!(conclusions[0], a);
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_beta_or() {
        let a = Formula::atom("A");
        let b = Formula::atom("B");
        let disj = Formula::or(a.clone(), b.clone());

        let result = try_beta(&disj);
        assert!(
            matches!(result, Some(RuleResult::Beta { ref left, ref right, .. })
            if left.len() == 1 && right.len() == 1)
        );

        if let Some(RuleResult::Beta { left, right, .. }) = result {
            assert_eq!(left[0], a);
            assert_eq!(right[0], b);
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_beta_implies() {
        let a = Formula::atom("A");
        let b = Formula::atom("B");
        let imp = Formula::implies(a.clone(), b.clone());

        let result = try_beta(&imp);
        assert!(
            matches!(result, Some(RuleResult::Beta { ref left, ref right, .. })
            if left.len() == 1 && right.len() == 1)
        );

        if let Some(RuleResult::Beta { left, right, .. }) = result {
            // Should be ¬A and B
            assert!(matches!(&left[0], Formula::Not(_)));
            assert_eq!(right[0], b);
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_gamma_forall() {
        let x = Term::var("x");
        let px = Formula::pred("P", vec![x.clone()]);
        let forall_x_px = Formula::forall("x", px);

        let c = Term::constant("c");
        let result = try_gamma(&forall_x_px, &c);

        assert!(
            matches!(result, Some(RuleResult::Gamma { ref conclusions, .. }) if conclusions.len() == 1)
        );

        if let Some(RuleResult::Gamma { conclusions, .. }) = result {
            // Should be P(c)
            if let Formula::Pred(name, args) = &conclusions[0] {
                assert_eq!(name, "P");
                assert!(matches!(&args[0], Term::Const(n) if n == "c"));
            } else {
                panic!("Expected Pred");
            }
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_delta_exists() {
        let x = Term::var("x");
        let px = Formula::pred("P", vec![x.clone()]);
        let exists_x_px = Formula::exists("x", px);

        let result = try_delta(&exists_x_px, "sk0");

        assert!(
            matches!(result, Some(RuleResult::Delta { ref conclusions, ref witness, .. })
            if conclusions.len() == 1 && witness == "sk0")
        );

        if let Some(RuleResult::Delta { conclusions, .. }) = result {
            // Should be P(sk0)
            if let Formula::Pred(name, args) = &conclusions[0] {
                assert_eq!(name, "P");
                assert!(matches!(&args[0], Term::Const(n) if n == "sk0"));
            } else {
                panic!("Expected Pred");
            }
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_classify() {
        let a = Formula::atom("A");
        assert_eq!(classify(&a), FormulaKind::Literal);
        assert_eq!(classify(&Formula::not(a.clone())), FormulaKind::Literal);

        assert_eq!(classify(&Formula::True), FormulaKind::TrueConst);
        assert_eq!(classify(&Formula::False), FormulaKind::FalseConst);

        let b = Formula::atom("B");
        assert_eq!(
            classify(&Formula::and(a.clone(), b.clone())),
            FormulaKind::Alpha
        );
        assert_eq!(
            classify(&Formula::or(a.clone(), b.clone())),
            FormulaKind::Beta
        );
        assert_eq!(
            classify(&Formula::implies(a.clone(), b.clone())),
            FormulaKind::Beta
        );

        let x = Term::var("x");
        let px = Formula::pred("P", vec![x]);
        assert_eq!(
            classify(&Formula::forall("x", px.clone())),
            FormulaKind::Gamma
        );
        assert_eq!(classify(&Formula::exists("x", px)), FormulaKind::Delta);
    }
}
