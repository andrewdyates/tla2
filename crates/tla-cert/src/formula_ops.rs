// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Formula operations: substitution, alpha-equivalence, tableau decomposition, and unification.

use crate::types::{Formula, Term};

// ============================================================================
// Negation and tableau helpers
// ============================================================================

fn neg(formula: &Formula) -> Formula {
    Formula::Not(Box::new(formula.clone()))
}

fn is_negated_quantifier_instance(body: &Formula, var: &str, formula: &Formula) -> bool {
    if let Formula::Not(inner) = formula {
        is_existential_intro_instance(body, var, inner)
    } else {
        false
    }
}

pub(crate) fn is_valid_tableau_decomposition(premise: &Formula, conclusion: &Formula) -> bool {
    if alpha_equiv(premise, conclusion) {
        return true;
    }

    match premise {
        // alpha/beta decomposition rules
        Formula::And(a, b) | Formula::Or(a, b) => {
            alpha_equiv(conclusion, a.as_ref()) || alpha_equiv(conclusion, b.as_ref())
        }
        Formula::Implies(a, b) => {
            alpha_equiv(conclusion, &neg(a.as_ref())) || alpha_equiv(conclusion, b.as_ref())
        }
        Formula::Equiv(a, b) => {
            let ab = Formula::Implies(Box::new(a.as_ref().clone()), Box::new(b.as_ref().clone()));
            let ba = Formula::Implies(Box::new(b.as_ref().clone()), Box::new(a.as_ref().clone()));
            alpha_equiv(conclusion, &ab) || alpha_equiv(conclusion, &ba)
        }

        // quantifier decomposition
        Formula::Forall(var, body) | Formula::Exists(var, body) => {
            is_existential_intro_instance(body, var, conclusion)
        }

        // equality symmetry
        Formula::Eq(a, b) => {
            let sym = Formula::Eq(b.clone(), a.clone());
            alpha_equiv(conclusion, &sym)
        }

        Formula::Not(inner) => match inner.as_ref() {
            // alpha: ¬(A ∨ B) -> ¬A, ¬B
            Formula::Or(a, b) => {
                alpha_equiv(conclusion, &neg(a.as_ref()))
                    || alpha_equiv(conclusion, &neg(b.as_ref()))
            }
            // alpha: ¬(A -> B) -> A, ¬B
            Formula::Implies(a, b) => {
                alpha_equiv(conclusion, a.as_ref()) || alpha_equiv(conclusion, &neg(b.as_ref()))
            }
            // beta: ¬(A ∧ B) -> ¬A, ¬B
            Formula::And(a, b) => {
                alpha_equiv(conclusion, &neg(a.as_ref()))
                    || alpha_equiv(conclusion, &neg(b.as_ref()))
            }
            // beta: ¬(A ↔ B) -> A, ¬B, ¬A, B
            Formula::Equiv(a, b) => {
                alpha_equiv(conclusion, a.as_ref())
                    || alpha_equiv(conclusion, &neg(b.as_ref()))
                    || alpha_equiv(conclusion, &neg(a.as_ref()))
                    || alpha_equiv(conclusion, b.as_ref())
            }
            // gamma/delta variants through negated quantifiers
            Formula::Exists(var, body) | Formula::Forall(var, body) => {
                is_negated_quantifier_instance(body, var, conclusion)
            }
            // ¬FALSE -> TRUE
            Formula::Bool(false) => matches!(conclusion, Formula::Bool(true)),
            _ => false,
        },

        _ => false,
    }
}

// ============================================================================
// Term and formula substitution
// ============================================================================

/// Substitute all occurrences of `old` term with `new` term in a formula
pub(crate) fn substitute_term_in_formula(formula: &Formula, old: &Term, new: &Term) -> Formula {
    match formula {
        Formula::Bool(b) => Formula::Bool(*b),
        Formula::Predicate(name, terms) => {
            let new_terms: Vec<Term> = terms.iter().map(|t| substitute_term(t, old, new)).collect();
            Formula::Predicate(name.clone(), new_terms)
        }
        Formula::Not(f) => Formula::Not(Box::new(substitute_term_in_formula(f, old, new))),
        Formula::And(l, r) => Formula::And(
            Box::new(substitute_term_in_formula(l, old, new)),
            Box::new(substitute_term_in_formula(r, old, new)),
        ),
        Formula::Or(l, r) => Formula::Or(
            Box::new(substitute_term_in_formula(l, old, new)),
            Box::new(substitute_term_in_formula(r, old, new)),
        ),
        Formula::Implies(l, r) => Formula::Implies(
            Box::new(substitute_term_in_formula(l, old, new)),
            Box::new(substitute_term_in_formula(r, old, new)),
        ),
        Formula::Equiv(l, r) => Formula::Equiv(
            Box::new(substitute_term_in_formula(l, old, new)),
            Box::new(substitute_term_in_formula(r, old, new)),
        ),
        Formula::Forall(var, body) => {
            // Don't substitute if the variable is shadowed
            if let Term::Var(v) = old {
                if v == var {
                    return formula.clone();
                }
            }
            Formula::Forall(
                var.clone(),
                Box::new(substitute_term_in_formula(body, old, new)),
            )
        }
        Formula::Exists(var, body) => {
            // Don't substitute if the variable is shadowed
            if let Term::Var(v) = old {
                if v == var {
                    return formula.clone();
                }
            }
            Formula::Exists(
                var.clone(),
                Box::new(substitute_term_in_formula(body, old, new)),
            )
        }
        Formula::Eq(l, r) => {
            Formula::Eq(substitute_term(l, old, new), substitute_term(r, old, new))
        }
    }
}

/// Substitute all occurrences of `old` term with `new` term in a term
fn substitute_term(term: &Term, old: &Term, new: &Term) -> Term {
    if term == old {
        return new.clone();
    }
    match term {
        Term::Var(_) | Term::Const(_) | Term::Int(_) => term.clone(),
        Term::App(name, args) => {
            let new_args: Vec<Term> = args.iter().map(|a| substitute_term(a, old, new)).collect();
            Term::App(name.clone(), new_args)
        }
    }
}

/// Substitute all occurrences of variable `var` with term `replacement` in a formula
pub(crate) fn substitute_var_in_formula(
    formula: &Formula,
    var: &str,
    replacement: &Term,
) -> Formula {
    let var_term = Term::Var(var.to_string());
    substitute_term_in_formula(formula, &var_term, replacement)
}

// ============================================================================
// Alpha-equivalence
// ============================================================================

/// Check if two formulas are alpha-equivalent (equal up to renaming of bound variables).
///
/// For example, `∀x. P(x)` and `∀y. P(y)` are alpha-equivalent.
pub fn alpha_equiv(f1: &Formula, f2: &Formula) -> bool {
    alpha_equiv_formula(f1, f2, &mut Vec::new(), &mut Vec::new())
}

/// Check alpha-equivalence of formulas with bound variable tracking.
/// `bindings1` and `bindings2` track corresponding bound variables from f1 and f2.
fn alpha_equiv_formula(
    f1: &Formula,
    f2: &Formula,
    bindings1: &mut Vec<String>,
    bindings2: &mut Vec<String>,
) -> bool {
    match (f1, f2) {
        (Formula::Bool(a), Formula::Bool(b)) => a == b,

        (Formula::Predicate(name1, args1), Formula::Predicate(name2, args2)) => {
            name1 == name2
                && args1.len() == args2.len()
                && args1
                    .iter()
                    .zip(args2)
                    .all(|(t1, t2)| alpha_equiv_term(t1, t2, bindings1, bindings2))
        }

        (Formula::Not(a), Formula::Not(b)) => alpha_equiv_formula(a, b, bindings1, bindings2),

        (Formula::And(a1, a2), Formula::And(b1, b2))
        | (Formula::Or(a1, a2), Formula::Or(b1, b2))
        | (Formula::Implies(a1, a2), Formula::Implies(b1, b2))
        | (Formula::Equiv(a1, a2), Formula::Equiv(b1, b2)) => {
            alpha_equiv_formula(a1, b1, bindings1, bindings2)
                && alpha_equiv_formula(a2, b2, bindings1, bindings2)
        }

        (Formula::Forall(v1, body1), Formula::Forall(v2, body2))
        | (Formula::Exists(v1, body1), Formula::Exists(v2, body2)) => {
            // Push corresponding bound variables
            bindings1.push(v1.clone());
            bindings2.push(v2.clone());
            let result = alpha_equiv_formula(body1, body2, bindings1, bindings2);
            bindings1.pop();
            bindings2.pop();
            result
        }

        (Formula::Eq(t1a, t1b), Formula::Eq(t2a, t2b)) => {
            alpha_equiv_term(t1a, t2a, bindings1, bindings2)
                && alpha_equiv_term(t1b, t2b, bindings1, bindings2)
        }

        _ => false,
    }
}

/// Check alpha-equivalence of terms with bound variable tracking.
fn alpha_equiv_term(t1: &Term, t2: &Term, bindings1: &[String], bindings2: &[String]) -> bool {
    match (t1, t2) {
        (Term::Var(v1), Term::Var(v2)) => {
            // Check if both are bound at corresponding positions
            let pos1 = bindings1.iter().rposition(|b| b == v1);
            let pos2 = bindings2.iter().rposition(|b| b == v2);

            match (pos1, pos2) {
                // Both bound at the same relative position
                (Some(p1), Some(p2)) => p1 == p2,
                // Both free - must have same name
                (None, None) => v1 == v2,
                // One bound, one free - not equivalent
                _ => false,
            }
        }

        (Term::Const(c1), Term::Const(c2)) => c1 == c2,
        (Term::Int(i1), Term::Int(i2)) => i1 == i2,

        (Term::App(name1, args1), Term::App(name2, args2)) => {
            name1 == name2
                && args1.len() == args2.len()
                && args1
                    .iter()
                    .zip(args2)
                    .all(|(a1, a2)| alpha_equiv_term(a1, a2, bindings1, bindings2))
        }

        _ => false,
    }
}

// ============================================================================
// Existential introduction and unification
// ============================================================================

/// Check if `witness` is an instance of `body` where free occurrences of `var`
/// are replaced by a single (consistent) witness term.
/// This function supports alpha-equivalence for inner quantifiers.
pub(crate) fn is_existential_intro_instance(body: &Formula, var: &str, witness: &Formula) -> bool {
    let mut inferred: Option<Term> = None;
    let mut bindings_body: Vec<String> = Vec::new();
    let mut bindings_witness: Vec<String> = Vec::new();

    if !unify_formula_with_witness_term(
        body,
        witness,
        var,
        &mut inferred,
        &mut bindings_body,
        &mut bindings_witness,
    ) {
        return false;
    }

    match inferred {
        Some(t) => {
            // Verify by substitution and alpha-equivalence check
            let substituted = substitute_var_in_formula(body, var, &t);
            alpha_equiv(&substituted, witness)
        }
        None => alpha_equiv(body, witness),
    }
}

/// Unify `body` against `witness` to find what term `var` was replaced with.
/// Supports alpha-equivalence for inner quantifiers by tracking bound variables.
fn unify_formula_with_witness_term(
    body: &Formula,
    witness: &Formula,
    var: &str,
    inferred: &mut Option<Term>,
    bindings_body: &mut Vec<String>,
    bindings_witness: &mut Vec<String>,
) -> bool {
    match (body, witness) {
        (Formula::Bool(a), Formula::Bool(b)) => a == b,
        (Formula::Predicate(name_a, args_a), Formula::Predicate(name_b, args_b)) => {
            name_a == name_b
                && args_a.len() == args_b.len()
                && args_a.iter().zip(args_b).all(|(t1, t2)| {
                    unify_term_with_witness_term(
                        t1,
                        t2,
                        var,
                        inferred,
                        bindings_body,
                        bindings_witness,
                    )
                })
        }
        (Formula::Not(a), Formula::Not(b)) => {
            unify_formula_with_witness_term(a, b, var, inferred, bindings_body, bindings_witness)
        }
        (Formula::And(al, ar), Formula::And(bl, br))
        | (Formula::Or(al, ar), Formula::Or(bl, br))
        | (Formula::Implies(al, ar), Formula::Implies(bl, br))
        | (Formula::Equiv(al, ar), Formula::Equiv(bl, br)) => {
            unify_formula_with_witness_term(al, bl, var, inferred, bindings_body, bindings_witness)
                && unify_formula_with_witness_term(
                    ar,
                    br,
                    var,
                    inferred,
                    bindings_body,
                    bindings_witness,
                )
        }
        (Formula::Forall(v1, a), Formula::Forall(v2, b))
        | (Formula::Exists(v1, a), Formula::Exists(v2, b)) => {
            // Track bindings for alpha-equivalence
            bindings_body.push(v1.clone());
            bindings_witness.push(v2.clone());
            let result = unify_formula_with_witness_term(
                a,
                b,
                var,
                inferred,
                bindings_body,
                bindings_witness,
            );
            bindings_body.pop();
            bindings_witness.pop();
            result
        }
        (Formula::Eq(a1, a2), Formula::Eq(b1, b2)) => {
            unify_term_with_witness_term(a1, b1, var, inferred, bindings_body, bindings_witness)
                && unify_term_with_witness_term(
                    a2,
                    b2,
                    var,
                    inferred,
                    bindings_body,
                    bindings_witness,
                )
        }
        _ => false,
    }
}

/// Check if `var` is currently shadowed by a binding in the body.
fn is_var_shadowed(var: &str, bindings_body: &[String]) -> bool {
    bindings_body.iter().any(|b| b == var)
}

fn unify_term_with_witness_term(
    body: &Term,
    witness: &Term,
    var: &str,
    inferred: &mut Option<Term>,
    bindings_body: &[String],
    bindings_witness: &[String],
) -> bool {
    // Check if we're at the existential variable (not shadowed)
    if !is_var_shadowed(var, bindings_body) {
        if let Term::Var(v) = body {
            if v == var {
                return match inferred {
                    None => {
                        *inferred = Some(witness.clone());
                        true
                    }
                    Some(existing) => existing == witness,
                };
            }
        }
    }

    // For other terms, use alpha-equivalence logic
    match (body, witness) {
        (Term::Var(v1), Term::Var(v2)) => {
            // Check if both are bound at corresponding positions
            let pos1 = bindings_body.iter().rposition(|b| b == v1);
            let pos2 = bindings_witness.iter().rposition(|b| b == v2);

            match (pos1, pos2) {
                // Both bound at the same relative position
                (Some(p1), Some(p2)) => p1 == p2,
                // Both free - must have same name
                (None, None) => v1 == v2,
                // One bound, one free - not equivalent
                _ => false,
            }
        }
        (Term::Const(a), Term::Const(b)) => a == b,
        (Term::Int(a), Term::Int(b)) => a == b,
        (Term::App(name_a, args_a), Term::App(name_b, args_b)) => {
            name_a == name_b
                && args_a.len() == args_b.len()
                && args_a.iter().zip(args_b).all(|(t1, t2)| {
                    unify_term_with_witness_term(
                        t1,
                        t2,
                        var,
                        inferred,
                        bindings_body,
                        bindings_witness,
                    )
                })
        }
        _ => false,
    }
}
