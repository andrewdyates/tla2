// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::property_xml::{CtlFormula, Formula, Property, StatePredicate};

/// Check whether a CTL formula contains an immediate-successor operator (EX or AX).
///
/// EX/AX are stutter-sensitive: they depend on exact next-step reachability,
/// so output-pruning via the deeper query-local slice is unsound when present.
pub(crate) fn ctl_formula_contains_next_step(formula: &CtlFormula) -> bool {
    match formula {
        CtlFormula::EX(_) | CtlFormula::AX(_) => true,
        CtlFormula::Atom(_) => false,
        CtlFormula::Not(inner)
        | CtlFormula::EF(inner)
        | CtlFormula::AF(inner)
        | CtlFormula::EG(inner)
        | CtlFormula::AG(inner) => ctl_formula_contains_next_step(inner),
        CtlFormula::And(children) | CtlFormula::Or(children) => {
            children.iter().any(ctl_formula_contains_next_step)
        }
        CtlFormula::EU(phi, psi) | CtlFormula::AU(phi, psi) => {
            ctl_formula_contains_next_step(phi) || ctl_formula_contains_next_step(psi)
        }
    }
}

/// Check whether any property in a CTL batch contains EX or AX.
///
/// When true, the whole batch stays on the conservative induced-subnet slice.
pub(crate) fn ctl_batch_contains_next_step(properties: &[Property]) -> bool {
    properties.iter().any(|prop| {
        if let Formula::Ctl(ctl) = &prop.formula {
            ctl_formula_contains_next_step(ctl)
        } else {
            false
        }
    })
}

/// A CTL property whose truth at the initial state depends only on reachability.
#[derive(Debug)]
#[cfg_attr(test, derive(Clone, PartialEq, Eq))]
pub(crate) enum ShallowCtl {
    /// EF(pred): TRUE iff some reachable state satisfies pred.
    ExistsFinally(StatePredicate),
    /// AG(pred): TRUE iff all reachable states satisfy pred.
    AlwaysGlobally(StatePredicate),
}

/// A CTL property whose truth at the initial state depends only on
/// maximal-path suffix analysis (not full fixpoint CTL).
#[derive(Debug)]
#[cfg_attr(test, derive(Clone, PartialEq, Eq))]
pub(crate) enum ShallowCtlSuffix {
    /// EG(pred): TRUE iff some maximal path from initial stays in pred.
    ExistsGlobally(StatePredicate),
    /// AF(pred): TRUE iff every maximal path eventually reaches pred.
    AlwaysFinally(StatePredicate),
}

/// Classify a CTL formula as shallow suffix (routable through maximal-path
/// suffix analysis) or deep.
///
/// Returns `Some` for `AF(atom)`, `EG(atom)`, idempotent wrappers like
/// `AF(AF(atom))`, and negated duals `Not(EG(atom))` = `AF(Not(atom))`.
pub(crate) fn classify_shallow_ctl_suffix(formula: &CtlFormula) -> Option<ShallowCtlSuffix> {
    match formula {
        CtlFormula::AF(inner) => extract_state_pred_ctl(inner)
            .map(ShallowCtlSuffix::AlwaysFinally)
            .or_else(|| match inner.as_ref() {
                CtlFormula::AF(_) => classify_shallow_ctl_suffix(inner),
                _ => None,
            }),
        CtlFormula::EG(inner) => extract_state_pred_ctl(inner)
            .map(ShallowCtlSuffix::ExistsGlobally)
            .or_else(|| match inner.as_ref() {
                CtlFormula::EG(_) => classify_shallow_ctl_suffix(inner),
                _ => None,
            }),
        CtlFormula::Not(inner) => match inner.as_ref() {
            CtlFormula::EG(eg_inner) => extract_state_pred_ctl(eg_inner)
                .map(|pred| ShallowCtlSuffix::AlwaysFinally(StatePredicate::Not(Box::new(pred)))),
            CtlFormula::AF(af_inner) => extract_state_pred_ctl(af_inner)
                .map(|pred| ShallowCtlSuffix::ExistsGlobally(StatePredicate::Not(Box::new(pred)))),
            _ => None,
        },
        _ => None,
    }
}

/// Classify a CTL formula as shallow (routable through reachability) or deep.
///
/// Returns `Some` for `EF(atom)`, `AG(atom)`, idempotent wrappers like
/// `EF(EF(atom))`, and negated duals `Not(AG(atom))` = `EF(Not(atom))`.
pub(crate) fn classify_shallow_ctl(formula: &CtlFormula) -> Option<ShallowCtl> {
    match formula {
        // EF(atom) or EF(EF(...(atom)))
        CtlFormula::EF(inner) => extract_state_pred_ctl(inner)
            .map(ShallowCtl::ExistsFinally)
            .or_else(|| match inner.as_ref() {
                CtlFormula::EF(_) => classify_shallow_ctl(inner),
                _ => None,
            }),
        // AG(atom) or AG(AG(...(atom)))
        CtlFormula::AG(inner) => extract_state_pred_ctl(inner)
            .map(ShallowCtl::AlwaysGlobally)
            .or_else(|| match inner.as_ref() {
                CtlFormula::AG(_) => classify_shallow_ctl(inner),
                _ => None,
            }),
        // Not(AG(atom)) = EF(Not(atom)); Not(EF(atom)) = AG(Not(atom))
        CtlFormula::Not(inner) => match inner.as_ref() {
            CtlFormula::AG(ag_inner) => extract_state_pred_ctl(ag_inner)
                .map(|pred| ShallowCtl::ExistsFinally(StatePredicate::Not(Box::new(pred)))),
            CtlFormula::EF(ef_inner) => extract_state_pred_ctl(ef_inner)
                .map(|pred| ShallowCtl::AlwaysGlobally(StatePredicate::Not(Box::new(pred)))),
            _ => None,
        },
        _ => None,
    }
}

/// Extract a pure state predicate from a CTL formula.
///
/// Returns `Some` only if the formula is a boolean combination of atoms
/// (no temporal operators).
fn extract_state_pred_ctl(formula: &CtlFormula) -> Option<StatePredicate> {
    match formula {
        CtlFormula::Atom(pred) => Some(pred.clone()),
        CtlFormula::Not(inner) => {
            extract_state_pred_ctl(inner).map(|p| StatePredicate::Not(Box::new(p)))
        }
        CtlFormula::And(children) => {
            let preds: Option<Vec<_>> = children.iter().map(extract_state_pred_ctl).collect();
            preds.map(StatePredicate::And)
        }
        CtlFormula::Or(children) => {
            let preds: Option<Vec<_>> = children.iter().map(extract_state_pred_ctl).collect();
            preds.map(StatePredicate::Or)
        }
        // Any temporal operator means not a pure state predicate.
        CtlFormula::EX(_)
        | CtlFormula::AX(_)
        | CtlFormula::EF(_)
        | CtlFormula::AF(_)
        | CtlFormula::EG(_)
        | CtlFormula::AG(_)
        | CtlFormula::EU(_, _)
        | CtlFormula::AU(_, _) => None,
    }
}
