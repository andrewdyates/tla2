// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Temporal formula simplification — fold temporal shells around constants.
//!
//! After state-predicate simplification, temporal operators wrapping True/False
//! atoms can often be resolved immediately without exploration.

use crate::property_xml::{CtlFormula, Formula, LtlFormula, ReachabilityFormula, StatePredicate};

use super::predicate::simplify_predicate_ctx;
use super::SimplificationContext;

/// Simplify a top-level formula using a shared mutable context.
pub(crate) fn simplify_formula_ctx(
    formula: &Formula,
    ctx: &mut SimplificationContext<'_>,
) -> Formula {
    match formula {
        Formula::Reachability(r) => {
            let pred = simplify_predicate_ctx(&r.predicate, ctx);
            Formula::Reachability(ReachabilityFormula {
                quantifier: r.quantifier,
                predicate: pred,
            })
        }
        Formula::Ctl(ctl) => Formula::Ctl(simplify_ctl(ctl, ctx)),
        Formula::Ltl(ltl) => Formula::Ltl(simplify_ltl(ltl, ctx)),
        Formula::PlaceBound(_) => formula.clone(),
    }
}

/// Convenience wrapper for test code using the old `(formula, net, facts, aliases)` signature.
#[cfg(test)]
pub(crate) fn simplify_formula(
    formula: &Formula,
    net: &crate::petri_net::PetriNet,
    facts: &super::facts::SimplificationFacts,
    aliases: &crate::model::PropertyAliases,
) -> Formula {
    let mut ctx = SimplificationContext::new(net, aliases, facts.clone());
    simplify_formula_ctx(formula, &mut ctx)
}

// ---------------------------------------------------------------------------
// CTL simplification
// ---------------------------------------------------------------------------

fn simplify_ctl(ctl: &CtlFormula, ctx: &mut SimplificationContext<'_>) -> CtlFormula {
    match ctl {
        CtlFormula::Atom(pred) => CtlFormula::Atom(simplify_predicate_ctx(pred, ctx)),
        CtlFormula::Not(inner) => {
            let s = simplify_ctl(inner, ctx);
            fold_ctl_not(s)
        }
        CtlFormula::And(children) => {
            let simplified: Vec<_> = children.iter().map(|c| simplify_ctl(c, ctx)).collect();
            fold_ctl_and(simplified)
        }
        CtlFormula::Or(children) => {
            let simplified: Vec<_> = children.iter().map(|c| simplify_ctl(c, ctx)).collect();
            fold_ctl_or(simplified)
        }
        CtlFormula::EX(inner) => {
            let s = simplify_ctl(inner, ctx);
            fold_ctl_temporal_unary(s, CtlFormula::EX)
        }
        CtlFormula::AX(inner) => {
            let s = simplify_ctl(inner, ctx);
            fold_ctl_temporal_unary(s, CtlFormula::AX)
        }
        CtlFormula::EF(inner) => {
            let s = simplify_ctl(inner, ctx);
            fold_ctl_ef(s)
        }
        CtlFormula::AF(inner) => {
            let s = simplify_ctl(inner, ctx);
            fold_ctl_af(s)
        }
        CtlFormula::EG(inner) => {
            let s = simplify_ctl(inner, ctx);
            fold_ctl_eg(s)
        }
        CtlFormula::AG(inner) => {
            let s = simplify_ctl(inner, ctx);
            fold_ctl_ag(s)
        }
        CtlFormula::EU(phi, psi) => {
            let sp = simplify_ctl(phi, ctx);
            let sq = simplify_ctl(psi, ctx);
            fold_ctl_eu(sp, sq)
        }
        CtlFormula::AU(phi, psi) => {
            let sp = simplify_ctl(phi, ctx);
            let sq = simplify_ctl(psi, ctx);
            fold_ctl_au(sp, sq)
        }
    }
}

fn is_ctl_true(f: &CtlFormula) -> bool {
    matches!(f, CtlFormula::Atom(StatePredicate::True))
}

fn is_ctl_false(f: &CtlFormula) -> bool {
    matches!(f, CtlFormula::Atom(StatePredicate::False))
}

fn ctl_true() -> CtlFormula {
    CtlFormula::Atom(StatePredicate::True)
}

fn ctl_false() -> CtlFormula {
    CtlFormula::Atom(StatePredicate::False)
}

fn fold_ctl_not(inner: CtlFormula) -> CtlFormula {
    if is_ctl_true(&inner) {
        return ctl_false();
    }
    if is_ctl_false(&inner) {
        return ctl_true();
    }
    CtlFormula::Not(Box::new(inner))
}

fn fold_ctl_and(children: Vec<CtlFormula>) -> CtlFormula {
    let mut filtered = Vec::with_capacity(children.len());
    for child in children {
        if is_ctl_false(&child) {
            return ctl_false();
        }
        if !is_ctl_true(&child) {
            filtered.push(child);
        }
    }
    match filtered.len() {
        0 => ctl_true(),
        1 => filtered.into_iter().next().unwrap(),
        _ => CtlFormula::And(filtered),
    }
}

fn fold_ctl_or(children: Vec<CtlFormula>) -> CtlFormula {
    let mut filtered = Vec::with_capacity(children.len());
    for child in children {
        if is_ctl_true(&child) {
            return ctl_true();
        }
        if !is_ctl_false(&child) {
            filtered.push(child);
        }
    }
    match filtered.len() {
        0 => ctl_false(),
        1 => filtered.into_iter().next().unwrap(),
        _ => CtlFormula::Or(filtered),
    }
}

fn fold_ctl_temporal_unary(
    inner: CtlFormula,
    ctor: fn(Box<CtlFormula>) -> CtlFormula,
) -> CtlFormula {
    ctor(Box::new(inner))
}

fn fold_ctl_ef(inner: CtlFormula) -> CtlFormula {
    if is_ctl_true(&inner) {
        return ctl_true();
    }
    if is_ctl_false(&inner) {
        return ctl_false();
    }
    CtlFormula::EF(Box::new(inner))
}

fn fold_ctl_af(inner: CtlFormula) -> CtlFormula {
    if is_ctl_true(&inner) {
        return ctl_true();
    }
    if is_ctl_false(&inner) {
        return ctl_false();
    }
    CtlFormula::AF(Box::new(inner))
}

fn fold_ctl_eg(inner: CtlFormula) -> CtlFormula {
    if is_ctl_true(&inner) {
        return ctl_true();
    }
    if is_ctl_false(&inner) {
        return ctl_false();
    }
    CtlFormula::EG(Box::new(inner))
}

fn fold_ctl_ag(inner: CtlFormula) -> CtlFormula {
    if is_ctl_true(&inner) {
        return ctl_true();
    }
    if is_ctl_false(&inner) {
        return ctl_false();
    }
    CtlFormula::AG(Box::new(inner))
}

fn fold_ctl_eu(phi: CtlFormula, psi: CtlFormula) -> CtlFormula {
    if is_ctl_true(&psi) {
        return ctl_true();
    }
    if is_ctl_false(&psi) {
        return ctl_false();
    }
    if is_ctl_false(&phi) {
        return psi;
    }
    CtlFormula::EU(Box::new(phi), Box::new(psi))
}

fn fold_ctl_au(phi: CtlFormula, psi: CtlFormula) -> CtlFormula {
    if is_ctl_true(&psi) {
        return ctl_true();
    }
    if is_ctl_false(&psi) {
        return ctl_false();
    }
    if is_ctl_false(&phi) {
        return psi;
    }
    CtlFormula::AU(Box::new(phi), Box::new(psi))
}

// ---------------------------------------------------------------------------
// LTL simplification
// ---------------------------------------------------------------------------

fn simplify_ltl(ltl: &LtlFormula, ctx: &mut SimplificationContext<'_>) -> LtlFormula {
    match ltl {
        LtlFormula::Atom(pred) => LtlFormula::Atom(simplify_predicate_ctx(pred, ctx)),
        LtlFormula::Not(inner) => {
            let s = simplify_ltl(inner, ctx);
            fold_ltl_not(s)
        }
        LtlFormula::And(children) => {
            let simplified: Vec<_> = children.iter().map(|c| simplify_ltl(c, ctx)).collect();
            fold_ltl_and(simplified)
        }
        LtlFormula::Or(children) => {
            let simplified: Vec<_> = children.iter().map(|c| simplify_ltl(c, ctx)).collect();
            fold_ltl_or(simplified)
        }
        LtlFormula::Next(inner) => {
            let s = simplify_ltl(inner, ctx);
            LtlFormula::Next(Box::new(s))
        }
        LtlFormula::Finally(inner) => {
            let s = simplify_ltl(inner, ctx);
            fold_ltl_finally(s)
        }
        LtlFormula::Globally(inner) => {
            let s = simplify_ltl(inner, ctx);
            fold_ltl_globally(s)
        }
        LtlFormula::Until(phi, psi) => {
            let sp = simplify_ltl(phi, ctx);
            let sq = simplify_ltl(psi, ctx);
            fold_ltl_until(sp, sq)
        }
    }
}

fn is_ltl_true(f: &LtlFormula) -> bool {
    matches!(f, LtlFormula::Atom(StatePredicate::True))
}

fn is_ltl_false(f: &LtlFormula) -> bool {
    matches!(f, LtlFormula::Atom(StatePredicate::False))
}

fn ltl_true() -> LtlFormula {
    LtlFormula::Atom(StatePredicate::True)
}

fn ltl_false() -> LtlFormula {
    LtlFormula::Atom(StatePredicate::False)
}

fn fold_ltl_not(inner: LtlFormula) -> LtlFormula {
    if is_ltl_true(&inner) {
        return ltl_false();
    }
    if is_ltl_false(&inner) {
        return ltl_true();
    }
    LtlFormula::Not(Box::new(inner))
}

fn fold_ltl_and(children: Vec<LtlFormula>) -> LtlFormula {
    let mut filtered = Vec::with_capacity(children.len());
    for child in children {
        if is_ltl_false(&child) {
            return ltl_false();
        }
        if !is_ltl_true(&child) {
            filtered.push(child);
        }
    }
    match filtered.len() {
        0 => ltl_true(),
        1 => filtered.into_iter().next().unwrap(),
        _ => LtlFormula::And(filtered),
    }
}

fn fold_ltl_or(children: Vec<LtlFormula>) -> LtlFormula {
    let mut filtered = Vec::with_capacity(children.len());
    for child in children {
        if is_ltl_true(&child) {
            return ltl_true();
        }
        if !is_ltl_false(&child) {
            filtered.push(child);
        }
    }
    match filtered.len() {
        0 => ltl_false(),
        1 => filtered.into_iter().next().unwrap(),
        _ => LtlFormula::Or(filtered),
    }
}

fn fold_ltl_finally(inner: LtlFormula) -> LtlFormula {
    if is_ltl_true(&inner) {
        return ltl_true();
    }
    if is_ltl_false(&inner) {
        return ltl_false();
    }
    LtlFormula::Finally(Box::new(inner))
}

fn fold_ltl_globally(inner: LtlFormula) -> LtlFormula {
    if is_ltl_true(&inner) {
        return ltl_true();
    }
    if is_ltl_false(&inner) {
        return ltl_false();
    }
    LtlFormula::Globally(Box::new(inner))
}

fn fold_ltl_until(phi: LtlFormula, psi: LtlFormula) -> LtlFormula {
    if is_ltl_true(&psi) {
        return ltl_true();
    }
    if is_ltl_false(&psi) {
        return ltl_false();
    }
    if is_ltl_false(&phi) {
        return psi;
    }
    LtlFormula::Until(Box::new(phi), Box::new(psi))
}
