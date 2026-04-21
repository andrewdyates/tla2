// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use z4_core::term::{Symbol, TermData};
use z4_core::{Sort, TermId, TermStore};

use super::arithmetic::{is_lia_relevant_term, is_lra_relevant_term};
use super::interface_terms::involves_uninterpreted_function;

/// If `term` is an equality `(= a b)` (excluding Boolean equality), return `(a, b)`.
pub(crate) fn decode_non_bool_eq(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            let lhs = args[0];
            let rhs = args[1];
            if terms.sort(lhs) == &Sort::Bool && terms.sort(rhs) == &Sort::Bool {
                return None;
            }
            Some((lhs, rhs))
        }
        _ => None,
    }
}

/// If `term` is an `and` with exactly two non-Boolean equalities, return the two eq terms.
pub(super) fn decode_and_two_eqs(
    terms: &TermStore,
    term: TermId,
) -> Option<((TermId, TermId), (TermId, TermId))> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "and" && args.len() == 2 => {
            let eq1 = decode_non_bool_eq(terms, args[0])?;
            let eq2 = decode_non_bool_eq(terms, args[1])?;
            Some((eq1, eq2))
        }
        _ => None,
    }
}

/// If two equalities form a length-2 chain `a=b` and `b=c`, return `(a, c)` (canonical order).
pub(super) fn chain_endpoints(
    eq1: (TermId, TermId),
    eq2: (TermId, TermId),
) -> Option<(TermId, TermId)> {
    let terms = [eq1.0, eq1.1, eq2.0, eq2.1];
    let mut uniq: [TermId; 4] = [terms[0], terms[0], terms[0], terms[0]];
    let mut counts: [u8; 4] = [0, 0, 0, 0];
    let mut uniq_len: usize = 0;

    for t in terms {
        let found = uniq[..uniq_len].iter().position(|&u| u == t);
        if let Some(i) = found {
            counts[i] = counts[i].saturating_add(1);
        } else {
            uniq[uniq_len] = t;
            counts[uniq_len] = 1;
            uniq_len += 1;
        }
    }

    if uniq_len != 3 {
        return None;
    }

    let mut endpoints: [TermId; 2] = [TermId(0), TermId(0)];
    let mut end_len = 0;
    for i in 0..uniq_len {
        if counts[i] == 1 {
            if end_len >= 2 {
                return None;
            }
            endpoints[end_len] = uniq[i];
            end_len += 1;
        } else if counts[i] != 2 {
            return None;
        }
    }
    if end_len != 2 {
        return None;
    }

    let [a, b] = endpoints;
    #[allow(clippy::tuple_array_conversions)]
    if a <= b {
        Some((a, b))
    } else {
        Some((b, a))
    }
}

/// Check if a literal is an Int-sorted equality involving UF subterms.
pub(crate) fn is_uf_int_equality(terms: &TermStore, literal: TermId) -> Option<(TermId, TermId)> {
    let inner = match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => literal,
    };
    let (lhs, rhs) = decode_non_bool_eq(terms, inner)?;

    if !matches!(terms.sort(lhs), Sort::Int) || !matches!(terms.sort(rhs), Sort::Int) {
        return None;
    }
    if is_lia_relevant_term(terms, lhs) && is_lia_relevant_term(terms, rhs) {
        return None;
    }

    let lhs_has_uf = involves_uninterpreted_function(terms, lhs);
    let rhs_has_uf = involves_uninterpreted_function(terms, rhs);
    if !lhs_has_uf && !rhs_has_uf {
        return None;
    }

    Some((lhs, rhs))
}

/// Detect Real-sorted equalities involving uninterpreted functions (#5050).
pub(crate) fn is_uf_real_equality(terms: &TermStore, literal: TermId) -> Option<(TermId, TermId)> {
    let inner = match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => literal,
    };
    let (lhs, rhs) = decode_non_bool_eq(terms, inner)?;

    if !matches!(terms.sort(lhs), Sort::Real) || !matches!(terms.sort(rhs), Sort::Real) {
        return None;
    }
    if is_lra_relevant_term(terms, lhs) && is_lra_relevant_term(terms, rhs) {
        return None;
    }

    let lhs_has_uf = involves_uninterpreted_function(terms, lhs);
    let rhs_has_uf = involves_uninterpreted_function(terms, rhs);
    if !lhs_has_uf && !rhs_has_uf {
        return None;
    }

    Some((lhs, rhs))
}

/// Detect Real-sorted equalities where at least one side is `select` (#5109).
pub(crate) fn is_select_real_equality(
    terms: &TermStore,
    literal: TermId,
) -> Option<(TermId, TermId)> {
    let inner = match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => literal,
    };
    let (lhs, rhs) = decode_non_bool_eq(terms, inner)?;
    if !matches!(terms.sort(lhs), Sort::Real) || !matches!(terms.sort(rhs), Sort::Real) {
        return None;
    }
    let is_select =
        |t: TermId| matches!(terms.get(t), TermData::App(Symbol::Named(n), _) if n == "select");
    if is_select(lhs) || is_select(rhs) {
        Some((lhs, rhs))
    } else {
        None
    }
}

/// Detect the EUF transitivity pattern.
pub(crate) fn or_implies_eq_endpoints(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), or_args) = terms.get(term) else {
        return None;
    };
    if name != "or" || or_args.len() != 2 {
        return None;
    }

    let (a1, a2) = decode_and_two_eqs(terms, or_args[0])?;
    let (b1, b2) = decode_and_two_eqs(terms, or_args[1])?;

    let e1 = chain_endpoints(a1, a2)?;
    let e2 = chain_endpoints(b1, b2)?;

    if e1 == e2 {
        Some(e1)
    } else {
        None
    }
}
