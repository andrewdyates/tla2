// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use z4_core::term::{Symbol, TermData};
use z4_core::{TermId, TermStore};

use super::arithmetic::{has_arithmetic_structure, is_pure_arithmetic_term};
use super::euf_patterns::decode_non_bool_eq;

/// Check if a term involves an uninterpreted function application (#1893).
pub(super) fn involves_uninterpreted_function(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Const(_) | TermData::Var(_, _) => false,
        TermData::App(Symbol::Named(name), args) => {
            if matches!(
                name.as_str(),
                "+" | "-"
                    | "*"
                    | "/"
                    | "div"
                    | "mod"
                    | "abs"
                    | "to_real"
                    | "to_int"
                    | "<"
                    | "<="
                    | ">"
                    | ">="
                    | "="
                    | "distinct"
                    | "and"
                    | "or"
                    | "not"
                    | "=>"
                    | "ite"
                    | "select"
                    | "store"
            ) {
                args.iter()
                    .any(|&arg| involves_uninterpreted_function(terms, arg))
            } else {
                true
            }
        }
        TermData::Not(inner) => involves_uninterpreted_function(terms, *inner),
        TermData::Ite(c, t, e) => {
            involves_uninterpreted_function(terms, *c)
                || involves_uninterpreted_function(terms, *t)
                || involves_uninterpreted_function(terms, *e)
        }
        _ => false,
    }
}

/// Extract interface arithmetic term from an equality between UF and arithmetic.
pub(crate) fn extract_interface_arith_term(terms: &TermStore, literal: TermId) -> Option<TermId> {
    let inner = match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => literal,
    };
    let (lhs, rhs) = decode_non_bool_eq(terms, inner)?;

    let lhs_pure_arith = is_pure_arithmetic_term(terms, lhs);
    let rhs_pure_arith = is_pure_arithmetic_term(terms, rhs);
    let lhs_involves_uf = involves_uninterpreted_function(terms, lhs);
    let rhs_involves_uf = involves_uninterpreted_function(terms, rhs);

    if lhs_pure_arith && rhs_involves_uf {
        Some(lhs)
    } else if rhs_pure_arith && lhs_involves_uf {
        Some(rhs)
    } else {
        None
    }
}

/// Extract BOTH interface terms from a UF-arithmetic equality (#4767).
pub(crate) fn extract_uf_mixed_interface_term(
    terms: &TermStore,
    literal: TermId,
) -> Option<TermId> {
    let inner = match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => literal,
    };
    let (lhs, rhs) = decode_non_bool_eq(terms, inner)?;

    let lhs_pure_arith = is_pure_arithmetic_term(terms, lhs);
    let rhs_pure_arith = is_pure_arithmetic_term(terms, rhs);
    let lhs_involves_uf = involves_uninterpreted_function(terms, lhs);
    let rhs_involves_uf = involves_uninterpreted_function(terms, rhs);

    if rhs_involves_uf && lhs_pure_arith && !rhs_pure_arith && has_arithmetic_structure(terms, rhs)
    {
        return Some(rhs);
    }
    if lhs_involves_uf && rhs_pure_arith && !lhs_pure_arith && has_arithmetic_structure(terms, lhs)
    {
        return Some(lhs);
    }
    None
}
