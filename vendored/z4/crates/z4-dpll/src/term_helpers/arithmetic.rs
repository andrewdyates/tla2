// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[cfg(not(kani))]
use hashbrown::HashSet;
#[cfg(kani)]
use z4_core::kani_compat::DetHashSet as HashSet;
use z4_core::term::{Constant, Symbol, TermData};
use z4_core::{Sort, TermId, TermStore};

/// Check if a term is a "pure arithmetic" term that LIA can represent.
///
/// Returns true if the term is:
/// - An integer/rational constant
/// - A variable of Int/Real sort
/// - An arithmetic operation (+, -, *, /) applied to pure arithmetic terms
///
/// Returns false if the term contains uninterpreted function applications.
pub(super) fn is_pure_arithmetic_term(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Const(Constant::Int(_) | Constant::Rational(_)) => true,
        TermData::Var(_, _) => matches!(terms.sort(term), Sort::Int | Sort::Real),
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" | "-" | "*" | "/" | "to_real" | "to_int" | "div" | "mod" | "abs" => {
                args.iter().all(|&arg| is_pure_arithmetic_term(terms, arg))
            }
            _ => false,
        },
        _ => false,
    }
}

/// Check if a term is LIA-relevant for equality routing (#5041).
pub(super) fn is_lia_relevant_term(terms: &TermStore, term: TermId) -> bool {
    if is_pure_arithmetic_term(terms, term) {
        return true;
    }
    if let TermData::App(Symbol::Named(name), _) = terms.get(term) {
        if name == "select" && matches!(terms.sort(term), Sort::Int) {
            return true;
        }
    }
    false
}

/// Check whether a term should be routed to arithmetic solvers.
pub(crate) fn contains_arithmetic_ops(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => {
            if matches!(name.as_str(), "<" | "<=" | ">" | ">=") {
                return true;
            }
            if matches!(name.as_str(), "+" | "-" | "*" | "/") {
                return true;
            }
            if name == "=" && args.len() == 2 {
                return is_lia_relevant_term(terms, args[0])
                    && is_lia_relevant_term(terms, args[1]);
            }
            if name == "distinct" && args.iter().all(|&arg| is_lia_relevant_term(terms, arg)) {
                return true;
            }
            false
        }
        TermData::Not(inner) => contains_arithmetic_ops(terms, *inner),
        TermData::Ite(_, t, e) => {
            contains_arithmetic_ops(terms, *t) || contains_arithmetic_ops(terms, *e)
        }
        _ => false,
    }
}

/// Check if a term contains string-int bridge operations that require LIA.
pub(crate) fn contains_string_ops(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => {
            if matches!(
                name.as_str(),
                "str.len"
                    | "str.indexof"
                    | "str.to_int"
                    | "str.to.int"
                    | "str.from_int"
                    | "int.to.str"
                    | "str.replace"
                    | "str.replace_all"
                    | "str.substr"
            ) {
                return true;
            }
            if matches!(name.as_str(), "str.to_code" | "str.from_code") {
                return !is_ground_term(terms, term);
            }
            if matches!(
                name.as_str(),
                "str.contains" | "str.prefixof" | "str.suffixof"
            ) && !is_ground_term(terms, term)
            {
                return true;
            }
            if name == "="
                && args.len() == 2
                && matches!(terms.sort(args[0]), Sort::String)
                && (is_absorbing_concat_eq(terms, args[0], args[1])
                    || is_absorbing_concat_eq(terms, args[1], args[0]))
            {
                return true;
            }
            args.iter().any(|&arg| contains_string_ops(terms, arg))
        }
        TermData::Not(inner) => contains_string_ops(terms, *inner),
        TermData::Ite(c, t, e) => {
            contains_string_ops(terms, *c)
                || contains_string_ops(terms, *t)
                || contains_string_ops(terms, *e)
        }
        _ => false,
    }
}

/// Check if a term contains seq-int bridge operations that require LIA.
pub(crate) fn contains_seq_len_ops(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => {
            if name == "seq.len" {
                return true;
            }
            if name == "=" && args.len() == 2 {
                return contains_seq_len_ops(terms, args[0])
                    || contains_seq_len_ops(terms, args[1]);
            }
            if matches!(
                name.as_str(),
                "<" | "<=" | ">" | ">=" | "+" | "-" | "*" | "/" | "div" | "mod" | "abs"
            ) {
                return args.iter().any(|&arg| contains_seq_len_ops(terms, arg));
            }
            false
        }
        TermData::Not(inner) => contains_seq_len_ops(terms, *inner),
        _ => false,
    }
}

/// Check if `lhs = rhs` is an absorbing concat equation where `lhs` appears
/// inside a `str.++` on the `rhs` side.
pub(super) fn is_absorbing_concat_eq(terms: &TermStore, lhs: TermId, rhs: TermId) -> bool {
    if matches!(terms.get(lhs), TermData::Const(_)) {
        return false;
    }
    match terms.get(rhs) {
        TermData::App(Symbol::Named(name), args) if name == "str.++" => args
            .iter()
            .any(|&arg| arg == lhs || is_absorbing_concat_eq(terms, lhs, arg)),
        _ => false,
    }
}

/// Check whether a term is ground (contains no free variables).
pub(super) fn is_ground_term(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Var(..) | TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => {
            false
        }
        TermData::Const(_) => true,
        TermData::App(_, args) => args.iter().all(|&arg| is_ground_term(terms, arg)),
        TermData::Not(inner) => is_ground_term(terms, *inner),
        TermData::Ite(c, t, e) => [*c, *t, *e].into_iter().all(|id| is_ground_term(terms, id)),
        other => unreachable!("unhandled TermData variant in is_ground_term(): {other:?}"),
    }
}

/// Check if a literal could affect the array sub-solver's state.
pub(crate) fn involves_array(terms: &TermStore, term: TermId) -> bool {
    let inner = match terms.get(term) {
        TermData::Not(inner) => *inner,
        _ => term,
    };
    if matches!(terms.sort(inner), Sort::Array(_)) {
        return true;
    }
    match terms.get(inner) {
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "select" | "store" => true,
            "=" | "distinct" => true,
            _ => args
                .iter()
                .any(|&arg| matches!(terms.sort(arg), Sort::Array(_))),
        },
        _ => false,
    }
}

/// Check if a term involves Int-sorted arithmetic operands.
pub(crate) fn involves_int_arithmetic(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => {
            if matches!(name.as_str(), "<" | "<=" | ">" | ">=") && args.len() == 2 {
                return matches!(terms.sort(args[0]), Sort::Int)
                    || matches!(terms.sort(args[1]), Sort::Int);
            }
            if name == "=" && args.len() == 2 {
                let has_int = matches!(terms.sort(args[0]), Sort::Int)
                    || matches!(terms.sort(args[1]), Sort::Int);
                if !has_int {
                    return false;
                }
                return is_lia_relevant_term(terms, args[0])
                    && is_lia_relevant_term(terms, args[1]);
            }
            if matches!(name.as_str(), "+" | "-" | "*" | "/") {
                return matches!(terms.sort(term), Sort::Int);
            }
            if name == "distinct" {
                let has_int = args.iter().any(|&arg| matches!(terms.sort(arg), Sort::Int));
                let all_pure = args.iter().all(|&arg| is_lia_relevant_term(terms, arg));
                return has_int && all_pure;
            }
            false
        }
        TermData::Const(Constant::Int(_)) => true,
        TermData::Var(_, _) => matches!(terms.sort(term), Sort::Int),
        TermData::Not(inner) => involves_int_arithmetic(terms, *inner),
        _ => false,
    }
}

/// Check if ANY assertion contains substantive integer arithmetic constraints.
pub(crate) fn has_substantive_int_constraints(terms: &TermStore, assertions: &[TermId]) -> bool {
    fn check_term(terms: &TermStore, term: TermId, visited: &mut HashSet<TermId>) -> bool {
        if !visited.insert(term) {
            return false;
        }
        match terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                if matches!(name.as_str(), "<" | "<=" | ">" | ">=")
                    && args.len() == 2
                    && (matches!(terms.sort(args[0]), Sort::Int)
                        || matches!(terms.sort(args[1]), Sort::Int))
                {
                    return true;
                }
                if matches!(
                    name.as_str(),
                    "+" | "-" | "*" | "/" | "mod" | "div" | "rem" | "abs"
                ) && matches!(terms.sort(term), Sort::Int)
                {
                    return true;
                }
                if name == "distinct"
                    && args.iter().any(|&arg| matches!(terms.sort(arg), Sort::Int))
                {
                    return true;
                }
                args.iter().any(|&arg| check_term(terms, arg, visited))
            }
            TermData::Const(Constant::Int(_)) => false,
            TermData::Not(inner) => check_term(terms, *inner, visited),
            TermData::Ite(c, t, e) => {
                check_term(terms, *c, visited)
                    || check_term(terms, *t, visited)
                    || check_term(terms, *e, visited)
            }
            _ => false,
        }
    }

    let mut visited = HashSet::new();
    assertions
        .iter()
        .any(|&a| check_term(terms, a, &mut visited))
}

/// Check if a term is LRA-relevant for equality routing (#5041).
pub(super) fn is_lra_relevant_term(terms: &TermStore, term: TermId) -> bool {
    if is_pure_arithmetic_term(terms, term) {
        return true;
    }
    if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
        if name == "select" && matches!(terms.sort(term), Sort::Real) {
            return true;
        }
        if name == "to_real" && args.len() == 1 {
            if let TermData::App(Symbol::Named(inner_name), _) = terms.get(args[0]) {
                if inner_name == "select" {
                    return true;
                }
            }
        }
    }
    false
}

/// Check if a term involves Real-sorted arithmetic operands.
pub(crate) fn involves_real_arithmetic(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => {
            if matches!(name.as_str(), "<" | "<=" | ">" | ">=") && args.len() == 2 {
                return matches!(terms.sort(args[0]), Sort::Real)
                    || matches!(terms.sort(args[1]), Sort::Real);
            }
            if name == "=" && args.len() == 2 {
                let has_real = matches!(terms.sort(args[0]), Sort::Real)
                    || matches!(terms.sort(args[1]), Sort::Real);
                if !has_real {
                    return false;
                }
                return is_lra_relevant_term(terms, args[0])
                    && is_lra_relevant_term(terms, args[1]);
            }
            if matches!(name.as_str(), "+" | "-" | "*" | "/") {
                return matches!(terms.sort(term), Sort::Real);
            }
            if name == "distinct" {
                let has_real = args
                    .iter()
                    .any(|&arg| matches!(terms.sort(arg), Sort::Real));
                let all_relevant = args.iter().all(|&arg| is_lra_relevant_term(terms, arg));
                return has_real && all_relevant;
            }
            false
        }
        TermData::Const(Constant::Rational(_)) => true,
        TermData::Var(_, _) => matches!(terms.sort(term), Sort::Real),
        TermData::Not(inner) => involves_real_arithmetic(terms, *inner),
        _ => false,
    }
}

/// Check if a term has arithmetic structure (contains +, -, *, / operations).
pub(super) fn has_arithmetic_structure(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" | "-" | "*" | "/" | "div" | "mod" => true,
            _ => args.iter().any(|&a| has_arithmetic_structure(terms, a)),
        },
        _ => false,
    }
}

/// Check if a term is a `select` or `store` application.
pub(crate) fn is_select_or_store(terms: &TermStore, term: TermId) -> bool {
    if let TermData::App(ref sym, _) = terms.get(term) {
        let name = sym.name();
        name == "select" || name == "store"
    } else {
        false
    }
}

/// Check if a comparison atom's argument involves select/store terms.
pub(crate) fn arg_involves_select_or_store(terms: &TermStore, arg: TermId) -> bool {
    if is_select_or_store(terms, arg) {
        return true;
    }
    if let TermData::App(ref sym, ref inner_args) = terms.get(arg) {
        let name = sym.name();
        if name == "+" || name == "-" || name == "*" {
            return inner_args.iter().any(|&a| is_select_or_store(terms, a));
        }
    }
    false
}
