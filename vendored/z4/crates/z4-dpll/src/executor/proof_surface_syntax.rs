// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface-syntax preservation helpers for Alethe proof export.

#[cfg(not(kani))]
use hashbrown::HashMap;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;
use z4_core::term::TermData;
use z4_core::{quote_symbol, TermId, TermStore};
use z4_frontend::command::{
    Constant as FrontendConstant, Sort as FrontendSort, Term as FrontendTerm,
};

pub(super) fn strip_frontend_annotations(term: &FrontendTerm) -> &FrontendTerm {
    match term {
        FrontendTerm::Annotated(inner, _) => strip_frontend_annotations(inner),
        other => other,
    }
}

pub(super) fn collect_surface_term_overrides(
    terms: &TermStore,
    canonical: TermId,
    parsed: &FrontendTerm,
    overrides: &mut HashMap<TermId, String>,
) {
    let parsed = strip_frontend_annotations(parsed);
    overrides.insert(canonical, format_frontend_term(parsed));

    if let (FrontendTerm::App(op, args), TermData::Not(inner)) = (parsed, terms.get(canonical)) {
        if op == "not" && args.len() == 1 {
            collect_surface_term_overrides(terms, *inner, &args[0], overrides);
        }
    }
}

pub(super) fn format_frontend_term(term: &FrontendTerm) -> String {
    match strip_frontend_annotations(term) {
        FrontendTerm::Const(c) => format_frontend_constant(c),
        FrontendTerm::Symbol(name) => format_frontend_symbol(name),
        FrontendTerm::App(name, args) => format_frontend_application(name, args),
        FrontendTerm::IndexedApp(name, indices, args) => {
            format_frontend_head_application(&format_indexed_head(name, indices), args)
        }
        FrontendTerm::QualifiedApp(name, sort, args) => {
            format_frontend_head_application(&format_qualified_head(name, sort), args)
        }
        FrontendTerm::Let(bindings, body) => format_frontend_let(bindings, body),
        FrontendTerm::Forall(bindings, body) => {
            format_frontend_quantifier("forall", bindings, body)
        }
        FrontendTerm::Exists(bindings, body) => {
            format_frontend_quantifier("exists", bindings, body)
        }
        FrontendTerm::Annotated(_, _) => unreachable!("annotations stripped above"),
        other => unreachable!("unsupported frontend term in proof export override: {other:?}"),
    }
}

fn format_frontend_application(name: &str, args: &[FrontendTerm]) -> String {
    format_frontend_head_application(&format_frontend_symbol(name), args)
}

fn format_frontend_head_application(head: &str, args: &[FrontendTerm]) -> String {
    if args.is_empty() {
        head.to_string()
    } else {
        let rendered_args: Vec<String> = args.iter().map(format_frontend_term).collect();
        format!("({head} {})", rendered_args.join(" "))
    }
}

fn format_indexed_head(name: &str, indices: &[String]) -> String {
    format!("(_ {} {})", format_frontend_symbol(name), indices.join(" "))
}

fn format_qualified_head(name: &str, sort: &FrontendSort) -> String {
    format!(
        "(as {} {})",
        format_frontend_symbol(name),
        format_frontend_sort(sort)
    )
}

fn format_frontend_let(bindings: &[(String, FrontendTerm)], body: &FrontendTerm) -> String {
    let rendered_bindings: Vec<String> = bindings
        .iter()
        .map(|(name, value)| format!("({} {})", quote_symbol(name), format_frontend_term(value)))
        .collect();
    format!(
        "(let ({}) {})",
        rendered_bindings.join(" "),
        format_frontend_term(body)
    )
}

fn format_frontend_quantifier(
    keyword: &str,
    bindings: &[(String, FrontendSort)],
    body: &FrontendTerm,
) -> String {
    let rendered_bindings: Vec<String> = bindings
        .iter()
        .map(|(name, sort)| format!("({} {})", quote_symbol(name), format_frontend_sort(sort)))
        .collect();
    format!(
        "({keyword} ({}) {})",
        rendered_bindings.join(" "),
        format_frontend_term(body)
    )
}

fn format_frontend_symbol(name: &str) -> String {
    if name.starts_with('(') {
        name.to_string()
    } else {
        quote_symbol(name)
    }
}

fn format_frontend_sort(sort: &FrontendSort) -> String {
    match sort {
        FrontendSort::Simple(name) => format_frontend_symbol(name),
        FrontendSort::Parameterized(name, params) => {
            let rendered_params: Vec<String> = params.iter().map(format_frontend_sort).collect();
            format!(
                "({} {})",
                format_frontend_symbol(name),
                rendered_params.join(" ")
            )
        }
        FrontendSort::Indexed(name, indices) => {
            format!("(_ {} {})", format_frontend_symbol(name), indices.join(" "))
        }
        other => unreachable!("unsupported frontend sort in proof export override: {other:?}"),
    }
}

fn format_frontend_constant(constant: &FrontendConstant) -> String {
    match constant {
        FrontendConstant::True => "true".to_string(),
        FrontendConstant::False => "false".to_string(),
        FrontendConstant::Numeral(n)
        | FrontendConstant::Decimal(n)
        | FrontendConstant::Hexadecimal(n)
        | FrontendConstant::Binary(n) => n.clone(),
        FrontendConstant::String(s) => format!("\"{}\"", s.replace('\"', "\"\"")),
        other => unreachable!("unsupported frontend constant in proof export override: {other:?}"),
    }
}
