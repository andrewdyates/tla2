// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the Rust code emitter: expression translation, code generation,
//! operator expansion, and validation.

use super::*;
use tla_core::name_intern::NameId;
use tla_core::span::{FileId, Span, Spanned};

pub(super) fn make_span() -> Span {
    Span::new(FileId(0), 0, 0)
}

pub(super) fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::new(node, make_span())
}

pub(super) fn make_counter_module() -> Module {
    use tla_core::ast::{Module, OperatorDef, Unit};

    // Build a simple counter spec:
    // VARIABLE count
    // Init == count = 0
    // Next == count' = count + 1

    let init_body = Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "count".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(0.into()))),
    );

    let next_body = Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "count".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
        Box::new(spanned(Expr::Add(
            Box::new(spanned(Expr::Ident(
                "count".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(1.into()))),
        ))),
    );

    Module {
        name: spanned("Counter".to_string()),
        extends: vec![],
        units: vec![
            spanned(Unit::Variable(vec![spanned("count".to_string())])),
            spanned(Unit::Operator(OperatorDef {
                name: spanned("Init".to_string()),
                params: vec![],
                body: spanned(init_body),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            })),
            spanned(Unit::Operator(OperatorDef {
                name: spanned("Next".to_string()),
                params: vec![],
                body: spanned(next_body),
                local: false,
                contains_prime: false,
                guards_depend_on_prime: false,
                has_primed_param: false,
                is_recursive: false,
                self_call_count: 0,
            })),
        ],
        action_subscript_spans: Default::default(),
        span: make_span(),
    }
}

mod code_generation;
mod expr_translation;
mod instance;
mod operator_expansion;
mod validation;
