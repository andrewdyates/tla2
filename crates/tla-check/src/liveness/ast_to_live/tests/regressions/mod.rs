// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bug-specific regression tests: #1744, #2117, #2434, #2806 eval_speculative Err paths
//!
//! Split from liveness/ast_to_live/tests.rs — Part of #2779

use super::helpers::make_ctx;
use super::*;
use crate::eval::OpEnv;
use tla_core::ast::{OperatorDef, Substitution};

pub(super) fn ident_expr(name: &str) -> Expr {
    Expr::Ident(name.to_string(), tla_core::name_intern::NameId::INVALID)
}

pub(super) fn zero_arg_operator(name: &str, body: Expr, contains_prime: bool) -> Arc<OperatorDef> {
    Arc::new(OperatorDef {
        name: Spanned::dummy(name.to_string()),
        params: vec![],
        body: Spanned::dummy(body),
        local: false,
        contains_prime,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    })
}

pub(super) fn ctx_with_instance_bool(ops: OpEnv, value: bool) -> EvalCtx {
    EvalCtx::new()
        .with_local_ops(ops)
        .with_instance_substitutions(vec![Substitution {
            from: Spanned::dummy("inst_x".to_string()),
            to: Spanned::dummy(Expr::Bool(value)),
        }])
}

pub(super) fn assert_always_bool(live: &LiveExpr, expected: bool) {
    let LiveExpr::Always(inner) = live else {
        panic!("Expected Always, got: {live:?}");
    };
    assert!(
        matches!(inner.as_ref(), LiveExpr::Bool(value) if *value == expected),
        "Expected Always(Bool({expected})), got: {live:?}"
    );
}

pub(super) fn assert_named_level(conv: &AstToLive, ctx: &EvalCtx, name: &str, expected: ExprLevel) {
    let level = conv.get_level_with_ctx(ctx, &ident_expr(name));
    assert_eq!(
        level, expected,
        "{name} level should be {expected:?}, got: {level:?}"
    );
}

mod error_handling;
mod instance_scope;
