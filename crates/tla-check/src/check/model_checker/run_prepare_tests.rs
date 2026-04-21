// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `precompute_constant_operators` — the setup-time constant-folding
//! pass that mirrors TLC's `SpecProcessor.processConstantDefns()`.
//!
//! Part of #3125: replaced shallow `body_references_state_var` tests with
//! semantic level classification tests against the actual precompute pass.

use crate::check::model_checker::precompute::precompute_constant_operators;
use crate::eval::EvalCtx;
use tla_core::ast::{Expr, OperatorDef};
use tla_core::name_intern::intern_name;
use tla_core::span::Spanned;

fn make_op(name: &str, body: Expr) -> OperatorDef {
    OperatorDef {
        name: Spanned::dummy(name.to_string()),
        params: vec![],
        body: Spanned::dummy(body),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    }
}

/// #3125 regression: a zero-arg wrapper (`JsonInv`) that transitively references
/// a state-level operator (`Inv`) must NOT be precomputed. The old shallow gate
/// missed this because it only checked for direct `Expr::StateVar` nodes.
#[test]
fn test_precompute_skips_transitive_state_wrapper() {
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");

    // Inv == x = 0  (state-level: references state variable x)
    let inv_body = Expr::Eq(
        Box::new(Spanned::dummy(Expr::StateVar(
            "x".to_string(),
            0,
            intern_name("x"),
        ))),
        Box::new(Spanned::dummy(Expr::Int(0.into()))),
    );
    ctx.define_op("Inv".to_string(), make_op("Inv", inv_body));

    // JsonInv == Inv  (wrapper — body is just Ident("Inv"))
    let json_inv_body = Expr::Ident("Inv".to_string(), intern_name("Inv"));
    ctx.define_op("JsonInv".to_string(), make_op("JsonInv", json_inv_body));

    precompute_constant_operators(&mut ctx);

    let name_id = intern_name("JsonInv");
    assert!(
        ctx.shared().precomputed_constants.get(&name_id).is_none(),
        "JsonInv transitively references state var x — must NOT be precomputed"
    );

    let inv_id = intern_name("Inv");
    assert!(
        ctx.shared().precomputed_constants.get(&inv_id).is_none(),
        "Inv directly references state var x — must NOT be precomputed"
    );
}

/// Genuine constant operators (no state dependency at any level) must still
/// be precomputed for O(1) lookup during BFS.
#[test]
fn test_precompute_keeps_true_constants() {
    let mut ctx = EvalCtx::new();

    // N == 3  (constant: pure integer literal)
    let n_body = Expr::Int(3.into());
    ctx.define_op("N".to_string(), make_op("N", n_body));

    precompute_constant_operators(&mut ctx);

    let name_id = intern_name("N");
    assert!(
        ctx.shared().precomputed_constants.get(&name_id).is_some(),
        "N is a pure constant — must be precomputed"
    );
}

/// A constant wrapper over a constant operator should still be precomputed.
#[test]
fn test_precompute_keeps_transitive_constant_wrapper() {
    let mut ctx = EvalCtx::new();

    // Base == 42
    let base_body = Expr::Int(42.into());
    ctx.define_op("Base".to_string(), make_op("Base", base_body));

    // Wrapper == Base  (transitively constant)
    let wrapper_body = Expr::Ident("Base".to_string(), intern_name("Base"));
    ctx.define_op("Wrapper".to_string(), make_op("Wrapper", wrapper_body));

    precompute_constant_operators(&mut ctx);

    let base_id = intern_name("Base");
    assert!(
        ctx.shared().precomputed_constants.get(&base_id).is_some(),
        "Base is constant — must be precomputed"
    );

    let wrapper_id = intern_name("Wrapper");
    assert!(
        ctx.shared()
            .precomputed_constants
            .get(&wrapper_id)
            .is_some(),
        "Wrapper transitively references only constants — must be precomputed"
    );
}
