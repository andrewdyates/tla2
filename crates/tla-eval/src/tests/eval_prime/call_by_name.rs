// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tier 2: Call-by-name substitution tests for eval_prime.

use super::*;

// ==========================================================================
// Tier 2: Call-by-name substitution — x' → (expr)'
// ==========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier2_call_by_name_substitution() {
    // When x has a call-by-name substitution x -> expr, x' should become (expr)'.
    let mut ctx = EvalCtx::new();
    ctx.register_var("y");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(99)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    // x -> y, so x' becomes y' which should resolve to 99
    let ctx_with_cbn = ctx.with_call_by_name_subs(vec![Substitution {
        from: Spanned::dummy("x".to_string()),
        to: Spanned::dummy(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
    }]);

    let result = eval_str_with_ctx("x'", &ctx_with_cbn).expect("x'");
    assert_eq!(
        result,
        Value::int(99),
        "call-by-name sub x->y should make x' resolve to y'=99"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier2_call_by_name_no_match_falls_through() {
    // Call-by-name substitution that doesn't match should fall through to Tier 1.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(42)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    // Substitution for "other", not "x"
    let ctx_with_cbn = ctx.with_call_by_name_subs(vec![Substitution {
        from: Spanned::dummy("other".to_string()),
        to: Spanned::dummy(Expr::Int(999.into())),
    }]);

    let result = eval_str_with_ctx("x'", &ctx_with_cbn).expect("x'");
    assert_eq!(
        result,
        Value::int(42),
        "non-matching call-by-name sub should fall through to array fast path"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier2_call_by_name_blocks_tier1_fast_path() {
    // When x has a call-by-name sub, Tier 1 should be bypassed even with
    // next_state_env set. The CBN path (Tier 2) should handle it.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    let state = vec![Value::int(1), Value::int(2)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(10), Value::int(20)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    // x -> y substitution
    let ctx_with_cbn = ctx.with_call_by_name_subs(vec![Substitution {
        from: Spanned::dummy("x".to_string()),
        to: Spanned::dummy(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
    }]);

    let result = eval_str_with_ctx("x'", &ctx_with_cbn).expect("x'");
    // x' -> (y)' -> y' -> next_state_env[1] = 20
    assert_eq!(
        result,
        Value::int(20),
        "call-by-name x->y should resolve x' to y' = 20, not x' = 10"
    );
}
