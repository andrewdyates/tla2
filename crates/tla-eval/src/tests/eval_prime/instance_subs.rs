// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tier 3: INSTANCE substitution and SubstIn prime routing tests.

use super::*;

// ==========================================================================
// Tier 3: INSTANCE substitution — bug-fix #295
// ==========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier3_instance_substitution() {
    // When x has an INSTANCE substitution x -> y, x' should become (y)'.
    // This avoids infinite recursion by stripping instance_substitutions.
    let mut ctx = EvalCtx::new();
    ctx.register_var("y");
    let state = vec![Value::int(5)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(50)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    let ctx_with_subs = ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::dummy("x".to_string()),
        to: Spanned::dummy(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
    }]);

    let result = eval_str_with_ctx("x'", &ctx_with_subs).expect("x'");
    assert_eq!(
        result,
        Value::int(50),
        "INSTANCE sub x->y should make x' resolve to y' = 50"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier3_instance_sub_blocks_tier1_fast_path() {
    // With INSTANCE substitution, Tier 1 Ident fast path should be bypassed.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    let state = vec![Value::int(1), Value::int(2)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(10), Value::int(20)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    // x -> y substitution: x' should become y' (=20), not x' (=10)
    let ctx_with_subs = ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::dummy("x".to_string()),
        to: Spanned::dummy(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
    }]);

    let result = eval_str_with_ctx("x'", &ctx_with_subs).expect("x'");
    assert_eq!(
        result,
        Value::int(20),
        "INSTANCE sub x->y must bypass Tier 1 fast path"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier3_instance_sub_no_match_falls_through() {
    // INSTANCE substitution for "other" should not affect x' lookup.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(42)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    let ctx_with_subs = ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::dummy("other".to_string()),
        to: Spanned::dummy(Expr::Int(999.into())),
    }]);

    let result = eval_str_with_ctx("x'", &ctx_with_subs).expect("x'");
    assert_eq!(
        result,
        Value::int(42),
        "non-matching INSTANCE sub should not affect x'"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier3_instance_sub_state_var_skips_fast_path_bug_1096() {
    // BUG FIX #1096: When instance_substitutions is set, StateVar fast path
    // must be skipped entirely because VarIndex was assigned from the instanced
    // module's VarRegistry, which may differ from the current state array.
    let src = r#"
---- MODULE Test ----
VARIABLE x
Op == x'
===="#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty());
    let module = lower_result.module.expect("no module");

    clear_for_test_reset();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);

    // Set up HashMap-based next_state (used as fallback)
    let mut next_map = Env::new();
    next_map.insert(Arc::from("x"), Value::int(77));
    ctx.stable_mut().next_state = Some(Arc::new(next_map));

    // Add an INSTANCE substitution for an unrelated variable.
    // This triggers the skip at line 79 in eval_prime: when instance_substitutions
    // is Some, StateVar fast path is skipped.
    let ctx_with_subs = ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::dummy("unrelated".to_string()),
        to: Spanned::dummy(Expr::Int(0.into())),
    }]);

    // With both next_state_env and next_state set, but instance_substitutions present,
    // the StateVar path should skip Tier 1 and fall through.
    let op_def = ctx_with_subs.get_op("Op").expect("Op not found").clone();
    let v = eval(&ctx_with_subs, &op_def.body).unwrap();
    // Should still resolve x' correctly (via Tier 4 HashMap fallback after Tier 1 skip)
    assert_eq!(
        v,
        Value::int(77),
        "StateVar must skip fast path when INSTANCE subs are present"
    );
}

// ==========================================================================
// SubstIn prime routing — #3056 Phase 5, #3147
// ==========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_instance_prime_via_subst_in_lazy_binding() {
    // Part of #3056 Phase 5: INSTANCE prime access via SubstIn/LazyBinding path.
    //
    // Original test (`test_is_instance_sub_target_with_eager_bindings`) used
    // eager_subst_bindings to verify the NameId fast path in is_instance_sub_target.
    // Phase 5 removed the special-case INSTANCE prime handler from eval_prime —
    // primed access now flows through the binding chain (LazyBinding with dual
    // OnceLock: cached + cached_primed). This test verifies end-to-end INSTANCE
    // prime resolution using Expr::SubstIn, which triggers eval_dispatch's
    // SubstIn handler (build_lazy_subst_bindings → LazyBinding chain).

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    let state = vec![Value::int(1), Value::int(2)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(10), Value::int(20)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    // Build SubstIn(x -> y, x') — the production path for INSTANCE primed access.
    // The SubstIn handler creates LazyBindings: when x is looked up, the LazyBinding
    // for x captures the definition-site chain and evaluates Ident("y") in context.
    // In primed mode (StateLookupMode::Next), the cached_primed OnceLock is used.
    let subs = vec![Substitution {
        from: Spanned::dummy("x".to_string()),
        to: Spanned::dummy(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
    }];
    let inner_prime = Spanned::dummy(Expr::Prime(Box::new(Spanned::dummy(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    )))));
    let subst_in_expr = Spanned::dummy(Expr::SubstIn(subs, Box::new(inner_prime)));

    // x' inside SubstIn should be redirected via LazyBinding x->y to y' = 20.
    let result = eval(&ctx, &subst_in_expr).expect("SubstIn x' eval");
    assert_eq!(
        result,
        Value::int(20),
        "SubstIn LazyBinding should redirect x' to y' via cached_primed OnceLock"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_statevar_prime_via_subst_in_invalid_nameid_uses_substitution() {
    // Part of #3147: Some cross-module StateVar nodes can carry NameId::INVALID
    // even though the variable name is still correct. The prime fast path must
    // treat INVALID like "unknown" and fall back to the interned name instead of
    // bypassing INSTANCE substitution.
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    let state = vec![Value::int(1), Value::int(2)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(10), Value::int(20)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    let subs = vec![Substitution {
        from: Spanned::dummy("x".to_string()),
        to: Spanned::dummy(Expr::Ident("y".to_string(), NameId::INVALID)),
    }];
    let inner_prime = Spanned::dummy(Expr::Prime(Box::new(Spanned::dummy(Expr::StateVar(
        "x".to_string(),
        0,
        NameId::INVALID,
    )))));
    let subst_in_expr = Spanned::dummy(Expr::SubstIn(subs, Box::new(inner_prime)));

    let result = eval(&ctx, &subst_in_expr).expect("SubstIn x' StateVar eval");
    assert_eq!(
        result,
        Value::int(20),
        "StateVar x' with NameId::INVALID must still honor SubstIn x -> y"
    );

    clear_for_test_reset();
}
