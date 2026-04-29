// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Hoist-cache bypass, HashMap fallback, complex expression, and error tests
//! for eval_prime.

use super::*;

// ==========================================================================
// Hoist-cache bypass regression (#3147)
// ==========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_prime_ignores_cached_current_state_value_for_next_state_tuple() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(2)];
    let _next_guard = ctx.bind_next_state_array_guard(&next);

    let x_id = intern_name("x");
    let inner = Spanned::dummy(Expr::Tuple(vec![Spanned::dummy(Expr::Ident(
        "x".to_string(),
        x_id,
    ))]));
    let current_value = eval(&ctx, &inner).expect("current-state tuple should evaluate");

    let mut hoistable = FxHashSet::default();
    hoistable.insert(std::ptr::addr_of!(inner.node) as usize);
    let _hoist_guard =
        enter_quantifier_hoist_scope(Rc::new(hoistable)).expect("manual hoist scope should push");
    quantifier_hoist_store(&inner.node, &current_value);

    let next_value =
        crate::eval_prime::eval_prime(&ctx, &inner, None).expect("prime tuple should evaluate");
    let elems = next_value
        .as_seq_or_tuple_elements()
        .expect("prime result should stay tuple-like");
    assert_eq!(
        elems.as_ref(),
        &[Value::int(2)],
        "next-state tuple must bypass hoist entries recorded for the current state"
    );

    clear_for_test_reset();
}

// ==========================================================================
// Tier 4: HashMap fallback — direct lookup in next_state HashMap
// ==========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier4_hashmap_fallback_simple() {
    // Without next_state_env, eval_prime falls back to HashMap-based next_state.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.bind_mut("x", Value::int(1));

    let mut next = Env::new();
    next.insert(Arc::from("x"), Value::int(100));
    ctx.stable_mut().next_state = Some(Arc::new(next));

    let result = eval_str_with_ctx("x'", &ctx).expect("x'");
    assert_eq!(
        result,
        Value::int(100),
        "HashMap fallback should resolve x'"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier4_hashmap_fallback_multiple_vars() {
    let mut ctx = EvalCtx::new();
    ctx.register_var("a");
    ctx.register_var("b");
    ctx.bind_mut("a", Value::int(1));
    ctx.bind_mut("b", Value::int(2));

    let mut next = Env::new();
    next.insert(Arc::from("a"), Value::int(10));
    next.insert(Arc::from("b"), Value::int(20));
    ctx.stable_mut().next_state = Some(Arc::new(next));

    let ra = eval_str_with_ctx("a'", &ctx).expect("a'");
    let rb = eval_str_with_ctx("b'", &ctx).expect("b'");
    assert_eq!(ra, Value::int(10));
    assert_eq!(rb, Value::int(20));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier4_hashmap_instance_sub_blocks_lookup() {
    // With INSTANCE substitution for x, HashMap direct lookup should be bypassed.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    ctx.bind_mut("x", Value::int(1));
    ctx.bind_mut("y", Value::int(2));

    let mut next = Env::new();
    next.insert(Arc::from("x"), Value::int(10));
    next.insert(Arc::from("y"), Value::int(20));
    ctx.stable_mut().next_state = Some(Arc::new(next));

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
        "INSTANCE sub x->y should redirect x' to y' in HashMap path too"
    );
}

// ==========================================================================
// Tier 5: Complex expression path — (f(x))' etc.
// ==========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier5_complex_expression_with_next_state_env() {
    // Prime of a non-variable expression like (x + 1)' should swap next_state_env
    // into state_env and evaluate the inner expression.
    // Uses register_var + eval_str_with_ctx (not load_module + bind_mut) to avoid
    // env HashMap shadowing the array-backed state_env lookup.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(5)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(10)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    // (x + 1)' should evaluate to x' + 1 = 10 + 1 = 11
    let v = eval_str_with_ctx("(x + 1)'", &ctx).expect("(x+1)'");
    assert_eq!(
        v,
        Value::int(11),
        "complex expression (x+1)' should use next-state"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier5_complex_expression_with_hashmap_next_state() {
    // Complex expression with HashMap-based next_state (no array path).
    let src = r#"
---- MODULE Test ----
Foo == x
Op == Foo'
===="#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty());
    let module = lower_result.module.expect("no module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.bind_mut("x", Value::int(1));

    let mut next = Env::new();
    next.insert(Arc::from("x"), Value::int(2));
    ctx.stable_mut().next_state = Some(Arc::new(next));

    let op_def = ctx.get_op("Op").expect("Op not found").clone();
    let v = eval(&ctx, &op_def.body).unwrap();
    assert_eq!(
        v,
        Value::int(2),
        "Foo' with HashMap next_state should resolve to 2"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier5_complex_expression_hashmap_with_state_env_full() {
    // Complex expression with HashMap next_state AND state_env set (full coverage).
    // This exercises the "is_full_next_state" branch that clears state_env and
    // writes all next_state vars into env.
    let src = r#"
---- MODULE Test ----
VARIABLE x
Op == (x + 10)'
===="#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty());
    let module = lower_result.module.expect("no module");

    clear_for_test_reset();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");
    ctx.bind_mut("x", Value::int(5));
    let state = vec![Value::int(5)];
    ctx.bind_state_array(&state);

    // Set HashMap next_state with all vars covered (is_full_next_state=true)
    let mut next = Env::new();
    next.insert(Arc::from("x"), Value::int(100));
    ctx.stable_mut().next_state = Some(Arc::new(next));

    // Remove next_state_env so we hit the HashMap complex path
    let _ = ctx.take_next_state_env();

    let op_def = ctx.get_op("Op").expect("Op not found").clone();
    let v = eval(&ctx, &op_def.body).unwrap();
    assert_eq!(
        v,
        Value::int(110),
        "(x+10)' with full HashMap should evaluate to 110"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier5_complex_expression_hashmap_with_state_env_partial() {
    // Complex expression with partial HashMap next_state AND state_env set.
    // This exercises the partial branch that uses push_binding_preinterned.
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Op == (x + y)'
===="#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty());
    let module = lower_result.module.expect("no module");

    clear_for_test_reset();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");
    ctx.register_var("y");
    ctx.bind_mut("x", Value::int(5));
    ctx.bind_mut("y", Value::int(7));
    let state = vec![Value::int(5), Value::int(7)];
    ctx.bind_state_array(&state);

    // Only x changes — partial next_state
    let mut next = Env::new();
    next.insert(Arc::from("x"), Value::int(100));
    ctx.stable_mut().next_state = Some(Arc::new(next));

    // Remove next_state_env to force HashMap path
    let _ = ctx.take_next_state_env();

    let op_def = ctx.get_op("Op").expect("Op not found").clone();
    let v = eval(&ctx, &op_def.body).unwrap();
    // x'=100, y unchanged from current state y=7 → 100 + 7 = 107
    assert_eq!(
        v,
        Value::int(107),
        "(x+y)' with partial HashMap should use next x=100 and current y=7"
    );
}

// ==========================================================================
// Error cases
// ==========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_prime_without_next_state_returns_error() {
    // Evaluating x' without any next-state context should return PrimedVariableNotBound.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.bind_mut("x", Value::int(1));
    // No next_state or next_state_env set

    let result = eval_str_with_ctx("x'", &ctx);
    assert!(
        result.is_err(),
        "x' without next_state should fail with PrimedVariableNotBound"
    );
}
