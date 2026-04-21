// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for RAII guard types in `eval_ctx_guards.rs`.
//!
//! These tests verify that `NextStateEnvGuard`, `ExplicitNextStateGuard`,
//! `SkipPrimeValidationGuard`, and `ScopeGuard` correctly restore EvalCtx
//! state on both normal drop and panic unwind. Complements the existing
//! `StateEnvGuard` test in `lazy_eval.rs`.

use super::*;

// ---- NextStateEnvGuard ----

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_env_guard_restores_on_normal_drop() {
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let base_next = vec![Value::int(10)];
    let inner_next = vec![Value::int(20)];

    // Bind base next-state
    let _base_guard = ctx.bind_next_state_array_guard(&base_next);
    assert!(
        ctx.has_next_state_env(),
        "next_state_env should be bound after base guard"
    );

    {
        // Bind inner next-state inside a scope
        let _inner_guard = ctx.bind_next_state_array_guard(&inner_next);
        // While inner guard is alive, next_state_env points to inner_next
    }
    // After inner guard drops, next_state_env should be restored to base_next.
    // Verify by evaluating x' which reads from next_state_env.
    let result = eval_str_with_ctx("x'", &ctx).expect("x' should evaluate to base next-state");
    assert_eq!(
        result,
        Value::int(10),
        "next_state_env should restore to 10 after inner guard drops"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_next_state_env_guard_restores_on_panic_unwind() {
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let base_next = vec![Value::int(10)];
    let panic_next = vec![Value::int(99)];

    let _base_guard = ctx.bind_next_state_array_guard(&base_next);

    let unwind_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _panic_guard = ctx.bind_next_state_array_guard(&panic_next);
        // Verify the panic state is active
        let during = eval_str_with_ctx("x'", &ctx).expect("x' should evaluate during panic guard");
        assert_eq!(during, Value::int(99));
        panic!("intentional unwind to exercise NextStateEnvGuard::drop");
    }));
    assert!(unwind_result.is_err(), "panic should be caught");

    let after = eval_str_with_ctx("x'", &ctx).expect("next_state_env should restore after unwind");
    assert_eq!(
        after,
        Value::int(10),
        "next_state_env should restore to base after panic"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_take_next_state_env_guard_clears_and_restores() {
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let base_next = vec![Value::int(42)];

    let _base_guard = ctx.bind_next_state_array_guard(&base_next);
    assert!(
        ctx.has_next_state_env(),
        "should have next_state_env after bind"
    );

    {
        let _take_guard = ctx.take_next_state_env_guard();
        assert!(
            !ctx.has_next_state_env(),
            "take_next_state_env_guard should clear next_state_env"
        );
    }
    // After take guard drops, next_state_env should be restored
    assert!(
        ctx.has_next_state_env(),
        "next_state_env should be restored after take guard drops"
    );
    let result = eval_str_with_ctx("x'", &ctx).expect("x' should evaluate after take guard drops");
    assert_eq!(result, Value::int(42));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_explicit_next_state_guard_overrides_array_next_state_and_restores_on_drop() {
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let base_next = vec![Value::int(10)];

    let _base_guard = ctx.bind_next_state_array_guard(&base_next);
    let baseline = eval_str_with_ctx("x'", &ctx).expect("x' should read the array next-state");
    assert_eq!(baseline, Value::int(10));

    {
        let mut explicit_next = Env::default();
        explicit_next.insert(Arc::from("x"), Value::int(20));
        let _explicit_guard = ctx.bind_explicit_next_state_guard(explicit_next);
        let during = eval_str_with_ctx("x'", &ctx).expect("x' should read the explicit next-state");
        assert_eq!(
            during,
            Value::int(20),
            "explicit guard must override the array next-state while active"
        );
    }

    let after =
        eval_str_with_ctx("x'", &ctx).expect("x' should restore the array next-state on drop");
    assert_eq!(
        after,
        Value::int(10),
        "explicit next-state guard should restore the outer array next-state"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_explicit_next_state_guard_restores_on_panic_unwind() {
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let mut base_next = Env::default();
    base_next.insert(Arc::from("x"), Value::int(7));
    ctx.set_next_state(base_next);

    let unwind_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut explicit_next = Env::default();
        explicit_next.insert(Arc::from("x"), Value::int(99));
        let _guard = ctx.bind_explicit_next_state_guard(explicit_next);
        let during =
            eval_str_with_ctx("x'", &ctx).expect("x' should evaluate during explicit guard");
        assert_eq!(during, Value::int(99));
        panic!("intentional unwind to exercise ExplicitNextStateGuard::drop");
    }));
    assert!(unwind_result.is_err(), "panic should be caught");

    let after =
        eval_str_with_ctx("x'", &ctx).expect("x' should restore the base explicit next-state");
    assert_eq!(
        after,
        Value::int(7),
        "explicit next-state should restore after panic unwind"
    );
}

// ---- SkipPrimeValidationGuard ----

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_skip_prime_guard_restores_false_on_normal_drop() {
    let mut ctx = EvalCtx::new();
    assert!(!ctx.skip_prime_validation(), "default should be false");

    {
        let _guard = ctx.skip_prime_guard(true);
        assert!(
            ctx.skip_prime_validation(),
            "skip_prime_validation should be true while guard is alive"
        );
    }
    assert!(
        !ctx.skip_prime_validation(),
        "skip_prime_validation should restore to false after guard drops"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_skip_prime_guard_restores_true_on_normal_drop() {
    let mut ctx = EvalCtx::new();
    ctx.set_skip_prime_validation(true);
    assert!(ctx.skip_prime_validation(), "precondition: should be true");

    {
        // Guard with should_skip=false: leaves current value unchanged
        let guard = ctx.skip_prime_guard(false);
        assert!(
            ctx.skip_prime_validation(),
            "should_skip=false should not change current value"
        );
        assert!(guard.prev(), "prev() should return the saved true value");
    }
    assert!(
        ctx.skip_prime_validation(),
        "skip_prime_validation should still be true after guard drops"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_skip_prime_guard_restores_on_panic_unwind() {
    let mut ctx = EvalCtx::new();
    assert!(!ctx.skip_prime_validation(), "default should be false");

    let unwind_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = ctx.skip_prime_guard(true);
        assert!(ctx.skip_prime_validation(), "should be true during guard");
        panic!("intentional unwind to exercise SkipPrimeValidationGuard::drop");
    }));
    assert!(unwind_result.is_err(), "panic should be caught");

    assert!(
        !ctx.skip_prime_validation(),
        "skip_prime_validation should restore to false after panic unwind"
    );
}

// ---- ScopeGuard ----

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scope_guard_restores_env_on_normal_drop() {
    let mut ctx = EvalCtx::new();
    let key: Arc<str> = Arc::from("x");
    ctx.env_mut().insert(Arc::clone(&key), Value::int(1));
    assert_eq!(
        ctx.env().get(&key),
        Some(&Value::int(1)),
        "precondition: env has x=1"
    );

    {
        let _guard = ctx.scope_guard();
        // Modify env while guard is alive
        ctx.env_mut().insert(Arc::clone(&key), Value::int(999));
        assert_eq!(
            ctx.env().get(&key),
            Some(&Value::int(999)),
            "env should have x=999 during guard"
        );
    }
    // After guard drops, env should be restored
    assert_eq!(
        ctx.env().get(&key),
        Some(&Value::int(1)),
        "env should restore to x=1 after scope guard drops"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scope_guard_restores_env_on_panic_unwind() {
    let mut ctx = EvalCtx::new();
    let key: Arc<str> = Arc::from("x");
    ctx.env_mut().insert(Arc::clone(&key), Value::int(1));

    let unwind_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = ctx.scope_guard();
        ctx.env_mut().insert(Arc::clone(&key), Value::int(999));
        assert_eq!(ctx.env().get(&key), Some(&Value::int(999)));
        panic!("intentional unwind to exercise ScopeGuard::drop");
    }));
    assert!(unwind_result.is_err(), "panic should be caught");

    assert_eq!(
        ctx.env().get(&key),
        Some(&Value::int(1)),
        "env should restore to x=1 after panic unwind"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scope_guard_with_next_state_restores_both() {
    let mut ctx = EvalCtx::new();
    let key: Arc<str> = Arc::from("y");
    assert!(ctx.env().get(&key).is_none(), "precondition: env has no y");
    assert!(
        ctx.next_state().is_none(),
        "next_state should be None initially"
    );

    {
        let _guard = ctx.scope_guard_with_next_state();
        // Modify both env and next_state while guard is alive
        ctx.env_mut().insert(Arc::clone(&key), Value::int(42));
        ctx.set_next_state(crate::Env::default());
        assert!(ctx.env().get(&key).is_some(), "y should exist during guard");
        assert!(
            ctx.next_state().is_some(),
            "next_state should be Some during guard"
        );
    }
    // Both should be restored
    assert!(
        ctx.env().get(&key).is_none(),
        "env should not contain y after scope_guard_with_next_state drops"
    );
    assert!(
        ctx.next_state().is_none(),
        "next_state should be restored to None after scope_guard_with_next_state drops"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scope_guard_with_next_state_restores_on_panic_unwind() {
    let mut ctx = EvalCtx::new();
    let key: Arc<str> = Arc::from("z");
    assert!(ctx.next_state().is_none(), "precondition");

    let unwind_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = ctx.scope_guard_with_next_state();
        ctx.env_mut().insert(Arc::clone(&key), Value::int(77));
        ctx.set_next_state(crate::Env::default());
        panic!("intentional unwind to exercise ScopeGuard::drop with next_state");
    }));
    assert!(unwind_result.is_err(), "panic should be caught");

    assert!(
        ctx.env().get(&key).is_none(),
        "env should not contain z after panic unwind"
    );
    assert!(
        ctx.next_state().is_none(),
        "next_state should be restored to None after panic unwind"
    );
}
