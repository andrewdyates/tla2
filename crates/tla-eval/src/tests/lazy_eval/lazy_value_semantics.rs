// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_lazy_func_apply_recovers_from_poisoned_memo_lock() {
    let lazy_value = eval_str(r#"[x \in Nat |-> x]"#).unwrap();
    let Value::LazyFunc(ref lazy) = lazy_value else {
        panic!("expected lazy function");
    };

    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        lazy.with_memo_lock(|_| panic!("intentional poison"));
    }));
    assert!(lazy.memo_is_poisoned(), "memo lock should be poisoned");

    let module_src = "---- MODULE Test ----\n\nOp == f[1]\n\n====";
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result
        .module
        .expect("lower module for poisoned memo apply test");

    let op_body = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Op" => Some(&def.body),
            _ => None,
        })
        .expect("Op definition exists");

    let ctx = EvalCtx::new().bind_local("f", Value::LazyFunc(lazy.clone()));
    let result = eval(&ctx, op_body).expect("poisoned memo should not fail evaluation");
    assert_eq!(result, Value::int(1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_lazy_func_except_recovers_from_poisoned_memo_lock() {
    let lazy_value = eval_str(r#"[x \in Nat |-> x]"#).unwrap();
    let Value::LazyFunc(ref lazy) = lazy_value else {
        panic!("expected lazy function");
    };

    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        lazy.with_memo_lock(|_| panic!("intentional poison"));
    }));
    assert!(lazy.memo_is_poisoned(), "memo lock should be poisoned");

    let ctx = EvalCtx::new().bind_local("f", Value::LazyFunc(lazy.clone()));
    let result = eval_str_with_ctx(r#"[f EXCEPT ![1] = 42][1]"#, &ctx)
        .expect("poisoned memo should not fail lazy EXCEPT evaluation");
    assert_eq!(result, Value::int(42));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_random_element_accepts_lazy_sets() {
    let elem = eval_str(r#"RandomElement(SUBSET {1,2})"#).unwrap();
    let powerset = eval_str(r#"SUBSET {1,2}"#).unwrap();
    assert_eq!(powerset.set_contains(&elem), Some(true));
}

#[cfg_attr(test, ntest::timeout(1000))]
#[test]
fn test_eval_let_zero_arg_is_lazy_under_short_circuit_or() {
    // Part of #562: Zero-arg LET definitions must be lazy, matching TLC's LazyValue semantics.
    // If `x` were evaluated eagerly, this would error (CHOOSE from {}), but because the OR
    // short-circuits on TRUE, `x` must never be forced.
    let v = eval_str(r#"LET x == CHOOSE p \in {} : TRUE IN TRUE \/ (x = 0)"#).unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(1000))]
#[test]
fn test_eval_let_zero_arg_is_lazy_under_short_circuit_and() {
    // Dual of the OR case: AND must short-circuit on FALSE, so the RHS must not be forced.
    let v = eval_str(r#"LET x == CHOOSE p \in {} : TRUE IN FALSE /\ (x = 0)"#).unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(1000))]
#[test]
fn test_eval_let_zero_arg_is_lazy_under_if_branch_selection() {
    // IF must evaluate only the selected branch; `x` must never be forced here.
    let v =
        eval_str(r#"LET x == CHOOSE p \in {} : TRUE IN IF TRUE THEN TRUE ELSE (x = 0)"#).unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(1000))]
#[test]
fn test_eval_let_zero_arg_is_lazy_when_unused() {
    // Even if the bound name is never referenced, the definition must remain unforced.
    let v = eval_str(r#"LET x == CHOOSE p \in {} : TRUE IN TRUE"#).unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(2000))]
#[test]
fn test_eval_let_zero_arg_caching_multiple_references() {
    // Part of #607: Multiple references to the same LET binding should evaluate only once.
    // Use a simple expression that would be slow to re-evaluate many times.
    let v = eval_str(
        r#"LET expensive == Cardinality({s \in SUBSET {1,2,3,4} : TRUE})
           IN expensive + expensive + expensive + expensive = 64"#,
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_apply_builtin_operator_via_replacement() {
    let module_src = "---- MODULE Test ----\n\nOp == Plus(1, 2)\n\n====";
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("Expected module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.add_op_replacement("Plus".to_string(), "+".to_string());

    assert_eq!(ctx.eval_op("Op").unwrap(), Value::int(3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_apply_uses_closure_from_lookup_binding() {
    // Regression for eval_apply() lookup path: when an identifier resolves to a
    // closure in the current environment, apply_closure must run before op lookup.
    let closure = eval_str("LAMBDA x : x + 1").unwrap();
    let ctx = EvalCtx::new().bind("F", closure);
    assert_eq!(eval_str_with_ctx("F(2)", &ctx).unwrap(), Value::int(3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_apply_nonclosure_lookup_falls_through_to_local_operator() {
    // Regression for eval_apply() non-closure lookup path: a non-closure value
    // bound to an operator name must not block local-operator resolution.
    let ctx = EvalCtx::new().bind("Foo", Value::int(99));
    let v = eval_str_with_ctx("LET Foo(x) == x + 1 IN Foo(2)", &ctx).unwrap();
    assert_eq!(v, Value::int(3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_prime_of_derived_operator_uses_next_state_env() {
    // Prime should work for non-variable expressions like `Foo'` where Foo is a zero-arg
    // operator (e.g., a derived view over variables).
    let src = r#"
---- MODULE Test ----
Foo == x
Op == Foo'
===="#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("lower produced no module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.bind_mut("x", Value::int(1));

    let mut next = Env::new();
    next.insert(Arc::from("x"), Value::int(2));
    ctx.stable_mut().next_state = Some(Arc::new(next));

    let op_def = ctx.get_op("Op").expect("Op not found").clone();
    let v = eval(&ctx, &op_def.body).unwrap();
    assert_eq!(v, Value::int(2));
}
