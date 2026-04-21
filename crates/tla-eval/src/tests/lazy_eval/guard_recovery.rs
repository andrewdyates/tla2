// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::Arc;
use tla_core::name_intern::intern_name;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_op_dep_guard_unwind_pops_frame_and_dep_tracking_recovers() {
    use crate::cache::{eval_with_dep_tracking, OpDepGuard};

    let src = r#"
---- MODULE Test ----
VARIABLE x
ReadX == x
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");
    let read_x_body = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "ReadX" => {
                Some(def.body.clone())
            }
            _ => None,
        })
        .expect("ReadX operator should exist");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");
    let state = vec![Value::int(7)];
    ctx.bind_state_array(&state);

    assert!(
        ctx.runtime_state.op_dep_stack.borrow().is_empty(),
        "precondition: dep stack should start empty"
    );

    let unwind_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = OpDepGuard::from_ctx(&ctx, ctx.binding_depth);
        assert_eq!(ctx.runtime_state.op_dep_stack.borrow().len(), 1);
        assert_eq!(ctx.runtime_state.dep_tracking_depth.get(), 1);
        panic!("intentional unwind to exercise OpDepGuard::drop");
    }));
    assert!(unwind_result.is_err(), "panic should be caught");
    assert!(
        ctx.runtime_state.op_dep_stack.borrow().is_empty(),
        "OpDepGuard::drop should pop dep frame during unwind"
    );
    assert_eq!(
        ctx.runtime_state.dep_tracking_depth.get(),
        0,
        "OpDepGuard::drop should decrement dep_tracking_depth during unwind"
    );

    let (value, deps) =
        eval_with_dep_tracking(&ctx, &read_x_body).expect("dep tracking should recover");
    assert_eq!(value, Value::int(7));
    assert_eq!(
        deps.state.len(),
        1,
        "state dependency should still be tracked after unwind"
    );
    assert!(deps.next.is_empty());
    assert!(deps.local.is_empty());
    assert!(!deps.inconsistent);
    assert!(
        ctx.runtime_state.op_dep_stack.borrow().is_empty(),
        "dep stack should be empty after successful tracked evaluation"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bind_state_array_guard_restores_state_env_on_panic_unwind() {
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let base_state = vec![Value::int(7)];
    let panic_state = vec![Value::int(42)];

    let _base_guard = ctx.bind_state_array_guard(&base_state);
    let before = eval_str_with_ctx("x", &ctx).expect("base state should evaluate");
    assert_eq!(before, Value::int(7));

    let unwind_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _state_guard = ctx.bind_state_array_guard(&panic_state);
        let during = eval_str_with_ctx("x", &ctx).expect("panic state should evaluate");
        assert_eq!(during, Value::int(42));
        panic!("intentional unwind to exercise StateEnvGuard::drop");
    }));
    assert!(unwind_result.is_err(), "panic should be caught");

    let after = eval_str_with_ctx("x", &ctx).expect("state env should restore after unwind");
    assert_eq!(after, Value::int(7));
}

/// Regression test for #2761: `force_lazy_thunk_if_needed` must reset BindingChain.
///
/// When a lazy thunk (zero-arg LET closure) is forced, the BindingChain from the
/// forcing site must not leak into the thunk's evaluation context. Without the fix,
/// BindingChain entries (from ForAll/Exists/Choose quantifiers) would shadow the
/// thunk's captured definition-site bindings because BindingChain is checked FIRST
/// in eval_ident.
///
/// This test directly constructs the problematic scenario:
/// 1. A lazy thunk captures x=42 in its captured_chain (BindingChain)
/// 2. The forcing context has x=1 in BindingChain (simulating ForAll iteration)
/// 3. The thunk body evaluates Ident("x")
/// 4. Expected: x=42 (from captured chain), NOT x=1 (from BindingChain)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_force_lazy_thunk_binding_chain_isolation() {
    use crate::binding_chain::BindingChain;
    use crate::value::ClosureValue;
    use tla_core::Span;

    // Create a lazy thunk whose body is just `x`.
    // It captures x=42 in its captured_chain (BindingChain).
    let x_body = Spanned {
        node: Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
        span: Span::dummy(),
    };
    let x_name_id = intern_name("x");
    let captured_chain =
        BindingChain::from_values(vec![(Arc::from("x"), Value::int(42), x_name_id)]);
    let thunk = Value::Closure(Arc::new(
        ClosureValue::new(
            vec![], // Empty params = lazy thunk
            x_body,
            Arc::new(HashMap::new()), // captured_env (empty)
            None,                     // no local_ops
        )
        .with_captured_chain(Box::new(captured_chain), 1),
    ));

    // Build a context with x=1 in BindingChain (simulating being inside a ForAll).
    let mut ctx = EvalCtx::new();
    ctx.push_binding(Arc::from("x"), Value::int(1));

    // Bind the thunk as "val" in local_stack.
    // into_bind_local pushes to local_stack + env but NOT BindingChain,
    // so BindingChain still has x=1.
    let ctx = ctx.into_bind_local("val", thunk);

    // Evaluate "val" which triggers force_lazy_thunk_if_needed.
    // The thunk body (Ident("x")) should resolve from captured_chain (x=42),
    // not from the leaked BindingChain (x=1).
    let result = eval_str_with_ctx("val", &ctx).expect("lazy thunk forcing should succeed");

    assert_eq!(
        result,
        Value::int(42),
        "Bug #2761: BindingChain from forcing site leaked into lazy thunk. \
         Thunk body 'x' resolved to BindingChain value (x=1) instead of \
         captured definition-site binding (x=42). \
         Fix: force_lazy_thunk_if_needed must reset fctx.bindings to empty."
    );
}
