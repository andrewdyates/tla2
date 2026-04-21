// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for stack overflow risk in lazy membership checks.
//!
//! Part of #758: `eval_membership_lazy` historically used recursion for `Union`, and unions
//! produced by stdlib expansions can be deep enough to overflow small thread stacks.
//!
//! This test runs the membership check in a subprocess so that a stack overflow (which aborts
//! the process) is reported as a test failure rather than hard-aborting the whole suite.

use ntest::timeout;
use num_bigint::BigInt;
use std::process::Command;
use tla_check::{eval, EvalCtx, Value};
use tla_core::ast::Expr;
use tla_core::Spanned;

const CHILD_ENV: &str = "TLA2_DEEP_UNION_MEMBERSHIP_CHILD";

fn empty_set() -> Spanned<Expr> {
    Spanned::dummy(Expr::SetEnum(Vec::new()))
}

fn singleton_int(n: i64) -> Spanned<Expr> {
    Spanned::dummy(Expr::SetEnum(vec![Spanned::dummy(Expr::Int(
        BigInt::from(n),
    ))]))
}

fn deep_left_union_chain(depth: usize) -> Spanned<Expr> {
    // ((({0} ∪ {}) ∪ {}) ∪ ...) so recursive left-first traversal is depth-proportional.
    let mut expr = singleton_int(0);
    for _ in 0..depth {
        expr = Spanned::dummy(Expr::Union(Box::new(expr), Box::new(empty_set())));
    }
    expr
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn deep_union_membership_child() {
    if std::env::var_os(CHILD_ENV).is_none() {
        return;
    }

    let depth = std::env::var("TLA2_DEEP_UNION_DEPTH")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(100_000);

    let stack_size = std::env::var("TLA2_DEEP_UNION_STACK_SIZE_BYTES")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(1024 * 1024);

    let result = std::thread::Builder::new()
        .name("deep_union_membership_child".to_string())
        .stack_size(stack_size)
        .spawn(move || {
            let ctx = EvalCtx::new();
            let set_expr = deep_left_union_chain(depth);

            let elem_expr = Spanned::dummy(Expr::Int(BigInt::from(0)));
            let in_expr = Spanned::dummy(Expr::In(Box::new(elem_expr), Box::new(set_expr)));

            let v = eval(&ctx, &in_expr).expect("eval failed");
            assert_eq!(v, Value::Bool(true));

            // Avoid stack overflow in recursive Drop for a very deep UNION chain.
            // If UNION membership regresses back to recursion, we'll overflow before this point.
            std::mem::forget(in_expr);
        })
        .expect("failed to spawn child thread")
        .join();

    match result {
        Ok(()) => {}
        Err(panic_payload) => std::panic::resume_unwind(panic_payload),
    }
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn deep_union_membership_does_not_abort_on_small_stack() {
    let exe = std::env::current_exe().expect("current_exe");
    let output = Command::new(exe)
        .env(CHILD_ENV, "1")
        .arg("--exact")
        .arg("deep_union_membership_child")
        .arg("--nocapture")
        .output()
        .expect("failed to spawn child process");

    assert!(
        output.status.success(),
        "child process failed (status={:?})\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}
