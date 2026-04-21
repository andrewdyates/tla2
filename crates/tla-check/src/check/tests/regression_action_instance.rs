// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for action instance splitting (action_instance.rs).
//!
//! These tests verify the Defer-vs-Fatal error discrimination in
//! `try_split_exists_all_bounds` — the core fix from #1886.

use crate::action_instance::split_action_instances;
use crate::EvalCtx;
use tla_core::ast::OperatorDef;
use tla_core::{lower, parse_to_syntax_tree, FileId};

fn load_and_find_op(src: &str, name: &str) -> (EvalCtx, OperatorDef) {
    let tree = parse_to_syntax_tree(src);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "unexpected lower errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.expect("lowered module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            tla_core::ast::Unit::Operator(d) if d.name.node == name => Some(d.clone()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("missing operator {name}"));
    (ctx, def)
}

/// Regression test for #1920: Verify that split_action_instances PROPAGATES
/// fatal errors from eval_iter_set when try_eval_const_level succeeds.
///
/// This exercises the Defer-vs-Fatal discrimination in `try_split_exists_all_bounds`
/// (action_instance.rs line 323-329). The domain `{n \in SUBSET {1,2} : 1}` uses
/// SUBSET (a lazy set), so `try_eval_const_level` returns `Some(Value::SetPred(...))`
/// without evaluating the predicate. Then `eval_iter_set` materializes the SetPred,
/// evaluating predicate `1` for each element → TypeError(expected: BOOLEAN) → Fatal →
/// propagated as Err.
///
/// Background: The 3 existing `test_1886_*` tests in action_instance.rs do not
/// exercise this code path because `try_eval_const_level` catches errors before
/// `eval_iter_set` runs. This is the ONLY test that exercises the Fatal return
/// path at line 328.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1920_split_fatal_error_propagated_from_lazy_setpred() {
    // SUBSET {1,2} is lazy → SetFilter over it creates a SetPred value.
    // try_eval_const_level returns Some(SetPred) — construction succeeds.
    // eval_iter_set evaluates the predicate `1` (not a boolean) → Fatal TypeError.
    let src = r#"
---- MODULE SplitFatalSetPred ----
EXTENDS FiniteSets
VARIABLE x
Next == \E v \in {n \in SUBSET {1, 2} : 1} : x' = v
====
"#;
    let (ctx, next_def) = load_and_find_op(src, "Next");
    let result = split_action_instances(&ctx, &next_def.body);
    assert!(
        result.is_err(),
        "#1920: SetPred with non-boolean predicate should propagate \
         Fatal error, not silently defer to leaf action. Got Ok({:?})",
        result.as_ref().ok().map(std::vec::Vec::len)
    );
}
