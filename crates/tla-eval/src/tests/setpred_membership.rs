// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::cache::lifecycle::clear_for_test_reset;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_setpred_membership_uses_captured_state_not_current() {
    clear_for_test_reset();

    let src = r#"
---- MODULE Test ----
EXTENDS Integers, Sequences
VARIABLE x
Filtered == {ss \in Seq({1, 2}) : Len(ss) > x}
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty(), "{:?}", lower_result.errors);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");

    let captured_state = vec![Value::int(1)];
    ctx.bind_state_array(&captured_state);
    let setpred_val = ctx.eval_op("Filtered").unwrap();

    let current_state = vec![Value::int(2)];
    ctx.bind_state_array(&current_state);

    let Value::SetPred(ref spv) = setpred_val else {
        panic!("Filtered should stay lazy over Seq domain");
    };

    let member = Value::seq([Value::int(1), Value::int(2)]);
    assert!(
        check_set_pred_membership(&ctx, &member, &spv, None).unwrap(),
        "membership must use the captured state x=1, not the current state x=2"
    );

    let non_member = Value::seq([Value::int(1)]);
    assert!(
        !check_set_pred_membership(&ctx, &non_member, &spv, None).unwrap(),
        "captured state x=1 should still reject length-1 sequences"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_setpred_membership_tuple_pattern_destructures() {
    clear_for_test_reset();

    let src = r#"
---- MODULE Test ----
EXTENDS Integers
VARIABLE x
Filtered == {<<a, b>> \in {1, 2} \X {3, 4} : a + b > x}
===="#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty(), "{:?}", lower_result.errors);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");

    let state = vec![Value::int(4)];
    ctx.bind_state_array(&state);
    let setpred_val = ctx.eval_op("Filtered").unwrap();

    let Value::SetPred(ref spv) = setpred_val else {
        panic!("Filtered should stay lazy over tuple-set domain");
    };

    let member = Value::tuple([Value::int(2), Value::int(4)]);
    assert!(
        check_set_pred_membership(&ctx, &member, &spv, None).unwrap(),
        "tuple-pattern membership should bind a=2, b=4 and satisfy a+b > 4"
    );

    let non_member = Value::tuple([Value::int(1), Value::int(3)]);
    assert!(
        !check_set_pred_membership(&ctx, &non_member, &spv, None).unwrap(),
        "tuple-pattern membership should reject values that fail the predicate"
    );
}
