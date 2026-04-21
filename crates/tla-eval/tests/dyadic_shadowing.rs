// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;
use tla_core::{lower, parse_to_syntax_tree, FileId};
use tla_eval::{clear_for_test_reset, EvalCtx};
use tla_value::error::EvalError;
use tla_value::Value;

fn eval_with_extended_modules(
    defs: &str,
    expr: &str,
    extended_modules: &[&str],
) -> Result<Value, EvalError> {
    clear_for_test_reset();

    let module_src = format!(
        "---- MODULE Test ----\n\n{}\n\nOp == {}\n\n====",
        defs, expr
    );
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lowering errors: {:?}",
        lower_result.errors
    );

    let module = lower_result.module.expect("lowered module");
    let mut ctx = EvalCtx::new();
    {
        let shared = Arc::make_mut(ctx.shared_arc_mut());
        for module_name in extended_modules {
            shared
                .extended_module_names
                .insert((*module_name).to_string());
        }
    }
    ctx.load_module(&module);
    ctx.eval_op("Op")
}

#[test]
fn test_user_defined_add_shadows_dyadic_builtin_direct_apply() {
    let value = eval_with_extended_modules(
        "EXTENDS DyadicRationals\nAdd(a, b) == a + b",
        "Add(3, 4)",
        &["DyadicRationals"],
    )
    .expect("direct user-defined Add should evaluate");
    assert_eq!(value, Value::int(7));
}

#[test]
fn test_recursive_fold_named_add_shadows_dyadic_builtin() {
    let value = eval_with_extended_modules(
        r#"EXTENDS DyadicRationals
           RECURSIVE SumSlow(_)
           SumSlow(S) ==
               IF S = {} THEN 0
               ELSE LET x == CHOOSE x \in S : TRUE
                    IN Add(x, SumSlow(S \ {x}))
           Add(a, b) == a + b"#,
        "SumSlow({1, 2, 3, 4})",
        &["DyadicRationals"],
    )
    .expect("recursive fold should use main-module Add");
    assert_eq!(value, Value::int(10));
}
