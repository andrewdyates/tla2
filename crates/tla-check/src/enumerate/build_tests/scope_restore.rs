// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! #1629 ScopeRestore coverage tests — split from scope_and_analysis.rs.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1629_nested_let_scope_restore_chain_restores_context() {
    // #1629 regression: nested LET-within-LET must chain scope_restore records
    // correctly (parent_scope_restore) and fully restore context after enumeration.
    let src = r#"
---- MODULE Test1629NestedLet ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next ==
  /\ LET a == 2 IN
       LET b == a + 1 IN
         x' = b
  /\ x = 0
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let next_def = find_operator(&module, "Next");

    let sentinel_ops = Arc::new(OpEnv::default());
    *ctx.local_ops_mut() = Some(Arc::clone(&sentinel_ops));
    ctx.set_skip_prime_validation(true);

    let current_array = ArrayState::from_values(vec![Value::SmallInt(0)]);
    let _state_guard = ctx.bind_state_env_guard(current_array.env_ref());
    let initial_stack_len = ctx.local_stack_len();

    let succs = enumerate_successors_array(&mut ctx, next_def, &current_array, &vars)
        .expect("invariant: nested LET enumeration must not error");
    assert_eq!(succs.len(), 1);
    assert_eq!(
        succs[0].get(VarIndex(0)).as_i64(),
        Some(3),
        "nested LET bindings must evaluate in inner scope and emit x'=3"
    );
    assert_scope_restore_cleanup(&ctx, initial_stack_len, true, &sentinel_ops);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1629_apply_with_outer_scope_restore_preserves_context() {
    // #1629 regression: Apply in LET continuation must use inner scope_restore
    // when an outer scope_restore exists, so parameter bindings are isolated.
    let src = r#"
---- MODULE Test1629ApplyScopeRestore ----
VARIABLE x
Init == x = 0
SetX(v) == x' = v
Next ==
  /\ LET h == 3 IN SetX(h)
  /\ x = 0
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let next_def = find_operator(&module, "Next");

    let sentinel_ops = Arc::new(OpEnv::default());
    *ctx.local_ops_mut() = Some(Arc::clone(&sentinel_ops));
    ctx.set_skip_prime_validation(true);

    let current_array = ArrayState::from_values(vec![Value::SmallInt(0)]);
    let _state_guard = ctx.bind_state_env_guard(current_array.env_ref());
    let initial_stack_len = ctx.local_stack_len();

    let succs = enumerate_successors_array(&mut ctx, next_def, &current_array, &vars)
        .expect("invariant: apply with scope_restore must not error");
    assert_eq!(succs.len(), 1);
    assert_eq!(
        succs[0].get(VarIndex(0)).as_i64(),
        Some(3),
        "Apply call in LET body must preserve argument binding and emit x'=3"
    );
    assert_scope_restore_cleanup(&ctx, initial_stack_len, true, &sentinel_ops);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1629_all_assigned_fast_path_with_scope_restore_restores_context() {
    // #1629 regression: all_assigned_fast_path must honor scope_restore and
    // continue parent continuation after guard evaluation.
    let src = r#"
---- MODULE Test1629AllAssignedFastPath ----
VARIABLE x
Init == x = 0
SetX(v) == /\ x' = v /\ v = 3
Next ==
  /\ LET h == 3 IN SetX(h)
  /\ x = 0
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let next_def = find_operator(&module, "Next");

    let sentinel_ops = Arc::new(OpEnv::default());
    *ctx.local_ops_mut() = Some(Arc::clone(&sentinel_ops));
    ctx.set_skip_prime_validation(true);

    let current_array = ArrayState::from_values(vec![Value::SmallInt(0)]);
    let _state_guard = ctx.bind_state_env_guard(current_array.env_ref());
    let initial_stack_len = ctx.local_stack_len();

    let succs = enumerate_successors_array(&mut ctx, next_def, &current_array, &vars)
        .expect("invariant: all_assigned fast path enumeration must not error");
    assert_eq!(succs.len(), 1);
    assert_eq!(
        succs[0].get(VarIndex(0)).as_i64(),
        Some(3),
        "all_assigned fast path must evaluate remaining guard and emit x'=3"
    );
    assert_scope_restore_cleanup(&ctx, initial_stack_len, true, &sentinel_ops);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1629_pop_to_mark_noop_when_scope_restore_pops_past_exists_mark() {
    // #1629 regression: when scope_restore pops past EXISTS binding cleanup mark,
    // pop_to_mark(mark > stack.len()) must no-op safely without underflow.
    let src = r#"
---- MODULE Test1629PopToMarkNoop ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next ==
  /\ LET a == 10 IN (\E h \in {1} : x' = a + h)
  /\ x = 0
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let next_def = find_operator(&module, "Next");

    let sentinel_ops = Arc::new(OpEnv::default());
    *ctx.local_ops_mut() = Some(Arc::clone(&sentinel_ops));
    ctx.set_skip_prime_validation(true);

    let current_array = ArrayState::from_values(vec![Value::SmallInt(0)]);
    let _state_guard = ctx.bind_state_env_guard(current_array.env_ref());
    let initial_stack_len = ctx.local_stack_len();

    let succs = enumerate_successors_array(&mut ctx, next_def, &current_array, &vars)
        .expect("invariant: pop_to_mark noop path must not error");
    assert_eq!(succs.len(), 1);
    assert_eq!(
        succs[0].get(VarIndex(0)).as_i64(),
        Some(11),
        "EXISTS body must still emit successor when outer scope_restore pops earlier marks"
    );
    assert_scope_restore_cleanup(&ctx, initial_stack_len, true, &sentinel_ops);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1629_multi_conjunct_let_continuation_uses_outer_binding() {
    // #1629 regression: continuation conjuncts after LET must observe outer
    // bindings, not LET-local shadowed names.
    let src = r#"
---- MODULE Test1629MultiConjunctLet ----
VARIABLE x, y
Init == /\ x = 0 /\ y = 0
Next ==
  \E block \in {1, 2} :
    /\ LET block == 10 IN x' = block
    /\ y' = block
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let next_def = find_operator(&module, "Next");

    let sentinel_ops = Arc::new(OpEnv::default());
    *ctx.local_ops_mut() = Some(Arc::clone(&sentinel_ops));
    ctx.set_skip_prime_validation(true);

    let current_array = ArrayState::from_values(vec![Value::SmallInt(0), Value::SmallInt(0)]);
    let _state_guard = ctx.bind_state_env_guard(current_array.env_ref());
    let initial_stack_len = ctx.local_stack_len();

    let succs = enumerate_successors_array(&mut ctx, next_def, &current_array, &vars)
        .expect("invariant: multi-conjunct LET continuation must not error");
    assert_eq!(succs.len(), 2);

    let registry = ctx.var_registry().clone();
    let x_idx = registry.get("x").expect("invariant: var x must exist");
    let y_idx = registry.get("y").expect("invariant: var y must exist");
    let mut pairs: Vec<(i64, i64)> = succs
        .iter()
        .map(|state| {
            (
                state.get(x_idx).as_i64().expect("invariant: x must be int"),
                state.get(y_idx).as_i64().expect("invariant: y must be int"),
            )
        })
        .collect();
    pairs.sort_unstable();
    assert_eq!(
        pairs,
        vec![(10, 1), (10, 2)],
        "LET-local block binding must not leak into continuation y' = block"
    );
    assert_scope_restore_cleanup(&ctx, initial_stack_len, true, &sentinel_ops);
}
