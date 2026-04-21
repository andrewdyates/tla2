// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Part of #3099: Tests for the `local_ops_mut()` -> INVALIDATED scope_ids
//! migration in the unified enumerator's LET handling path.

use super::*;

/// Part of #3099: Verify that the migrated `local_ops_mut()` -> INVALIDATED path
/// produces correct enumeration when a LET-bound n-ary operator is called.
///
/// The unified_scope.rs LET handler uses `local_ops_mut()` to save/restore scope,
/// which sets `scope_ids.local_ops = INVALIDATED`. The NARY_OP_CACHE key builder
/// then uses `resolve_local_ops_id(INVALIDATED, ...)` to lazily compute the id.
/// This test verifies that enumeration through this path produces correct successors.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_3099_let_bound_operator_correct_under_invalidated_scope_ids() {
    let src = r#"
---- MODULE Test3099LetBoundOp ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next ==
  /\ LET
       base == 100
       Add(n) == base + n
     IN x' = Add(x)
  /\ x \in 0..2
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let next_def = find_operator(&module, "Next");

    let sentinel_ops = Arc::new(OpEnv::default());
    *ctx.local_ops_mut() = Some(Arc::clone(&sentinel_ops));
    ctx.set_skip_prime_validation(true);

    // Enumerate from x=0: LET base==100, Add(n)==base+n, x'=Add(0) => x'=100.
    let state0 = ArrayState::from_values(vec![Value::SmallInt(0)]);
    let _guard0 = ctx.bind_state_env_guard(state0.env_ref());
    let initial_stack_len = ctx.local_stack_len();

    let succs0 = enumerate_successors_array(&mut ctx, next_def, &state0, &vars)
        .expect("invariant: LET-bound operator enumeration must succeed");
    assert_eq!(succs0.len(), 1);
    assert_eq!(
        succs0[0].get(VarIndex(0)).as_i64(),
        Some(100),
        "Add(0) must evaluate to base + 0 = 100"
    );
    assert_scope_restore_cleanup(&ctx, initial_stack_len, true, &sentinel_ops);

    // Enumerate from x=1: Add(1) => x'=101.
    drop(_guard0);
    let state1 = ArrayState::from_values(vec![Value::SmallInt(1)]);
    let _guard1 = ctx.bind_state_env_guard(state1.env_ref());

    let succs1 = enumerate_successors_array(&mut ctx, next_def, &state1, &vars)
        .expect("invariant: second LET-bound operator enumeration must succeed");
    assert_eq!(succs1.len(), 1);
    assert_eq!(
        succs1[0].get(VarIndex(0)).as_i64(),
        Some(101),
        "Add(1) must evaluate to base + 1 = 101, not cached Add(0) result"
    );
    assert_scope_restore_cleanup(&ctx, initial_stack_len, true, &sentinel_ops);
}
