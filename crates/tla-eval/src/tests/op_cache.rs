// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bitwise_xor() {
    // Test the ^^ (XOR) operator from the Bitwise module
    // XOR truth table: 0 ^^ 0 = 0, 0 ^^ 1 = 1, 1 ^^ 0 = 1, 1 ^^ 1 = 0
    // Example: 5 ^^ 3 = 101 ^^ 011 = 110 = 6
    let src = r#"
---- MODULE Test ----
EXTENDS Integers, Bitwise
Xor1 == 5 ^^ 3      \* 5 XOR 3 = 6
Xor2 == 0 ^^ 0      \* 0
Xor3 == 12 ^^ 12    \* Self-XOR = 0
Xor4 == 10 ^^ 5     \* 1010 ^^ 0101 = 1111 = 15
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    assert_eq!(ctx.eval_op("Xor1").unwrap(), Value::int(6));
    assert_eq!(ctx.eval_op("Xor2").unwrap(), Value::int(0));
    assert_eq!(ctx.eval_op("Xor3").unwrap(), Value::int(0));
    assert_eq!(ctx.eval_op("Xor4").unwrap(), Value::int(15));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bitwise_and() {
    // Test the & (AND) operator from the Bitwise module
    let src = r#"
---- MODULE Test ----
EXTENDS Integers, Bitwise
And1 == 5 & 3      \* 101 & 011 = 001 = 1
And2 == 12 & 10    \* 1100 & 1010 = 1000 = 8
And3 == 7 & 0      \* 0
And4 == 255 & 255  \* 255
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    assert_eq!(ctx.eval_op("And1").unwrap(), Value::int(1));
    assert_eq!(ctx.eval_op("And2").unwrap(), Value::int(8));
    assert_eq!(ctx.eval_op("And3").unwrap(), Value::int(0));
    assert_eq!(ctx.eval_op("And4").unwrap(), Value::int(255));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bitwise_or() {
    // Test the | (OR) operator from the Bitwise module
    let src = r#"
---- MODULE Test ----
EXTENDS Integers, Bitwise
Or1 == 5 | 3      \* 101 | 011 = 111 = 7
Or2 == 12 | 10    \* 1100 | 1010 = 1110 = 14
Or3 == 7 | 0      \* 7
Or4 == 0 | 0      \* 0
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    assert_eq!(ctx.eval_op("Or1").unwrap(), Value::int(7));
    assert_eq!(ctx.eval_op("Or2").unwrap(), Value::int(14));
    assert_eq!(ctx.eval_op("Or3").unwrap(), Value::int(7));
    assert_eq!(ctx.eval_op("Or4").unwrap(), Value::int(0));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bitwise_shiftr() {
    // Test shiftR(n, pos) - logical right shift
    let src = r#"
---- MODULE Test ----
EXTENDS Integers, Bitwise
Shift1 == shiftR(8, 1)   \* 1000 >> 1 = 0100 = 4
Shift2 == shiftR(8, 2)   \* 1000 >> 2 = 0010 = 2
Shift3 == shiftR(15, 2)  \* 1111 >> 2 = 0011 = 3
Shift4 == shiftR(1, 1)   \* 1 >> 1 = 0
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    assert_eq!(ctx.eval_op("Shift1").unwrap(), Value::int(4));
    assert_eq!(ctx.eval_op("Shift2").unwrap(), Value::int(2));
    assert_eq!(ctx.eval_op("Shift3").unwrap(), Value::int(3));
    assert_eq!(ctx.eval_op("Shift4").unwrap(), Value::int(0));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_op_cache_hit_same_args_same_state() {
    // Test: Calling the same operator with same args returns correct result.
    // Part of #3000: OP_RESULT_CACHE insertion path removed. Lazy argument
    // evaluation (OnceLock per-call) replaces operator-level result caching.
    // Correctness verified: Add(1,2) + Add(1,2) == 6 regardless of caching.

    let src = r#"
---- MODULE Test ----
VARIABLE x
Add(a, b) == a + b
Test == Add(1, 2) + Add(1, 2)
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    // Set up state environment
    let state = vec![Value::int(10)]; // x = 10
    ctx.register_var("x");
    ctx.bind_state_array(&state);

    let result = ctx.eval_op("Test").unwrap();
    assert_eq!(result, Value::int(6)); // 3 + 3
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_op_cache_miss_different_args() {
    // Test: Different arguments produce correct distinct results.
    // Part of #3000: OP_RESULT_CACHE removed. Lazy evaluation ensures each
    // call evaluates its own arguments independently.

    let src = r#"
---- MODULE Test ----
VARIABLE x
Add(a, b) == a + b
Test == Add(1, 2) + Add(2, 3)
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let state = vec![Value::int(10)];
    ctx.register_var("x");
    ctx.bind_state_array(&state);

    let result = ctx.eval_op("Test").unwrap();
    assert_eq!(result, Value::int(8)); // 3 + 5
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_op_cache_miss_state_change() {
    // Test: Operator correctly returns different results when state changes.
    // Part of #3000: OP_RESULT_CACHE removed. With lazy evaluation, each
    // operator call evaluates in its current state context — no stale cache
    // entries possible.

    let src = r#"
---- MODULE Test ----
VARIABLE x
GetX(dummy) == x + dummy
Test1 == GetX(0)
Test2 == GetX(0)
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");

    // First evaluation with x = 10
    let state1 = vec![Value::int(10)];
    ctx.bind_state_array(&state1);
    let result1 = ctx.eval_op("Test1").unwrap();
    assert_eq!(result1, Value::int(10)); // x + 0 = 10

    // Second evaluation with different state x = 20
    let state2 = vec![Value::int(20)];
    ctx.bind_state_array(&state2);
    let result2 = ctx.eval_op("Test2").unwrap();
    assert_eq!(result2, Value::int(20)); // x + 0 = 20
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_op_cache_primed_operator_next_state_miss() {
    // Test: Operators using primed variables (x') must invalidate when
    // next_state_env changes.
    clear_for_test_reset();

    let src = r#"
---- MODULE Test ----
VARIABLE x
GetNextX(dummy) == x' + dummy
Test1 == GetNextX(0)
Test2 == GetNextX(0)
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");

    // Set up current state
    let state = vec![Value::int(10)];
    ctx.bind_state_array(&state);

    // First evaluation with next_state x' = 100
    let next_state1 = vec![Value::int(100)];
    ctx.bind_next_state_array(&next_state1);
    let result1 = ctx.eval_op("Test1").unwrap();
    assert_eq!(result1, Value::int(100)); // x' + 0 = 100

    // Second evaluation with different next_state x' = 200
    let next_state2 = vec![Value::int(200)];
    ctx.bind_next_state_array(&next_state2);
    let result2 = ctx.eval_op("Test2").unwrap();
    assert_eq!(
        result2,
        Value::int(200),
        "Primed operator must return new next_state value"
    );

    // The key correctness check: result2 should be 200, not cached 100.
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_op_cache_non_primed_ignores_next_state() {
    // Test: Operators WITHOUT primed variables should NOT invalidate when
    // next_state_env changes. This is the key optimization for bosco.
    clear_for_test_reset();

    let src = r#"
---- MODULE Test ----
VARIABLE x
GetX(dummy) == x + dummy
Test1 == GetX(0)
Test2 == GetX(0)
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");

    // Set up current state (stays constant)
    let state = vec![Value::int(42)];
    ctx.bind_state_array(&state);

    // First evaluation with next_state x' = 100
    let next_state1 = vec![Value::int(100)];
    ctx.bind_next_state_array(&next_state1);
    let result1 = ctx.eval_op("Test1").unwrap();
    assert_eq!(result1, Value::int(42)); // x + 0 = 42

    // Second evaluation with DIFFERENT next_state x' = 999
    // GetX doesn't use x', so this should produce the same result.
    let next_state2 = vec![Value::int(999)];
    ctx.bind_next_state_array(&next_state2);
    let result2 = ctx.eval_op("Test2").unwrap();
    assert_eq!(
        result2,
        Value::int(42),
        "Non-primed operator must return same value regardless of next_state"
    );
}

// Part of #3025: test_op_cache_size_cap_clears_at_10000 removed — it tested the
// dead OP_RESULT_CACHE soft cap. Active cache soft caps are tested in
// lifecycle_trim_tests.rs.

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_op_cache_correctness_with_complex_args() {
    // Test: Operators correctly handle complex argument values (sets).
    // Part of #3000: OP_RESULT_CACHE removed. Lazy evaluation evaluates
    // each call independently — correctness is the key property.

    let src = r#"
---- MODULE Test ----
VARIABLE x
SetSize(s) == Cardinality(s)
Test1 == SetSize({1, 2, 3})
Test2 == SetSize({1, 2, 3})
Test3 == SetSize({4, 5})
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let state = vec![Value::int(0)];
    ctx.register_var("x");
    ctx.bind_state_array(&state);

    let result1 = ctx.eval_op("Test1").unwrap();
    let result2 = ctx.eval_op("Test2").unwrap();
    let result3 = ctx.eval_op("Test3").unwrap();

    assert_eq!(result1, Value::int(3));
    assert_eq!(result2, Value::int(3));
    assert_eq!(result3, Value::int(2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_op_cache_expr_has_any_prime_detection() {
    // Test: Verify expr_has_any_prime correctly identifies primed expressions.
    // This is crucial for cache correctness.

    // Test a simple primed variable
    let src1 = r#"
---- MODULE Test ----
VARIABLE x
HasPrime == x'
====
"#;
    let tree1 = tla_core::parse_to_syntax_tree(src1);
    let lower_result1 = tla_core::lower(tla_core::FileId(0), &tree1);
    let module1 = lower_result1.module.expect("Module should lower");

    // Find the HasPrime operator and check its body
    let def1 = module1
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(d) = &u.node {
                if d.name.node == "HasPrime" {
                    return Some(d);
                }
            }
            None
        })
        .expect("HasPrime operator should exist");
    assert!(
        expr_has_any_prime(&def1.body.node),
        "x' should be detected as having primes"
    );

    // Test an expression without primes
    let src2 = r#"
---- MODULE Test ----
VARIABLE x
NoPrime == x + 1
====
"#;
    let tree2 = tla_core::parse_to_syntax_tree(src2);
    let lower_result2 = tla_core::lower(tla_core::FileId(0), &tree2);
    let module2 = lower_result2.module.expect("Module should lower");

    let def2 = module2
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(d) = &u.node {
                if d.name.node == "NoPrime" {
                    return Some(d);
                }
            }
            None
        })
        .expect("NoPrime operator should exist");
    assert!(
        !expr_has_any_prime(&def2.body.node),
        "x + 1 should NOT be detected as having primes"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_op_cache_nested_operator_calls() {
    // Test: Nested operator calls produce correct results.
    // Part of #3000: OP_RESULT_CACHE removed. Lazy evaluation handles
    // nested calls by creating fresh LazyBindings at each call site.
    // Inner(n) is called twice with same arg — lazy arg `n` is evaluated
    // once per call (OnceLock per LazyBinding instance, not per value).

    let src = r#"
---- MODULE Test ----
VARIABLE x
Inner(n) == n * 2
Outer(n) == Inner(n) + Inner(n)
Test == Outer(5)
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let state = vec![Value::int(0)];
    ctx.register_var("x");
    ctx.bind_state_array(&state);

    let result = ctx.eval_op("Test").unwrap();
    assert_eq!(result, Value::int(20)); // (5*2) + (5*2) = 10 + 10 = 20
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bind_many_matches_chained_bind_with_local_op_shadowing() {
    let src = r#"
---- MODULE Test ----
Dummy(v) == v
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut base = EvalCtx::new();
    base.load_module(&module);
    let dummy_op = base
        .get_op("Dummy")
        .expect("Dummy operator should exist")
        .clone();
    let mut local_ops = OpEnv::new();
    local_ops.insert("x".to_string(), dummy_op);
    let base = base.with_local_ops(local_ops);

    let chained = base
        .bind("x", Value::int(1))
        .bind("y", Value::int(2))
        .bind("x", Value::int(3));
    let batched = base.bind_many([
        (std::sync::Arc::<str>::from("x"), Value::int(1)),
        (std::sync::Arc::<str>::from("y"), Value::int(2)),
        (std::sync::Arc::<str>::from("x"), Value::int(3)),
    ]);

    assert_eq!(chained.lookup("x"), batched.lookup("x"));
    assert_eq!(chained.lookup("y"), batched.lookup("y"));

    // Part of #2955: Use get_local_bindings() instead of removed local_stack_iter().
    let chained_stack: Vec<(String, Value)> = chained
        .get_local_bindings()
        .into_iter()
        .map(|(name, value)| (name.to_string(), value))
        .collect();
    let batched_stack: Vec<(String, Value)> = batched
        .get_local_bindings()
        .into_iter()
        .map(|(name, value)| (name.to_string(), value))
        .collect();
    assert_eq!(chained_stack, batched_stack);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bind2_bind3_match_chained_bind() {
    let base = EvalCtx::new();

    let chained2 = base.bind("a", Value::int(10)).bind("b", Value::int(20));
    let batched2 = base.bind2("a", Value::int(10), "b", Value::int(20));
    assert_eq!(chained2.lookup("a"), batched2.lookup("a"));
    assert_eq!(chained2.lookup("b"), batched2.lookup("b"));

    let chained3 = base
        .bind("a", Value::int(1))
        .bind("b", Value::int(2))
        .bind("c", Value::int(3));
    let batched3 = base.bind3("a", Value::int(1), "b", Value::int(2), "c", Value::int(3));
    assert_eq!(chained3.lookup("a"), batched3.lookup("a"));
    assert_eq!(chained3.lookup("b"), batched3.lookup("b"));
    assert_eq!(chained3.lookup("c"), batched3.lookup("c"));
}

/// Build a NaryOpCacheKey from an EvalCtx, resolving scope ids.
fn build_nary_key(
    ctx: &EvalCtx,
    op_name: tla_core::name_intern::NameId,
    def_loc: u32,
) -> crate::cache::op_result_cache::NaryOpCacheKey {
    use crate::cache::scope_ids;
    crate::cache::op_result_cache::NaryOpCacheKey {
        shared_id: ctx.shared.id,
        local_ops_id: scope_ids::resolve_local_ops_id(ctx.scope_ids.local_ops, &ctx.local_ops),
        instance_subs_id: scope_ids::resolve_instance_subs_id(
            ctx.scope_ids.instance_substitutions,
            &ctx.instance_substitutions,
        ),
        op_name,
        def_loc,
        is_next_state: false,
        args_hash: 0,
        param_args_hash: 0,
    }
}

/// Part of #3099 Step 5: NaryOpCacheKey built from two reconstructed-but-identical
/// non-local local_ops scopes must be equal, enabling cross-reconstruction cache hits.
/// When scope content differs, keys must differ to prevent incorrect aliasing.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_3099_nary_cache_key_stable_across_reconstructed_local_ops() {
    use tla_core::name_intern::intern_name;

    let src = r#"
---- MODULE Test ----
VARIABLE x
Add(a, b) == a + b
Mul(a, b) == a * b
Test == Add(1, 2)
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut base_ctx = EvalCtx::new();
    base_ctx.load_module(&module);

    let add_def = base_ctx.get_op("Add").expect("Add must exist").clone();
    let mul_def = base_ctx.get_op("Mul").expect("Mul must exist").clone();
    let def_loc = add_def.body.span.start;
    let op_name_id = intern_name("Add");

    // Two OpEnv instances with identical non-local content, different Arc wrappers.
    let mut ops1 = OpEnv::new();
    let mut ops2 = OpEnv::new();
    ops1.insert("Add".into(), Arc::clone(&add_def));
    ops2.insert("Add".into(), Arc::clone(&add_def));

    let ctx1 = base_ctx.with_local_ops(ops1);
    let ctx2 = base_ctx.with_local_ops(ops2);

    let key1 = build_nary_key(&ctx1, op_name_id, def_loc);
    let key2 = build_nary_key(&ctx2, op_name_id, def_loc);
    assert_eq!(
        key1, key2,
        "same local_ops content must produce equal NaryOpCacheKey"
    );

    // Different local_ops content must produce a different key.
    let mut ops3 = OpEnv::new();
    ops3.insert("Mul".into(), Arc::clone(&mul_def));
    let ctx3 = base_ctx.with_local_ops(ops3);

    let key3 = build_nary_key(&ctx3, op_name_id, def_loc);
    assert_ne!(
        key1, key3,
        "different local_ops content must produce different NaryOpCacheKey"
    );
}
