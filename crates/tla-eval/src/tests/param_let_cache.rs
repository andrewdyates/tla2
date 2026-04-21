// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for PARAM_LET_CACHE (Tier 1.5 parameter-dependent LET caching).
//!
//! Part of #3034: The PARAM_LET_CACHE uses hash + equality verification to
//! prevent silent correctness bugs from 64-bit hash collisions. These tests
//! verify the cache returns distinct results for distinct dep values and
//! consistent results for identical dep values.

use super::*;
use crate::cache::small_caches::SMALL_CACHES;

fn parse_module(src: &str) -> tla_core::ast::Module {
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    lower_result
        .module
        .unwrap_or_else(|| panic!("failed to lower module: {:?}", lower_result.errors))
}

/// Helper: count total entries across all cache keys in PARAM_LET_CACHE.
/// Part of #3962: Access via consolidated SMALL_CACHES.
fn param_let_cache_total_entries() -> usize {
    SMALL_CACHES.with(|sc| sc.borrow().param_let_cache.values().map(|entries| entries.len()).sum())
}

/// Helper: check if PARAM_LET_DEPS has any entries registered.
/// Part of #3962: Access via consolidated SMALL_CACHES.
fn param_let_deps_count() -> usize {
    SMALL_CACHES.with(|sc| sc.borrow().param_let_deps.len())
}

/// Verify that PARAM_LET_CACHE correctly caches and distinguishes
/// LET bodies that depend on different local parameter values.
///
/// Scenario: `\E x \in {1, 2, 3} : LET y == x + 10 IN y = p`
/// where `p` varies. The LET body `x + 10` depends on local `x`,
/// so it enters the Tier 1.5 cache. We verify that evaluating with
/// different `x` values produces correct, distinct results.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_param_let_cache_returns_correct_values_for_different_deps() {
    clear_for_test_reset();

    // Evaluate: the set {11, 12, 13} is built by LET y == x + 10 IN y
    // for x in {1, 2, 3}. The LET body `x + 10` has local-only dep on x.
    let result = eval_str(r#"{LET y == x + 10 IN y : x \in {1, 2, 3}}"#).unwrap();
    let expected = eval_str(r#"{11, 12, 13}"#).unwrap();
    assert_eq!(
        result, expected,
        "LET with local dep should produce distinct values for each x"
    );

    clear_for_test_reset();
}

/// Verify that the PARAM_LET_CACHE gets populated when evaluating a LET body
/// with local-only dependencies. We evaluate the expression, then immediately
/// check the cache state before any other eval_str call clears it.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_param_let_cache_populates_on_local_dep_let() {
    clear_for_test_reset();

    // Evaluate an expression where a LET body has local-only deps.
    // The set comprehension iterates x over {1, 2} and evaluates
    // `LET sq == x * x IN sq` for each value of x.
    let result = eval_str(r#"{LET sq == x * x IN sq : x \in {1, 2}}"#).unwrap();

    // Check cache state BEFORE calling eval_str again (which clears caches).
    let deps_count = param_let_deps_count();
    let cache_count = param_let_cache_total_entries();

    // Verify correctness (use direct Value comparison, not eval_str).
    // Check the result contains both 1 and 4 using Value's set membership.
    assert!(result.is_set(), "Expected set result, got {:?}", result);
    // The set {1, 4} should contain both elements.
    use num_bigint::BigInt;
    assert_eq!(
        result.set_len().unwrap(),
        BigInt::from(2),
        "LET with local dep for x in {{1,2}} should produce 2-element set"
    );

    // The cache should have been populated. The exact counts depend on
    // evaluation order, but we expect at least 1 dep registration and
    // at least 1 cache entry.
    assert!(
        deps_count >= 1,
        "PARAM_LET_DEPS should register dep names for local-dep LET body, got {}",
        deps_count
    );
    assert!(
        cache_count >= 1,
        "PARAM_LET_CACHE should store entries for evaluated dep values, got {}",
        cache_count
    );

    clear_for_test_reset();
}

/// Verify that LET bodies with NO local deps go to CONST_LET_CACHE (Tier 1),
/// not PARAM_LET_CACHE (Tier 1.5).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_const_let_does_not_pollute_param_cache() {
    clear_for_test_reset();

    // `LET c == 2 + 3 IN c` has no local deps — should go to CONST_LET_CACHE.
    let result = eval_str(r#"LET c == 2 + 3 IN c"#).unwrap();
    assert_eq!(result, Value::int(5));

    let param_deps = param_let_deps_count();
    let param_entries = param_let_cache_total_entries();
    assert_eq!(
        param_deps, 0,
        "Constant LET body should NOT register in PARAM_LET_DEPS"
    );
    assert_eq!(
        param_entries, 0,
        "Constant LET body should NOT enter PARAM_LET_CACHE"
    );

    clear_for_test_reset();
}

/// Verify that PARAM_LET_CACHE entries store dep values for equality
/// verification (Part of #3034). After caching, the stored entries must
/// contain the actual dep values, not just the hash.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_param_let_cache_entries_store_dep_values() {
    clear_for_test_reset();

    // Evaluate LET body with local dep. The set comprehension forces
    // multiple evaluations with different dep values.
    let _result = eval_str(r#"{LET doubled == x + x IN doubled : x \in {5, 10}}"#).unwrap();

    // Inspect the cache entries: each entry should be (hash, dep_values, result)
    // where dep_values is non-empty.
    // Part of #3962: Access via consolidated SMALL_CACHES.
    SMALL_CACHES.with(|sc| {
        let sc = sc.borrow();
        for (_key, entries) in sc.param_let_cache.iter() {
            for (hash, dep_vals, result) in entries {
                assert!(
                    *hash != 0 || !dep_vals.is_empty(),
                    "Cache entry should have meaningful hash or dep values"
                );
                assert!(
                    !dep_vals.is_empty(),
                    "Part of #3034: dep_values must be stored for equality verification"
                );
                // Verify the cached result matches the dep values:
                // For dep_val [5], result should be 10; for [10], result should be 20.
                if dep_vals.len() == 1 {
                    if dep_vals[0] == Value::int(5) {
                        assert_eq!(
                            *result,
                            Value::int(10),
                            "cached result for dep=[5] should be 10"
                        );
                    } else if dep_vals[0] == Value::int(10) {
                        assert_eq!(
                            *result,
                            Value::int(20),
                            "cached result for dep=[10] should be 20"
                        );
                    }
                }
            }
        }
    });

    clear_for_test_reset();
}

/// Verify that Tier 1.5 does not permanently under-key a branchy LET body based
/// only on the first branch observed.
///
/// Regression for VerifyThis `MergesortRuns`: a zero-arg LET body may first be
/// classified while one branch is inactive, recording only a subset of the true
/// local dependencies. Later evaluations that take a different branch must not
/// reuse a cached result keyed only by that first branch's deps.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_param_let_cache_widens_branch_sensitive_local_deps() {
    clear_for_test_reset();

    let defs = r#"
F(flag, x) == LET y == IF flag THEN x ELSE 0 IN y
"#;

    let result = eval_with_ops(defs, "<<F(FALSE, 1), F(TRUE, 2), F(TRUE, 3)>>").unwrap();
    let expected = eval_str(r#"<<0, 2, 3>>"#).unwrap();

    assert_eq!(
        result, expected,
        "branch-sensitive LET cache must distinguish TRUE-branch results by x"
    );

    clear_for_test_reset();
}

/// Regression for SlidingPuzzles-style nested operator caching: when a zero-arg
/// LET body reuses a Tier 1.5 cache entry, the hit must still propagate the
/// captured local deps into any enclosing dep-tracking frame.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_param_let_cache_hit_propagates_local_deps() {
    clear_for_test_reset();

    let module_src = "---- MODULE Test ----\n\nProbe == LET sq == x * x IN sq\n\n====";
    let module = parse_module(module_src);

    let probe_body = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Probe" => Some(&def.body),
            _ => None,
        })
        .expect("Probe operator should exist");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let ctx_with_x = ctx.bind("x", Value::int(7));
    let x_id = tla_core::name_intern::intern_name("x");

    let (first_value, first_deps) =
        eval_with_dep_tracking(&ctx_with_x, probe_body).expect("first Probe eval should succeed");
    assert_eq!(first_value, Value::int(49));
    assert!(
        first_deps.local.iter().any(|(name_id, _)| *name_id == x_id),
        "first eval should classify the LET body as depending on x"
    );

    let (second_value, second_deps) =
        eval_with_dep_tracking(&ctx_with_x, probe_body).expect("second Probe eval should succeed");
    assert_eq!(second_value, Value::int(49));
    assert!(
        second_deps
            .local
            .iter()
            .any(|(name_id, _)| *name_id == x_id),
        "param LET cache hit must replay local deps into the outer dep frame"
    );

    clear_for_test_reset();
}

/// Regression for SlidingPuzzles `move`: the zero-arg LET witness chosen via a
/// higher-order operator must stay keyed by the current board binding, not only
/// by the captured lambda locals.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_param_let_cache_distinguishes_higher_order_board_binding() {
    clear_for_test_reset();

    let module_src = r#"---- MODULE Test ----

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x
Probe == LET pc == ChooseOne(board, LAMBDA pc : s \in pc) IN pc

===="#;
    let module = parse_module(module_src);

    let probe_body = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Probe" => Some(&def.body),
            _ => None,
        })
        .expect("Probe operator should exist");

    let p1 = Value::set([
        Value::tuple([Value::int(0), Value::int(0)]),
        Value::tuple([Value::int(0), Value::int(1)]),
    ]);
    let p2 = Value::set([Value::tuple([Value::int(0), Value::int(1)])]);
    let q = Value::set([Value::tuple([Value::int(1), Value::int(0)])]);
    let r = Value::set([
        Value::tuple([Value::int(0), Value::int(0)]),
        Value::tuple([Value::int(1), Value::int(0)]),
    ]);
    let board1 = Value::set([p1.clone(), q]);
    let board2 = Value::set([p2.clone(), r]);
    let s = Value::tuple([Value::int(0), Value::int(1)]);

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let ctx1 = ctx.clone().bind("board", board1).bind("s", s.clone());
    let ctx2 = ctx.bind("board", board2).bind("s", s);

    let first = eval(&ctx1, probe_body).expect("first Probe eval should succeed");
    assert_eq!(first, p1);

    let second = eval(&ctx2, probe_body).expect("second Probe eval should succeed");
    assert_eq!(
        second, p2,
        "param LET cache must distinguish the current board binding for ChooseOne"
    );

    clear_for_test_reset();
}

/// Regression for SlidingPuzzles `move`: once the zero-arg LET witness is
/// primed in PARAM_LET_CACHE, an outer n-ary operator cache entry must still
/// retain the free `board` binding as a dependency when the LET body hits.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_param_let_cache_hit_keeps_outer_nary_cache_bound_to_board() {
    clear_for_test_reset();

    let module_src = r#"---- MODULE Test ----

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x
Probe(s) == LET pc == ChooseOne(board, LAMBDA pc : s \in pc) IN pc
Run == Probe(s)

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result
        .module
        .unwrap_or_else(|| panic!("failed to lower module: {:?}", lower_result.errors));

    let probe_body = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Probe" => Some(&def.body),
            _ => None,
        })
        .expect("Probe operator should exist");
    let run_body = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Run" => Some(&def.body),
            _ => None,
        })
        .expect("Run operator should exist");

    let p1 = Value::set([
        Value::tuple([Value::int(0), Value::int(0)]),
        Value::tuple([Value::int(0), Value::int(1)]),
    ]);
    let p2 = Value::set([Value::tuple([Value::int(0), Value::int(1)])]);
    let q = Value::set([Value::tuple([Value::int(1), Value::int(0)])]);
    let r = Value::set([
        Value::tuple([Value::int(0), Value::int(0)]),
        Value::tuple([Value::int(1), Value::int(0)]),
    ]);
    let board1 = Value::set([p1.clone(), q]);
    let board2 = Value::set([p2.clone(), r]);
    let s = Value::tuple([Value::int(0), Value::int(1)]);

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let ctx1 = ctx.clone().bind("board", board1).bind("s", s.clone());
    let ctx2 = ctx.bind("board", board2).bind("s", s);

    // Prime PARAM_LET_CACHE directly, without going through the outer n-ary
    // operator cache. The next Run() evaluation must still propagate `board`.
    let primed = eval(&ctx1, probe_body).expect("Probe priming eval should succeed");
    assert_eq!(primed, p1);

    let first_outer = eval(&ctx1, run_body).expect("first Run eval should succeed");
    assert_eq!(first_outer, p1);

    let second_outer = eval(&ctx2, run_body).expect("second Run eval should succeed");
    assert_eq!(
        second_outer, p2,
        "outer n-ary cache must not reuse Probe(s) across different free board bindings"
    );

    clear_for_test_reset();
}

/// Regression for SlidingPuzzles `move`: when the free `board` binding comes
/// from `state_env` instead of the local binding chain, cached higher-order
/// operator results must still be revalidated against the current state.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_higher_order_state_env_board_binding_revalidates_across_states() {
    clear_for_test_reset();

    let module_src = r#"---- MODULE Test ----
VARIABLE board

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x
Probe(s) == LET pc == ChooseOne(board, LAMBDA pc : s \in pc) IN pc
Run == Probe(<<0, 1>>)

===="#;
    let module = parse_module(module_src);

    let p1 = Value::set([
        Value::tuple([Value::int(0), Value::int(0)]),
        Value::tuple([Value::int(0), Value::int(1)]),
    ]);
    let p2 = Value::set([Value::tuple([Value::int(0), Value::int(1)])]);
    let q = Value::set([Value::tuple([Value::int(1), Value::int(0)])]);
    let r = Value::set([
        Value::tuple([Value::int(0), Value::int(0)]),
        Value::tuple([Value::int(1), Value::int(0)]),
    ]);
    let board1 = Value::set([p1.clone(), q]);
    let board2 = Value::set([p2.clone(), r]);

    let mut ctx = EvalCtx::new();
    ctx.register_var("board");
    ctx.load_module(&module);

    let first = {
        let state = [board1];
        let mut eval_ctx = ctx.clone();
        eval_ctx.bind_state_array(&state);
        assert_eq!(
            eval_ctx.lookup_state_var("board"),
            Some(state[0].clone()),
            "state-backed test harness must resolve board through lookup_state_var()"
        );
        eval_ctx
            .eval_op("Run")
            .expect("first Run eval against state-backed board should succeed")
    };
    assert_eq!(first, p1);

    let second = {
        let state = [board2];
        let mut eval_ctx = ctx.clone();
        eval_ctx.bind_state_array(&state);
        eval_ctx
            .eval_op("Run")
            .expect("second Run eval against different state-backed board should succeed")
    };
    assert_eq!(
        second, p2,
        "state-backed board binding must invalidate cached higher-order results"
    );

    clear_for_test_reset();
}

/// The state-backed SlidingPuzzles regression above should also surface a
/// concrete dependency on the `board` state variable during dep tracking.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_higher_order_state_env_board_binding_records_state_dep() {
    clear_for_test_reset();

    let module_src = r#"---- MODULE Test ----
VARIABLE board

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x
Probe(s) == LET pc == ChooseOne(board, LAMBDA pc : s \in pc) IN pc
Run == Probe(<<0, 1>>)

===="#;
    let module = parse_module(module_src);

    let run_body = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Run" => Some(&def.body),
            _ => None,
        })
        .expect("Run operator should exist");

    let p1 = Value::set([
        Value::tuple([Value::int(0), Value::int(0)]),
        Value::tuple([Value::int(0), Value::int(1)]),
    ]);
    let q = Value::set([Value::tuple([Value::int(1), Value::int(0)])]);
    let board = Value::set([p1, q]);

    let mut ctx = EvalCtx::new();
    ctx.register_var("board");
    ctx.load_module(&module);

    let (_value, deps) = {
        let state = [board];
        let mut eval_ctx = ctx.clone();
        eval_ctx.bind_state_array(&state);
        assert_eq!(
            eval_ctx.lookup_state_var("board"),
            Some(state[0].clone()),
            "state-backed dep test harness must resolve board through lookup_state_var()"
        );
        eval_with_dep_tracking(&eval_ctx, run_body)
            .expect("state-backed Run dep-tracked eval should succeed")
    };
    assert_eq!(
        deps.state.len(),
        1,
        "dep tracking should record the free board state variable for higher-order Probe"
    );

    clear_for_test_reset();
}

/// Regression for SlidingPuzzles `move`: on the first evaluation of a cached
/// n-ary operator, zero-arg LET bodies must propagate their state deps into the
/// enclosing operator frame before the n-ary cache entry is stored.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_move_like_zero_arg_let_first_eval_revalidates_against_state_board() {
    clear_for_test_reset();

    let module_src = r#"---- MODULE Test ----
VARIABLE board

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x
Move(p, d) == LET s == <<p[1] + d[1], p[2] + d[2]>>
                  pc == ChooseOne(board, LAMBDA pc : s \in pc)
              IN <<pc, {<<q[1] - d[1], q[2] - d[2]>> : q \in pc}>>
Run == Move(<<0, 0>>, <<0, 1>>)

===="#;
    let module = parse_module(module_src);

    let p1 = Value::set([
        Value::tuple([Value::int(0), Value::int(0)]),
        Value::tuple([Value::int(0), Value::int(1)]),
    ]);
    let p2 = Value::set([Value::tuple([Value::int(0), Value::int(1)])]);
    let q = Value::set([Value::tuple([Value::int(1), Value::int(0)])]);
    let r = Value::set([
        Value::tuple([Value::int(0), Value::int(0)]),
        Value::tuple([Value::int(1), Value::int(0)]),
    ]);
    let board1 = Value::set([p1.clone(), q]);
    let board2 = Value::set([p2.clone(), r]);

    let expected_first = Value::tuple([
        p1.clone(),
        Value::set([
            Value::tuple([Value::int(0), Value::int(-1)]),
            Value::tuple([Value::int(0), Value::int(0)]),
        ]),
    ]);
    let expected_second = Value::tuple([
        p2.clone(),
        Value::set([Value::tuple([Value::int(0), Value::int(0)])]),
    ]);

    let mut ctx = EvalCtx::new();
    ctx.register_var("board");
    ctx.load_module(&module);

    let first = {
        let state = [board1.clone()];
        let mut eval_ctx = ctx.clone();
        eval_ctx.bind_state_array(&state);
        eval_ctx
            .eval_op("Run")
            .expect("first Move-like eval against board1 should succeed")
    };
    assert_eq!(first, expected_first);

    let second = {
        let state = [board2.clone()];
        let mut eval_ctx = ctx.clone();
        eval_ctx.bind_state_array(&state);
        eval_ctx
            .eval_op("Run")
            .expect("second Move-like eval against board2 should succeed")
    };
    assert_eq!(
        second, expected_second,
        "Move-like n-ary cache must not reuse a stale board witness across states"
    );

    let third = {
        let state = [board1];
        let mut eval_ctx = ctx.clone();
        eval_ctx.bind_state_array(&state);
        eval_ctx
            .eval_op("Run")
            .expect("third Move-like eval against board1 should succeed")
    };
    assert_eq!(
        third, expected_first,
        "known-non-constant zero-arg LET bodies must keep replaying state deps into the outer cache"
    );

    clear_for_test_reset();
}
