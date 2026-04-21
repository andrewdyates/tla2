// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! StateLookupMode guard tests, dep tracking, eager bindings, and scope ID stability.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_lookup_mode_guard_restores_on_normal_drop() {
    let ctx = EvalCtx::new();
    assert_eq!(
        ctx.runtime_state.state_lookup_mode.get(),
        StateLookupMode::Current,
        "initial mode should be Current"
    );

    {
        let _guard = StateLookupModeGuard::new(&ctx, StateLookupMode::Next);
        assert_eq!(
            ctx.runtime_state.state_lookup_mode.get(),
            StateLookupMode::Next,
            "mode should be Next while guard is active"
        );
    }

    assert_eq!(
        ctx.runtime_state.state_lookup_mode.get(),
        StateLookupMode::Current,
        "guard drop should restore mode to Current"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_lookup_mode_guard_restores_on_panic_unwind() {
    let ctx = EvalCtx::new();
    assert_eq!(
        ctx.runtime_state.state_lookup_mode.get(),
        StateLookupMode::Current,
        "initial mode should be Current"
    );

    let unwind_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _guard = StateLookupModeGuard::new(&ctx, StateLookupMode::Next);
        assert_eq!(
            ctx.runtime_state.state_lookup_mode.get(),
            StateLookupMode::Next,
            "mode should be Next before panic"
        );
        panic!("intentional unwind to exercise StateLookupModeGuard::drop");
    }));

    assert!(unwind_result.is_err(), "panic should be caught");
    assert_eq!(
        ctx.runtime_state.state_lookup_mode.get(),
        StateLookupMode::Current,
        "guard drop should restore mode to Current during unwind"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_clear_for_state_eval_replay_resets_lookup_mode_and_clears_eval_scope_cache() {
    clear_for_test_reset();

    let ctx = EvalCtx::new();
    insert_subst_cache("before_replay", Value::Bool(true));
    assert_eq!(subst_cache_len(), 1, "setup should populate SUBST_CACHE");

    ctx.runtime_state
        .state_lookup_mode
        .set(StateLookupMode::Next);
    assert_eq!(
        ctx.runtime_state.state_lookup_mode.get(),
        StateLookupMode::Next,
        "setup should simulate leaked Next mode"
    );

    clear_for_state_eval_replay(&ctx);

    assert_eq!(
        ctx.runtime_state.state_lookup_mode.get(),
        StateLookupMode::Current,
        "replay helper should restore top-level evaluation to Current mode"
    );
    assert_eq!(
        subst_cache_len(),
        0,
        "replay helper should clear eval-scope caches before the next top-level evaluation"
    );

    clear_for_test_reset();
}

/// Regression test for #2372: verify that `ctx.lookup()` in the eval_ident slow path
/// (reached when instance_substitutions are active) correctly records state variable
/// dependencies via `record_state_read()`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_slow_path_lookup_records_state_deps_with_instance_subs() {
    clear_for_test_reset();

    // Set up a context with a state variable "x"
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(42)];
    ctx.bind_state_array(&state);

    // Add a dummy instance substitution for an unrelated name to force the slow path.
    // The slow path is taken when instance_substitutions.is_some() (eval_ident.rs:46).
    // The substitution maps "unrelated" -> 99, which won't match "x".
    let ctx_with_subs = ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::new("unrelated".to_string(), Span::dummy()),
        to: Spanned::new(Expr::Int(99.into()), Span::dummy()),
    }]);

    // Create an Expr::Ident for "x" — this will take the slow path because
    // instance_substitutions is Some, and resolve via ctx.lookup() at line 522.
    let x_ident = Spanned::new(
        Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
        Span::dummy(),
    );

    // Evaluate with dep tracking to capture state variable dependencies.
    let (value, deps) = eval_with_dep_tracking(&ctx_with_subs, &x_ident)
        .expect("evaluating state var 'x' via slow path should succeed");

    assert_eq!(value, Value::int(42), "should resolve to state var value");
    assert!(
        !deps.state.is_empty(),
        "slow path ctx.lookup() must record state variable dependency for 'x' — \
         if this fails, record_state_read is missing in the slow path (see #2372)"
    );
    assert!(
        deps.next.is_empty(),
        "current-state lookup should not record next-state deps"
    );

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hoist_cache_is_suppressed_during_dep_tracking() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(42)];
    ctx.bind_state_array(&state);

    let x_id = intern_name("x");
    let expr = Spanned::dummy(Expr::StateVar("x".to_string(), 0, x_id));
    let current_value = eval(&ctx, &expr).expect("current-state state var should evaluate");

    let mut hoistable = FxHashSet::default();
    hoistable.insert(std::ptr::addr_of!(expr.node) as usize);
    let _hoist_guard =
        enter_quantifier_hoist_scope(Rc::new(hoistable)).expect("manual hoist scope should push");
    quantifier_hoist_store(&expr.node, &current_value);

    let (value, deps) =
        eval_with_dep_tracking(&ctx, &expr).expect("dep-tracked state var should evaluate");
    assert_eq!(value, Value::int(42));
    assert_eq!(
        deps.state.len(),
        1,
        "dep tracking must still see the underlying state read even when a hoist entry exists"
    );

    clear_for_test_reset();
}

#[cfg(debug_assertions)]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sliding_puzzles_successor_set_matches_when_hoist_is_suppressed() {
    clear_for_test_reset();

    let module_src = r#"---- MODULE Test ----
EXTENDS Integers

W == 4 H == 5
Pos == (0 .. W - 1) \X (0 .. H - 1)

Klotski ==
  {{<<0, 0>>, <<0, 1>>},
   {<<1, 0>>, <<2, 0>>, <<1, 1>>, <<2, 1>>},
   {<<3, 0>>, <<3, 1>>},
   {<<0, 2>>, <<0, 3>>},
   {<<1, 2>>, <<2, 2>>},
   {<<3, 2>>, <<3, 3>>},
   {<<1, 3>>}, {<<2, 3>>}, {<<0, 4>>}, {<<3, 4>>}}

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

dir(p, es) ==
  LET dir == {<<1, 0>>, <<0, 1>>, <<-1, 0>>, <<0, -1>>}
  IN {d \in dir :
        /\ <<p[1] + d[1], p[2] + d[2]>> \in Pos
        /\ <<p[1] + d[1], p[2] + d[2]>> \notin es}

move(board, p, d) ==
  LET s == <<p[1] + d[1], p[2] + d[2]>>
      pc == ChooseOne(board, LAMBDA pc : s \in pc)
  IN <<pc, {<<q[1] - d[1], q[2] - d[2]>> : q \in pc}>>

update(board, e, es) ==
  LET dirs  == dir(e, es)
      moved == {move(board, e, d) : d \in dirs}
      free  == {<<pc, m>> \in moved :
                  /\ m \cap (UNION (board \ {pc})) = {}
                  /\ \A p \in m : p \in Pos}
  IN UNION {{(board \ {pc}) \cup {m}} : <<pc, m>> \in free}

NextBoards(board) ==
  LET empty == Pos \ UNION board
  IN UNION {update(board, e, empty) : e \in empty}

Op == UNION {NextBoards(board) : board \in NextBoards(Klotski)}

===="#;

    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result
        .module
        .unwrap_or_else(|| panic!("failed to lower module: {:?}", lower_result.errors));

    let op_body = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == "Op" => Some(&def.body),
            _ => None,
        })
        .expect("Op operator should exist");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let hoisted = eval(&ctx, op_body).expect("hoisted successor-set eval should succeed");

    clear_for_test_reset();
    let mut fresh_ctx = EvalCtx::new();
    fresh_ctx.load_module(&module);
    let unhoisted = {
        let _guard = suppress_hoist_lookup();
        eval(&fresh_ctx, op_body).expect("suppressed-hoist successor-set eval should succeed")
    };

    assert_eq!(
        hoisted, unhoisted,
        "SlidingPuzzles-style successor-set evaluation must not depend on hoist cache hits"
    );

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eager_bindings_keep_substitution_target_on_slow_path() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(42)];
    ctx.bind_state_array(&state);

    let mut ctx_with_subs = ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::new("x".to_string(), Span::dummy()),
        to: Spanned::new(Expr::Int(99.into()), Span::dummy()),
    }]);
    ctx_with_subs.stable_mut().eager_subst_bindings = Some(Arc::new(vec![(
        intern_name("x"),
        Value::int(99),
        OpEvalDeps::default(),
    )]));

    let x_ident = Spanned::new(
        Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
        Span::dummy(),
    );
    let value = eval(&ctx_with_subs, &x_ident).expect("substitution target should resolve");
    assert_eq!(
        value,
        Value::int(99),
        "eager substitution targets must bypass state/env lookup"
    );

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eager_bindings_non_target_can_read_state_var() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(42)];
    ctx.bind_state_array(&state);

    let mut ctx_with_subs = ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::new("unrelated".to_string(), Span::dummy()),
        to: Spanned::new(Expr::Int(99.into()), Span::dummy()),
    }]);
    ctx_with_subs.stable_mut().eager_subst_bindings = Some(Arc::new(vec![(
        intern_name("unrelated"),
        Value::int(99),
        OpEvalDeps::default(),
    )]));

    let x_ident = Spanned::new(
        Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
        Span::dummy(),
    );
    let (value, deps) = eval_with_dep_tracking(&ctx_with_subs, &x_ident)
        .expect("non-target identifier should resolve from state");
    assert_eq!(value, Value::int(42));
    assert!(
        !deps.state.is_empty(),
        "state read dependency must be recorded for non-target lookups"
    );

    clear_for_test_reset();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eager_bindings_do_not_bypass_call_by_name_substitution() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(42)];
    ctx.bind_state_array(&state);

    let mut ctx_with_subs = ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::new("unrelated".to_string(), Span::dummy()),
        to: Spanned::new(Expr::Int(99.into()), Span::dummy()),
    }]);
    ctx_with_subs.stable_mut().eager_subst_bindings = Some(Arc::new(vec![(
        intern_name("unrelated"),
        Value::int(99),
        OpEvalDeps::default(),
    )]));
    let ctx_with_subs = ctx_with_subs.with_call_by_name_subs(vec![Substitution {
        from: Spanned::new("x".to_string(), Span::dummy()),
        to: Spanned::new(Expr::Int(7.into()), Span::dummy()),
    }]);

    let x_ident = Spanned::new(
        Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
        Span::dummy(),
    );
    let value = eval(&ctx_with_subs, &x_ident)
        .expect("call-by-name substitution should run before state/env fallback");
    assert_eq!(
        value,
        Value::int(7),
        "call-by-name substitution must not be skipped by eager fast-path guard"
    );

    clear_for_test_reset();
}

// === Scope ID stability tests (Part of #3099) ===

/// Part of #3099 Step 5: Repeated `with_instance_substitutions` calls with logically
/// identical substitutions produce the same `scope_ids.instance_substitutions`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scope_ids_stable_across_reconstructed_instance_subs() {
    let ctx = EvalCtx::new();

    let make_subs = || {
        vec![Substitution {
            from: Spanned::new("x".to_string(), Span::dummy()),
            to: Spanned::new(Expr::Int(42.into()), Span::dummy()),
        }]
    };

    // Two independent constructions with the same substitution content.
    let ctx1 = ctx.with_instance_substitutions(make_subs());
    let ctx2 = ctx.with_instance_substitutions(make_subs());

    let id1 = ctx1.stable.scope_ids.instance_substitutions;
    let id2 = ctx2.stable.scope_ids.instance_substitutions;

    assert_ne!(id1, 0, "non-empty subs should produce non-zero scope id");
    assert_eq!(
        id1, id2,
        "logically identical instance_substitutions must produce the same scope id"
    );

    // Different substitution content should produce a different id.
    let ctx3 = ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::new("y".to_string(), Span::dummy()),
        to: Spanned::new(Expr::Int(99.into()), Span::dummy()),
    }]);
    let id3 = ctx3.stable.scope_ids.instance_substitutions;
    assert_ne!(
        id1, id3,
        "different substitution content must produce different scope ids"
    );
}

/// Part of #3099 Step 5: SubstCacheKey built from two reconstructed-but-identical
/// scopes must be equal, enabling cross-reconstruction cache hits.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subst_cache_key_stable_across_reconstructed_scopes() {
    let ctx = EvalCtx::new();

    let make_subs = || {
        vec![Substitution {
            from: Spanned::new("x".to_string(), Span::dummy()),
            to: Spanned::new(Expr::Int(42.into()), Span::dummy()),
        }]
    };

    let ctx1 = ctx.with_instance_substitutions(make_subs());
    let ctx2 = ctx.with_instance_substitutions(make_subs());

    let name_id = intern_name("test_op");
    let key1 = SubstCacheKey {
        is_next_state: false,
        name_id,
        shared_id: ctx1.stable.shared.id,
        local_ops_id: ctx1.stable.scope_ids.local_ops,
        instance_subs_id: ctx1.stable.scope_ids.instance_substitutions,
        chained_ref_eval: false,
    };
    let key2 = SubstCacheKey {
        is_next_state: false,
        name_id,
        shared_id: ctx2.stable.shared.id,
        local_ops_id: ctx2.stable.scope_ids.local_ops,
        instance_subs_id: ctx2.stable.scope_ids.instance_substitutions,
        chained_ref_eval: false,
    };

    assert!(
        key1 == key2,
        "SubstCacheKey must be identical across reconstructed scopes with same content"
    );
}
