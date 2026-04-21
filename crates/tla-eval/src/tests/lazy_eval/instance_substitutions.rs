// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use tla_core::ast::Substitution;
use tla_core::name_intern::intern_name;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_instance_lazy_binding_preserves_state_deps_after_untracked_force() {
    use crate::cache::eval_with_dep_tracking;

    let mut ctx = EvalCtx::new();
    let x_idx = ctx.register_var("x");
    let state = vec![Value::int(7)];
    ctx.bind_state_array(&state);

    let subs = std::sync::Arc::new(vec![Substitution {
        from: Spanned::dummy("y".to_string()),
        to: Spanned::dummy(Expr::StateVar("x".to_string(), x_idx.0, intern_name("x"))),
    }]);

    let mut sub_ctx = ctx.clone();
    sub_ctx.bindings = build_lazy_subst_bindings(&ctx.bindings, &subs);
    let stable = sub_ctx.stable_mut();
    stable.instance_substitutions = Some(subs);
    // Part of #3099: Invalidate scope_ids since we wrote instance_substitutions directly.
    stable.scope_ids.instance_substitutions = crate::cache::scope_ids::INVALIDATED;
    stable.eager_subst_bindings = Some(std::sync::Arc::new(vec![]));

    let y_expr = Spanned::dummy(Expr::Ident("y".to_string(), intern_name("y")));

    let first = eval(&sub_ctx, &y_expr).expect("initial lazy substitution force should succeed");
    assert_eq!(first, Value::int(7));

    let (second, deps) = eval_with_dep_tracking(&sub_ctx, &y_expr)
        .expect("cached lazy substitution should retain state deps for tracked reads");
    assert_eq!(second, Value::int(7));
    assert_eq!(
        deps.state.len(),
        1,
        "tracked read of cached lazy substitution must recover the underlying state dependency"
    );
    assert!(deps.next.is_empty());
    assert!(deps.local.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_module_ref_resolves_unqualified_ops_within_instance_module() {
    // Regression: when evaluating an instance reference `Inst!Next(1)`, operator calls inside
    // `Next` must resolve within the instanced module, not against the current module.
    //
    // This matters when both modules define the same operator name with different arities.
    let mod_m = r#"
---- MODULE M ----
EXTENDS Integers
SendMsg(x) == x + 1
Next(i) == SendMsg(i)
===="#;
    let mod_main = r#"
---- MODULE Main ----
EXTENDS Integers
SendMsg(x, y) == x + y
Inst == INSTANCE M
Op == Inst!Next(1)
===="#;

    let tree_m = parse_to_syntax_tree(mod_m);
    let lower_m = lower(FileId(0), &tree_m);
    assert!(
        lower_m.errors.is_empty(),
        "lower M errors: {:?}",
        lower_m.errors
    );
    let module_m = lower_m.module.expect("lower produced no module M");

    let tree_main = parse_to_syntax_tree(mod_main);
    let lower_main = lower(FileId(0), &tree_main);
    assert!(
        lower_main.errors.is_empty(),
        "lower Main errors: {:?}",
        lower_main.errors
    );
    let module_main = lower_main.module.expect("lower produced no module Main");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module_main);
    ctx.load_instance_module("M".to_string(), &module_m);

    let op_def = ctx.get_op("Op").expect("Op not found").clone();
    let v = eval(&ctx, &op_def.body).unwrap();
    assert_eq!(v, Value::int(2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_chained_module_ref_cache_respects_outer_instance_substitutions() {
    let mod_b = r#"
---- MODULE B ----
Val == x
===="#;
    let mod_a = r#"
---- MODULE A ----
BInst == INSTANCE B WITH x <- y
===="#;
    let mod_main = r#"
---- MODULE Main ----
AInst == INSTANCE A WITH y <- z
z == 0
Op == AInst!BInst!Val
===="#;

    let tree_b = parse_to_syntax_tree(mod_b);
    let lower_b = lower(FileId(0), &tree_b);
    assert!(
        lower_b.errors.is_empty(),
        "lower B errors: {:?}",
        lower_b.errors
    );
    let module_b = lower_b.module.expect("lower produced no module B");

    let tree_a = parse_to_syntax_tree(mod_a);
    let lower_a = lower(FileId(0), &tree_a);
    assert!(
        lower_a.errors.is_empty(),
        "lower A errors: {:?}",
        lower_a.errors
    );
    let module_a = lower_a.module.expect("lower produced no module A");

    let tree_main = parse_to_syntax_tree(mod_main);
    let lower_main = lower(FileId(0), &tree_main);
    assert!(
        lower_main.errors.is_empty(),
        "lower Main errors: {:?}",
        lower_main.errors
    );
    let module_main = lower_main.module.expect("lower produced no module Main");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module_main);
    ctx.load_instance_module("A".to_string(), &module_a);
    ctx.load_instance_module("B".to_string(), &module_b);

    let op_def = ctx.get_op("Op").expect("Op not found").clone();

    // Evaluate once to populate the chained reference cache.
    let ctx_z1 = ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::dummy("z".to_string()),
        to: Spanned::dummy(Expr::Int(1.into())),
    }]);
    let v1 = eval(&ctx_z1, &op_def.body).expect("first chained module ref eval should succeed");
    assert_eq!(v1, Value::int(1));

    // Evaluate again with a different outer substitution. If cache entries are keyed
    // too coarsely, this would incorrectly return 1.
    let ctx_z2 = ctx.with_instance_substitutions(vec![Substitution {
        from: Spanned::dummy("z".to_string()),
        to: Spanned::dummy(Expr::Int(2.into())),
    }]);
    let v2 = eval(&ctx_z2, &op_def.body).expect("second chained module ref eval should succeed");
    assert_eq!(v2, Value::int(2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_instance_substitution_uses_outer_operator_scope() {
    // Regression for #3056 Phase 5: forcing a lazy INSTANCE substitution must
    // clear the current instance's local operator scope. Otherwise the inner
    // module's `Node` would shadow Main's `Node`, and `I!Val` would incorrectly
    // evaluate to 1 instead of 2.
    let mod_inner = r#"
---- MODULE Inner ----
CONSTANT x
Node == 1
Val == x
===="#;
    let mod_main = r#"
---- MODULE Main ----
Node == 2
I == INSTANCE Inner WITH x <- Node
Op == I!Val
===="#;

    let tree_inner = parse_to_syntax_tree(mod_inner);
    let lower_inner = lower(FileId(0), &tree_inner);
    assert!(
        lower_inner.errors.is_empty(),
        "lower Inner errors: {:?}",
        lower_inner.errors
    );
    let module_inner = lower_inner.module.expect("lower produced no module Inner");

    let tree_main = parse_to_syntax_tree(mod_main);
    let lower_main = lower(FileId(0), &tree_main);
    assert!(
        lower_main.errors.is_empty(),
        "lower Main errors: {:?}",
        lower_main.errors
    );
    let module_main = lower_main.module.expect("lower produced no module Main");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module_main);
    ctx.load_instance_module("Inner".to_string(), &module_inner);

    let op_def = ctx.get_op("Op").expect("Op not found").clone();
    let value = eval(&ctx, &op_def.body).expect("lazy instance substitution should evaluate");
    assert_eq!(
        value,
        Value::int(2),
        "lazy substitution RHS must resolve Node in the outer module scope"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_instance_substitution_resolves_outer_instance_operator() {
    // Regression: nested named INSTANCE evaluation must keep the outer instance
    // module's operators available for substitution RHS evaluation.
    //
    // MidInst!Spec evaluates InnerInst!Spec inside Mid, where InnerInst maps
    // `pending <- Node`. `Node` is defined in Mid (not in Main). If nested
    // evaluation drops Mid's local operator scope, this fails with:
    // "Undefined variable: Node".
    let mod_inner = r#"
---- MODULE Inner ----
VARIABLE pending
Spec == pending = pending
===="#;
    let mod_mid = r#"
---- MODULE Mid ----
Node == {0, 1}
InnerInst == INSTANCE Inner WITH pending <- Node
Spec == InnerInst!Spec
===="#;
    let mod_main = r#"
---- MODULE Main ----
MidInst == INSTANCE Mid
Op == MidInst!Spec
===="#;

    let tree_inner = parse_to_syntax_tree(mod_inner);
    let lower_inner = lower(FileId(0), &tree_inner);
    assert!(
        lower_inner.errors.is_empty(),
        "lower Inner errors: {:?}",
        lower_inner.errors
    );
    let module_inner = lower_inner.module.expect("lower produced no module Inner");

    let tree_mid = parse_to_syntax_tree(mod_mid);
    let lower_mid = lower(FileId(0), &tree_mid);
    assert!(
        lower_mid.errors.is_empty(),
        "lower Mid errors: {:?}",
        lower_mid.errors
    );
    let module_mid = lower_mid.module.expect("lower produced no module Mid");

    let tree_main = parse_to_syntax_tree(mod_main);
    let lower_main = lower(FileId(0), &tree_main);
    assert!(
        lower_main.errors.is_empty(),
        "lower Main errors: {:?}",
        lower_main.errors
    );
    let module_main = lower_main.module.expect("lower produced no module Main");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module_main);
    ctx.load_instance_module("Mid".to_string(), &module_mid);
    ctx.load_instance_module("Inner".to_string(), &module_inner);

    let op_def = ctx.get_op("Op").expect("Op not found").clone();
    let v = eval(&ctx, &op_def.body).expect("nested instance substitution should evaluate");
    assert_eq!(v, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_substin_ident_substitution_preserves_outer_binding_chain() {
    // Regression for #3056 Phase 5 reachability: Expr::SubstIn installs
    // instance_substitutions without going through with_instance_scope().
    // The explicit-substitution fallback still runs here with a non-empty
    // binding chain, so clearing that chain would lose the outer binding for y.
    let expr = Spanned::dummy(Expr::SubstIn(
        vec![Substitution {
            from: Spanned::dummy("x".to_string()),
            to: Spanned::dummy(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
        }],
        Box::new(Spanned::dummy(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let ctx = EvalCtx::new().bind_local("y", Value::int(7));
    let value = eval(&ctx, &expr).expect("SubstIn ident substitution should evaluate");
    assert_eq!(
        value,
        Value::int(7),
        "SubstIn fallback must preserve the outer binding chain for substitution RHS evaluation"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_substin_statevar_substitution_preserves_outer_binding_chain() {
    // Same reachability gap as the ident case, but through eval_statevar's
    // explicit-substitution fallback. The substitution RHS depends on an outer
    // local binding, so dropping the chain would incorrectly make y undefined.
    let mut ctx = EvalCtx::new();
    let x_idx = ctx.register_var("x");
    let state = vec![Value::int(99)];
    ctx.bind_state_array(&state);
    let ctx = ctx.bind_local("y", Value::int(11));

    let expr = Spanned::dummy(Expr::SubstIn(
        vec![Substitution {
            from: Spanned::dummy("x".to_string()),
            to: Spanned::dummy(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )),
        }],
        Box::new(Spanned::dummy(Expr::StateVar(
            "x".to_string(),
            x_idx.0,
            tla_core::name_intern::intern_name("x"),
        ))),
    ));

    let value = eval(&ctx, &expr).expect("SubstIn state var substitution should evaluate");
    assert_eq!(
        value,
        Value::int(11),
        "SubstIn state-var fallback must preserve the outer binding chain for substitution RHS evaluation"
    );
}

// #3056 Phase 5 boundary rewind tests moved to instance_boundary.rs
