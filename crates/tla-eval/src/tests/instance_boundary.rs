// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! #3056 Phase 5 boundary rewind regression tests.
//!
//! These test the 3 audited `with_outer_resolution_scope()` call sites.
//! Each proves the pre-INSTANCE binding chain must be restored, not just
//! the metadata cleared.

use super::*;
use rustc_hash::FxHashMap;
use std::sync::Arc;
use tla_core::ast::{Expr, Substitution};
use tla_core::name_intern::{intern_name, NameId};

fn zero_arg_operator(name: &str, body: Expr) -> Arc<tla_core::ast::OperatorDef> {
    Arc::new(tla_core::ast::OperatorDef {
        name: Spanned::dummy(name.to_string()),
        params: vec![],
        body: Spanned::dummy(body),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    })
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_boundary_rewind_shared_zero_arg_op_uses_outer_scope() {
    // Boundary site 1: eval_ident_shared_zero_arg_op (eval_ident_zero_arg.rs)
    //
    // Inside `INSTANCE M WITH x <- y`, a shared zero-arg operator `Node` defined
    // in the outer module must resolve in the outer module's scope, not in the
    // instance scope. If with_outer_resolution_scope() doesn't restore the
    // pre-INSTANCE binding chain, instance bindings for `x` would shadow the
    // outer definition of `Node`.
    //
    // Spec: Main defines Node == 42, M has a variable x, Op == I!x where
    // I == INSTANCE M WITH x <- Node. Evaluating I!x should substitute x <- Node,
    // and Node must resolve to 42 from the outer scope.
    let mod_inner = r#"
---- MODULE Inner ----
VARIABLE x
Op == x
===="#;
    let mod_main = r#"
---- MODULE Main ----
Node == 42
Inst == INSTANCE Inner WITH x <- Node
Op == Inst!Op
===="#;

    let tree_inner = parse_to_syntax_tree(mod_inner);
    let lower_inner = lower(FileId(0), &tree_inner);
    assert!(
        lower_inner.errors.is_empty(),
        "Inner: {:?}",
        lower_inner.errors
    );
    let module_inner = lower_inner.module.expect("Inner module");

    let tree_main = parse_to_syntax_tree(mod_main);
    let lower_main = lower(FileId(0), &tree_main);
    assert!(
        lower_main.errors.is_empty(),
        "Main: {:?}",
        lower_main.errors
    );
    let module_main = lower_main.module.expect("Main module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module_main);
    ctx.load_instance_module("Inner".to_string(), &module_inner);

    let op_def = ctx.get_op("Op").expect("Op not found").clone();
    let value = eval(&ctx, &op_def.body).expect("shared zero-arg op should evaluate");
    assert_eq!(
        value,
        Value::int(42),
        "Boundary rewind site 1: shared zero-arg operator Node must resolve \
         in the outer scope (42), not be shadowed by instance substitution bindings"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_boundary_rewind_implicit_substitution_uses_outer_operator() {
    // Boundary site 2: eval_statevar_implicit_instance_substitution (eval_statevar.rs)
    //
    // If the outer module defines an operator with the same name as an inner
    // module's variable, the implicit substitution must evaluate the outer
    // operator body in the outer scope. If with_outer_resolution_scope() fails
    // to restore the pre-INSTANCE chain, the instance binding for the variable
    // name would shadow the outer operator.
    //
    // Spec: Main defines `pending == {0, 1}`, Inner has `VARIABLE pending`,
    // Op references `pending` inside INSTANCE scope. The implicit substitution
    // should resolve `pending` as the outer operator (returning {0, 1}).
    let mod_inner = r#"
---- MODULE Inner ----
VARIABLE pending
Op == pending = pending
===="#;
    let mod_main = r#"
---- MODULE Main ----
pending == {0, 1}
Inst == INSTANCE Inner WITH pending <- pending
Op == Inst!Op
===="#;

    let tree_inner = parse_to_syntax_tree(mod_inner);
    let lower_inner = lower(FileId(0), &tree_inner);
    assert!(
        lower_inner.errors.is_empty(),
        "Inner: {:?}",
        lower_inner.errors
    );
    let module_inner = lower_inner.module.expect("Inner module");

    let tree_main = parse_to_syntax_tree(mod_main);
    let lower_main = lower(FileId(0), &tree_main);
    assert!(
        lower_main.errors.is_empty(),
        "Main: {:?}",
        lower_main.errors
    );
    let module_main = lower_main.module.expect("Main module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module_main);
    ctx.load_instance_module("Inner".to_string(), &module_inner);

    let op_def = ctx.get_op("Op").expect("Op not found").clone();
    let value = eval(&ctx, &op_def.body).expect("implicit substitution should evaluate");
    assert_eq!(
        value,
        Value::Bool(true),
        "Boundary rewind site 2: implicit substitution must evaluate the outer \
         operator `pending` in the outer scope, not shadow it with instance bindings"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_implicit_instance_substitution_rejects_non_member_outer_operator() {
    let mod_inner = r#"
---- MODULE Inner ----
VARIABLE x
Op == x
===="#;
    let mod_main = r#"
---- MODULE Main ----
Foo == 42
Inst == INSTANCE Inner
Op == Inst!Foo
===="#;

    let tree_inner = parse_to_syntax_tree(mod_inner);
    let lower_inner = lower(FileId(0), &tree_inner);
    assert!(
        lower_inner.errors.is_empty(),
        "Inner: {:?}",
        lower_inner.errors
    );
    let module_inner = lower_inner.module.expect("Inner module");

    let tree_main = parse_to_syntax_tree(mod_main);
    let lower_main = lower(FileId(0), &tree_main);
    assert!(
        lower_main.errors.is_empty(),
        "Main: {:?}",
        lower_main.errors
    );
    let module_main = lower_main.module.expect("Main module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module_main);
    ctx.load_instance_module("Inner".to_string(), &module_inner);

    let op_def = ctx.get_op("Op").expect("Op not found").clone();
    let err = eval(&ctx, &op_def.body).expect_err("Inst!Foo must stay undefined");
    assert!(
        matches!(err, EvalError::UndefinedOp { ref name, .. } if name == "Inst!Foo"),
        "non-member outer operator must not be treated as implicit substitution: {err:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_boundary_rewind_nested_instance_restores_outer_local_ops() {
    let mut root_ctx = EvalCtx::new();
    Arc::make_mut(root_ctx.shared_arc_mut()).ops.insert(
        "Node".into(),
        zero_arg_operator("Node", Expr::Int(0.into())),
    );
    Arc::make_mut(root_ctx.shared_arc_mut()).ops.insert(
        "Term".into(),
        zero_arg_operator("Term", Expr::Ident("Node".into(), NameId::INVALID)),
    );

    let mut outer_ops = OpEnv::new();
    outer_ops.insert(
        "Node".into(),
        zero_arg_operator("Node", Expr::Int(42.into())),
    );
    let outer_ctx = root_ctx.with_instance_scope(outer_ops, vec![]);

    let mut inner_ops = OpEnv::new();
    inner_ops.insert(
        "Node".into(),
        zero_arg_operator("Node", Expr::Int((-1).into())),
    );
    let inner_ctx = outer_ctx.with_instance_scope(inner_ops, vec![]);

    let value = eval(
        &inner_ctx,
        &Spanned::dummy(Expr::Ident("Term".into(), NameId::INVALID)),
    )
    .expect("nested instance outer operator should evaluate");

    assert_eq!(
        value,
        Value::int(42),
        "outer-scope rewind must restore the enclosing instance local_ops, \
         not drop to the root shared operator or keep the inner shadow"
    );
}

// Boundary site 3 (eval_module_ref_target config override) is exercised by
// integration specs that use config overrides on instance-qualified operators
// (e.g., Bug44 / `I!Op <- XOverride`). The override path only invokes
// with_outer_resolution_scope() when the ModuleRef is evaluated from WITHIN
// a different INSTANCE scope, which requires nested INSTANCE chains. This
// scenario is covered by diagnose specs rather than unit tests.

fn lower_module_for_instance_test(file_id: FileId, src: &str) -> tla_core::ast::Module {
    let tree = parse_to_syntax_tree(src);
    let lowered = lower(file_id, &tree);
    assert!(
        lowered.errors.is_empty(),
        "lower errors: {:?}",
        lowered.errors
    );
    lowered.module.expect("module should lower")
}

fn always_body_span(module: &tla_core::ast::Module, op_name: &str) -> tla_core::Span {
    let def = module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == op_name => Some(def),
            _ => None,
        })
        .unwrap_or_else(|| panic!("operator {op_name} not found"));
    match &def.body.node {
        Expr::Always(inner) => inner.span,
        other => panic!("operator {op_name} should be Always(...), got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_instance_module_with_extends_registers_real_action_subscript_spans() {
    let module = lower_module_for_instance_test(
        FileId(0),
        r#"
---- MODULE Inner ----
EXTENDS Integers
VARIABLE x
vars == <<x>>
Next == x' = x + 1
Prop == [][Next]_vars
===="#,
    );
    let action_span = always_body_span(&module, "Prop");

    let mut ctx = EvalCtx::new();
    let module_by_name = [(module.name.node.as_str(), &module)]
        .into_iter()
        .collect::<FxHashMap<_, _>>();
    ctx.load_instance_module_with_extends("Inner".to_string(), &module, &module_by_name);

    assert!(
        ctx.is_action_subscript_span(action_span),
        "named-instance loading must preserve real [A]_v provenance for property classification"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_instance_module_with_extends_keeps_expanded_action_always_unmarked() {
    let module = lower_module_for_instance_test(
        FileId(0),
        r#"
---- MODULE InnerExpanded ----
EXTENDS Integers
VARIABLE x
vars == <<x>>
Next == x' = x + 1
Prop == []((Next) \/ UNCHANGED vars)
===="#,
    );
    let action_span = always_body_span(&module, "Prop");

    let mut ctx = EvalCtx::new();
    let module_by_name = [(module.name.node.as_str(), &module)]
        .into_iter()
        .collect::<FxHashMap<_, _>>();
    ctx.load_instance_module_with_extends("InnerExpanded".to_string(), &module, &module_by_name);

    assert!(
        !ctx.is_action_subscript_span(action_span),
        "named-instance loading must not mark the manually expanded [](A \\/ UNCHANGED v) form"
    );
}

struct PrimeShapeFixture {
    ctx: EvalCtx,
    _state: Vec<Value>,
    _next: Vec<Value>,
}

fn make_substin_instance_ctx_for_shape_test() -> PrimeShapeFixture {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    let state = vec![Value::int(1), Value::int(2)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(10), Value::int(20)];
    ctx.bind_next_state_array(&next);

    let subs = Arc::new(vec![Substitution {
        from: Spanned::dummy("x".to_string()),
        to: Spanned::dummy(Expr::Ident("y".to_string(), tla_core::NameId::INVALID)),
    }]);

    let mut sub_ctx = ctx.clone();
    sub_ctx.bindings = build_lazy_subst_bindings(&ctx.bindings, &subs);
    let stable = sub_ctx.stable_mut();
    stable.instance_substitutions = Some(subs);
    stable.scope_ids.instance_substitutions = crate::cache::scope_ids::compute_instance_subs_id(
        stable
            .instance_substitutions
            .as_deref()
            .expect("shape test installs instance substitutions"),
    );
    stable.eager_subst_bindings = Some(Arc::new(vec![]));
    PrimeShapeFixture {
        ctx: sub_ctx,
        _state: state,
        _next: next,
    }
}

fn make_with_instance_scope_ctx_for_shape_test() -> PrimeShapeFixture {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("y");
    let state = vec![Value::int(2)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(20)];
    ctx.bind_next_state_array(&next);

    let scoped_ctx = ctx.with_instance_scope(
        OpEnv::new(),
        vec![Substitution {
            from: Spanned::dummy("x".to_string()),
            to: Spanned::dummy(Expr::Ident("y".to_string(), tla_core::NameId::INVALID)),
        }],
    );

    PrimeShapeFixture {
        ctx: scoped_ctx,
        _state: state,
        _next: next,
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_substin_instance_prime_ctx_uses_non_legacy_shape() {
    let fixture = make_substin_instance_ctx_for_shape_test();
    let sub_ctx = &fixture.ctx;
    let prime_expr = Spanned::dummy(Expr::Prime(Box::new(Spanned::dummy(Expr::Ident(
        "x".to_string(),
        tla_core::NameId::INVALID,
    )))));

    assert!(
        sub_ctx.instance_substitutions().is_some(),
        "SubstIn instance contexts should carry instance_substitutions"
    );
    assert!(
        sub_ctx.eager_subst_bindings.is_some(),
        "SubstIn instance contexts should install the eager-substitution marker"
    );
    assert!(
        sub_ctx.bindings.has_instance_binding(intern_name("x")),
        "SubstIn instance contexts should install an Instance-sourced binding-chain entry"
    );

    let result = eval(sub_ctx, &prime_expr).expect("SubstIn x' evaluation should succeed");
    assert_eq!(
        result,
        Value::int(20),
        "INSTANCE prime resolution should still flow through the lazy binding chain"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_with_instance_scope_is_legacy_prime_shape() {
    let fixture = make_with_instance_scope_ctx_for_shape_test();
    let scoped_ctx = &fixture.ctx;
    let prime_expr = Spanned::dummy(Expr::Prime(Box::new(Spanned::dummy(Expr::Ident(
        "x".to_string(),
        tla_core::NameId::INVALID,
    )))));

    assert!(
        scoped_ctx.instance_substitutions().is_some(),
        "with_instance_scope should still carry instance_substitutions"
    );
    assert!(
        scoped_ctx.eager_subst_bindings.is_none(),
        "with_instance_scope leaves eager_subst_bindings unset, which is the legacy eval_prime shape"
    );
    assert!(
        scoped_ctx.bindings.is_empty(),
        "with_instance_scope clears the binding chain instead of installing Instance bindings"
    );

    let result = eval(scoped_ctx, &prime_expr).expect("legacy x' evaluation should succeed");
    assert_eq!(
        result,
        Value::int(20),
        "legacy with_instance_scope evaluation should still resolve through instance_substitutions"
    );
}
