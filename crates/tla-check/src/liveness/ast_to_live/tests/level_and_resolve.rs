// Licensed under the Apache License, Version 2.0

// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Level detection and resolve_action_expr tests
//!
//! Split from liveness/ast_to_live/tests.rs — Part of #2779

use super::helpers::make_ctx;
use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_debug_flag_helpers_are_callable() {
    // Regression guard for OnceLock initializer recursion in debug helpers.
    // Each returns a bool indicating whether the debug flag env var is set.
    let resolve = debug_resolve();
    let let_ = debug_let();
    let instance = debug_instance_resolve();
    let subst = debug_subst();
    // In test environment without debug env vars, all should be false.
    // The key property: they return deterministic booleans without panicking.
    assert_eq!(
        resolve,
        debug_resolve(),
        "debug_resolve() should be idempotent"
    );
    assert_eq!(let_, debug_let(), "debug_let() should be idempotent");
    assert_eq!(
        instance,
        debug_instance_resolve(),
        "debug_instance_resolve() should be idempotent"
    );
    assert_eq!(subst, debug_subst(), "debug_subst() should be idempotent");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_level_constant() {
    let conv = AstToLive::new();
    assert_eq!(conv.get_level(&Expr::Bool(true)), ExprLevel::Constant);
    assert_eq!(
        conv.get_level(&Expr::Int(BigInt::from(42))),
        ExprLevel::Constant
    );
    assert_eq!(
        conv.get_level(&Expr::String("hello".to_string())),
        ExprLevel::Constant
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_level_state() {
    let conv = AstToLive::new();
    assert_eq!(
        conv.get_level(&Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID
        )),
        ExprLevel::State
    );

    // x + 1 is state level
    let add = Expr::Add(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    );
    assert_eq!(conv.get_level(&add), ExprLevel::State);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_level_action() {
    let conv = AstToLive::new();

    // x' is action level
    let prime = Expr::Prime(Box::new(spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ))));
    assert_eq!(conv.get_level(&prime), ExprLevel::Action);

    // UNCHANGED x is action level
    let unchanged = Expr::Unchanged(Box::new(spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ))));
    assert_eq!(conv.get_level(&unchanged), ExprLevel::Action);

    // x' = x + 1 is action level
    let next = Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))))),
        Box::new(spanned(Expr::Add(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
        ))),
    );
    assert_eq!(conv.get_level(&next), ExprLevel::Action);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_action_expr_skips_pre_eval_for_action_level_zero_arg_op() {
    use tla_core::ast::OperatorDef;

    let conv = AstToLive::new();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");

    let op_def = OperatorDef {
        name: spanned("Op".to_string()),
        params: Vec::new(),
        // Action-level: uses a primed variable reference.
        body: spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))))),
        local: false,
        contains_prime: true,
        guards_depend_on_prime: true,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };
    Arc::make_mut(ctx.shared_arc_mut())
        .ops
        .insert("Op".to_string(), Arc::new(op_def));

    // Bind next-state so that evaluating x' would succeed if we accidentally pre-evaluated.
    let mut next_state = crate::eval::Env::new();
    next_state.insert(Arc::<str>::from("x"), Value::SmallInt(7));
    let ctx = ctx.with_next_state(next_state);

    let resolved = conv.resolve_action_expr(
        &ctx,
        &spanned(Expr::Ident(
            "Op".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );
    assert!(
        matches!(resolved.node, Expr::Prime(_)),
        "expected action-level op to remain unevaluated, got {:?}",
        resolved.node
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_action_expr_pre_eval_for_constant_level_zero_arg_op() {
    use tla_core::ast::OperatorDef;

    let conv = AstToLive::new();

    let mut ctx = EvalCtx::new();

    let op_def = OperatorDef {
        name: spanned("Op".to_string()),
        params: Vec::new(),
        body: spanned(Expr::Add(
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
            Box::new(spanned(Expr::Int(BigInt::from(2)))),
        )),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };
    Arc::make_mut(ctx.shared_arc_mut())
        .ops
        .insert("Op".to_string(), Arc::new(op_def));

    let resolved = conv.resolve_action_expr(
        &ctx,
        &spanned(Expr::Ident(
            "Op".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );
    match resolved.node {
        Expr::Int(n) => assert_eq!(n, BigInt::from(3)),
        other => panic!("expected Expr::Int(3), got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_level_temporal() {
    let conv = AstToLive::new();

    // []P is temporal
    let always = Expr::Always(Box::new(spanned(Expr::Ident(
        "P".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ))));
    assert_eq!(conv.get_level(&always), ExprLevel::Temporal);

    // <>P is temporal
    let eventually = Expr::Eventually(Box::new(spanned(Expr::Ident(
        "P".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ))));
    assert_eq!(conv.get_level(&eventually), ExprLevel::Temporal);

    // P ~> Q is temporal
    let leads_to = Expr::LeadsTo(
        Box::new(spanned(Expr::Ident(
            "P".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "Q".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    );
    assert_eq!(conv.get_level(&leads_to), ExprLevel::Temporal);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unique_tags() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // Each state predicate should get a unique tag
    let expr1 = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let expr2 = spanned(Expr::Ident(
        "y".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));

    let live1 = conv.convert(&ctx, &expr1).unwrap();
    let live2 = conv.convert(&ctx, &expr2).unwrap();

    let tag1 = match live1 {
        LiveExpr::StatePred { tag, .. } => tag,
        _ => panic!("Expected StatePred"),
    };
    let tag2 = match live2 {
        LiveExpr::StatePred { tag, .. } => tag,
        _ => panic!("Expected StatePred"),
    };

    assert_ne!(tag1, tag2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_level_complex_nested() {
    // Test level detection for complex nested expressions
    let conv = AstToLive::new();

    // (x + 1) > 0 /\ y' = y + 1 is action level (contains primed)
    let complex = Expr::And(
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(Expr::Add(
                Box::new(spanned(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(0)))),
        ))),
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Prime(Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            )))))),
            Box::new(spanned(Expr::Add(
                Box::new(spanned(Expr::Ident(
                    "y".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
            ))),
        ))),
    );
    assert_eq!(conv.get_level(&complex), ExprLevel::Action);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_action_expr_expands_let_into_except_paths() {
    let conv = AstToLive::new();
    let ctx = make_ctx();

    // LET r == [adr |-> 1, val |-> 2]
    // IN  wmem' = [wmem EXCEPT ![r.adr] = r.val]
    let r_def = tla_core::ast::OperatorDef {
        name: Spanned::dummy("r".to_string()),
        params: Vec::new(),
        body: Spanned::dummy(Expr::Record(vec![
            (
                Spanned::dummy("adr".to_string()),
                Spanned::dummy(Expr::Int(BigInt::from(1))),
            ),
            (
                Spanned::dummy("val".to_string()),
                Spanned::dummy(Expr::Int(BigInt::from(2))),
            ),
        ])),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };

    let except = Expr::Except(
        Box::new(Spanned::dummy(Expr::Ident(
            "wmem".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![tla_core::ast::ExceptSpec {
            path: vec![tla_core::ast::ExceptPathElement::Index(Spanned::dummy(
                Expr::RecordAccess(
                    Box::new(Spanned::dummy(Expr::Ident(
                        "r".to_string(),
                        tla_core::name_intern::NameId::INVALID,
                    ))),
                    Spanned::dummy("adr".to_string()).into(),
                ),
            ))],
            value: Spanned::dummy(Expr::RecordAccess(
                Box::new(Spanned::dummy(Expr::Ident(
                    "r".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                ))),
                Spanned::dummy("val".to_string()).into(),
            )),
        }],
    );

    let let_expr = Spanned::dummy(Expr::Let(
        vec![r_def],
        Box::new(Spanned::dummy(Expr::Eq(
            Box::new(Spanned::dummy(Expr::Prime(Box::new(Spanned::dummy(
                Expr::Ident("wmem".to_string(), tla_core::name_intern::NameId::INVALID),
            ))))),
            Box::new(Spanned::dummy(except)),
        ))),
    ));

    let resolved = conv.resolve_action_expr(&ctx, &let_expr);
    assert!(
        !AstToLive::expr_references_name(&resolved.node, "r"),
        "resolved expr still references LET name 'r': {resolved:?}"
    );
}
