// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates Apache-2.0.

//! Tests for prime binding detection, guard safety, primed var refs,
//! and op_replacement resolution through prime visitors.

use super::*;

#[test]
fn test_might_need_prime_binding_v_respects_skip_prime_validation() {
    let mut ctx = ctx_with_ops(vec![make_zero_arg_op(
        "NeedsPrime",
        Expr::Bool(true),
        true,
        false,
    )]);
    let expr = Expr::Ident("NeedsPrime".into(), tla_core::name_intern::NameId::INVALID);

    assert!(might_need_prime_binding_v(&ctx, &expr));
    ctx.set_skip_prime_validation(true);
    assert!(!might_need_prime_binding_v(&ctx, &expr));
}

#[test]
fn test_might_need_prime_binding_v_treats_simple_prime_assignment_as_rhs_only() {
    let ctx = ctx_with_ops(vec![make_zero_arg_op(
        "HiddenPrimeOp",
        Expr::Bool(true),
        true,
        false,
    )]);
    let lhs_prime = Expr::Prime(boxed(Expr::Ident(
        "x".into(),
        tla_core::name_intern::NameId::INVALID,
    )));

    let no_rhs_prime = Expr::Eq(Box::new(sp(lhs_prime.clone())), boxed(Expr::Bool(true)));
    assert!(!might_need_prime_binding_v(&ctx, &no_rhs_prime));

    let rhs_prime_dep = Expr::Eq(
        Box::new(sp(lhs_prime)),
        boxed(Expr::Ident(
            "HiddenPrimeOp".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );
    assert!(might_need_prime_binding_v(&ctx, &rhs_prime_dep));
}

#[test]
fn test_is_operator_reference_guard_unsafe_v_ident_and_unresolved_module_ref() {
    let ctx = ctx_with_ops(vec![
        make_zero_arg_op("UnsafeOp", Expr::Bool(true), true, false),
        make_zero_arg_op("SafeOp", Expr::Bool(true), false, false),
    ]);

    assert!(is_operator_reference_guard_unsafe_v(
        &ctx,
        &Expr::Ident("UnsafeOp".into(), tla_core::name_intern::NameId::INVALID)
    ));
    assert!(!is_operator_reference_guard_unsafe_v(
        &ctx,
        &Expr::Ident("SafeOp".into(), tla_core::name_intern::NameId::INVALID)
    ));

    let unresolved_module_ref = Expr::ModuleRef(
        ModuleTarget::Named("UnknownInstance".to_string()),
        "Op".to_string(),
        vec![],
    );
    assert!(is_operator_reference_guard_unsafe_v(
        &ctx,
        &unresolved_module_ref
    ));
}

#[test]
fn test_is_operator_reference_guard_unsafe_v_enabled_expr_is_safe() {
    let ctx = ctx_with_ops(vec![make_zero_arg_op(
        "UnsafeOp",
        Expr::Bool(true),
        true,
        false,
    )]);
    let enabled_unsafe = Expr::Enabled(boxed(Expr::Ident(
        "UnsafeOp".into(),
        tla_core::name_intern::NameId::INVALID,
    )));
    let not_enabled_unsafe = Expr::Not(boxed(enabled_unsafe));

    assert!(!is_operator_reference_guard_unsafe_v(
        &ctx,
        &not_enabled_unsafe
    ));
}

#[test]
fn test_expr_references_primed_vars_v_follows_operator_body() {
    let ctx = ctx_with_ops(vec![make_zero_arg_op(
        "OpWithPrime",
        Expr::Prime(boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        false,
        false,
    )]);
    let tracked: FxHashSet<Arc<str>> = [Arc::from("x")].into_iter().collect();

    assert!(expr_references_primed_vars_v(
        &ctx,
        &Expr::Ident("OpWithPrime".into(), tla_core::name_intern::NameId::INVALID),
        &tracked,
    ));
}

#[test]
fn test_expr_references_primed_vars_v_under_prime_statevar_and_instance_expr() {
    let ctx = crate::eval::EvalCtx::new();
    let tracked: FxHashSet<Arc<str>> = [Arc::from("x")].into_iter().collect();

    let complex_under_prime = Expr::Prime(boxed(Expr::And(
        boxed(Expr::StateVar("x".into(), 0, intern_name("x"))),
        boxed(Expr::Bool(true)),
    )));
    assert!(expr_references_primed_vars_v(
        &ctx,
        &complex_under_prime,
        &tracked,
    ));

    let instance_expr = Expr::InstanceExpr(
        "M".to_string(),
        vec![Substitution {
            from: sp_str("x"),
            to: sp(Expr::Prime(boxed(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            )))),
        }],
    );
    assert!(!expr_references_primed_vars_v(
        &ctx,
        &instance_expr,
        &tracked
    ));
}

/// Build an EvalCtx with `Orig <- ReplacementWithPrime` op replacement.
/// ReplacementWithPrime body contains `x'` (prime).
fn build_op_replacement_ctx() -> (crate::eval::EvalCtx, Expr, Expr) {
    let replacement_def = make_zero_arg_op(
        "ReplacementWithPrime",
        Expr::Prime(boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        true,
        false,
    );
    let mut ctx = ctx_with_ops(vec![replacement_def]);
    ctx.add_op_replacement("Orig".to_string(), "ReplacementWithPrime".to_string());
    let ident_expr = Expr::Ident("Orig".into(), tla_core::name_intern::NameId::INVALID);
    let apply_expr = Expr::Apply(
        boxed(Expr::Ident(
            "Orig".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        vec![],
    );
    (ctx, ident_expr, apply_expr)
}

/// Regression test for #1473 (part 1): prime detection visitors follow op_replacements.
#[test]
fn test_op_replacement_resolution_prime_detection() {
    let (ctx, ident_expr, apply_expr) = build_op_replacement_ctx();

    assert!(expr_contains_prime_ctx_v(&ctx, &ident_expr));
    assert!(expr_contains_prime_ctx_v(&ctx, &apply_expr));
    assert!(expr_is_action_level_v(&ctx, &ident_expr));
    assert!(expr_is_action_level_v(&ctx, &apply_expr));
    assert!(might_need_prime_binding_v(&ctx, &ident_expr));
    assert!(might_need_prime_binding_v(&ctx, &apply_expr));
}

/// Regression test for #1473 (part 2): primed var refs and guard safety follow op_replacements.
#[test]
fn test_op_replacement_resolution_refs_and_guards() {
    let (ctx, ident_expr, apply_expr) = build_op_replacement_ctx();
    let tracked: FxHashSet<Arc<str>> = [Arc::from("x")].into_iter().collect();

    assert!(expr_references_primed_vars_v(&ctx, &ident_expr, &tracked));
    assert!(expr_references_primed_vars_v(&ctx, &apply_expr, &tracked));

    let refs = get_primed_var_refs_with_ctx_v(&ctx, &ident_expr);
    assert!(refs.contains(&Arc::from("x")), "got {:?}", refs);
    assert!(is_operator_reference_guard_unsafe_v(&ctx, &ident_expr));

    let or_expr = Expr::Or(
        boxed(Expr::Ident(
            "Orig".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        boxed(Expr::Bool(false)),
    );
    assert!(expr_contains_or_with_primed_ctx_v(&ctx, &or_expr));
}
