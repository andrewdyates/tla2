// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[allow(clippy::module_inception)]
mod tests {
    use crate::enumerate::expand_operators;
    use crate::eval::EvalCtx;
    use crate::test_support::parse_module;
    use num_bigint::BigInt;
    use tla_core::ast::Expr;
    use tla_core::Spanned;

    fn assert_int_expr(expr: &Spanned<Expr>, expected: i64) {
        match &expr.node {
            Expr::Int(n) => assert_eq!(n, &BigInt::from(expected)),
            other => unreachable!("expected Int({expected}), got {other:?}"),
        }
    }

    #[test]
    fn test_expand_operators_inlines_let_local_operator_body() {
        let src = r#"
---- MODULE ExpandLocal ----
Expr == LET AddOne(v) == v + 1 IN AddOne(2)
====
"#;
        let module = parse_module(src);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);

        let expr = ctx.get_op("Expr").expect("Expr op").body.clone();
        let expanded = expand_operators(&ctx, &expr);

        match &expanded.node {
            Expr::Let(_, body) => match &body.node {
                Expr::Add(lhs, rhs) => {
                    assert_int_expr(lhs, 2);
                    assert_int_expr(rhs, 1);
                }
                other => unreachable!("expected Add in LET body, got {other:?}"),
            },
            other => unreachable!("expected Let expression, got {other:?}"),
        }
    }

    #[test]
    fn test_expand_operators_stops_zero_arg_recursion() {
        let src = r#"
---- MODULE ExpandRec ----
Self == Self
Expr == Self
====
"#;
        let module = parse_module(src);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);

        let expr = ctx.get_op("Expr").expect("Expr op").body.clone();
        let expanded = expand_operators(&ctx, &expr);

        match &expanded.node {
            Expr::Ident(name, _) => assert_eq!(name, "Self"),
            other => unreachable!("expected recursion guard to keep Ident(Self), got {other:?}"),
        }
    }

    /// Regression #1558: FuncDef bound vars must shadow outer LET defs during expansion.
    #[test]
    fn test_expand_operators_funcdef_bound_var_shadows_let() {
        let src = "---- MODULE ExpandShadow ----
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
  ELSE LET x == CHOOSE x \\in S : TRUE IN f[x] + Sum(f, S \\ {x})
sc == [x \\in {1, 2, 3} |-> x + 1]
Expr == Sum(sc, {1, 2, 3})
====";
        let module = parse_module(src);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);
        let expanded = expand_operators(
            &ctx,
            &ctx.get_op("Expr")
                .expect("invariant: Expr op defined in test module")
                .body,
        );

        // Verify no FuncDef body contains a Choose (the capture bug).
        fn has_choose(e: &Expr) -> bool {
            match e {
                Expr::Choose(..) => true,
                Expr::Add(a, b)
                | Expr::Gt(a, b)
                | Expr::Lt(a, b)
                | Expr::Geq(a, b)
                | Expr::Leq(a, b) => has_choose(&a.node) || has_choose(&b.node),
                _ => false,
            }
        }
        fn walk(e: &Expr) -> bool {
            match e {
                Expr::FuncDef(_, body) => has_choose(&body.node) || walk(&body.node),
                Expr::Let(defs, body) => {
                    defs.iter().any(|d| walk(&d.body.node)) || walk(&body.node)
                }
                Expr::If(c, t, f) => walk(&c.node) || walk(&t.node) || walk(&f.node),
                Expr::Add(a, b) | Expr::FuncApply(a, b) => walk(&a.node) || walk(&b.node),
                _ => false,
            }
        }
        assert!(
            !walk(&expanded.node),
            "FuncDef body captured CHOOSE (#1558)"
        );
    }

    /// Regression #1596: Forall bound vars must shadow outer LET defs during expansion.
    #[test]
    fn test_expand_operators_forall_bound_var_shadows_let() {
        let src = r#"
---- MODULE ExpandForall ----
Expr == LET x == 42 IN \A x \in {1, 2, 3} : x > 0
====
"#;
        let module = parse_module(src);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);
        let expanded = expand_operators(
            &ctx,
            &ctx.get_op("Expr")
                .expect("invariant: Expr op defined in test module")
                .body,
        );

        // Inside the Forall body, x should remain as Ident("x"), not be inlined to 42.
        // Walk into Let -> Forall -> body and check that x is still an Ident.
        fn forall_body_has_ident_x(e: &Expr) -> bool {
            match e {
                Expr::Let(_, body) => forall_body_has_ident_x(&body.node),
                Expr::Forall(_, body) => {
                    crate::expr_visitor::expr_contains_ident_v(&body.node, "x")
                }
                _ => false,
            }
        }
        assert!(
            forall_body_has_ident_x(&expanded.node),
            "Forall body should contain Ident(x), not inlined constant (#1596)"
        );
    }

    /// Regression #1596: Exists bound vars must shadow outer LET defs during expansion.
    #[test]
    fn test_expand_operators_exists_bound_var_shadows_let() {
        let src = r#"
---- MODULE ExpandExists ----
Expr == LET x == 42 IN \E x \in {1, 2, 3} : x > 0
====
"#;
        let module = parse_module(src);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);
        let expanded = expand_operators(
            &ctx,
            &ctx.get_op("Expr")
                .expect("invariant: Expr op defined in test module")
                .body,
        );

        fn exists_body_has_ident_x(e: &Expr) -> bool {
            match e {
                Expr::Let(_, body) => exists_body_has_ident_x(&body.node),
                Expr::Exists(_, body) => {
                    crate::expr_visitor::expr_contains_ident_v(&body.node, "x")
                }
                _ => false,
            }
        }
        assert!(
            exists_body_has_ident_x(&expanded.node),
            "Exists body should contain Ident(x), not inlined constant (#1596)"
        );
    }

    /// Regression #1596: Choose bound vars must shadow outer LET defs during expansion.
    #[test]
    fn test_expand_operators_choose_bound_var_shadows_let() {
        let src = r#"
---- MODULE ExpandChoose ----
Expr == LET x == 42 IN CHOOSE x \in {1, 2, 3} : x > 0
====
"#;
        let module = parse_module(src);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);
        let expanded = expand_operators(
            &ctx,
            &ctx.get_op("Expr")
                .expect("invariant: Expr op defined in test module")
                .body,
        );

        fn choose_body_has_ident_x(e: &Expr) -> bool {
            match e {
                Expr::Let(_, body) => choose_body_has_ident_x(&body.node),
                Expr::Choose(_, body) => {
                    crate::expr_visitor::expr_contains_ident_v(&body.node, "x")
                }
                _ => false,
            }
        }
        assert!(
            choose_body_has_ident_x(&expanded.node),
            "Choose body should contain Ident(x), not inlined constant (#1596)"
        );
    }

    /// Regression #1596: SetFilter bound vars must shadow outer LET defs during expansion.
    #[test]
    fn test_expand_operators_setfilter_bound_var_shadows_let() {
        let src = r#"
---- MODULE ExpandSetFilter ----
Expr == LET x == 42 IN {x \in {1, 2, 3} : x > 0}
====
"#;
        let module = parse_module(src);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);
        let expanded = expand_operators(
            &ctx,
            &ctx.get_op("Expr")
                .expect("invariant: Expr op defined in test module")
                .body,
        );

        fn setfilter_body_has_ident_x(e: &Expr) -> bool {
            match e {
                Expr::Let(_, body) => setfilter_body_has_ident_x(&body.node),
                Expr::SetFilter(_, body) => {
                    crate::expr_visitor::expr_contains_ident_v(&body.node, "x")
                }
                _ => false,
            }
        }
        assert!(
            setfilter_body_has_ident_x(&expanded.node),
            "SetFilter body should contain Ident(x), not inlined constant (#1596)"
        );
    }

    /// Regression #1596: SetBuilder bound vars must shadow outer LET defs during expansion.
    #[test]
    fn test_expand_operators_setbuilder_bound_var_shadows_let() {
        let src = r#"
---- MODULE ExpandSetBuilder ----
Expr == LET x == 42 IN {x + 1 : x \in {1, 2, 3}}
====
"#;
        let module = parse_module(src);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);
        let expanded = expand_operators(
            &ctx,
            &ctx.get_op("Expr")
                .expect("invariant: Expr op defined in test module")
                .body,
        );

        fn setbuilder_body_has_ident_x(e: &Expr) -> bool {
            match e {
                Expr::Let(_, body) => setbuilder_body_has_ident_x(&body.node),
                Expr::SetBuilder(body, _) => {
                    crate::expr_visitor::expr_contains_ident_v(&body.node, "x")
                }
                _ => false,
            }
        }
        assert!(
            setbuilder_body_has_ident_x(&expanded.node),
            "SetBuilder body should contain Ident(x), not inlined constant (#1596)"
        );
    }

    /// Regression #1596: Lambda params must shadow outer LET defs during expansion.
    #[test]
    fn test_expand_operators_lambda_param_shadows_let() {
        let src = r#"
---- MODULE ExpandLambda ----
EXTENDS Naturals
Expr == LET x == 42 IN (LAMBDA x : x + 1)
====
"#;
        let module = parse_module(src);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);
        let expanded = expand_operators(
            &ctx,
            &ctx.get_op("Expr")
                .expect("invariant: Expr op defined in test module")
                .body,
        );

        fn lambda_body_has_ident_x(e: &Expr) -> bool {
            match e {
                Expr::Let(_, body) => lambda_body_has_ident_x(&body.node),
                Expr::Lambda(_, body) => {
                    crate::expr_visitor::expr_contains_ident_v(&body.node, "x")
                }
                _ => false,
            }
        }
        assert!(
            lambda_body_has_ident_x(&expanded.node),
            "Lambda body should contain Ident(x), not inlined constant (#1596)"
        );
    }

    /// Regression #1596: When an argument identifier would be captured by a
    /// binding in the operator body, the expansion must be skipped to preserve
    /// correct semantics. This tests the `would_capture` path in `fold_apply_expr`.
    #[test]
    fn test_expand_operators_capture_avoidance_skips_inline() {
        // RemovePending(cmd) has `LET filter(c) == c # cmd IN ...`
        // Calling RemovePending(c) would substitute cmd->c, creating
        // `LET filter(c) == c # c` which incorrectly captures the outer `c`.
        // The expander must detect this and keep the Apply node un-inlined.
        let src = r#"
---- MODULE ExpandCapture ----
EXTENDS Sequences
RemovePending(cmd) == LET filter(c) == c # cmd IN filter(1)
Expr == LET c == 1 IN RemovePending(c)
====
"#;
        let module = parse_module(src);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);
        let expanded = expand_operators(
            &ctx,
            &ctx.get_op("Expr")
                .expect("invariant: Expr op defined in test module")
                .body,
        );

        // The expanded tree should still contain an Apply(RemovePending, ...)
        // because capture avoidance prevented inlining.
        fn has_apply_remove_pending(e: &Expr) -> bool {
            match e {
                Expr::Apply(op, _) => {
                    if let Expr::Ident(name, _) = &op.node {
                        if name == "RemovePending" {
                            return true;
                        }
                    }
                    false
                }
                Expr::Let(defs, body) => {
                    defs.iter().any(|d| has_apply_remove_pending(&d.body.node))
                        || has_apply_remove_pending(&body.node)
                }
                _ => false,
            }
        }
        assert!(
            has_apply_remove_pending(&expanded.node),
            "Capture avoidance should keep Apply(RemovePending, ...) un-inlined (#1596)"
        );
    }

    #[test]
    fn test_expand_operators_inlines_when_binder_does_not_capture_param_use() {
        let src = r#"
---- MODULE ExpandPreciseCapture ----
Safe(cmd) == cmd + (CHOOSE x \in {1} : TRUE)
Expr == LET x == 1 IN Safe(x)
====
"#;
        let module = parse_module(src);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);
        let expanded = expand_operators(
            &ctx,
            &ctx.get_op("Expr")
                .expect("invariant: Expr op defined in test module")
                .body,
        );

        fn body_contains_safe_apply(e: &Expr) -> bool {
            match e {
                Expr::Apply(op, _) => matches!(&op.node, Expr::Ident(name, _) if name == "Safe"),
                Expr::Let(defs, body) => {
                    defs.iter().any(|d| body_contains_safe_apply(&d.body.node))
                        || body_contains_safe_apply(&body.node)
                }
                Expr::Add(lhs, rhs) => {
                    body_contains_safe_apply(&lhs.node) || body_contains_safe_apply(&rhs.node)
                }
                Expr::Choose(_, body) => body_contains_safe_apply(&body.node),
                _ => false,
            }
        }

        match &expanded.node {
            Expr::Let(_, body) => match &body.node {
                Expr::Add(lhs, rhs) => {
                    assert_int_expr(lhs, 1);
                    assert!(
                        matches!(&rhs.node, Expr::Choose(_, _)),
                        "expected unrelated binder to remain after inlining, got {:?}",
                        rhs.node
                    );
                }
                other => unreachable!("expected Add in LET body, got {other:?}"),
            },
            other => unreachable!("expected Let expression, got {other:?}"),
        }
        assert!(
            !body_contains_safe_apply(&expanded.node),
            "precise capture analysis should inline Safe(x) despite unrelated binder"
        );
    }

    #[test]
    fn test_expand_operators_preserves_recursive_param_substitutions() {
        let src = r#"
---- MODULE ExpandRecursiveParam ----
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                   ELSE LET z == CHOOSE z \in S : TRUE
                        IN f[z] + Sum(f, S \ {z})

Expr == LET sc == [i \in {1, 2} |-> i]
        IN Sum(sc, {1, 2})
====
"#;
        let module = parse_module(src);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);

        let expr = ctx.get_op("Expr").expect("Expr op").body.clone();
        let expanded = expand_operators(&ctx, &expr);

        assert!(
            !crate::expr_visitor::expr_contains_ident_v(&expanded.node, "f"),
            "expanded expression must not retain unbound recursive parameter f: {:?}",
            expanded.node
        );
        assert!(
            !crate::expr_visitor::expr_contains_ident_v(&expanded.node, "S"),
            "expanded expression must not retain unbound recursive parameter S: {:?}",
            expanded.node
        );
    }
}
