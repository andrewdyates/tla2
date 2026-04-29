// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CHC translation tests: direct translation, operator expansion, capture safety
//!
//! Split from z4_pdr/tests.rs — Part of #3692

use super::helpers::*;
use super::*;
use crate::bind_constants_from_config;
use crate::test_support::parse_module;
use num_bigint::BigInt;
use tla_core::ast::Expr;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_direct_chc_translation_safe() {
    // Test that we can construct a CHC problem directly
    // Init: count = 0
    // Next: count < 5 /\ count' = count + 1
    // Safety: count <= 5

    let vars: Vec<(&str, TlaSort)> = vec![("count", TlaSort::Int)];
    let mut trans = ChcTranslator::new(&vars).unwrap();

    let init = eq_expr(var_expr("count"), int_expr(0));
    trans.add_init(&init).unwrap();

    let guard = lt_expr(var_expr("count"), int_expr(5));
    let update = eq_expr(
        prime_expr("count"),
        add_expr(var_expr("count"), int_expr(1)),
    );
    let next = and_expr(guard, update);
    trans.add_next(&next).unwrap();

    let safety = le_expr(var_expr("count"), int_expr(5));
    trans.add_safety(&safety).unwrap();

    let result = trans.solve_pdr(pdr_config(10, 100)).unwrap();

    match result {
        PdrCheckResult::Safe { .. } | PdrCheckResult::Unknown { .. } => {
            // Expected: safe or unknown for skeleton PDR
        }
        PdrCheckResult::Unsafe { .. } => {
            panic!("Expected Safe or Unknown for safe spec");
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_direct_chc_translation_unsafe() {
    // Test unsafe spec: counter grows unboundedly
    // Init: count = 0
    // Next: count' = count + 1 (no guard)
    // Safety: count <= 5

    let vars: Vec<(&str, TlaSort)> = vec![("count", TlaSort::Int)];
    let mut trans = ChcTranslator::new(&vars).unwrap();

    let init = eq_expr(var_expr("count"), int_expr(0));
    trans.add_init(&init).unwrap();

    let next = eq_expr(
        prime_expr("count"),
        add_expr(var_expr("count"), int_expr(1)),
    );
    trans.add_next(&next).unwrap();

    let safety = le_expr(var_expr("count"), int_expr(5));
    trans.add_safety(&safety).unwrap();

    let result = trans.solve_pdr(pdr_config(10, 100)).unwrap();

    // Either Unsafe (found counterexample) or Unknown (couldn't prove)
    match result {
        PdrCheckResult::Unsafe { trace } => {
            assert!(!trace.is_empty(), "counterexample should have states");
        }
        PdrCheckResult::Unknown { .. } => {
            // Acceptable
        }
        PdrCheckResult::Safe { .. } => {
            panic!("Expected Unsafe or Unknown for unsafe spec");
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expand_operators_for_chc_recurses_into_in_range_setenum_and_let() {
    let src = r#"
---- MODULE ExpandOps ----
VARIABLE x
Lo == 0
Hi == 5
Rng == Lo..Hi
A == 1
S == {A, 2}
E1 == x \in Rng
E2 == x \in S
E3 == LET t == 1 IN x \in Rng
====
"#;
    let module = parse_module(src);
    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let e1 = ctx.get_op("E1").unwrap().body.clone();
    let e1_expanded = expand_operators_for_chc(&ctx, &e1, false);
    match &e1_expanded.node {
        Expr::In(_, set) => match &set.node {
            Expr::Range(lo, hi) => {
                match &lo.node {
                    Expr::Int(n) => assert_eq!(n, &BigInt::from(0)),
                    other => panic!("expected Int(0), got {other:?}"),
                }
                match &hi.node {
                    Expr::Int(n) => assert_eq!(n, &BigInt::from(5)),
                    other => panic!("expected Int(5), got {other:?}"),
                }
            }
            other => panic!("expected Range, got {other:?}"),
        },
        other => panic!("expected In, got {other:?}"),
    }

    let e2 = ctx.get_op("E2").unwrap().body.clone();
    let e2_expanded = expand_operators_for_chc(&ctx, &e2, false);
    match &e2_expanded.node {
        Expr::In(_, set) => match &set.node {
            Expr::SetEnum(elems) => {
                assert_eq!(elems.len(), 2);
                match &elems[0].node {
                    Expr::Int(n) => assert_eq!(n, &BigInt::from(1)),
                    other => panic!("expected Int(1), got {other:?}"),
                }
                match &elems[1].node {
                    Expr::Int(n) => assert_eq!(n, &BigInt::from(2)),
                    other => panic!("expected Int(2), got {other:?}"),
                }
            }
            other => panic!("expected SetEnum, got {other:?}"),
        },
        other => panic!("expected In, got {other:?}"),
    }

    let e3 = ctx.get_op("E3").unwrap().body.clone();
    let e3_expanded = expand_operators_for_chc(&ctx, &e3, false);
    match &e3_expanded.node {
        Expr::Let(_, body) => match &body.node {
            Expr::In(_, set) => match &set.node {
                Expr::Range(lo, hi) => {
                    assert!(matches!(&lo.node, Expr::Int(_)));
                    assert!(matches!(&hi.node, Expr::Int(_)));
                }
                other => panic!("expected Range under LET body, got {other:?}"),
            },
            other => panic!("expected In under LET body, got {other:?}"),
        },
        other => panic!("expected Let, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expand_operators_for_chc_skips_capture_unsafe_inlining() {
    let src = r#"
---- MODULE CaptureUnsafe ----
VARIABLE y
Wrap(x) == LET g(y) == x IN g(0)
Out == Wrap(y)
====
"#;
    let module = parse_module(src);
    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let out = ctx.get_op("Out").unwrap().body.clone();
    let expanded = expand_operators_for_chc(&ctx, &out, false);

    match &expanded.node {
        Expr::Apply(op, args) => {
            assert!(matches!(&op.node, Expr::Ident(name, _) if name == "Wrap"));
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected Apply for capture-unsafe inlining, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expand_operators_for_chc_inlines_when_capture_safe() {
    let src = r#"
---- MODULE CaptureSafe ----
VARIABLE y
Wrap(x) == LET g(z) == x IN g(0)
Out == Wrap(y)
====
"#;
    let module = parse_module(src);
    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let out = ctx.get_op("Out").unwrap().body.clone();
    let expanded = expand_operators_for_chc(&ctx, &out, false);

    match &expanded.node {
        Expr::Let(defs, _) => {
            assert_eq!(defs.len(), 1);
            assert!(matches!(
                &defs[0].body.node,
                Expr::Ident(name, _) | Expr::StateVar(name, _, _) if name == "y"
            ));
        }
        other => panic!("expected Let for capture-safe inlining, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expand_operators_for_chc_reifies_config_constants() {
    let src = r#"
---- MODULE ConfigConstExpand ----
CONSTANT N
VARIABLE x
Rng == 0..N
E == x \in Rng
====
"#;
    let module = parse_module(src);
    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let mut config = crate::Config::default();
    config.constants.insert(
        "N".to_string(),
        crate::ConstantValue::Value("5".to_string()),
    );
    bind_constants_from_config(&mut ctx, &config).expect("config constants should bind");

    let e = ctx.get_op("E").unwrap().body.clone();
    let expanded = expand_operators_for_chc(&ctx, &e, false);
    match &expanded.node {
        Expr::In(_, set) => match &set.node {
            Expr::Range(lo, hi) => {
                assert!(matches!(&lo.node, Expr::Int(n) if *n == BigInt::from(0)));
                assert!(matches!(&hi.node, Expr::Int(n) if *n == BigInt::from(5)));
            }
            other => panic!("expected Range, got {other:?}"),
        },
        other => panic!("expected In, got {other:?}"),
    }
}
