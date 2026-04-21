// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::helpers::make_ctx;
use super::*;

fn make_test_operator(name: &str, body: Expr) -> tla_core::ast::OperatorDef {
    tla_core::ast::OperatorDef {
        name: Spanned::dummy(name.to_string()),
        params: vec![],
        body: Spanned::dummy(body),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    }
}

fn fairness_let_defs() -> Vec<tla_core::ast::OperatorDef> {
    vec![
        make_test_operator(
            "vars",
            Expr::Tuple(vec![
                Spanned::dummy(Expr::Ident(
                    "x".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                )),
                Spanned::dummy(Expr::Ident(
                    "p".to_string(),
                    tla_core::name_intern::NameId::INVALID,
                )),
            ]),
        ),
        make_test_operator(
            "Step",
            Expr::Eq(
                Box::new(Spanned::dummy(Expr::Prime(Box::new(Spanned::dummy(
                    Expr::Ident("x".to_string(), tla_core::name_intern::NameId::INVALID),
                ))))),
                Box::new(Spanned::dummy(Expr::Int(BigInt::from(1)))),
            ),
        ),
    ]
}

fn collect_fairness_atoms(
    expr: &LiveExpr,
    actions: &mut Vec<Arc<Spanned<Expr>>>,
    subscripts: &mut Vec<Arc<Spanned<Expr>>>,
) {
    match expr {
        LiveExpr::ActionPred { expr, .. } => actions.push(Arc::clone(expr)),
        LiveExpr::Enabled {
            action, subscript, ..
        } => {
            actions.push(Arc::clone(action));
            if let Some(s) = subscript {
                subscripts.push(Arc::clone(s));
            }
        }
        LiveExpr::StateChanged { subscript, .. } => {
            if let Some(s) = subscript {
                subscripts.push(Arc::clone(s));
            }
        }
        LiveExpr::Not(inner)
        | LiveExpr::Always(inner)
        | LiveExpr::Eventually(inner)
        | LiveExpr::Next(inner) => collect_fairness_atoms(inner, actions, subscripts),
        LiveExpr::And(exprs) | LiveExpr::Or(exprs) => {
            for e in exprs {
                collect_fairness_atoms(e, actions, subscripts);
            }
        }
        LiveExpr::Bool(_) | LiveExpr::StatePred { .. } => {}
    }
}

fn assert_wrapped_let_ident(expr: &Arc<Spanned<Expr>>, expected_name: &str) {
    let Expr::Let(defs, body) = &expr.node else {
        panic!("expected top-level LET wrapper, got {:?}", expr.node);
    };
    let def_names: Vec<_> = defs.iter().map(|d| d.name.node.clone()).collect();
    assert_eq!(
        def_names,
        vec!["vars".to_string(), "Step".to_string()],
        "LET wrapper should retain in-scope fairness defs"
    );
    assert!(
        matches!(&body.node, Expr::Ident(name, _) if name == expected_name),
        "expected LET body to preserve Ident(\"{expected_name}\"), got {:?}",
        body.node
    );
}

fn assert_parsed_fairness_fallback_preserves_let_scope(op_name: &str) {
    let conv = AstToLive::new();
    let ctx = make_ctx();
    let let_defs = fairness_let_defs();
    let _guard = conv.push_let_defs(let_defs);

    let expr = spanned(Expr::Apply(
        Box::new(spanned(Expr::Ident(
            op_name.to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        vec![spanned(Expr::Ident(
            "Step".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))],
    ));

    let live = conv
        .convert(&ctx, &expr)
        .expect("parsed fairness fallback should convert");

    let mut actions = Vec::new();
    let mut subscripts = Vec::new();
    collect_fairness_atoms(&live, &mut actions, &mut subscripts);

    assert!(
        !actions.is_empty(),
        "parsed fairness fallback should store action expressions"
    );
    assert!(
        !subscripts.is_empty(),
        "parsed fairness fallback should store subscript expressions"
    );

    for action in &actions {
        assert_wrapped_let_ident(action, "Step");
    }
    for subscript in &subscripts {
        assert_wrapped_let_ident(subscript, "vars");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parsed_wf_fallback_preserves_let_scope_for_action_and_subscript() {
    assert_parsed_fairness_fallback_preserves_let_scope("WF_vars");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parsed_sf_fallback_preserves_let_scope_for_action_and_subscript() {
    assert_parsed_fairness_fallback_preserves_let_scope("SF_vars");
}
