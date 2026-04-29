// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Temporal operator conversion tests: Always, Eventually, LeadsTo, fairness, IF/CASE
//!
//! Split from liveness/ast_to_live/tests.rs — Part of #2779

use super::helpers::make_ctx;
use super::*;

mod branching;
mod core_ops;
mod fairness;

/// Regression test for #2116: WF_vars(A) with simple-identifier subscript must NOT
/// inline the body of `vars` when quantifier bindings are active, because inlining
/// `vars == <<x, p>>` into `\A p \in Procs : WF_vars(Step(p))` would expose the
/// inlined `p` to the quantifier-bound `p`, causing accidental variable capture.
///
/// The fix in `resolve_fairness_subscript` keeps `Ident("vars")` instead of inlining.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_wf_simple_ident_subscript_not_inlined_under_quantifier() {
    use crate::eval::{BindingChain, BindingValue};
    use tla_core::ast::OperatorDef;
    use tla_core::name_intern::intern_name;

    let conv = AstToLive::new();
    let mut ctx = make_ctx();

    // Register state variables x and p
    ctx.register_var("x");
    ctx.register_var("p");

    // Define shared op: vars == <<x, p>>
    let vars_body = Expr::Tuple(vec![
        Spanned::dummy(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
        Spanned::dummy(Expr::Ident(
            "p".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
    ]);
    let vars_op = Arc::new(OperatorDef {
        name: Spanned::dummy("vars".to_string()),
        params: vec![],
        body: Spanned::dummy(vars_body),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    });
    Arc::make_mut(ctx.shared_arc_mut())
        .ops
        .insert("vars".to_string(), vars_op);

    // Push a quantifier binding for p (simulates \A p \in Procs)
    let p_name_id = intern_name("p");
    let chain = BindingChain::empty().cons(p_name_id, BindingValue::eager(Value::int(1)));
    let _guard = conv.push_quantifier_bindings(Some(chain));

    // Build WF_vars(TRUE): WeakFair(Ident("vars"), Bool(true))
    let wf_expr = spanned(Expr::WeakFair(
        Box::new(spanned(Expr::Ident(
            "vars".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Bool(true))),
    ));

    let live = conv
        .convert(&ctx, &wf_expr)
        .expect("WF conversion should succeed");

    // Walk the LiveExpr tree to find subscripts in Enabled and StateChanged nodes.
    // They should contain Ident("vars"), NOT an inlined Tuple.
    fn collect_subscripts(expr: &LiveExpr, subscripts: &mut Vec<Arc<Spanned<Expr>>>) {
        match expr {
            LiveExpr::Enabled {
                subscript: Some(s), ..
            } => {
                subscripts.push(Arc::clone(s));
            }
            LiveExpr::StateChanged {
                subscript: Some(s), ..
            } => {
                subscripts.push(Arc::clone(s));
            }
            LiveExpr::Not(inner) | LiveExpr::Always(inner) | LiveExpr::Eventually(inner) => {
                collect_subscripts(inner, subscripts);
            }
            LiveExpr::And(exprs) | LiveExpr::Or(exprs) => {
                for e in exprs {
                    collect_subscripts(e, subscripts);
                }
            }
            _ => {}
        }
    }

    let mut subscripts = Vec::new();
    collect_subscripts(&live, &mut subscripts);
    assert!(
        !subscripts.is_empty(),
        "WF conversion should produce Enabled/StateChanged nodes with subscripts"
    );

    for sub in &subscripts {
        assert!(
            matches!(&sub.node, Expr::Ident(name, _) if name == "vars"),
            "Subscript should be Ident(\"vars\"), not inlined body. Got: {:?}",
            sub.node
        );
    }
}
