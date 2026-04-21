// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `mark_hoistable_tir` analysis and TIR hoist classification.

use super::*;
use crate::cache::clear_quantifier_hoist_cache;
use rustc_hash::FxHashSet;
use std::rc::Rc;
use tla_core::ast::{Expr, Module, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId, NameId, Span, Spanned};
use tla_tir::nodes::{
    TirBoolOp, TirBoundVar, TirCmpOp, TirExpr, TirLetDef, TirNameKind, TirNameRef,
};
use tla_tir::{lower_expr, TirType};
use tla_value::Value;

fn parse_module(src: &str) -> Module {
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors for module:\n{src}\n{:?}",
        lower_result.errors
    );
    lower_result.module.expect("module should lower")
}

fn find_operator_body<'a>(module: &'a Module, name: &str) -> &'a Spanned<Expr> {
    module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == name => Some(&def.body),
            _ => None,
        })
        .unwrap_or_else(|| panic!("operator '{name}' should exist"))
}

/// Extract the outermost Forall's vars and body from a lowered TIR expression.
///
/// After multi-variable quantifier desugaring (#3694), `\A x, y : body` becomes
/// `\A x : \A y : body`, so this returns only the outermost single-variable
/// forall. Use `unwrap_nested_forall` to reach deeper levels.
fn with_tir_forall_vars_and_body<T>(src: &str, f: impl FnOnce(&[TirBoundVar], &TirExpr) -> T) -> T {
    let module_src = format!("---- MODULE Test ----\n\nOp == {src}\n\n====");
    let module = parse_module(&module_src);
    let lowered =
        lower_expr(&module, find_operator_body(&module, "Op")).expect("forall body should lower");

    match &lowered.node {
        TirExpr::Forall { vars, body } => f(vars, &body.node),
        other => panic!("Op should lower to a forall expression, got {other:?}"),
    }
}

fn sp(node: TirExpr) -> Spanned<TirExpr> {
    Spanned::new(node, Span::dummy())
}

fn int_const(value: i64) -> Spanned<TirExpr> {
    sp(TirExpr::Const {
        value: Value::int(value),
        ty: TirType::Int,
    })
}

fn bool_const(value: bool) -> Spanned<TirExpr> {
    sp(TirExpr::Const {
        value: Value::Bool(value),
        ty: TirType::Bool,
    })
}

fn ident_name(name: &str, ty: TirType) -> TirNameRef {
    TirNameRef {
        name: name.to_string(),
        name_id: NameId::INVALID,
        kind: TirNameKind::Ident,
        ty,
    }
}

fn state_name(name: &str, index: u16, ty: TirType) -> TirNameRef {
    TirNameRef {
        name: name.to_string(),
        name_id: NameId::INVALID,
        kind: TirNameKind::StateVar { index },
        ty,
    }
}

fn bound_var(name: &str) -> TirBoundVar {
    TirBoundVar {
        name: name.to_string(),
        name_id: NameId::INVALID,
        domain: None,
        pattern: None,
    }
}

#[test]
fn test_mark_hoistable_tir_cache_distinguishes_bounds_suffixes() {
    clear_quantifier_hoist_cache();

    // After multi-variable quantifier desugaring (#3694):
    //   \A x \in {1,2}, y \in {3,4} : x = 1 /\ y = 3
    // becomes:
    //   \A x \in {1,2} : \A y \in {3,4} : x = 1 /\ y = 3
    //
    // The outer forall has vars=[x], body = Forall{vars=[y], body = conjunction}.
    // We test the hoist cache on the conjunction body with two different bound sets.
    with_tir_forall_vars_and_body(
        r#"\A x \in {1, 2}, y \in {3, 4} : x = 1 /\ y = 3"#,
        |outer_vars, outer_body| {
            // After desugaring, outer_body is the nested Forall for y
            let TirExpr::Forall {
                vars: inner_vars,
                body: inner_body,
            } = outer_body
            else {
                panic!(
                    "after desugaring, outer forall body should be nested Forall, got {outer_body:?}"
                );
            };

            // inner_body is the conjunction: x = 1 /\ y = 3
            let conjunction = &inner_body.node;
            let TirExpr::BoolBinOp {
                left,
                op: TirBoolOp::And,
                right,
            } = conjunction
            else {
                panic!("inner forall body should be a conjunction, got {conjunction:?}");
            };

            // Build bound-name sets: "both x and y" vs "only y"
            let mut both_bound_names = collect_tir_bound_names(outer_vars);
            both_bound_names.extend(collect_tir_bound_names(inner_vars));
            let y_only_bound_names = collect_tir_bound_names(inner_vars);

            let body_ptr = conjunction as *const TirExpr as usize;
            let both_key = (body_ptr, 1usize);
            let y_only_key = (body_ptr, 2usize);

            let both_hoistable = mark_hoistable_tir(conjunction, &both_bound_names, both_key);
            let both_again = mark_hoistable_tir(conjunction, &both_bound_names, both_key);
            let y_only_hoistable = mark_hoistable_tir(conjunction, &y_only_bound_names, y_only_key);

            let lhs_key = std::ptr::addr_of!(left.node) as usize;
            let rhs_key = std::ptr::addr_of!(right.node) as usize;

            assert!(
                Rc::ptr_eq(&both_hoistable, &both_again),
                "repeating the same TIR cache key should reuse the cached hoistable set"
            );
            assert!(
                !Rc::ptr_eq(&both_hoistable, &y_only_hoistable),
                "different bound-name sets must produce distinct cached TIR sets"
            );
            assert!(
                !both_hoistable.contains(&lhs_key),
                "x = 1 still depends on bound x in the 'both' set"
            );
            assert!(
                y_only_hoistable.contains(&lhs_key),
                "x = 1 must become hoistable when bounds narrow to only y"
            );
            assert!(
                !y_only_hoistable.contains(&rhs_key),
                "y = 3 still depends on the bound y"
            );
        },
    );

    clear_quantifier_hoist_cache();
}

#[test]
fn test_is_tir_hoist_cacheable_classification() {
    assert!(is_tir_hoist_cacheable(&TirExpr::BoolBinOp {
        left: Box::new(bool_const(true)),
        op: TirBoolOp::And,
        right: Box::new(bool_const(false)),
    }));
    assert!(is_tir_hoist_cacheable(&TirExpr::Range {
        lo: Box::new(int_const(1)),
        hi: Box::new(int_const(3)),
    }));
    assert!(is_tir_hoist_cacheable(&TirExpr::Record(vec![])));
    assert!(is_tir_hoist_cacheable(&TirExpr::Case {
        arms: vec![],
        other: None,
    }));

    assert!(!is_tir_hoist_cacheable(&TirExpr::Apply {
        op: Box::new(sp(TirExpr::OpRef("Id".to_string()))),
        args: vec![int_const(2)],
    }));
    assert!(!is_tir_hoist_cacheable(&TirExpr::FuncApply {
        func: Box::new(sp(TirExpr::OpRef("F".to_string()))),
        arg: Box::new(int_const(2)),
    }));
    assert!(!is_tir_hoist_cacheable(&TirExpr::Prime(Box::new(sp(
        TirExpr::Name(state_name("x", 0, TirType::Int),)
    )))));
    assert!(!is_tir_hoist_cacheable(&TirExpr::Enabled(Box::new(
        bool_const(true)
    ))));
    assert!(!is_tir_hoist_cacheable(&TirExpr::Name(ident_name(
        "x",
        TirType::Int,
    ))));
    assert!(!is_tir_hoist_cacheable(&TirExpr::Let {
        defs: vec![TirLetDef {
            name: "Tmp".to_string(),
            name_id: NameId::INVALID,
            params: vec![],
            body: int_const(1),
        }],
        body: Box::new(int_const(1)),
    }));
}

#[test]
fn test_set_construction_tir_binding_forms_are_safe_but_not_cacheable() {
    let var = bound_var("x");
    let set_builder = TirExpr::SetBuilder {
        body: Box::new(int_const(1)),
        vars: vec![var.clone()],
    };
    let set_filter = TirExpr::SetFilter {
        var: var.clone(),
        body: Box::new(bool_const(true)),
    };

    assert!(is_tir_hoist_safe(&set_builder));
    assert!(is_tir_hoist_safe(&set_filter));
    assert!(!is_tir_hoist_cacheable(&set_builder));
    assert!(!is_tir_hoist_cacheable(&set_filter));
    assert!(!is_tir_hoist_safe(&TirExpr::FuncDef {
        vars: vec![var.clone()],
        body: Box::new(int_const(1)),
    }));
    assert!(!is_tir_hoist_safe(&TirExpr::Choose {
        var: var.clone(),
        body: Box::new(bool_const(true)),
    }));
    assert!(!is_tir_hoist_safe(&TirExpr::Forall {
        vars: vec![var.clone()],
        body: Box::new(bool_const(true)),
    }));
    assert!(!is_tir_hoist_safe(&TirExpr::Exists {
        vars: vec![var],
        body: Box::new(bool_const(true)),
    }));
}

#[test]
fn test_unsafe_tir_forms_poison_parent_hoistability() {
    clear_quantifier_hoist_cache();

    let prime_cmp = TirExpr::Cmp {
        left: Box::new(sp(TirExpr::Prime(Box::new(sp(TirExpr::Name(state_name(
            "x",
            0,
            TirType::Int,
        ))))))),
        op: TirCmpOp::Eq,
        right: Box::new(int_const(1)),
    };
    let apply_cmp = TirExpr::Cmp {
        left: Box::new(sp(TirExpr::Apply {
            op: Box::new(sp(TirExpr::OpRef("Id".to_string()))),
            args: vec![int_const(2)],
        })),
        op: TirCmpOp::Eq,
        right: Box::new(int_const(2)),
    };

    for expr in [&prime_cmp, &apply_cmp] {
        let key = (expr as *const TirExpr as usize, 0);
        let hoistable = mark_hoistable_tir(expr, &FxHashSet::default(), key);
        let expr_key = expr as *const TirExpr as usize;
        assert!(
            !hoistable.contains(&expr_key),
            "unsafe TIR form should poison a bound-invariant parent instead of letting it cache"
        );
    }

    clear_quantifier_hoist_cache();
}

#[test]
fn test_label_does_not_poison_parent_hoistability() {
    clear_quantifier_hoist_cache();

    // A comparison wrapping a labeled invariant subexpression should remain
    // hoistable. Before the fix, Label was not in is_nonpoisoning_tir_binding,
    // so it would poison the parent Cmp even though labels have no runtime
    // effect in eval_tir.
    let labeled_const = sp(TirExpr::Label {
        name: "lbl".to_string(),
        body: Box::new(int_const(42)),
    });
    let cmp = TirExpr::Cmp {
        left: Box::new(labeled_const),
        op: TirCmpOp::Eq,
        right: Box::new(int_const(42)),
    };

    let key = (&cmp as *const TirExpr as usize, 0);
    let hoistable = mark_hoistable_tir(&cmp, &FxHashSet::default(), key);
    let cmp_key = &cmp as *const TirExpr as usize;

    assert!(
        hoistable.contains(&cmp_key),
        "a comparison containing a Label wrapper over an invariant constant \
         must remain hoistable — Label is a transparent wrapper"
    );

    clear_quantifier_hoist_cache();
}
