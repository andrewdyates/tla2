// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for `mark_hoistable` analysis and Stage 1 allowlist.
//!
//! Part of #3128: Extracted from mark_hoistable.rs to stay under the
//! 500-line file limit.

use super::*;
use rustc_hash::FxHashSet;
use crate::cache::clear_quantifier_hoist_cache;
use tla_core::ast::{BoundVar, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId, Spanned};

fn with_forall_bounds_and_body<T>(src: &str, f: impl FnOnce(&[BoundVar], &Expr) -> T) -> T {
    let module_src = format!("---- MODULE Test ----\n\nOp == {}\n\n====", src);
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("Op module should lower");

    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                if let Expr::Forall(bounds, body) = &def.body.node {
                    return f(bounds, &body.node);
                }
                panic!("Op should lower to a forall expression");
            }
        }
    }

    panic!("Op definition not found");
}

#[test]
fn test_mark_hoistable_cache_distinguishes_bounds_suffixes() {
    clear_quantifier_hoist_cache();

    with_forall_bounds_and_body(
        r#"\A x \in {1, 2}, y \in {3, 4} : x = 1 /\ y = 3"#,
        |bounds, body| {
            let outer_bound_names = bounds
                .iter()
                .map(|bound| bound.name.node.as_str())
                .collect::<FxHashSet<_>>();
            let inner_bounds = &bounds[1..];
            let inner_bound_names = inner_bounds
                .iter()
                .map(|bound| bound.name.node.as_str())
                .collect::<FxHashSet<_>>();
            let body_ptr = body as *const Expr as usize;
            let outer_key = (body_ptr, bounds.as_ptr() as usize);
            let inner_key = (body_ptr, inner_bounds.as_ptr() as usize);
            let outer_hoistable = mark_hoistable(body, &outer_bound_names, outer_key);
            let inner_hoistable = mark_hoistable(body, &inner_bound_names, inner_key);

            let Expr::And(lhs, rhs) = body else {
                panic!("forall body should be a conjunction");
            };
            let lhs_key = std::ptr::addr_of!(lhs.node) as usize;
            let rhs_key = std::ptr::addr_of!(rhs.node) as usize;

            assert_ne!(
                bounds.as_ptr(),
                inner_bounds.as_ptr(),
                "recursive bounds suffixes must have distinct addresses"
            );
            assert!(
                !outer_hoistable.contains(&lhs_key),
                "x = 1 still depends on outer x"
            );
            assert!(
                inner_hoistable.contains(&lhs_key),
                "x = 1 must become hoistable once recursion narrows bounds to y"
            );
            assert!(
                !inner_hoistable.contains(&rhs_key),
                "y = 3 still depends on the inner-bound y"
            );
            assert_eq!(
                MARK_HOISTABLE_CACHE.with(|cache| cache.borrow().len()),
                2,
                "outer and inner suffixes must occupy distinct cache entries"
            );
        },
    );

    clear_quantifier_hoist_cache();
}

/// Verify Stage 1 allowlist: pure structural expressions (Eq, Union, SetEnum)
/// are hoistable, but Apply nodes are NOT hoistable even when they don't
/// reference the bound variable.
#[test]
fn test_stage1_allowlist_excludes_apply() {
    clear_quantifier_hoist_cache();

    // \A x \in {1} : {2, 3} = {2, 3}
    // Body: Eq(SetEnum([2, 3]), SetEnum([2, 3]))
    // Both SetEnum and Eq are in the Stage 1 allowlist, so the whole
    // body should be hoistable (it doesn't reference x).
    with_forall_bounds_and_body(r#"\A x \in {1} : {2, 3} = {2, 3}"#, |bounds, body| {
        let bound_names = bounds
            .iter()
            .map(|b| b.name.node.as_str())
            .collect::<FxHashSet<_>>();
        let key = (body as *const Expr as usize, bounds.as_ptr() as usize);
        let hoistable = mark_hoistable(body, &bound_names, key);

        let body_key = body as *const Expr as usize;
        assert!(
            hoistable.contains(&body_key),
            "Eq(SetEnum, SetEnum) should be hoistable (Stage 1 safe)"
        );
    });

    clear_quantifier_hoist_cache();
}

/// Verify is_stage1_hoistable classification for individual expression types.
#[test]
fn test_is_stage1_hoistable_classification() {
    use tla_core::name_intern::NameId;
    use tla_core::Span;

    let span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };
    let dummy = || {
        Box::new(Spanned {
            node: Expr::Bool(true),
            span,
        })
    };

    // Allowed: binary pure ops
    assert!(is_stage1_hoistable(&Expr::Eq(dummy(), dummy())));
    assert!(is_stage1_hoistable(&Expr::Union(dummy(), dummy())));
    assert!(is_stage1_hoistable(&Expr::Range(dummy(), dummy())));
    assert!(is_stage1_hoistable(&Expr::In(dummy(), dummy())));
    assert!(is_stage1_hoistable(&Expr::Add(dummy(), dummy())));

    // Allowed: unary pure ops
    assert!(is_stage1_hoistable(&Expr::Not(dummy())));
    assert!(is_stage1_hoistable(&Expr::Domain(dummy())));
    assert!(is_stage1_hoistable(&Expr::Powerset(dummy())));

    // Allowed: value constructors
    assert!(is_stage1_hoistable(&Expr::Tuple(vec![])));
    assert!(is_stage1_hoistable(&Expr::SetEnum(vec![])));
    assert!(is_stage1_hoistable(&Expr::If(dummy(), dummy(), dummy())));

    // Excluded: binding constructs currently have unsound hoist interactions.
    let bound = BoundVar {
        name: Spanned {
            node: "x".into(),
            span,
        },
        domain: None,
        pattern: None,
    };
    assert!(!is_stage1_hoistable(&Expr::SetBuilder(
        dummy(),
        vec![bound.clone()]
    )));
    assert!(!is_stage1_hoistable(&Expr::SetFilter(
        bound.clone(),
        dummy()
    )));
    assert!(!is_stage1_hoistable(&Expr::FuncDef(
        vec![bound.clone()],
        dummy()
    )));
    assert!(!is_stage1_hoistable(&Expr::Choose(bound, dummy())));
    assert!(!is_stage1_hoistable(&Expr::Forall(vec![], dummy())));
    assert!(!is_stage1_hoistable(&Expr::Exists(vec![], dummy())));

    // EXCLUDED: complex evaluation forms with hidden dependencies
    assert!(!is_stage1_hoistable(&Expr::Apply(dummy(), vec![])));
    assert!(!is_stage1_hoistable(&Expr::FuncApply(dummy(), dummy())));
    assert!(!is_stage1_hoistable(&Expr::Prime(dummy())));
    assert!(!is_stage1_hoistable(&Expr::Enabled(dummy())));
    assert!(!is_stage1_hoistable(&Expr::Ident(
        "x".into(),
        NameId::INVALID,
    )));
    assert!(!is_stage1_hoistable(&Expr::Let(vec![], dummy())));
    assert!(!is_stage1_hoistable(&Expr::Lambda(vec![], dummy())));
}

#[test]
fn test_set_construction_binding_forms_are_safe_but_not_cacheable() {
    use tla_core::Span;

    let span = Span {
        file: FileId(0),
        start: 0,
        end: 0,
    };
    let dummy = || {
        Box::new(Spanned {
            node: Expr::Bool(true),
            span,
        })
    };
    let bound = BoundVar {
        name: Spanned {
            node: "x".into(),
            span,
        },
        domain: None,
        pattern: None,
    };

    assert!(is_hoist_safe(&Expr::SetBuilder(
        dummy(),
        vec![bound.clone()]
    )));
    assert!(is_hoist_safe(&Expr::SetFilter(bound.clone(), dummy())));
    assert!(!is_hoist_cacheable(&Expr::SetBuilder(
        dummy(),
        vec![bound.clone()]
    )));
    assert!(!is_hoist_cacheable(&Expr::SetFilter(
        bound.clone(),
        dummy()
    )));

    assert!(!is_hoist_safe(&Expr::FuncDef(vec![bound.clone()], dummy())));
    assert!(!is_hoist_safe(&Expr::Choose(bound.clone(), dummy())));
    assert!(!is_hoist_safe(&Expr::Forall(vec![bound.clone()], dummy())));
    assert!(!is_hoist_safe(&Expr::Exists(vec![bound], dummy())));
}
