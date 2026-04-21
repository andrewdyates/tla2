// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-verification behavior tests for the SMT backend.

use super::context::SmtContext;
use super::incremental::{IncrementalCheckResult, IncrementalSatContext};
use super::model_verify::{
    collect_theory_atoms_into, verify_sat_model, verify_sat_model_conjunction,
    verify_sat_model_conjunction_strict, verify_sat_model_conjunction_strict_with_mod_retry,
    verify_sat_model_strict, verify_sat_model_strict_with_mod_retry,
};
use super::types::{ModelVerifyResult, SmtResult, SmtValue};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use rustc_hash::FxHashMap;
use std::sync::Arc;
use z4_core::term::Symbol;
use z4_core::{Sort, TermStore};

#[test]
fn test_collect_theory_atoms_descends_through_theory_atom_root_6881() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let b_alias = terms.mk_var("b_alias", Sort::Bool);

    let eq_xy = terms.mk_eq(x, y);
    let eq_alias_atom = terms.mk_eq(b_alias, eq_xy);

    let mut collected = rustc_hash::FxHashSet::default();
    collect_theory_atoms_into(&terms, [eq_alias_atom], &mut collected);

    assert!(collected.contains(&eq_alias_atom));
    assert!(
        collected.contains(&eq_xy),
        "nested equality must be collected even when the root itself is a theory atom"
    );
}

#[test]
fn test_collect_theory_atoms_includes_bool_uf_arguments_6881() {
    let mut terms = TermStore::new();
    let b_alias = terms.mk_var("b_alias", Sort::Bool);
    let uf_bool = terms.mk_app(Symbol::named("pred"), vec![b_alias], Sort::Bool);

    let mut collected = rustc_hash::FxHashSet::default();
    collect_theory_atoms_into(&terms, [uf_bool], &mut collected);

    assert!(collected.contains(&uf_bool));
    assert!(
        collected.contains(&b_alias),
        "Bool arguments to reachable UF applications must stay visible for routing parity"
    );
}

#[test]
fn test_verify_sat_model_conjunction_detects_violated_member() {
    let x = ChcVar::new("x", ChcSort::Int);
    let background = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let assumption = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(1));

    assert!(
        !verify_sat_model_conjunction([&background, &assumption], &model),
        "conjunction should fail when any member is definitely false"
    );
}

#[test]
fn test_verify_sat_model_conjunction_fails_on_indeterminate_member() {
    let x = ChcVar::new("x", ChcSort::Int);
    let predicate = ChcExpr::predicate_app("P", PredicateId::new(0), vec![ChcExpr::var(x.clone())]);
    let arithmetic = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));

    assert!(
        !verify_sat_model_conjunction([&predicate, &arithmetic], &model),
        "indeterminate members must not silently pass model verification"
    );
    assert_eq!(
        verify_sat_model_conjunction_strict([&predicate, &arithmetic], &model),
        ModelVerifyResult::Indeterminate,
        "strict conjunction verification must report Indeterminate"
    );
}

#[test]
fn test_verify_sat_model_conjunction_strict_reports_invalid_when_any_member_fails() {
    let x = ChcVar::new("x", ChcSort::Int);
    let predicate = ChcExpr::predicate_app("P", PredicateId::new(0), vec![ChcExpr::var(x.clone())]);
    let violated = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));

    assert_eq!(
        verify_sat_model_conjunction_strict([&predicate, &violated], &model),
        ModelVerifyResult::Invalid,
        "strict conjunction verification must prioritize Invalid over Indeterminate"
    );
}

#[test]
fn test_verify_sat_model_strict_returns_indeterminate_for_predicates() {
    let x = ChcVar::new("x", ChcSort::Int);
    let predicate = ChcExpr::predicate_app("P", PredicateId::new(0), vec![ChcExpr::var(x.clone())]);

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));

    assert_eq!(
        verify_sat_model_strict(&predicate, &model),
        ModelVerifyResult::Indeterminate,
        "predicate expressions should return Indeterminate, not Valid"
    );

    let arithmetic = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));
    assert_eq!(
        verify_sat_model_strict(&arithmetic, &model),
        ModelVerifyResult::Valid,
        "satisfied arithmetic should return Valid"
    );

    let violated = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(0),
    );
    assert_eq!(
        verify_sat_model_strict(&violated, &model),
        ModelVerifyResult::Invalid,
        "violated arithmetic should return Invalid"
    );
}

#[test]
fn test_verify_sat_model_mod_retry_rechecks_eliminated_form() {
    let x = ChcVar::new("x", ChcSort::Int);
    let mod_expr = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(3)),
        ChcExpr::int(0),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(4));

    assert_eq!(
        verify_sat_model_strict(&mod_expr, &model),
        ModelVerifyResult::Invalid,
        "original strict verification should see the violated mod constraint"
    );
    assert!(
        !matches!(
            verify_sat_model_strict_with_mod_retry(&mod_expr, &model),
            ModelVerifyResult::Invalid
        ),
        "mod-aware retry should re-check the eliminated form instead of hard-rejecting"
    );
    assert!(
        !matches!(
            verify_sat_model_conjunction_strict_with_mod_retry([&mod_expr], &model),
            ModelVerifyResult::Invalid
        ),
        "conjunction helper should use the same mod-aware retry policy"
    );
}

#[test]
fn test_verify_sat_model_wrapper_returns_false_on_invalid() {
    let x = ChcVar::new("x", ChcSort::Int);
    let violated = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(3));

    assert!(
        !verify_sat_model(&violated, &model),
        "verify_sat_model must return false when model violates expression"
    );
}

#[test]
fn test_verify_sat_model_wrapper_returns_true_on_valid() {
    let x = ChcVar::new("x", ChcSort::Int);
    let satisfied = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));

    assert!(
        verify_sat_model(&satisfied, &model),
        "verify_sat_model must return true when model satisfies expression"
    );
}

#[test]
fn test_verify_sat_model_wrapper_returns_false_on_indeterminate() {
    let predicate = ChcExpr::predicate_app(
        "P",
        PredicateId::new(0),
        vec![ChcExpr::var(ChcVar::new("x", ChcSort::Int))],
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(1));

    assert!(
        !verify_sat_model(&predicate, &model),
        "verify_sat_model must fail closed on indeterminate expressions"
    );
}

#[test]
fn test_check_sat_accepts_indeterminate_as_sat() {
    // After #4712: Indeterminate model verification is accepted as Sat.
    // Indeterminate means evaluation is incomplete (uninterpreted predicates),
    // not that the model is wrong.
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let predicate = ChcExpr::predicate_app("P", PredicateId::new(0), vec![ChcExpr::var(x)]);

    assert!(
        matches!(ctx.check_sat(&predicate), SmtResult::Sat(_)),
        "indeterminate model verification must return Sat (not Unknown) per #4712"
    );
}

#[test]
fn test_assumption_mode_accepts_indeterminate_as_sat() {
    // After #4712: Indeterminate model verification is accepted as Sat.
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let background = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    let assumptions = vec![ChcExpr::predicate_app(
        "P",
        PredicateId::new(0),
        vec![ChcExpr::var(x)],
    )];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "indeterminate assumption-model verification must return Sat per #4712"
    );
}

#[test]
fn test_incremental_mode_accepts_indeterminate_as_sat() {
    // After #4712: Indeterminate model verification is accepted as Sat.
    let mut smt = SmtContext::new();
    let mut inc = IncrementalSatContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let background = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let assumption = ChcExpr::predicate_app("P", PredicateId::new(0), vec![ChcExpr::var(x)]);

    inc.assert_background(&background, &mut smt);
    inc.finalize_background(&smt);
    inc.push();
    let result = inc.check_sat_incremental(std::slice::from_ref(&assumption), &mut smt, None);
    inc.pop();

    assert!(
        matches!(result, IncrementalCheckResult::Sat(_)),
        "indeterminate incremental-model verification must return Sat per #4712"
    );
}

#[test]
fn test_assumption_mode_mod_div_by_zero_remains_sat() {
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let background = vec![ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5))];
    let assumptions = vec![
        ChcExpr::eq(
            ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::int(5),
        ),
        ChcExpr::eq(
            ChcExpr::Op(
                ChcOp::Div,
                vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(0))],
            ),
            ChcExpr::int(0),
        ),
    ];

    let result = ctx.check_sat_with_assumption_conjuncts(&background, &assumptions);
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "assumption SAT path should honor SMT-LIB total semantics for mod/div by zero, got {result:?}"
    );
}

#[test]
fn test_incremental_mode_mod_div_by_zero_remains_sat() {
    let mut smt = SmtContext::new();
    let mut inc = IncrementalSatContext::new();
    let x = ChcVar::new("x", ChcSort::Int);

    let background = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    let assumptions = vec![
        ChcExpr::eq(
            ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::int(5),
        ),
        ChcExpr::eq(
            ChcExpr::Op(
                ChcOp::Div,
                vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(0))],
            ),
            ChcExpr::int(0),
        ),
    ];

    inc.assert_background(&background, &mut smt);
    inc.finalize_background(&smt);
    inc.push();
    let result = inc.check_sat_incremental(&assumptions, &mut smt, None);
    inc.pop();

    assert!(
        matches!(result, IncrementalCheckResult::Sat(_)),
        "incremental SAT path should honor SMT-LIB total semantics for mod/div by zero, got {result:?}"
    );
}

#[test]
fn test_verify_sat_model_conjunction_strict_all_valid() {
    let x = ChcVar::new("x", ChcSort::Int);
    let ge_zero = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let le_ten = ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));

    assert_eq!(
        verify_sat_model_conjunction_strict([&ge_zero, &le_ten], &model),
        ModelVerifyResult::Valid,
        "conjunction of all-satisfied expressions must return Valid"
    );
}

#[test]
fn test_verify_sat_model_conjunction_strict_empty_is_valid() {
    let model = FxHashMap::default();
    let empty: Vec<&ChcExpr> = vec![];
    assert_eq!(
        verify_sat_model_conjunction_strict(empty, &model),
        ModelVerifyResult::Valid,
        "empty conjunction must return Valid (vacuous truth)"
    );
}

#[test]
fn test_verify_sat_model_strict_accepts_array_overwrite_model_1753() {
    let lhs = ChcVar::new(
        "lhs",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let rhs = ChcVar::new(
        "rhs",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let expr = ChcExpr::eq(ChcExpr::var(lhs.clone()), ChcExpr::var(rhs.clone()));

    let mut model = FxHashMap::default();
    model.insert(
        lhs.name,
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![
                (SmtValue::Int(1), SmtValue::Int(10)),
                (SmtValue::Int(1), SmtValue::Int(20)),
            ],
        },
    );
    model.insert(
        rhs.name,
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(1), SmtValue::Int(20))],
        },
    );

    assert_eq!(
        verify_sat_model_strict(&expr, &model),
        ModelVerifyResult::Valid
    );
}
