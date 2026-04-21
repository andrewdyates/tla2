// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Known gap and parity tests for temporal analysis: `is_liveness_conjunct`,
//! `contains_temporal_standalone`, ModuleRef resolution, and INSTANCE
//! property classification.

use super::*;

// ===========================================================================
// is_liveness_conjunct known limitation tests
// ===========================================================================

/// Part of #2740: `is_liveness_conjunct` does NOT resolve operator references.
///
/// If a property is `Prop == SafePart /\ LivePart` where SafePart and LivePart
/// are operator names, `is_liveness_conjunct` only sees `Ident("SafePart")` and
/// `Ident("LivePart")` — it doesn't look up their definitions to determine
/// whether they're temporal. Both are classified as non-liveness (init predicates).
///
/// This is a known gap vs the sequential checker's `classify_term` in
/// `safety_split.rs` which DOES resolve operator definitions. The gap only
/// affects tautology detection for properties written as conjunctions of
/// operator references (uncommon pattern). The classify_property_safety_parts
/// function is not affected (it correctly handles the else branch for
/// non-Always terms).
///
/// This test documents the gap rather than asserting "correct" behavior,
/// so it can serve as a regression test when the gap is fixed.
#[test]
fn tautology_via_operator_ref_known_gap() {
    let src = r#"
---- MODULE TautOpRef ----
EXTENDS Integers
VARIABLE x
SafePart == [](x >= 0)
LivePart == <>TRUE
Prop == SafePart /\ LivePart
===="#;
    let (op_defs, ctx, _root) = setup_for_classification(src);
    let properties = vec!["Prop".to_string()];
    let result = check_property_tautologies(&ctx, &properties, &op_defs, "TautOpRef");

    // Known gap: `is_liveness_conjunct` doesn't resolve Ident("LivePart") to
    // `<>TRUE`, so it classifies both conjuncts as non-liveness and skips
    // tautology analysis. The sequential checker's `separate_safety_liveness_parts`
    // would catch this because it resolves operator definitions.
    //
    // When this gap is fixed, change this assertion to:
    //   assert!(result.is_some(), "Should detect tautological liveness via operator ref");
    assert!(
        result.is_none(),
        "Known gap: tautology not detected when liveness is behind operator ref"
    );
}

// ===========================================================================
// contains_temporal_standalone parity gap tests
// ===========================================================================

/// Part of #2740: `contains_temporal_standalone` does NOT detect `Apply(WF_/SF_)` form.
///
/// The sequential checker's `contains_temporal_helper` (via `contains_temporal_with_mode`
/// in `SafetySplit` mode at `temporal_scan.rs:241-249`) recognizes
/// `Apply(Ident("WF_xxx"), _)` and `Apply(Ident("SF_xxx"), _)` as temporal.
/// The parallel checker's `contains_temporal_standalone` does not — its predicate
/// only matches native AST nodes (WeakFair, StrongFair, etc.).
///
/// In practice, the lowerer's `make_apply_expr` converts `WF_xxx(Action)` to
/// `Expr::WeakFair(vars, action)` at parse time, so the `Apply` form is rare.
/// However, it can arise from instance expansion or substitution, and the
/// sequential checker handles it defensively.
///
/// This test constructs the `Apply(WF_/SF_)` form directly to document the gap.
/// When fixed, change assertions to expect liveness classification.
#[test]
fn contains_temporal_standalone_misses_apply_wf_sf_known_gap() {
    use tla_core::span::{Span, Spanned};

    let dummy_span = Span::dummy();

    // Construct Apply(Ident("WF_vars"), [TRUE]) — the form that bypasses
    // the lowerer's WF_->WeakFair conversion.
    let wf_op = Box::new(Spanned::new(
        Expr::Ident("WF_vars".into(), tla_core::name_intern::NameId::INVALID),
        dummy_span,
    ));
    let wf_apply = Expr::Apply(wf_op, vec![Spanned::new(Expr::Bool(true), dummy_span)]);

    // Known gap: contains_temporal_standalone does NOT detect this as temporal.
    // The sequential contains_temporal_helper DOES detect it.
    //
    // When this gap is fixed, change to:
    //   assert!(contains_temporal_standalone(&wf_apply), "Should detect Apply(WF_) as temporal");
    assert!(
        !contains_temporal_standalone(&wf_apply),
        "Known gap: Apply(WF_) not detected by contains_temporal_standalone"
    );

    // Same for SF_ prefix
    let sf_op = Box::new(Spanned::new(
        Expr::Ident("SF_vars".into(), tla_core::name_intern::NameId::INVALID),
        dummy_span,
    ));
    let sf_apply = Expr::Apply(sf_op, vec![Spanned::new(Expr::Bool(true), dummy_span)]);

    assert!(
        !contains_temporal_standalone(&sf_apply),
        "Known gap: Apply(SF_) not detected by contains_temporal_standalone"
    );

    // Verify that `is_liveness_conjunct` inherits this gap: Apply(WF_) form
    // falls through to the catch-all, which calls contains_temporal_standalone,
    // which misses it, so it's classified as non-liveness.
    assert!(
        !is_liveness_conjunct(&wf_apply),
        "Known gap: Apply(WF_) misclassified as non-liveness by is_liveness_conjunct"
    );
}

/// Verify that the native WeakFair/StrongFair AST nodes ARE correctly detected
/// by both `contains_temporal_standalone` and `is_liveness_conjunct`.
/// This confirms the gap is specific to the Apply(WF_/SF_) form.
#[test]
fn contains_temporal_standalone_detects_native_weakfair_strongfair() {
    use tla_core::span::{Span, Spanned};

    let dummy_span = Span::dummy();

    let wf_expr = Expr::WeakFair(
        Box::new(Spanned::new(
            Expr::Ident("vars".into(), tla_core::name_intern::NameId::INVALID),
            dummy_span,
        )),
        Box::new(Spanned::new(Expr::Bool(true), dummy_span)),
    );
    assert!(contains_temporal_standalone(&wf_expr));
    assert!(is_liveness_conjunct(&wf_expr));

    let sf_expr = Expr::StrongFair(
        Box::new(Spanned::new(
            Expr::Ident("vars".into(), tla_core::name_intern::NameId::INVALID),
            dummy_span,
        )),
        Box::new(Spanned::new(Expr::Bool(true), dummy_span)),
    );
    assert!(contains_temporal_standalone(&sf_expr));
    assert!(is_liveness_conjunct(&sf_expr));
}

/// Verify `is_liveness_conjunct` correctly classifies `Always(Apply(WF_/SF_))`.
///
/// When the Apply(WF_/SF_) form appears inside an Always body, the sequential
/// checker's `classify_term` detects the nested temporal via `has_nested_temporal_for_safety_split`
/// (which delegates to `contains_temporal_helper` on the inner expression).
/// The parallel checker's `is_liveness_conjunct` calls `contains_temporal_standalone`
/// on the inner, which misses the Apply(WF_/SF_) form.
#[test]
fn is_liveness_conjunct_always_containing_apply_wf_known_gap() {
    use tla_core::span::{Span, Spanned};

    let dummy_span = Span::dummy();

    // Construct Always(Apply(Ident("WF_vars"), [TRUE]))
    let wf_op = Box::new(Spanned::new(
        Expr::Ident("WF_vars".into(), tla_core::name_intern::NameId::INVALID),
        dummy_span,
    ));
    let wf_apply = Expr::Apply(wf_op, vec![Spanned::new(Expr::Bool(true), dummy_span)]);
    let always_wf = Expr::Always(Box::new(Spanned::new(wf_apply, dummy_span)));

    // Known gap: is_liveness_conjunct checks contains_temporal_standalone on inner,
    // which misses Apply(WF_), so this is misclassified as safety.
    //
    // When fixed, change to:
    //   assert!(is_liveness_conjunct(&always_wf), "Should classify []WF_() as liveness");
    assert!(
        !is_liveness_conjunct(&always_wf),
        "Known gap: Always(Apply(WF_)) misclassified as safety"
    );
}

// ===========================================================================
// is_liveness_conjunct ModuleRef gap test
// ===========================================================================

/// Part of #2740: `is_liveness_conjunct` does NOT handle `ModuleRef`.
///
/// Similar to the `Ident` gap tested in `tautology_via_operator_ref_known_gap`,
/// `ModuleRef` nodes fall through to the catch-all in `is_liveness_conjunct`.
/// A `ModuleRef` node like `Instance!Spec` contains no temporal operators at
/// the syntactic level (the module target is just a name), so it would be
/// classified as non-liveness by the catch-all branch.
///
/// The sequential checker handles `ModuleRef` explicitly at `safety_split.rs:221-223`
/// via `classify_module_ref_term` which resolves instance operator definitions,
/// applies substitutions, and classifies each conjunct.
///
/// Unlike the `Ident` gap, this gap is NOT yet documented in the function's doc comment.
#[test]
fn is_liveness_conjunct_module_ref_known_gap() {
    // Construct ModuleRef(Named("Instance"), "Spec", []) — a zero-arg instance
    // operator reference. In practice this might resolve to a liveness property,
    // but is_liveness_conjunct only sees the syntactic shell.
    let module_ref = Expr::ModuleRef(
        tla_core::ast::ModuleTarget::Named("Instance".into()),
        "Spec".into(),
        vec![],
    );

    // Known gap: ModuleRef has no temporal operators syntactically, so
    // contains_temporal_standalone returns false. is_liveness_conjunct
    // classifies it as non-liveness.
    //
    // When fixed, this should resolve the ModuleRef body and classify accordingly.
    assert!(
        !is_liveness_conjunct(&module_ref),
        "Known gap: ModuleRef not resolved by is_liveness_conjunct"
    );

    // Verify that classify_property_safety_parts also skips ModuleRef
    // (it explicitly `continue`s at checker_ops.rs:602).
    let src = r#"
---- MODULE ModRefGap ----
VARIABLE x
===="#;
    let (op_defs, ctx, _root) = setup_for_classification(src);
    // We can't easily test with a real ModuleRef in the property body via
    // the TLA+ parser here (it requires an INSTANCE declaration). The gap
    // is confirmed by code inspection: checker_ops.rs:602 has
    // `Expr::ModuleRef(_, _, _) => continue,`
    let _ = (&op_defs, &ctx);
}

// ===========================================================================
// INSTANCE property classification regression test (Part of #2835)
// ===========================================================================

/// Regression test for W1 8b6033a: `classify_property_safety_parts` must resolve
/// ModuleRef bodies from named instances. Without resolution, properties like
/// `Safety == I!Inv` are skipped (treated as opaque ModuleRef), falling through
/// to the slow post-BFS liveness checker even when they are pure safety.
///
/// Setup: Load an inner module "Inner" with `Inv == x >= 0`, register a named
/// instance "I" pointing to "Inner", then create a property `Safety` with body
/// `ModuleRef(Named("I"), "Inv", [])`. After classification, `Safety` should be
/// recognized as a promoted safety invariant, not skipped.
#[test]
fn classify_instance_module_ref_resolved_as_safety() {
    use std::sync::Arc;
    use tla_core::ast::{Expr, ModuleTarget, OperatorDef};
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Step 1: Parse and load the inner module.
    let inner_src = r#"
---- MODULE Inner ----
EXTENDS Integers
VARIABLE x
Inv == x >= 0
===="#;
    let inner_tree = parse_to_syntax_tree(inner_src);
    let inner_lowered = lower(FileId(0), &inner_tree);
    let inner_module = inner_lowered.module.unwrap();

    // Step 2: Parse the outer module with a named instance declaration.
    // The parser produces an InstanceExpr for `I == INSTANCE Inner`.
    let outer_src = r#"
---- MODULE Outer ----
EXTENDS Integers
VARIABLE x
I == INSTANCE Inner
Safety == I!Inv
===="#;
    let outer_tree = parse_to_syntax_tree(outer_src);
    let outer_lowered = lower(FileId(0), &outer_tree);
    let outer_module = outer_lowered.module.unwrap();

    // Step 3: Build EvalCtx: load outer module (registers instance "I")
    // and load inner module as instance ops.
    let mut ctx = EvalCtx::new();
    ctx.register_var(Arc::from("x"));
    ctx.load_module(&outer_module);
    ctx.load_instance_module("Inner".to_string(), &inner_module);

    // Step 4: Collect op_defs from the outer module.
    let mut op_defs: FxHashMap<String, OperatorDef> = FxHashMap::default();
    for unit in &outer_module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            op_defs.insert(def.name.node.clone(), def.clone());
        }
    }

    // Verify the Safety operator has a ModuleRef body.
    let safety_def = op_defs.get("Safety").expect("Safety op should exist");
    assert!(
        matches!(
            &safety_def.body.node,
            Expr::ModuleRef(ModuleTarget::Named(_), _, _)
        ),
        "Safety body should be ModuleRef, got {:?}",
        safety_def.body.node
    );

    // Step 5: Classify — Safety should be resolved and promoted.
    let properties = vec!["Safety".to_string()];
    let result = classify_property_safety_parts(&ctx, &properties, &op_defs);

    // The resolved body is `x >= 0` (wrapped in []), which is a pure state
    // predicate. It should be extracted as a state_invariant or promoted.
    // At minimum, it must NOT be skipped (the pre-fix behavior was to `continue`
    // past ModuleRef, leaving it in the residual liveness set).
    assert!(
        !result.eval_state_invariants.is_empty()
            || !result.promoted_invariant_properties.is_empty(),
        "classify_property_safety_parts should resolve ModuleRef and promote Safety \
         as an eval-state invariant or promoted invariant, but got: \
         eval_state_invariants={:?}, promoted={:?}, eval_implied_actions={:?}",
        result.eval_state_invariants,
        result.promoted_invariant_properties,
        result.eval_implied_actions,
    );
}
