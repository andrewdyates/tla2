// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use tla_check::{
    detect_actions, resolve_param_binders_for_rewrite, ActionLabelParamBindErrorKind, EvalCtx,
};
use tla_core::ast::Unit;
use tla_core::{lower, parse_to_syntax_tree, FileId};

fn detected_action_from_next(src: &str, action_name: &str) -> tla_check::DetectedAction {
    let tree = parse_to_syntax_tree(src);
    let lowered = lower(FileId(0), &tree);
    assert!(
        lowered.errors.is_empty(),
        "test module must lower successfully, got errors: {:?}",
        lowered.errors
    );
    let module = lowered.module.expect("module must lower successfully");

    // `detect_actions` runs on a Next operator def.
    let next_def = module.units.iter().find_map(|u| match &u.node {
        Unit::Operator(def) if def.name.node == "Next" => Some(def.clone()),
        _ => None,
    });
    let next_def = next_def.expect("test module must define Next");

    // Ensure the module loads (mirrors real pipeline expectations).
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let actions = detect_actions(&next_def);
    actions
        .into_iter()
        .find(|a| a.name == action_name)
        .unwrap_or_else(|| panic!("expected detected action {action_name:?}"))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn rewrite_param_binding_succeeds_via_callsite_arg_when_formal_name_differs() {
    let src = r#"---- MODULE MySpec ----
S == {1, 2}
Approve(req) == TRUE
Next == \E reqId \in S : Approve(reqId)
===="#;

    let action = detected_action_from_next(src, "Approve");
    let params = vec!["req".to_string()];

    let resolved = resolve_param_binders_for_rewrite("L", "Approve", &action, &params)
        .expect("expected callsite arg binding to resolve req -> reqId");
    assert_eq!(resolved.len(), 1);
    assert_eq!(resolved[0].name, "reqId");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn rewrite_param_binding_error_ambiguous_binder() {
    let src = r#"---- MODULE MySpec ----
S == {1, 2}
Approve(p) == TRUE
Next == \E p \in S : \E p \in S : Approve(p)
===="#;

    let action = detected_action_from_next(src, "Approve");
    let params = vec!["p".to_string()];

    let err = resolve_param_binders_for_rewrite("L", "Approve", &action, &params).unwrap_err();
    match &err.kind {
        ActionLabelParamBindErrorKind::AmbiguousBinder { param, matches } => {
            assert_eq!(param, "p");
            assert_eq!(matches.len(), 2);
            assert!(matches.iter().all(|m| m.name == "p"));
        }
        other => panic!("expected AmbiguousBinder, got: {other:?}"),
    }

    let rendered = err.to_string();
    assert!(rendered.contains("action label L"), "got: {rendered}");
    assert!(rendered.contains("operator Approve"), "got: {rendered}");
    assert!(
        rendered.contains("multiple outer `\\E` binders"),
        "got: {rendered}"
    );
    assert!(
        rendered.contains("matching binders at spans"),
        "got: {rendered}"
    );
    assert!(
        rendered.contains(&action.id.to_string()),
        "rendered error should include stable action id: {rendered}"
    );
    assert_eq!(err.label, "L");
    assert_eq!(err.operator_raw, "Approve");
    assert_eq!(err.action_name, "Approve");
    assert_eq!(err.action_id, action.id);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn rewrite_param_binding_succeeds_under_let_wrapper() {
    let src = r#"---- MODULE MySpec ----
S == {1, 2}
Approve(reqId) == TRUE
Next == LET X == 1 IN \E reqId \in S : Approve(reqId)
===="#;

    let action = detected_action_from_next(src, "Approve");
    let params = vec!["reqId".to_string()];

    let resolved = resolve_param_binders_for_rewrite("L", "Approve", &action, &params)
        .expect("expected reqId binder to resolve under LET wrapper");
    assert_eq!(resolved.len(), 1);
    assert_eq!(resolved[0].name, "reqId");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn rewrite_param_binding_succeeds_for_tuple_pattern_binder() {
    let src = r#"---- MODULE MySpec ----
S == {<<1, 2>>}
Approve(x) == TRUE
Next == \E <<x, y>> \in S : Approve(x)
===="#;

    let action = detected_action_from_next(src, "Approve");
    let params = vec!["x".to_string()];

    let resolved = resolve_param_binders_for_rewrite("L", "Approve", &action, &params)
        .expect("expected tuple pattern binder to provide x");
    assert_eq!(resolved.len(), 1);
    assert_eq!(resolved[0].name, "x");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn rewrite_param_binding_succeeds_for_tuple_pattern_binder_multiple_params() {
    let src = r#"---- MODULE MySpec ----
S == {<<1, 2>>}
Approve(x, y) == TRUE
Next == \E <<x, y>> \in S : Approve(x, y)
===="#;

    let action = detected_action_from_next(src, "Approve");
    let params = vec!["x".to_string(), "y".to_string()];

    let resolved = resolve_param_binders_for_rewrite("L", "Approve", &action, &params)
        .expect("expected tuple pattern binder to provide x and y");
    assert_eq!(resolved.len(), 2);
    assert_eq!(resolved[0].name, "x");
    assert_eq!(resolved[1].name, "y");

    // Ensure we don't report the synthetic binder name `<<x, y>>` as an available binder site.
    let all_binders = tla_check::outer_exists_binder_sites(&action.expr);
    assert!(
        all_binders.iter().any(|b| b.name == "x") && all_binders.iter().any(|b| b.name == "y"),
        "expected tuple pattern binder sites for x and y, got: {all_binders:?}"
    );
    assert!(
        !all_binders.iter().any(|b| b.name.starts_with("<<")),
        "expected tuple pattern synthetic binder names to be excluded, got: {all_binders:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn rewrite_param_binding_preserves_param_key_order() {
    let src = r#"---- MODULE MySpec ----
S == {<<1, 2>>}
Approve(x, y) == TRUE
Next == \E <<x, y>> \in S : Approve(x, y)
===="#;

    let action = detected_action_from_next(src, "Approve");
    let params = vec!["y".to_string(), "x".to_string()];

    let resolved = resolve_param_binders_for_rewrite("L", "Approve", &action, &params)
        .expect("expected tuple pattern binder to resolve in param key order");
    assert_eq!(resolved.len(), 2);
    assert_eq!(resolved[0].name, "y");
    assert_eq!(resolved[1].name, "x");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn rewrite_param_binding_succeeds_for_tuple_pattern_binder_under_let_wrapper() {
    let src = r#"---- MODULE MySpec ----
S == {<<1, 2>>}
Approve(x, y) == TRUE
Next == LET X == 1 IN \E <<x, y>> \in S : Approve(x, y)
===="#;

    let action = detected_action_from_next(src, "Approve");
    let params = vec!["x".to_string(), "y".to_string()];

    let resolved = resolve_param_binders_for_rewrite("L", "Approve", &action, &params)
        .expect("expected tuple pattern binder to resolve under LET wrapper");
    assert_eq!(resolved.len(), 2);
    assert_eq!(resolved[0].name, "x");
    assert_eq!(resolved[1].name, "y");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn rewrite_param_binding_error_ambiguous_binder_tuple_pattern_shadowing() {
    let src = r#"---- MODULE MySpec ----
S == {<<1, 2>>}
T == {<<3, 4>>}
Approve(x) == TRUE
Next == \E <<x, y>> \in S : \E <<x, z>> \in T : Approve(x)
===="#;

    let action = detected_action_from_next(src, "Approve");
    let params = vec!["x".to_string()];

    let err = resolve_param_binders_for_rewrite("L", "Approve", &action, &params).unwrap_err();
    match &err.kind {
        ActionLabelParamBindErrorKind::AmbiguousBinder { param, matches } => {
            assert_eq!(param, "x");
            assert_eq!(matches.len(), 2);
            assert!(matches.iter().all(|m| m.name == "x"));
            assert_ne!(
                matches[0].span, matches[1].span,
                "expected distinct binder spans, got: {matches:?}"
            );
            for m in matches {
                assert_eq!(
                    m.span.file, err.action_span.file,
                    "expected binder span file to match action span file; binder={:?}, action_span={:?}",
                    m.span, err.action_span
                );
                assert!(
                    m.span.start < m.span.end,
                    "expected non-empty binder span, got: {:?}",
                    m.span
                );
            }
        }
        other => panic!("expected AmbiguousBinder, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn rewrite_param_binding_only_considers_outer_wrapper_spine() {
    let src = r#"---- MODULE MySpec ----
S == {1, 2}
Approve(x) == TRUE
Next == \E w \in S : (Approve(w) /\ \E x \in S : Approve(x))
===="#;

    // `detect_actions` names this action based on the left side (`Approve(x)`).
    let action = detected_action_from_next(src, "Approve");
    let params = vec!["x".to_string()];

    let resolved = resolve_param_binders_for_rewrite("L", "Approve", &action, &params)
        .expect("expected callsite arg binding to select the outer callsite");
    assert_eq!(resolved.len(), 1);
    assert_eq!(resolved[0].name, "w");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn rewrite_param_binding_error_missing_callsite() {
    let src = r#"---- MODULE MySpec ----
S == {1, 2}
Approve(req) == TRUE
Next == \E reqId \in S : TRUE
===="#;

    let action = detected_action_from_next(src, "Action_1");
    let params = vec!["req".to_string()];

    let err = resolve_param_binders_for_rewrite("L", "Approve", &action, &params).unwrap_err();
    match &err.kind {
        ActionLabelParamBindErrorKind::MissingCallsite { param } => assert_eq!(param, "req"),
        other => panic!("expected MissingCallsite, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn rewrite_param_binding_error_unsupported_callsite_arg() {
    let src = r#"---- MODULE MySpec ----
S == {1, 2}
Approve(req) == TRUE
Next == \E reqId \in S : Approve(reqId + 1)
===="#;

    let action = detected_action_from_next(src, "Approve");
    let params = vec!["req".to_string()];

    let err = resolve_param_binders_for_rewrite("L", "Approve", &action, &params).unwrap_err();
    match &err.kind {
        ActionLabelParamBindErrorKind::UnsupportedCallsiteArg {
            param, position, ..
        } => {
            assert_eq!(param, "req");
            assert_eq!(*position, 0);
        }
        other => panic!("expected UnsupportedCallsiteArg, got: {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn rewrite_param_binding_error_ambiguous_callsite() {
    let src = r#"---- MODULE MySpec ----
S == {1, 2}
Approve(req) == TRUE
Next == \E a \in S : \E b \in S : (Approve(a) /\ Approve(b))
===="#;

    let action = detected_action_from_next(src, "Approve");
    let params = vec!["req".to_string()];

    let err = resolve_param_binders_for_rewrite("L", "Approve", &action, &params).unwrap_err();
    match &err.kind {
        ActionLabelParamBindErrorKind::AmbiguousCallsite { param, callsites } => {
            assert_eq!(param, "req");
            assert_eq!(callsites.len(), 2);
            assert!(callsites.iter().all(|s| s.file == err.action_span.file));
        }
        other => panic!("expected AmbiguousCallsite, got: {other:?}"),
    }
}
