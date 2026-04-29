// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{detect_actions, CoverageStats, DetectedAction, DetectedActionId};
use tla_core::ast::{BoundVar, Expr, OperatorDef};
use tla_core::name_intern::NameId;
use tla_core::{FileId, Span, Spanned};

fn sp(expr: Expr) -> Spanned<Expr> {
    Spanned::new(expr, Span::dummy())
}

fn detected(name: &str, span: Span) -> DetectedAction {
    DetectedAction {
        id: DetectedActionId::new(span),
        name: name.to_string(),
        expr: Spanned::new(Expr::Ident(name.to_string(), NameId::INVALID), span),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_detected_action_id_display_is_span_backed() {
    let id = DetectedActionId::new(Span::new(FileId(7), 100, 200));
    assert_eq!(id.to_string(), "7:100-200");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_coverage_stats_dead_actions() {
    let mut stats = CoverageStats::new();
    let action1 = detected("Action1", Span::new(FileId(0), 1, 2));
    let action2 = detected("Action2", Span::new(FileId(0), 3, 4));
    let action3 = detected("Action3", Span::new(FileId(0), 5, 6));

    stats.register_action(&action1);
    stats.register_action(&action2);
    stats.register_action(&action3);

    // Action1 and Action3 fire, Action2 is dead
    stats.record_action(action1.id, 5);
    stats.record_action(action3.id, 2);

    let dead = stats.dead_actions();
    assert_eq!(dead, vec!["Action2"]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_coverage_stats_format() {
    let mut stats = CoverageStats::new();
    let send = detected("Send", Span::new(FileId(0), 10, 14));
    let recv = detected("Receive", Span::new(FileId(0), 20, 27));
    stats.total_states = 100;
    stats.total_transitions = 500;
    stats.register_action(&send);
    stats.register_action(&recv);
    stats.record_action(send.id, 300);
    stats.record_action(recv.id, 200);

    let report = stats.format_report();
    assert!(report.contains("100 distinct states"));
    assert!(report.contains("500 transitions"));
    assert!(report.contains("Send"));
    assert!(report.contains("Receive"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_coverage_with_dead_action() {
    let mut stats = CoverageStats::new();
    let active = detected("Active", Span::new(FileId(0), 1, 7));
    let never_used = detected("NeverUsed", Span::new(FileId(0), 8, 17));
    stats.register_action(&active);
    stats.register_action(&never_used);
    stats.record_action(active.id, 10);

    let report = stats.format_report();
    assert!(report.contains("[DEAD]"));
    assert!(report.contains("NeverUsed"));
    assert!(report.contains("WARNING"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_coverage_keeps_duplicate_names_separate_by_id() {
    let mut stats = CoverageStats::new();
    let first = detected("Foo", Span::new(FileId(0), 10, 13));
    let second = detected("Foo", Span::new(FileId(0), 30, 33));

    stats.register_action(&first);
    stats.register_action(&second);
    stats.record_action(first.id, 2);
    stats.record_action(second.id, 5);

    assert_eq!(stats.actions.len(), 2);
    assert_eq!(stats.action_order, vec![first.id, second.id]);
    assert_eq!(
        stats
            .actions
            .get(&first.id)
            .expect("first action should be tracked")
            .transitions,
        2
    );
    assert_eq!(
        stats
            .actions
            .get(&second.id)
            .expect("second action should be tracked")
            .transitions,
        5
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_detect_actions_preserves_exists_context() {
    let bounds = vec![BoundVar {
        name: Spanned::new("p".to_string(), Span::dummy()),
        domain: Some(Box::new(sp(Expr::Ident("S".to_string(), NameId::INVALID)))),
        pattern: None,
    }];

    let a = Spanned::new(
        Expr::Apply(
            Box::new(sp(Expr::Ident("A".to_string(), NameId::INVALID))),
            vec![sp(Expr::Ident("p".to_string(), NameId::INVALID))],
        ),
        Span::new(FileId(0), 10, 14),
    );
    let b = Spanned::new(
        Expr::Apply(
            Box::new(sp(Expr::Ident("B".to_string(), NameId::INVALID))),
            vec![sp(Expr::Ident("p".to_string(), NameId::INVALID))],
        ),
        Span::new(FileId(0), 20, 24),
    );

    let next_body = sp(Expr::Exists(
        bounds.clone(),
        Box::new(sp(Expr::Or(Box::new(a.clone()), Box::new(b.clone())))),
    ));

    let next_def = OperatorDef {
        name: Spanned::new("Next".to_string(), Span::dummy()),
        params: Vec::new(),
        body: next_body,
        local: false,
        contains_prime: true,
        guards_depend_on_prime: true,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };

    let actions = detect_actions(&next_def);
    assert_eq!(actions.len(), 2);
    assert_eq!(actions[0].name, "A");
    assert_eq!(actions[1].name, "B");

    for act in &actions {
        assert_eq!(act.id.span, act.expr.span);
        match &act.expr.node {
            Expr::Exists(ex_bounds, body) => {
                assert_eq!(ex_bounds.len(), 1);
                assert_eq!(ex_bounds[0].name.node, "p");
                match &body.node {
                    Expr::Apply(_, _) => {}
                    other => panic!("expected Apply body, got {other:?}"),
                }
            }
            other => panic!("expected Exists wrapper, got {other:?}"),
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_detect_actions_if_branches_get_guarded() {
    let cond = Spanned::new(
        Expr::Ident("c".to_string(), NameId::INVALID),
        Span::new(FileId(0), 1, 2),
    );
    let then_branch = Spanned::new(
        Expr::Ident("A".to_string(), NameId::INVALID),
        Span::new(FileId(0), 10, 11),
    );
    let else_branch = Spanned::new(
        Expr::Ident("B".to_string(), NameId::INVALID),
        Span::new(FileId(0), 20, 21),
    );
    let next_body = sp(Expr::If(
        Box::new(cond.clone()),
        Box::new(then_branch),
        Box::new(else_branch),
    ));

    let next_def = OperatorDef {
        name: Spanned::new("Next".to_string(), Span::dummy()),
        params: Vec::new(),
        body: next_body,
        local: false,
        contains_prime: true,
        guards_depend_on_prime: true,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };

    let actions = detect_actions(&next_def);
    assert_eq!(actions.len(), 2);
    assert_eq!(actions[0].name, "A");
    assert_eq!(actions[1].name, "B");
    assert_eq!(actions[0].id.span, actions[0].expr.span);
    assert_eq!(actions[1].id.span, actions[1].expr.span);

    match &actions[0].expr.node {
        Expr::And(g, a) => {
            assert!(matches!(&g.node, Expr::Ident(name, _) if name == "c"));
            assert!(matches!(&a.node, Expr::Ident(name, _) if name == "A"));
        }
        other => panic!("expected And guard for THEN, got {other:?}"),
    }

    match &actions[1].expr.node {
        Expr::And(g, b) => match &g.node {
            Expr::Not(inner) => {
                assert!(matches!(&inner.node, Expr::Ident(name, _) if name == "c"));
                assert!(matches!(&b.node, Expr::Ident(name, _) if name == "B"));
            }
            other => panic!("expected Not(c) guard for ELSE, got {other:?}"),
        },
        other => panic!("expected And guard for ELSE, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_detect_actions_duplicate_names_get_distinct_ids() {
    let left = Spanned::new(
        Expr::Ident("Foo".to_string(), NameId::INVALID),
        Span::new(FileId(0), 5, 8),
    );
    let right = Spanned::new(
        Expr::Ident("Foo".to_string(), NameId::INVALID),
        Span::new(FileId(0), 15, 18),
    );
    let next_def = OperatorDef {
        name: Spanned::new("Next".to_string(), Span::dummy()),
        params: Vec::new(),
        body: sp(Expr::Or(Box::new(left), Box::new(right))),
        local: false,
        contains_prime: true,
        guards_depend_on_prime: true,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };

    let actions = detect_actions(&next_def);
    assert_eq!(actions.len(), 2);
    assert_eq!(actions[0].name, "Foo");
    assert_eq!(actions[1].name, "Foo");
    assert_ne!(actions[0].id, actions[1].id);
}
