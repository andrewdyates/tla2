// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::hlpnml::{
    ColorConstant, ColorExpr, ColorSort, ColorTerm, ColoredArc, ColoredNet, ColoredPlace,
    ColoredTransition,
};

/// Helper: build a CyclicEnum sort with N constants.
fn cyclic_sort(id: &str, n: usize) -> ColorSort {
    ColorSort::CyclicEnum {
        id: id.to_string(),
        name: id.to_string(),
        constants: (0..n)
            .map(|i| ColorConstant {
                id: format!("{id}_c{i}"),
                name: format!("c{i}"),
            })
            .collect(),
    }
}

/// Helper: build a Dot sort.
fn dot_sort(id: &str) -> ColorSort {
    ColorSort::Dot {
        id: id.to_string(),
        name: "dot".to_string(),
    }
}

/// Helper: build a place.
fn place(id: &str, sort_id: &str, marking: Option<ColorExpr>) -> ColoredPlace {
    ColoredPlace {
        id: id.to_string(),
        name: Some(id.to_string()),
        sort_id: sort_id.to_string(),
        initial_marking: marking,
    }
}

/// Helper: build an arc with the given inscription.
fn arc(source: &str, target: &str, inscription: ColorExpr) -> ColoredArc {
    ColoredArc {
        id: format!("{source}_to_{target}"),
        source: source.to_string(),
        target: target.to_string(),
        inscription,
    }
}

fn all(sort_id: &str) -> ColorExpr {
    ColorExpr::All {
        sort_id: sort_id.to_string(),
    }
}

fn number_of_var(count: u64, var: &str) -> ColorExpr {
    ColorExpr::NumberOf {
        count,
        color: Box::new(ColorTerm::Variable(var.to_string())),
    }
}

fn transition(id: &str) -> ColoredTransition {
    ColoredTransition {
        id: id.to_string(),
        name: Some(id.to_string()),
        guard: None,
    }
}

fn empty_net() -> ColoredNet {
    ColoredNet {
        name: Some("test".to_string()),
        sorts: vec![],
        variables: vec![],
        places: vec![],
        transitions: vec![],
        arcs: vec![],
    }
}

#[test]
fn test_collapse_uniform_place() {
    // Place p1 has sort S (3 colors). All arcs use `All` inscription.
    // Should be collapsed to Dot.
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 3), dot_sort("dot")];
    net.places = vec![place("p1", "S", Some(all("S")))];
    net.transitions = vec![transition("t1")];
    net.arcs = vec![
        arc("p1", "t1", all("S")), // input arc
        arc("t1", "p1", all("S")), // output arc
    ];

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    assert_eq!(report.collapsed_places.len(), 1);
    assert_eq!(report.collapsed_places[0], ("p1".to_string(), 3));
    assert_eq!(report.places_saved(), 2); // 3 - 1 = 2

    // Place should now have Dot sort.
    assert_eq!(net.places[0].sort_id, "dot");

    // Initial marking should be per-color count (1 for All).
    match &net.places[0].initial_marking {
        Some(ColorExpr::NumberOf { count, color }) => {
            assert_eq!(*count, 1);
            assert!(matches!(color.as_ref(), ColorTerm::DotConstant));
        }
        other => panic!("expected NumberOf(1, DotConstant), got {other:?}"),
    }
}

#[test]
fn test_no_collapse_when_arc_uses_variable() {
    // Place p1 has sort S (3 colors), but one arc uses a variable inscription.
    // Should NOT be collapsed.
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 3)];
    net.places = vec![place("p1", "S", Some(all("S")))];
    net.transitions = vec![transition("t1")];
    net.arcs = vec![
        arc("p1", "t1", number_of_var(1, "x")), // non-uniform: variable binding
        arc("t1", "p1", all("S")),
    ];

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    assert!(report.collapsed_places.is_empty());
    assert_eq!(net.places[0].sort_id, "S"); // unchanged
}

#[test]
fn test_no_collapse_dot_place() {
    // Place already has Dot sort — nothing to collapse.
    let mut net = empty_net();
    net.sorts = vec![dot_sort("dot")];
    net.places = vec![place("p1", "dot", None)];
    net.transitions = vec![transition("t1")];
    net.arcs = vec![arc("p1", "t1", all("dot"))];

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    assert!(report.collapsed_places.is_empty());
}

#[test]
fn test_no_collapse_when_shared_transition_has_non_uniform_arc() {
    // Two places: p1 (uniform arcs) and p2 (non-uniform arcs), both touching t1.
    // Under the strengthened criterion (#1418), p1 is disqualified because t1
    // also has a non-uniform arc to p2. Collapsing p1 while t1 binds variables
    // for p2 would create N P/T transitions competing for the collapsed p1.
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 5), dot_sort("dot")];
    net.places = vec![
        place("p1", "S", Some(all("S"))),
        place("p2", "S", Some(all("S"))),
    ];
    net.transitions = vec![transition("t1")];
    net.arcs = vec![
        arc("p1", "t1", all("S")),
        arc("t1", "p1", all("S")),
        arc("p2", "t1", number_of_var(1, "x")), // non-uniform
        arc("t1", "p2", all("S")),
    ];

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    // Neither place should be collapsed: t1 has non-uniform arcs.
    assert!(
        report.collapsed_places.is_empty(),
        "p1 must not be collapsed when t1 has non-uniform arcs to p2"
    );
    assert_eq!(net.places[0].sort_id, "S");
    assert_eq!(net.places[1].sort_id, "S");
}

#[test]
fn test_collapse_no_marking() {
    // Place with no initial marking — collapse should work, marking stays None.
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 4), dot_sort("dot")];
    net.places = vec![place("p1", "S", None)];
    net.transitions = vec![transition("t1")];
    net.arcs = vec![arc("t1", "p1", all("S"))];

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    assert_eq!(report.collapsed_places.len(), 1);
    assert!(net.places[0].initial_marking.is_none());
}

#[test]
fn test_collapse_creates_dot_sort_if_missing() {
    // Net has no Dot sort — collapsing should create a synthetic one.
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 3)];
    net.places = vec![place("p1", "S", Some(all("S")))];
    net.transitions = vec![transition("t1")];
    net.arcs = vec![arc("p1", "t1", all("S")), arc("t1", "p1", all("S"))];

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    assert_eq!(report.collapsed_places.len(), 1);
    assert_eq!(net.places[0].sort_id, "dot_synthetic");
    // Verify the Dot sort was added.
    assert!(net
        .sorts
        .iter()
        .any(|s| matches!(s, ColorSort::Dot { id, .. } if id == "dot_synthetic")));
}

#[test]
fn test_places_saved_count() {
    // 3 places collapsed: sorts of size 5, 10, 2.
    // Saved = (5-1) + (10-1) + (2-1) = 4 + 9 + 1 = 14
    let report = ColorReductionReport {
        collapsed_places: vec![
            ("a".to_string(), 5),
            ("b".to_string(), 10),
            ("c".to_string(), 2),
        ],
    };
    assert_eq!(report.places_saved(), 14);
}

#[test]
fn test_arc_inscription_rewritten_to_dot() {
    // After collapsing, arc inscriptions should be NumberOf(1, DotConstant).
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 3), dot_sort("dot")];
    net.places = vec![place("p1", "S", Some(all("S")))];
    net.transitions = vec![transition("t1")];
    net.arcs = vec![arc("p1", "t1", all("S")), arc("t1", "p1", all("S"))];

    let mut _report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut _report);

    for a in &net.arcs {
        match &a.inscription {
            ColorExpr::NumberOf { count, color } => {
                assert_eq!(*count, 1);
                assert!(matches!(color.as_ref(), ColorTerm::DotConstant));
            }
            other => panic!("expected NumberOf after collapse, got {other:?}"),
        }
    }
}

#[test]
fn test_no_collapse_arc_between_two_candidates() {
    // Arc from p1 to p2 (via t1) with non-uniform inscription.
    // Both p1 and p2 are candidates (non-Dot sort). Under the strengthened
    // criterion (#1418), p1 is ALSO disqualified because t1 has non-uniform
    // arcs (to p2), meaning t1 binds variables and unfolds to N P/T transitions.
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 3), dot_sort("dot")];
    net.places = vec![
        place("p1", "S", Some(all("S"))),
        place("p2", "S", Some(all("S"))),
    ];
    net.transitions = vec![transition("t1")];
    net.arcs = vec![
        arc("p1", "t1", all("S")),              // uniform — p1's arcs are fine
        arc("t1", "p2", number_of_var(1, "x")), // non-uniform — t1 binds variables
        arc("p2", "t1", number_of_var(1, "x")), // non-uniform
    ];

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    // Neither place should be collapsed: t1 has non-uniform arcs.
    assert!(
        report.collapsed_places.is_empty(),
        "no places should be collapsed when the shared transition has non-uniform arcs"
    );
    assert_eq!(net.places[0].sort_id, "S");
    assert_eq!(net.places[1].sort_id, "S");
}

#[test]
fn test_no_collapse_non_uniform_initial_marking() {
    // Place has uniform arcs but non-uniform initial marking (variable-based).
    // Should NOT be collapsed.
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 3), dot_sort("dot")];
    net.places = vec![place(
        "p1",
        "S",
        Some(number_of_var(2, "x")), // non-uniform marking
    )];
    net.transitions = vec![transition("t1")];
    net.arcs = vec![arc("p1", "t1", all("S")), arc("t1", "p1", all("S"))];

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    assert!(report.collapsed_places.is_empty());
    assert_eq!(net.places[0].sort_id, "S");
}

#[test]
fn test_collapse_compound_add_marking() {
    // Place with Add([All, All]) marking — uniform, per-color count = 2.
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 4), dot_sort("dot")];
    let compound_marking = ColorExpr::Add(vec![all("S"), all("S")]);
    net.places = vec![place("p1", "S", Some(compound_marking))];
    net.transitions = vec![transition("t1")];
    net.arcs = vec![arc("p1", "t1", all("S")), arc("t1", "p1", all("S"))];

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    assert_eq!(report.collapsed_places.len(), 1);
    // per_color_count(Add([All, All])) = 1 + 1 = 2
    match &net.places[0].initial_marking {
        Some(ColorExpr::NumberOf { count, color }) => {
            assert_eq!(*count, 2);
            assert!(matches!(color.as_ref(), ColorTerm::DotConstant));
        }
        other => panic!("expected NumberOf(2, DotConstant), got {other:?}"),
    }
}

#[test]
fn test_collapse_rewrites_add_inscription_to_dot() {
    // Arc with Add([All, All]) inscription — both children should be rewritten.
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 3), dot_sort("dot")];
    net.places = vec![place("p1", "S", Some(all("S")))];
    net.transitions = vec![transition("t1")];
    let add_inscription = ColorExpr::Add(vec![all("S"), all("S")]);
    net.arcs = vec![arc("p1", "t1", all("S")), arc("t1", "p1", add_inscription)];

    let mut _report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut _report);

    // The Add inscription should have both children rewritten to DotConstant.
    match &net.arcs[1].inscription {
        ColorExpr::Add(children) => {
            assert_eq!(children.len(), 2);
            for child in children {
                match child {
                    ColorExpr::NumberOf { count, color } => {
                        assert_eq!(*count, 1);
                        assert!(matches!(color.as_ref(), ColorTerm::DotConstant));
                    }
                    other => panic!("expected NumberOf in Add child, got {other:?}"),
                }
            }
        }
        other => panic!("expected Add after rewrite, got {other:?}"),
    }
}

#[test]
fn test_no_collapse_add_inscription_with_mixed_children() {
    // Arc with Add([All, NumberOf(x)]) — not uniform, place should not collapse.
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 3), dot_sort("dot")];
    net.places = vec![place("p1", "S", Some(all("S")))];
    net.transitions = vec![transition("t1")];
    let mixed = ColorExpr::Add(vec![all("S"), number_of_var(1, "x")]);
    net.arcs = vec![arc("p1", "t1", mixed), arc("t1", "p1", all("S"))];

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    assert!(report.collapsed_places.is_empty());
    assert_eq!(net.places[0].sort_id, "S");
}

#[test]
fn test_no_collapse_when_transition_has_non_uniform_arc_elsewhere() {
    // Place p1 has uniform (All) arcs — would be collapsible by the old criterion.
    // But transition t1 ALSO connects to p2 with a variable inscription.
    // The strengthened criterion (#1418) disqualifies p1 because t1 would unfold
    // to N P/T transitions that compete for the collapsed p1's tokens.
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 3), dot_sort("dot")];
    net.places = vec![
        place("p1", "S", Some(all("S"))),
        place("p2", "S", Some(all("S"))),
    ];
    net.transitions = vec![transition("t1")];
    net.arcs = vec![
        arc("p1", "t1", all("S")),              // p1→t1: uniform ✓
        arc("t1", "p1", all("S")),              // t1→p1: uniform ✓
        arc("p2", "t1", number_of_var(1, "x")), // p2→t1: NON-uniform
        arc("t1", "p2", number_of_var(1, "x")), // t1→p2: NON-uniform
    ];

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    // p1 should NOT be collapsed: t1 has non-uniform arcs to p2.
    assert!(
        report.collapsed_places.is_empty(),
        "p1 must not be collapsed when a touching transition has non-uniform arcs elsewhere"
    );
    assert_eq!(net.places[0].sort_id, "S");
}

#[test]
fn test_collapse_when_all_transitions_fully_uniform() {
    // Place p1 has uniform arcs, AND the transition t1 has ALL arcs uniform
    // (including to other places). Safe to collapse.
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 3), dot_sort("dot")];
    net.places = vec![
        place("p1", "S", Some(all("S"))),
        place("p2", "S", Some(all("S"))),
    ];
    net.transitions = vec![transition("t1")];
    net.arcs = vec![
        arc("p1", "t1", all("S")),
        arc("t1", "p1", all("S")),
        arc("p2", "t1", all("S")),
        arc("t1", "p2", all("S")),
    ];

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    // Both p1 and p2 should be collapsed: t1 is fully color-blind.
    assert_eq!(report.collapsed_places.len(), 2);
}

#[test]
fn test_no_collapse_when_transition_has_guard() {
    // Place p1 has uniform arcs, but transition t1 has a guard.
    // A guard implies variable-dependent behavior, so collapsing is unsafe.
    use crate::hlpnml::GuardExpr;
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 3), dot_sort("dot")];
    net.places = vec![place("p1", "S", Some(all("S")))];
    net.transitions = vec![ColoredTransition {
        id: "t1".to_string(),
        name: Some("t1".to_string()),
        guard: Some(GuardExpr::True),
    }];
    net.arcs = vec![arc("p1", "t1", all("S")), arc("t1", "p1", all("S"))];

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    assert!(
        report.collapsed_places.is_empty(),
        "p1 must not be collapsed when a touching transition has a guard"
    );
}

#[test]
fn test_no_collapse_sibling_disqualification() {
    // Tests the sibling consistency guard (lines 198-276 of colored_reduce.rs).
    //
    // Setup: p1 (sort S, card 3) and p2 (sort R, card 4) share transition t1.
    // ALL arcs are uniform (All inscriptions), t1 has no guard → both places
    // pass the per-arc check AND the transition-level uniform check.
    //
    // p2 has a non-uniform initial marking, disqualifying it from collapsing.
    // So p2 is NOT in the surviving set.
    //
    // The sibling guard catches that p1 shares t1 with p2 (card > 1, not
    // surviving). Collapsing only p1 creates asymmetric unfolding.
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 3), cyclic_sort("R", 4), dot_sort("dot")];
    net.places = vec![
        place("p1", "S", Some(all("S"))),
        place("p2", "R", Some(number_of_var(2, "x"))), // non-uniform marking
    ];
    net.transitions = vec![transition("t1")];
    net.arcs = vec![
        arc("p1", "t1", all("S")), // uniform ✓
        arc("t1", "p1", all("S")), // uniform ✓
        arc("p2", "t1", all("R")), // uniform ✓
        arc("t1", "p2", all("R")), // uniform ✓
    ];

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    // p1 passes arc + guard + transition checks. But sibling guard catches
    // that t1 also touches p2 (card 4, not in surviving set due to non-uniform
    // marking). p1 must NOT be collapsed.
    assert!(
        report.collapsed_places.is_empty(),
        "p1 must not be collapsed when a sibling place on the same transition is non-collapsible with card > 1"
    );
    assert_eq!(net.places[0].sort_id, "S");
    assert_eq!(net.places[1].sort_id, "R");
}

#[test]
fn test_no_collapse_isolated_place() {
    // Place p1 has sort S (3 colors), uniform marking, but NO arcs.
    // Isolated places should not be collapsed: the optimization saves
    // nothing (no transitions touch them) and changing the unfolded
    // place count shifts place indices, which can break alias-based
    // predicate resolution (#1418).
    let mut net = empty_net();
    net.sorts = vec![cyclic_sort("S", 3), dot_sort("dot")];
    net.places = vec![place("p1", "S", Some(all("S")))];
    // No transitions, no arcs.

    let mut report = ColorReductionReport::default();
    collapse_constant_places(&mut net, &mut report);

    assert!(
        report.collapsed_places.is_empty(),
        "isolated places (no arcs) must not be collapsed"
    );
    assert_eq!(net.places[0].sort_id, "S");
}
