// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Committed MCC-derived fixtures keep these parser tests buildable in a clean checkout.
const PHILOSOPHERS_5_PNML: &str = include_str!("../testdata/colored/philosophers_col_5.pnml");
const BART_2_PNML: &str = include_str!("../testdata/colored/bart_col_2.pnml");
const TOKEN_RING_10_PNML: &str = include_str!("../testdata/colored/token_ring_10.pnml");

#[test]
fn test_parse_philosophers_col_5_sorts() {
    let net = parse_hlpnml(PHILOSOPHERS_5_PNML).expect("should parse");
    assert_eq!(net.sorts.len(), 1);
    match &net.sorts[0] {
        ColorSort::CyclicEnum {
            name, constants, ..
        } => {
            assert_eq!(name, "Philo");
            assert_eq!(constants.len(), 5);
        }
        other => panic!("expected CyclicEnum, got: {other:?}"),
    }
}

#[test]
fn test_parse_philosophers_col_5_variables() {
    let net = parse_hlpnml(PHILOSOPHERS_5_PNML).expect("should parse");
    assert_eq!(net.variables.len(), 1);
    assert_eq!(net.variables[0].name, "x");
    assert_eq!(net.variables[0].sort_id, "philo");
}

#[test]
fn test_parse_philosophers_col_5_places() {
    let net = parse_hlpnml(PHILOSOPHERS_5_PNML).expect("should parse");
    assert_eq!(
        net.places.len(),
        5,
        "5 colored places: Think, Fork, Catch1, Catch2, Eat"
    );

    let think = net.places.iter().find(|p| p.id == "Think").expect("Think");
    assert_eq!(think.sort_id, "philo");
    assert!(
        think.initial_marking.is_some(),
        "Think has 'all' initial marking"
    );

    let eat = net.places.iter().find(|p| p.id == "Eat").expect("Eat");
    assert!(eat.initial_marking.is_none(), "Eat has no initial marking");
}

#[test]
fn test_parse_philosophers_col_5_transitions() {
    let net = parse_hlpnml(PHILOSOPHERS_5_PNML).expect("should parse");
    assert_eq!(
        net.transitions.len(),
        5,
        "5 transitions: FF1a, FF1b, FF2a, FF2b, End"
    );
}

#[test]
fn test_parse_philosophers_col_5_arcs() {
    let net = parse_hlpnml(PHILOSOPHERS_5_PNML).expect("should parse");
    assert_eq!(net.arcs.len(), 15, "Philosophers has 15 arcs");
}

#[test]
fn test_parse_arc_predecessor_inscription() {
    let net = parse_hlpnml(PHILOSOPHERS_5_PNML).expect("should parse");

    // Fork2ff1a has inscription 1'(x--1) = predecessor of x.
    let fork_arc = net
        .arcs
        .iter()
        .find(|a| a.id == "Fork2ff1a")
        .expect("Fork2ff1a arc");

    match &fork_arc.inscription {
        ColorExpr::NumberOf { count, color } => {
            assert_eq!(*count, 1);
            assert!(
                matches!(color.as_ref(), ColorTerm::Predecessor(_)),
                "expected predecessor, got: {color:?}"
            );
        }
        other => panic!("expected NumberOf, got: {other:?}"),
    }
}

#[test]
fn test_parse_arc_add_inscription() {
    let net = parse_hlpnml(PHILOSOPHERS_5_PNML).expect("should parse");

    // End2fork has inscription 1'(x) + 1'(x--1) = add of two numberof.
    let end_fork = net
        .arcs
        .iter()
        .find(|a| a.id == "End2fork")
        .expect("End2fork arc");

    match &end_fork.inscription {
        ColorExpr::Add(children) => {
            assert_eq!(children.len(), 2, "add of two subterms");
        }
        other => panic!("expected Add, got: {other:?}"),
    }
}

#[test]
fn test_parse_bart_product_sorts() {
    let net = parse_hlpnml(BART_2_PNML).expect("should parse");

    let train_context = net
        .sorts
        .iter()
        .find(|sort| sort.id() == "traincontext")
        .expect("traincontext sort");

    match train_context {
        ColorSort::Product { components, .. } => {
            assert_eq!(
                components,
                &[
                    String::from("trainid"),
                    String::from("speed"),
                    String::from("distance"),
                ]
            );
        }
        other => panic!("expected Product sort, got: {other:?}"),
    }
}

#[test]
fn test_parse_bart_product_tuple_initial_marking() {
    let net = parse_hlpnml(BART_2_PNML).expect("should parse");
    let train_state = net
        .places
        .iter()
        .find(|place| place.id == "TrainState")
        .expect("TrainState");

    match train_state.initial_marking.as_ref() {
        Some(ColorExpr::Add(children)) => {
            assert_eq!(children.len(), 2, "TrainState has two initial tuples");
            for child in children {
                match child {
                    ColorExpr::NumberOf { color, .. } => match color.as_ref() {
                        ColorTerm::Tuple(terms) => {
                            assert_eq!(terms.len(), 3, "traincontext tuple has 3 components");
                        }
                        other => panic!("expected tuple term, got: {other:?}"),
                    },
                    other => panic!("expected numberof child, got: {other:?}"),
                }
            }
        }
        other => panic!("expected add initial marking, got: {other:?}"),
    }
}

#[test]
fn test_parse_token_ring_tuple_successor_component() {
    let net = parse_hlpnml(TOKEN_RING_10_PNML).expect("should parse");
    let main_arc = net
        .arcs
        .iter()
        .find(|arc| arc.id == "mainproc2state")
        .expect("mainproc2state arc");

    match &main_arc.inscription {
        ColorExpr::Add(children) => match &children[0] {
            ColorExpr::NumberOf { color, .. } => match color.as_ref() {
                ColorTerm::Tuple(terms) => {
                    assert_eq!(terms.len(), 2, "State tuple has two process components");
                    assert!(
                        matches!(terms[1], ColorTerm::Successor(_)),
                        "second tuple component should be successor(varx)"
                    );
                }
                other => panic!("expected tuple term, got: {other:?}"),
            },
            other => panic!("expected numberof child, got: {other:?}"),
        },
        other => panic!("expected add inscription, got: {other:?}"),
    }
}

#[test]
fn test_parse_bart_ordering_guards() {
    let net = parse_hlpnml(BART_2_PNML).expect("BART-002 should parse with ordering guards");

    // BART uses lessthanorequal and greaterthan guards on transitions.
    let guarded_transitions: Vec<_> = net
        .transitions
        .iter()
        .filter(|t| t.guard.is_some())
        .collect();

    assert!(
        !guarded_transitions.is_empty(),
        "BART should have guarded transitions"
    );

    // Verify at least one ordering guard is present (not just equality/inequality).
    let has_ordering = guarded_transitions
        .iter()
        .any(|t| guard_has_ordering(t.guard.as_ref().unwrap()));
    assert!(
        has_ordering,
        "BART should have at least one ordering guard (lessthan/greaterthan)"
    );
}

fn guard_has_ordering(guard: &GuardExpr) -> bool {
    match guard {
        GuardExpr::LessThan(_, _)
        | GuardExpr::LessThanOrEqual(_, _)
        | GuardExpr::GreaterThan(_, _)
        | GuardExpr::GreaterThanOrEqual(_, _) => true,
        GuardExpr::And(children) | GuardExpr::Or(children) => {
            children.iter().any(guard_has_ordering)
        }
        GuardExpr::Not(inner) => guard_has_ordering(inner),
        _ => false,
    }
}

#[test]
fn test_fail_closed_rejects_unknown_guard_operator() {
    // A guard with an unrecognized operator must cause parse failure.
    let xml = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="test" type="http://www.pnml.org/version-2009/grammar/symmetricnet">
    <page id="page0">
      <place id="p1">
        <type><structure><usersort declaration="s1"/></structure></type>
      </place>
      <transition id="t1">
        <condition><structure>
          <unknownoperator>
            <subterm><variable refvariable="x"/></subterm>
            <subterm><variable refvariable="y"/></subterm>
          </unknownoperator>
        </structure></condition>
      </transition>
    </page>
    <declaration><structure><declarations>
      <namedsort id="s1" name="S">
        <cyclicenumeration>
          <feconstant id="c1" name="a"/>
          <feconstant id="c2" name="b"/>
        </cyclicenumeration>
      </namedsort>
      <variabledecl id="x" name="x"><usersort declaration="s1"/></variabledecl>
      <variabledecl id="y" name="y"><usersort declaration="s1"/></variabledecl>
    </declarations></structure></declaration>
  </net>
</pnml>"#;

    let result = parse_hlpnml(xml);
    assert!(
        result.is_err(),
        "unknown guard operator must cause parse failure, got: {result:?}"
    );
}

#[test]
fn test_fail_closed_rejects_unknown_color_term() {
    // A color term with an unrecognized tag must cause parse failure.
    let xml = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="test" type="http://www.pnml.org/version-2009/grammar/symmetricnet">
    <page id="page0">
      <place id="p1">
        <type><structure><usersort declaration="s1"/></structure></type>
      </place>
      <transition id="t1"/>
      <arc id="a1" source="p1" target="t1">
        <hlinscription><structure>
          <numberof>
            <subterm><numberconstant value="1"/></subterm>
            <subterm><finiteintrangeconstant value="42">
              <finiteintrange start="0" end="100"/>
            </finiteintrangeconstant></subterm>
          </numberof>
        </structure></hlinscription>
      </arc>
    </page>
    <declaration><structure><declarations>
      <namedsort id="s1" name="S">
        <cyclicenumeration>
          <feconstant id="c1" name="a"/>
        </cyclicenumeration>
      </namedsort>
    </declarations></structure></declaration>
  </net>
</pnml>"#;

    let result = parse_hlpnml(xml);
    assert!(
        result.is_err(),
        "unknown color term must cause parse failure, got: {result:?}"
    );
}
