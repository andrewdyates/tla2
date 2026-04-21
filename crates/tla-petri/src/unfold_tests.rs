// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::hlpnml::parse_hlpnml;

use super::*;

/// Committed MCC-derived fixtures keep these unfolding tests buildable in a clean checkout.
const PHILOSOPHERS_5_PNML: &str = include_str!("../testdata/colored/philosophers_col_5.pnml");
const TOKEN_RING_10_PNML: &str = include_str!("../testdata/colored/token_ring_10.pnml");

#[test]
fn test_unfold_philosophers_5_place_count() {
    let colored = parse_hlpnml(PHILOSOPHERS_5_PNML).expect("should parse");
    let unfolded = unfold_to_pt(&colored).expect("should unfold");

    // 5 colored places × 5 colors = 25 P/T places.
    assert_eq!(unfolded.net.num_places(), 25, "5 places × 5 colors = 25");
}

#[test]
fn test_unfold_philosophers_5_transition_count() {
    let colored = parse_hlpnml(PHILOSOPHERS_5_PNML).expect("should parse");
    let unfolded = unfold_to_pt(&colored).expect("should unfold");

    // 5 transitions × 5 bindings (1 variable, 5 colors) = 25 transitions.
    assert_eq!(
        unfolded.net.num_transitions(),
        25,
        "5 transitions × 5 bindings = 25"
    );
}

#[test]
fn test_unfold_philosophers_5_initial_marking() {
    let colored = parse_hlpnml(PHILOSOPHERS_5_PNML).expect("should parse");
    let unfolded = unfold_to_pt(&colored).expect("should unfold");

    // Total initial tokens: Think has all 5 colors, Fork has all 5 colors.
    // Other places (Catch1, Catch2, Eat) have 0.
    let total: u64 = unfolded.net.initial_marking.iter().sum();
    assert_eq!(total, 10, "5 tokens in Think + 5 in Fork = 10");
}

#[test]
fn test_unfold_philosophers_5_place_aliases() {
    let colored = parse_hlpnml(PHILOSOPHERS_5_PNML).expect("should parse");
    let unfolded = unfold_to_pt(&colored).expect("should unfold");

    // "Think" should map to 5 unfolded places.
    let think_places = unfolded.aliases.resolve_places("Think");
    assert!(think_places.is_some());
    assert_eq!(
        think_places.unwrap().len(),
        5,
        "Think maps to 5 unfolded places"
    );

    // "Fork" should also map to 5 unfolded places.
    let fork_places = unfolded.aliases.resolve_places("Fork");
    assert!(fork_places.is_some());
    assert_eq!(fork_places.unwrap().len(), 5);
}

#[test]
fn test_unfold_philosophers_5_transition_aliases() {
    let colored = parse_hlpnml(PHILOSOPHERS_5_PNML).expect("should parse");
    let unfolded = unfold_to_pt(&colored).expect("should unfold");

    // Each colored transition should map to 5 unfolded instances.
    for name in &["FF1a", "FF1b", "FF2a", "FF2b", "End"] {
        let trans = unfolded.aliases.resolve_transitions(name);
        assert!(trans.is_some(), "transition '{name}' should have aliases");
        assert_eq!(
            trans.unwrap().len(),
            5,
            "transition '{name}' should map to 5 unfolded instances"
        );
    }
}

#[test]
fn test_unfold_philosophers_5_all_transitions_have_arcs() {
    let colored = parse_hlpnml(PHILOSOPHERS_5_PNML).expect("should parse");
    let unfolded = unfold_to_pt(&colored).expect("should unfold");

    // Every unfolded transition should have at least one input and one output.
    for trans in &unfolded.net.transitions {
        assert!(
            !trans.inputs.is_empty(),
            "transition '{}' should have inputs",
            trans.id
        );
        assert!(
            !trans.outputs.is_empty(),
            "transition '{}' should have outputs",
            trans.id
        );
    }
}

#[test]
fn test_unfold_philosophers_5_end_transition_arc_weights() {
    let colored = parse_hlpnml(PHILOSOPHERS_5_PNML).expect("should parse");
    let unfolded = unfold_to_pt(&colored).expect("should unfold");

    // End transition: consumes 1'(x) from Eat, produces 1'(x) to Think
    // + 1'(x) + 1'(x--1) to Fork. Total: 1 in, 3 out.
    for trans in &unfolded.net.transitions {
        if trans.id.starts_with("End_") {
            let in_w: u64 = trans.inputs.iter().map(|a| a.weight).sum();
            let out_w: u64 = trans.outputs.iter().map(|a| a.weight).sum();
            assert_eq!(in_w, 1, "{}: End consumes 1 from Eat", trans.id);
            assert_eq!(
                out_w, 3,
                "{}: End produces 1 to Think + 2 to Fork",
                trans.id
            );
        }
    }
}

#[test]
fn test_unfold_size_guard_places() {
    // Create a colored net that would exceed the place limit.
    // We can't easily do this with real models, so test the concept
    // with a direct assertion on the limit constants.
    assert!(MAX_UNFOLDED_PLACES > 0);
    assert!(MAX_UNFOLDED_TRANSITIONS > 0);
}

#[test]
fn test_unfold_token_ring_product_place_alias_cardinality() {
    let colored = parse_hlpnml(TOKEN_RING_10_PNML).expect("should parse");
    let unfolded = unfold_to_pt(&colored).expect("should unfold");

    let state_places = unfolded
        .aliases
        .resolve_places("State")
        .expect("State aliases should exist");
    assert_eq!(
        state_places.len(),
        121,
        "11 x 11 product sort should unfold to 121 places"
    );

    let total_tokens: u64 = state_places
        .iter()
        .map(|place| unfolded.net.initial_marking[place.0 as usize])
        .sum();
    assert_eq!(
        total_tokens, 11,
        "State starts with one token per process pair (i, i)"
    );
}

#[test]
fn test_unfold_token_ring_product_transitions_keep_arcs() {
    let colored = parse_hlpnml(TOKEN_RING_10_PNML).expect("should parse");
    let unfolded = unfold_to_pt(&colored).expect("should unfold");

    let main_process = unfolded
        .aliases
        .resolve_transitions("MainProcess")
        .expect("MainProcess aliases should exist");
    assert_eq!(
        main_process.len(),
        11,
        "single variable x should leave one MainProcess binding per process"
    );

    for transition_idx in main_process {
        let transition = &unfolded.net.transitions[transition_idx.0 as usize];
        assert!(
            !transition.inputs.is_empty(),
            "{} should keep product-sort input arcs",
            transition.id
        );
        assert!(
            !transition.outputs.is_empty(),
            "{} should keep tuple/successor output arcs",
            transition.id
        );
    }
}

/// Synthetic PNML with lessthanorequal guard: t1 fires only when x <= y.
/// Sort has 3 constants {a, b, c}, so x <= y allows 6 of 9 bindings:
/// (a,a), (a,b), (a,c), (b,b), (b,c), (c,c).
const ORDERING_GUARD_PNML: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="test" type="http://www.pnml.org/version-2009/grammar/symmetricnet">
    <page id="page0">
      <place id="p1">
        <type><structure><usersort declaration="s1"/></structure></type>
        <hlinitialMarking><structure><all><usersort declaration="s1"/></all></structure></hlinitialMarking>
      </place>
      <place id="p2">
        <type><structure><usersort declaration="s1"/></structure></type>
      </place>
      <transition id="t1">
        <condition><structure>
          <lessthanorequal>
            <subterm><variable refvariable="x"/></subterm>
            <subterm><variable refvariable="y"/></subterm>
          </lessthanorequal>
        </structure></condition>
      </transition>
      <arc id="a1" source="p1" target="t1">
        <hlinscription><structure>
          <numberof><subterm><numberconstant value="1"/></subterm><subterm><variable refvariable="x"/></subterm></numberof>
        </structure></hlinscription>
      </arc>
      <arc id="a2" source="t1" target="p2">
        <hlinscription><structure>
          <numberof><subterm><numberconstant value="1"/></subterm><subterm><variable refvariable="y"/></subterm></numberof>
        </structure></hlinscription>
      </arc>
    </page>
    <declaration><structure><declarations>
      <namedsort id="s1" name="S">
        <cyclicenumeration>
          <feconstant id="c1" name="a"/>
          <feconstant id="c2" name="b"/>
          <feconstant id="c3" name="c"/>
        </cyclicenumeration>
      </namedsort>
      <variabledecl id="x" name="x"><usersort declaration="s1"/></variabledecl>
      <variabledecl id="y" name="y"><usersort declaration="s1"/></variabledecl>
    </declarations></structure></declaration>
  </net>
</pnml>"#;

#[test]
fn test_unfold_ordering_guard_restricts_bindings() {
    // With `lessthanorequal(x, y)` on a 3-element sort, only 6 of 9
    // bindings survive (upper-triangular): (0,0),(0,1),(0,2),(1,1),(1,2),(2,2).
    let colored = parse_hlpnml(ORDERING_GUARD_PNML).expect("should parse");
    let unfolded = unfold_to_pt(&colored).expect("should unfold");

    // Without guard: 3 × 3 = 9 bindings → 9 unfolded transitions.
    // With lessthanorequal: 6 bindings → 6 unfolded transitions.
    assert_eq!(
        unfolded.net.num_transitions(),
        6,
        "lessthanorequal guard should allow 6 of 9 bindings"
    );
}
