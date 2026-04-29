// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

const SIMPLE_PNML: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="simple" type="http://www.pnml.org/version-2009/grammar/ptnet">
    <page id="p1">
      <place id="P0"><initialMarking><text>1</text></initialMarking></place>
      <place id="P1"/>
      <transition id="T0"/>
      <arc id="a1" source="P0" target="T0"/>
      <arc id="a2" source="T0" target="P1"/>
    </page>
  </net>
</pnml>"#;

#[test]
fn test_parse_simple_net() {
    let net = parse_pnml(SIMPLE_PNML).expect("should parse");
    assert_eq!(net.num_places(), 2);
    assert_eq!(net.num_transitions(), 1);
    assert_eq!(net.initial_marking, vec![1, 0]);
    assert_eq!(net.places[0].id, "P0");
    assert_eq!(net.places[1].id, "P1");
    assert_eq!(net.transitions[0].id, "T0");
    assert_eq!(net.transitions[0].inputs.len(), 1);
    assert_eq!(net.transitions[0].outputs.len(), 1);
    assert_eq!(net.transitions[0].inputs[0].place, PlaceIdx(0));
    assert_eq!(net.transitions[0].inputs[0].weight, 1);
    assert_eq!(net.transitions[0].outputs[0].place, PlaceIdx(1));
}

const WEIGHTED_PNML: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="weighted" type="http://www.pnml.org/version-2009/grammar/ptnet">
    <page id="p1">
      <place id="P0"><initialMarking><text>5</text></initialMarking></place>
      <place id="P1"/>
      <transition id="T0"/>
      <arc id="a1" source="P0" target="T0">
        <inscription><text>2</text></inscription>
      </arc>
      <arc id="a2" source="T0" target="P1">
        <inscription><text>3</text></inscription>
      </arc>
    </page>
  </net>
</pnml>"#;

#[test]
fn test_parse_weighted_arcs() {
    let net = parse_pnml(WEIGHTED_PNML).expect("should parse");
    assert_eq!(net.initial_marking, vec![5, 0]);
    assert_eq!(net.transitions[0].inputs[0].weight, 2);
    assert_eq!(net.transitions[0].outputs[0].weight, 3);
}

const COLORED_PNML: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="colored" type="http://www.pnml.org/version-2009/grammar/symmetricnet">
    <page id="p1"/>
  </net>
</pnml>"#;

#[test]
fn test_reject_colored_net() {
    let err = parse_pnml(COLORED_PNML).unwrap_err();
    assert!(
        matches!(err, PnmlError::UnsupportedNetType { .. }),
        "expected UnsupportedNetType, got: {err}"
    );
}

const NO_NET_PNML: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
</pnml>"#;

#[test]
fn test_reject_missing_net() {
    let err = parse_pnml(NO_NET_PNML).unwrap_err();
    assert!(
        matches!(err, PnmlError::MissingElement(_)),
        "expected MissingElement, got: {err}"
    );
}

const NAMED_PNML: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="named" type="http://www.pnml.org/version-2009/grammar/ptnet">
    <name><text>MyNet</text></name>
    <page id="p1">
      <place id="P0">
        <name><text>start</text></name>
        <initialMarking><text>3</text></initialMarking>
      </place>
      <transition id="T0">
        <name><text>fire</text></name>
      </transition>
      <arc id="a1" source="P0" target="T0"/>
      <arc id="a2" source="T0" target="P0"/>
    </page>
  </net>
</pnml>"#;

#[test]
fn test_parse_named_elements() {
    let net = parse_pnml(NAMED_PNML).expect("should parse");
    assert_eq!(net.name.as_deref(), Some("MyNet"));
    assert_eq!(net.places[0].name.as_deref(), Some("start"));
    assert_eq!(net.transitions[0].name.as_deref(), Some("fire"));
    assert_eq!(net.initial_marking, vec![3]);
}

const MULTI_TRANSITION_PNML: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="multi" type="http://www.pnml.org/version-2009/grammar/ptnet">
    <page id="p1">
      <place id="P0"><initialMarking><text>1</text></initialMarking></place>
      <place id="P1"/>
      <place id="P2"/>
      <transition id="T0"/>
      <transition id="T1"/>
      <arc id="a1" source="P0" target="T0"/>
      <arc id="a2" source="T0" target="P1"/>
      <arc id="a3" source="P0" target="T1"/>
      <arc id="a4" source="T1" target="P2"/>
    </page>
  </net>
</pnml>"#;

#[test]
fn test_parse_multiple_transitions() {
    let net = parse_pnml(MULTI_TRANSITION_PNML).expect("should parse");
    assert_eq!(net.num_places(), 3);
    assert_eq!(net.num_transitions(), 2);
    assert_eq!(net.transitions[0].inputs.len(), 1);
    assert_eq!(net.transitions[0].outputs.len(), 1);
    assert_eq!(net.transitions[1].inputs.len(), 1);
    assert_eq!(net.transitions[1].outputs.len(), 1);
}

#[test]
fn test_parse_real_benchmark() {
    // Try to parse a real MCC benchmark if available
    let path = std::path::Path::new("benchmarks/mcc/2024/INPUTS/Referendum-PT-0010/model.pnml");
    if !path.exists() {
        return; // Skip if benchmarks not downloaded
    }
    let net = parse_pnml_file(path).expect("should parse real benchmark");
    assert!(net.num_places() > 0);
    assert!(net.num_transitions() > 0);
    assert_eq!(net.initial_marking.len(), net.num_places());
}
