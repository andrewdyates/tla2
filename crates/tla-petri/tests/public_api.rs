// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fs;
use std::io::Write;

use tempfile::TempDir;
use tla_mc_core::{PorPropertyClass, PorProvider, TransitionSystem};
use tla_petri::{parser, PetriNetSystem, StubbornPorProvider, TransitionIdx};

const TWO_TRANSITION_PNML: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="test" type="http://www.pnml.org/version-2009/grammar/ptnet">
    <page id="p1">
      <place id="P0"><initialMarking><text>1</text></initialMarking></place>
      <place id="P1"><initialMarking><text>1</text></initialMarking></place>
      <place id="P2"/>
      <place id="P3"/>
      <transition id="T0"/>
      <transition id="T1"/>
      <arc id="a1" source="P0" target="T0"/>
      <arc id="a2" source="T0" target="P2"/>
      <arc id="a3" source="P1" target="T1"/>
      <arc id="a4" source="T1" target="P3"/>
    </page>
  </net>
</pnml>"#;

fn write_model(dir: &TempDir) {
    let path = dir.path().join("model.pnml");
    let mut file = std::fs::File::create(path).expect("create model.pnml");
    file.write_all(TWO_TRANSITION_PNML.as_bytes())
        .expect("write model.pnml");
}

#[test]
fn public_api_exposes_transition_system_and_por_provider() {
    let dir = TempDir::new().expect("tempdir");
    write_model(&dir);

    let net = parser::parse_pnml_dir(dir.path()).expect("parse PNML");
    let system = PetriNetSystem::new(net.clone());
    let provider = StubbornPorProvider::new(net);

    let initial = system.initial_states().pop().expect("initial state");
    let enabled = system.enabled_transitions(&initial);
    let successors = system.successors(&initial);
    let reduced = provider.reduce(&initial, &enabled, PorPropertyClass::Deadlock);

    assert_eq!(enabled, vec![TransitionIdx(0), TransitionIdx(1)]);
    assert_eq!(successors.len(), 2);
    assert_eq!(reduced.len(), 1);
}

#[test]
fn public_api_keeps_existing_mcc_examination_entrypoints() {
    let dir = TempDir::new().expect("tempdir");
    write_model(&dir);
    fs::write(
        dir.path().join("ReachabilityFireability.xml"),
        r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>TestModel-ReachabilityFireability-00</id>
    <formula>
      <exists-path>
        <finally>
          <is-fireable><transition>T0</transition></is-fireable>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#,
    )
    .expect("write ReachabilityFireability.xml");

    let net = parser::parse_pnml_dir(dir.path()).expect("parse PNML");
    let records = tla_petri::examination::collect_examination_with_dir(
        &net,
        "TestModel",
        dir.path(),
        tla_petri::examination::Examination::ReachabilityFireability,
        &tla_petri::explorer::ExplorationConfig::new(1_000),
    )
    .expect("collect examination");

    assert_eq!(records.len(), 1);
}
