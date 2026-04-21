// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::io::Write;
use std::path::PathBuf;

use tempfile::TempDir;

use super::{PlaceIdx, TransitionIdx};
use crate::model::{PreparedModel, PropertyAliases};

pub(super) const MINIMAL_PT_NET: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="test" type="http://www.pnml.org/version-2009/grammar/ptnet">
    <page id="p1">
      <place id="P0"><initialMarking><text>1</text></initialMarking></place>
      <place id="P1"/>
      <transition id="T0"/>
      <arc id="a1" source="P0" target="T0"/>
      <arc id="a2" source="T0" target="P1"/>
    </page>
  </net>
</pnml>"#;

pub(super) const COLORED_NET: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="test" type="http://www.pnml.org/version-2009/grammar/symmetricnet">
    <page id="p1">
      <place id="P0"/>
    </page>
  </net>
</pnml>"#;

pub(super) const UNFOLDED_ALIAS_PT_NET: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="alias-test" type="http://www.pnml.org/version-2009/grammar/ptnet">
    <page id="p1">
      <place id="Fork_0"><initialMarking><text>1</text></initialMarking></place>
      <place id="Fork_1"><initialMarking><text>1</text></initialMarking></place>
      <place id="Done"/>
      <transition id="Take_0"/>
      <transition id="Take_1"/>
      <arc id="a1" source="Fork_0" target="Take_0"/>
      <arc id="a2" source="Take_0" target="Done"/>
      <arc id="a3" source="Fork_1" target="Take_1"/>
      <arc id="a4" source="Take_1" target="Done"/>
    </page>
  </net>
</pnml>"#;

pub(super) fn write_pnml(dir: &TempDir, content: &str) {
    let path = dir.path().join("model.pnml");
    let mut f = std::fs::File::create(path).expect("create model.pnml");
    f.write_all(content.as_bytes()).expect("write model.pnml");
}

pub(super) fn mcc_input_dir(model: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/mcc/2024/INPUTS")
        .join(model)
}

pub(super) fn alias_enriched(model: &PreparedModel) -> PropertyAliases {
    let mut aliases = model.aliases.clone();
    aliases
        .place_aliases
        .insert(String::from("Fork"), vec![PlaceIdx(0), PlaceIdx(1)]);
    aliases.transition_aliases.insert(
        String::from("Take"),
        vec![TransitionIdx(0), TransitionIdx(1)],
    );
    aliases
}

pub(super) fn write_upper_bounds_alias_xml(dir: &TempDir) {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>AliasModel-UpperBounds-00</id>
    <description>sum unfolded Fork places</description>
    <formula>
      <place-bound>
        <place>Fork</place>
      </place-bound>
    </formula>
  </property>
</property-set>"#;
    std::fs::write(dir.path().join("UpperBounds.xml"), xml).expect("write UpperBounds.xml");
}

pub(super) fn write_reachability_fireability_alias_xml(dir: &TempDir) {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>AliasModel-ReachabilityFireability-00</id>
    <description>some unfolded Take transition is fireable</description>
    <formula>
      <exists-path>
        <finally>
          <is-fireable><transition>Take</transition></is-fireable>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    std::fs::write(dir.path().join("ReachabilityFireability.xml"), xml)
        .expect("write ReachabilityFireability.xml");
}

pub(super) fn write_reachability_cardinality_alias_xml(dir: &TempDir) {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>AliasModel-ReachabilityCardinality-00</id>
    <description>sum unfolded Fork places in the initial state</description>
    <formula>
      <exists-path>
        <finally>
          <integer-le>
            <integer-constant>2</integer-constant>
            <tokens-count>
              <place>Fork</place>
            </tokens-count>
          </integer-le>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    std::fs::write(dir.path().join("ReachabilityCardinality.xml"), xml)
        .expect("write ReachabilityCardinality.xml");
}
