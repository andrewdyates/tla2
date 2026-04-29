// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeSet;
use std::fs;

use pnml_tools::error::PnmlError;
use pnml_tools::model::{load_model_dir, SourceNetKind};
use tempfile::TempDir;

const UNKNOWN_GUARD_PNML: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="unknown-guard" type="http://www.pnml.org/version-2009/grammar/symmetricnet">
    <page id="page0">
      <place id="p0">
        <type><structure><usersort declaration="s1"/></structure></type>
      </place>
      <transition id="t0">
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

const UNKNOWN_COLOR_TERM_PNML: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="unknown-color-term" type="http://www.pnml.org/version-2009/grammar/symmetricnet">
    <page id="page0">
      <place id="p0">
        <type><structure><usersort declaration="s1"/></structure></type>
        <hlinitialMarking><structure>
          <numberof>
            <subterm><numberconstant value="1"/></subterm>
            <subterm><finiteintrangeconstant value="42">
              <finiteintrange start="0" end="100"/>
            </finiteintrangeconstant></subterm>
          </numberof>
        </structure></hlinitialMarking>
      </place>
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

const ORDERING_GUARD_PNML: &str = r#"<?xml version="1.0"?>
<pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
  <net id="ordering-guard" type="http://www.pnml.org/version-2009/grammar/symmetricnet">
    <page id="page0">
      <place id="p0">
        <type><structure><usersort declaration="s1"/></structure></type>
      </place>
      <transition id="t0">
        <condition><structure>
          <lessthan>
            <subterm><variable refvariable="x"/></subterm>
            <subterm><variable refvariable="y"/></subterm>
          </lessthan>
        </structure></condition>
      </transition>
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

fn write_model(dir: &TempDir, model: &str) {
    fs::write(dir.path().join("model.pnml"), model).expect("write model.pnml");
}

#[test]
fn test_load_model_dir_rejects_unknown_guard_operator_for_symmetric_net() {
    let dir = TempDir::new().expect("tempdir should create");
    write_model(&dir, UNKNOWN_GUARD_PNML);

    let error = load_model_dir(dir.path()).expect_err("unknown guard operator must fail closed");
    match error {
        PnmlError::UnsupportedNetType { net_type } => {
            assert!(
                net_type.contains("unsupported guard operator: unknownoperator"),
                "error should mention the unknown guard operator, got: {net_type}"
            );
        }
        other => panic!("expected UnsupportedNetType, got: {other:?}"),
    }
}

#[test]
fn test_load_model_dir_rejects_unknown_color_term_for_symmetric_net() {
    let dir = TempDir::new().expect("tempdir should create");
    write_model(&dir, UNKNOWN_COLOR_TERM_PNML);

    let error = load_model_dir(dir.path()).expect_err("unknown color term must fail closed");
    match error {
        PnmlError::UnsupportedNetType { net_type } => {
            assert!(
                net_type.contains("unsupported color term: finiteintrangeconstant"),
                "error should mention the unknown color term, got: {net_type}"
            );
        }
        other => panic!("expected UnsupportedNetType, got: {other:?}"),
    }
}

#[test]
fn test_load_model_dir_unfolds_only_ordered_bindings_for_less_than_guard() {
    let dir = TempDir::new().expect("tempdir should create");
    write_model(&dir, ORDERING_GUARD_PNML);

    let model = load_model_dir(dir.path()).expect("ordering guards should parse and unfold");
    assert_eq!(model.source_kind(), SourceNetKind::SymmetricNet);
    assert_eq!(
        model.net().num_places(),
        3,
        "one colored place should unfold per color"
    );

    let transition_ids: BTreeSet<_> = model
        .net()
        .transitions
        .iter()
        .map(|transition| transition.id.as_str())
        .collect();
    let expected: BTreeSet<_> = ["t0_a_b", "t0_a_c", "t0_b_c"].into_iter().collect();

    assert_eq!(
        transition_ids, expected,
        "less-than guard should keep only strictly ordered bindings"
    );
}
