// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fs;

use crate::property_xml::{
    parse_properties, parse_properties_xml, CtlFormula, Formula, LtlFormula, PathQuantifier,
    StatePredicate,
};
use tempfile::TempDir;

#[test]
fn test_parse_reachability_boolean_constant_state_predicates() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-RF-True</id>
    <description>test</description>
    <formula>
      <exists-path>
        <finally>
          <true/>
        </finally>
      </exists-path>
    </formula>
  </property>
  <property>
    <id>Model-RF-False</id>
    <description>test</description>
    <formula>
      <all-paths>
        <globally>
          <false/>
        </globally>
      </all-paths>
    </formula>
  </property>
</property-set>"#;

    let properties = parse_properties_xml(xml).expect("reachability constants should parse");
    assert_eq!(properties.len(), 2);

    let Formula::Reachability(true_formula) = &properties[0].formula else {
        panic!("expected reachability formula");
    };
    assert_eq!(true_formula.quantifier, PathQuantifier::EF);
    assert!(matches!(true_formula.predicate, StatePredicate::True));

    let Formula::Reachability(false_formula) = &properties[1].formula else {
        panic!("expected reachability formula");
    };
    assert_eq!(false_formula.quantifier, PathQuantifier::AG);
    assert!(matches!(false_formula.predicate, StatePredicate::False));
}

#[test]
fn test_parse_typed_boolean_constant_state_predicates_from_files() {
    let tempdir = TempDir::new().expect("tempdir should create");
    fs::write(
        tempdir.path().join("CTLCardinality.xml"),
        r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-CTLCardinality-00</id>
    <description>test</description>
    <formula>
      <all-paths>
        <globally>
          <true/>
        </globally>
      </all-paths>
    </formula>
  </property>
</property-set>"#,
    )
    .expect("CTL exam xml should write");
    fs::write(
        tempdir.path().join("LTLFireability.xml"),
        r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-LTLFireability-00</id>
    <description>test</description>
    <formula>
      <all-paths>
        <globally>
          <false/>
        </globally>
      </all-paths>
    </formula>
  </property>
</property-set>"#,
    )
    .expect("LTL exam xml should write");

    let ctl_properties =
        parse_properties(tempdir.path(), "CTLCardinality").expect("CTL constants should parse");
    assert_eq!(ctl_properties.len(), 1);
    let Formula::Ctl(CtlFormula::AG(inner)) = &ctl_properties[0].formula else {
        panic!("expected AG formula");
    };
    assert!(matches!(
        inner.as_ref(),
        CtlFormula::Atom(StatePredicate::True)
    ));

    let ltl_properties =
        parse_properties(tempdir.path(), "LTLFireability").expect("LTL constants should parse");
    assert_eq!(ltl_properties.len(), 1);
    let Formula::Ltl(LtlFormula::Globally(inner)) = &ltl_properties[0].formula else {
        panic!("expected Globally formula");
    };
    assert!(matches!(
        inner.as_ref(),
        LtlFormula::Atom(StatePredicate::False)
    ));
}
