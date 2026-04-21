// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::property_xml::{parse_properties_xml, Formula, IntExpr, PathQuantifier, StatePredicate};

#[test]
fn test_parse_upper_bounds_single_property() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-UpperBounds-00</id>
    <description>test</description>
    <formula>
      <place-bound>
        <place>p1</place>
        <place>p2</place>
      </place-bound>
    </formula>
  </property>
</property-set>"#;
    let props = parse_properties_xml(xml).expect("parse should succeed");
    assert_eq!(props.len(), 1);
    assert_eq!(props[0].id, "Model-UpperBounds-00");
    let Formula::PlaceBound(places) = &props[0].formula else {
        panic!("expected PlaceBound");
    };
    assert_eq!(places, &["p1", "p2"]);
}

#[test]
fn test_parse_upper_bounds_multiple_properties() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-UpperBounds-00</id>
    <description>test</description>
    <formula>
      <place-bound>
        <place>p1</place>
      </place-bound>
    </formula>
  </property>
  <property>
    <id>Model-UpperBounds-01</id>
    <description>test</description>
    <formula>
      <place-bound>
        <place>p2</place>
        <place>p3</place>
        <place>p4</place>
      </place-bound>
    </formula>
  </property>
</property-set>"#;
    let props = parse_properties_xml(xml).expect("parse should succeed");
    assert_eq!(props.len(), 2);
    let Formula::PlaceBound(places) = &props[1].formula else {
        panic!("expected PlaceBound");
    };
    assert_eq!(places.len(), 3);
}

#[test]
fn test_reject_empty_property_set() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("empty property-set should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("property-set"),
        "error should mention property-set: {msg}"
    );
    assert!(
        msg.contains("<property>"),
        "error should mention missing <property>: {msg}"
    );
}

#[test]
fn test_reject_wrong_root_element() {
    let xml = r#"<?xml version="1.0"?>
<not-a-property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-UB-00</id>
    <description>test</description>
    <formula>
      <place-bound><place>p1</place></place-bound>
    </formula>
  </property>
</not-a-property-set>"#;
    let err = parse_properties_xml(xml).expect_err("wrong root should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("expected <property-set>"),
        "error should mention expected root: {msg}"
    );
    assert!(
        msg.contains("not-a-property-set"),
        "error should mention actual root: {msg}"
    );
}

#[test]
fn test_parse_missing_id_returns_error() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <formula>
      <place-bound>
        <place>p1</place>
      </place-bound>
    </formula>
  </property>
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("should fail on missing id");
    let msg = err.to_string();
    assert!(
        msg.contains("property"),
        "error should mention property: {msg}"
    );
    assert!(msg.contains("<id>"), "error should mention <id>: {msg}");
}

#[test]
fn test_reject_duplicate_property_id() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-UB-00</id>
    <id>Model-UB-01</id>
    <formula>
      <place-bound><place>p1</place></place-bound>
    </formula>
  </property>
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("duplicate property id should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("property"),
        "error should mention property: {msg}"
    );
    assert!(
        msg.contains("<id>"),
        "error should mention duplicate <id>: {msg}"
    );
}

#[test]
fn test_reject_duplicate_property_formula() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-UB-00</id>
    <formula>
      <place-bound><place>p1</place></place-bound>
    </formula>
    <formula>
      <place-bound><place>p2</place></place-bound>
    </formula>
  </property>
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("duplicate property formula should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("property"),
        "error should mention property: {msg}"
    );
    assert!(
        msg.contains("<formula>"),
        "error should mention duplicate <formula>: {msg}"
    );
}

#[test]
fn test_parse_reachability_cardinality_ef() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-RC-00</id>
    <description>test</description>
    <formula>
      <exists-path>
        <finally>
          <integer-le>
            <integer-constant>5</integer-constant>
            <tokens-count>
              <place>p1</place>
              <place>p2</place>
            </tokens-count>
          </integer-le>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    let props = parse_properties_xml(xml).expect("parse should succeed");
    assert_eq!(props.len(), 1);
    let Formula::Reachability(rf) = &props[0].formula else {
        panic!("expected Reachability");
    };
    assert_eq!(rf.quantifier, PathQuantifier::EF);
    let StatePredicate::IntLe(left, right) = &rf.predicate else {
        panic!("expected IntLe");
    };
    let IntExpr::Constant(c) = left else {
        panic!("expected Constant");
    };
    assert_eq!(*c, 5);
    let IntExpr::TokensCount(places) = right else {
        panic!("expected TokensCount");
    };
    assert_eq!(places, &["p1", "p2"]);
}

#[test]
fn test_parse_reachability_fireability_ag() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-RF-00</id>
    <description>test</description>
    <formula>
      <all-paths>
        <globally>
          <negation>
            <is-fireable>
              <transition>t1</transition>
              <transition>t2</transition>
            </is-fireable>
          </negation>
        </globally>
      </all-paths>
    </formula>
  </property>
</property-set>"#;
    let props = parse_properties_xml(xml).expect("parse should succeed");
    let Formula::Reachability(rf) = &props[0].formula else {
        panic!("expected Reachability");
    };
    assert_eq!(rf.quantifier, PathQuantifier::AG);
    let StatePredicate::Not(inner) = &rf.predicate else {
        panic!("expected Not");
    };
    let StatePredicate::IsFireable(transitions) = inner.as_ref() else {
        panic!("expected IsFireable");
    };
    assert_eq!(transitions, &["t1", "t2"]);
}

#[test]
fn test_parse_reachability_nested_boolean() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-RC-01</id>
    <description>test</description>
    <formula>
      <exists-path>
        <finally>
          <conjunction>
            <integer-le>
              <tokens-count><place>p1</place></tokens-count>
              <integer-constant>3</integer-constant>
            </integer-le>
            <disjunction>
              <is-fireable><transition>t1</transition></is-fireable>
              <is-fireable><transition>t2</transition></is-fireable>
            </disjunction>
          </conjunction>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    let props = parse_properties_xml(xml).expect("parse should succeed");
    let Formula::Reachability(rf) = &props[0].formula else {
        panic!("expected Reachability");
    };
    assert_eq!(rf.quantifier, PathQuantifier::EF);
    let StatePredicate::And(children) = &rf.predicate else {
        panic!("expected And");
    };
    assert_eq!(children.len(), 2);
    assert!(matches!(&children[0], StatePredicate::IntLe(..)));
    let StatePredicate::Or(disj) = &children[1] else {
        panic!("expected Or");
    };
    assert_eq!(disj.len(), 2);
}

// --- Empty-operand rejection tests (#1258) ---

#[test]
fn test_reject_empty_place_bound() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-UB-empty</id>
    <description>test</description>
    <formula>
      <place-bound/>
    </formula>
  </property>
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("empty place-bound should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("place-bound"),
        "error should mention place-bound: {msg}"
    );
    assert!(
        msg.contains("<place>"),
        "error should mention missing <place>: {msg}"
    );
}

#[test]
fn test_reject_empty_tokens_count() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-RC-empty-tc</id>
    <description>test</description>
    <formula>
      <exists-path>
        <finally>
          <integer-le>
            <tokens-count/>
            <integer-constant>0</integer-constant>
          </integer-le>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("empty tokens-count should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("tokens-count"),
        "error should mention tokens-count: {msg}"
    );
    assert!(
        msg.contains("<place>"),
        "error should mention missing <place>: {msg}"
    );
}

#[test]
fn test_reject_empty_is_fireable() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-RF-empty-if</id>
    <description>test</description>
    <formula>
      <exists-path>
        <finally>
          <is-fireable/>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("empty is-fireable should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("is-fireable"),
        "error should mention is-fireable: {msg}"
    );
    assert!(
        msg.contains("<transition>"),
        "error should mention missing <transition>: {msg}"
    );
}

#[test]
fn test_reject_empty_state_predicate_conjunction() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-RC-empty-conj</id>
    <description>test</description>
    <formula>
      <exists-path>
        <finally>
          <conjunction/>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("empty conjunction should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("conjunction"),
        "error should mention conjunction: {msg}"
    );
}

#[test]
fn test_reject_empty_state_predicate_disjunction() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-RC-empty-disj</id>
    <description>test</description>
    <formula>
      <exists-path>
        <finally>
          <disjunction/>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("empty disjunction should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("disjunction"),
        "error should mention disjunction: {msg}"
    );
}

// --- Empty-text element rejection (audit follow-up for #1258) ---

#[test]
fn test_reject_place_with_empty_text() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-UB-empty-text</id>
    <description>test</description>
    <formula>
      <place-bound>
        <place></place>
        <place>p1</place>
      </place-bound>
    </formula>
  </property>
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("place with empty text should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("no text content"),
        "error should mention missing text: {msg}"
    );
}

#[test]
fn test_reject_transition_with_empty_text() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-RF-empty-text</id>
    <description>test</description>
    <formula>
      <exists-path>
        <finally>
          <is-fireable>
            <transition/>
            <transition>t1</transition>
          </is-fireable>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("transition with empty text should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("no text content"),
        "error should mention missing text: {msg}"
    );
}

// --- Over-arity rejection tests (#1260) ---

#[test]
fn test_reject_reachability_finally_with_two_children() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-RC-arity</id>
    <description>test</description>
    <formula>
      <exists-path>
        <finally>
          <is-fireable><transition>t1</transition></is-fireable>
          <is-fireable><transition>t2</transition></is-fireable>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("over-arity finally should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("finally"),
        "error should mention finally: {msg}"
    );
    assert!(
        msg.contains("exactly one"),
        "error should say exactly one: {msg}"
    );
}

#[test]
fn test_reject_state_predicate_negation_with_two_children() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-RF-arity</id>
    <description>test</description>
    <formula>
      <exists-path>
        <finally>
          <negation>
            <is-fireable><transition>t1</transition></is-fireable>
            <is-fireable><transition>t2</transition></is-fireable>
          </negation>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("over-arity negation should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("negation"),
        "error should mention negation: {msg}"
    );
    assert!(
        msg.contains("exactly one"),
        "error should say exactly one: {msg}"
    );
}

#[test]
fn test_reject_integer_le_with_three_operands() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-RC-arity3</id>
    <description>test</description>
    <formula>
      <exists-path>
        <finally>
          <integer-le>
            <integer-constant>1</integer-constant>
            <integer-constant>2</integer-constant>
            <integer-constant>3</integer-constant>
          </integer-le>
        </finally>
      </exists-path>
    </formula>
  </property>
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("integer-le with three operands should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("integer-le"),
        "error should mention integer-le: {msg}"
    );
    assert!(
        msg.contains("exactly two"),
        "error should say exactly two: {msg}"
    );
}

#[test]
fn test_reject_reachability_formula_with_two_top_level_elements() {
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-RC-arity2</id>
    <description>test</description>
    <formula>
      <exists-path>
        <finally>
          <is-fireable><transition>t1</transition></is-fireable>
        </finally>
      </exists-path>
      <all-paths>
        <globally>
          <is-fireable><transition>t2</transition></is-fireable>
        </globally>
      </all-paths>
    </formula>
  </property>
</property-set>"#;
    let err = parse_properties_xml(xml).expect_err("two top-level formulas should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("formula"),
        "error should mention formula: {msg}"
    );
    assert!(
        msg.contains("exactly one"),
        "error should say exactly one: {msg}"
    );
}
