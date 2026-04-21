// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fs;

use super::super::ctl::parse_root_formula as parse_ctl_root_formula;
use super::super::ltl::parse_root_formula as parse_ltl_root_formula;
use crate::property_xml::{
    parse_properties, CtlFormula, Formula, IntExpr, LtlFormula, StatePredicate,
};
use tempfile::TempDir;

fn parse_ctl_root(xml: &str) -> Formula {
    let doc = roxmltree::Document::parse(xml).expect("xml should parse");
    parse_ctl_root_formula(&doc.root_element()).expect("CTL formula should parse")
}

fn parse_ltl_root(xml: &str) -> Formula {
    let doc = roxmltree::Document::parse(xml).expect("xml should parse");
    parse_ltl_root_formula(&doc.root_element()).expect("LTL formula should parse")
}

fn write_exam_file(tempdir: &TempDir, exam_name: &str, body: &str) {
    let xml = format!(
        r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>Model-{exam_name}-00</id>
    <description>test</description>
    <formula>
{body}
    </formula>
  </property>
</property-set>"#
    );
    fs::write(tempdir.path().join(format!("{exam_name}.xml")), xml).expect("exam xml should write");
}

#[test]
fn test_parse_ctl_until_with_nested_quantifier() {
    let formula = parse_ctl_root(
        r#"<formula>
  <all-paths>
    <until>
      <before>
        <is-fireable><transition>t0</transition></is-fireable>
      </before>
      <reach>
        <exists-path>
          <next>
            <integer-le>
              <tokens-count><place>p0</place></tokens-count>
              <integer-constant>1</integer-constant>
            </integer-le>
          </next>
        </exists-path>
      </reach>
    </until>
  </all-paths>
</formula>"#,
    );

    let Formula::Ctl(CtlFormula::AU(before, reach)) = formula else {
        panic!("expected AU");
    };
    let CtlFormula::Atom(StatePredicate::IsFireable(transitions)) = before.as_ref() else {
        panic!("expected fireability atom");
    };
    assert_eq!(transitions, &["t0"]);

    let CtlFormula::EX(inner) = reach.as_ref() else {
        panic!("expected EX reach clause");
    };
    let CtlFormula::Atom(StatePredicate::IntLe(left, right)) = inner.as_ref() else {
        panic!("expected integer atom");
    };
    let IntExpr::TokensCount(places) = left else {
        panic!("expected tokens-count");
    };
    assert_eq!(places, &["p0"]);
    let IntExpr::Constant(value) = right else {
        panic!("expected constant");
    };
    assert_eq!(*value, 1);
}

#[test]
fn test_parse_ltl_globally_until_with_next() {
    let formula = parse_ltl_root(
        r#"<formula>
  <all-paths>
    <globally>
      <until>
        <before>
          <negation>
            <is-fireable><transition>t0</transition></is-fireable>
          </negation>
        </before>
        <reach>
          <next>
            <integer-le>
              <tokens-count><place>p1</place></tokens-count>
              <integer-constant>2</integer-constant>
            </integer-le>
          </next>
        </reach>
      </until>
    </globally>
  </all-paths>
</formula>"#,
    );

    let Formula::Ltl(LtlFormula::Globally(inner)) = formula else {
        panic!("expected Globally");
    };
    let LtlFormula::Until(before, reach) = inner.as_ref() else {
        panic!("expected Until");
    };
    let LtlFormula::Not(negated) = before.as_ref() else {
        panic!("expected negated before clause");
    };
    let LtlFormula::Atom(StatePredicate::IsFireable(transitions)) = negated.as_ref() else {
        panic!("expected fireability atom");
    };
    assert_eq!(transitions, &["t0"]);

    let LtlFormula::Next(next_inner) = reach.as_ref() else {
        panic!("expected Next reach clause");
    };
    let LtlFormula::Atom(StatePredicate::IntLe(left, right)) = next_inner.as_ref() else {
        panic!("expected integer atom");
    };
    let IntExpr::TokensCount(places) = left else {
        panic!("expected tokens-count");
    };
    assert_eq!(places, &["p1"]);
    let IntExpr::Constant(value) = right else {
        panic!("expected constant");
    };
    assert_eq!(*value, 2);
}

#[test]
fn test_parse_properties_dispatches_ctl_examination_from_file() {
    let tempdir = TempDir::new().expect("tempdir should create");
    write_exam_file(
        &tempdir,
        "CTLCardinality",
        r#"      <all-paths>
        <until>
          <before>
            <is-fireable><transition>t0</transition></is-fireable>
          </before>
          <reach>
            <exists-path>
              <next>
                <integer-le>
                  <tokens-count><place>p0</place></tokens-count>
                  <integer-constant>1</integer-constant>
                </integer-le>
              </next>
            </exists-path>
          </reach>
        </until>
      </all-paths>"#,
    );

    let properties =
        parse_properties(tempdir.path(), "CTLCardinality").expect("CTL file should parse");
    assert_eq!(properties.len(), 1);

    let Formula::Ctl(CtlFormula::AU(before, reach)) = &properties[0].formula else {
        panic!("expected AU formula");
    };
    let CtlFormula::Atom(StatePredicate::IsFireable(transitions)) = before.as_ref() else {
        panic!("expected fireability atom");
    };
    assert_eq!(transitions, &["t0"]);

    let CtlFormula::EX(inner) = reach.as_ref() else {
        panic!("expected EX reach clause");
    };
    let CtlFormula::Atom(StatePredicate::IntLe(left, right)) = inner.as_ref() else {
        panic!("expected integer atom");
    };
    let IntExpr::TokensCount(places) = left else {
        panic!("expected tokens-count");
    };
    assert_eq!(places, &["p0"]);
    let IntExpr::Constant(value) = right else {
        panic!("expected constant");
    };
    assert_eq!(*value, 1);
}

#[test]
fn test_parse_properties_dispatches_ltl_examination_from_file() {
    let tempdir = TempDir::new().expect("tempdir should create");
    write_exam_file(
        &tempdir,
        "LTLCardinality",
        r#"      <all-paths>
        <globally>
          <until>
            <before>
              <negation>
                <is-fireable><transition>t0</transition></is-fireable>
              </negation>
            </before>
            <reach>
              <next>
                <integer-le>
                  <tokens-count><place>p1</place></tokens-count>
                  <integer-constant>2</integer-constant>
                </integer-le>
              </next>
            </reach>
          </until>
        </globally>
      </all-paths>"#,
    );

    let properties =
        parse_properties(tempdir.path(), "LTLCardinality").expect("LTL file should parse");
    assert_eq!(properties.len(), 1);

    let Formula::Ltl(LtlFormula::Globally(inner)) = &properties[0].formula else {
        panic!("expected Globally");
    };
    let LtlFormula::Until(before, reach) = inner.as_ref() else {
        panic!("expected Until");
    };
    let LtlFormula::Not(negated) = before.as_ref() else {
        panic!("expected negated before clause");
    };
    let LtlFormula::Atom(StatePredicate::IsFireable(transitions)) = negated.as_ref() else {
        panic!("expected fireability atom");
    };
    assert_eq!(transitions, &["t0"]);

    let LtlFormula::Next(next_inner) = reach.as_ref() else {
        panic!("expected Next reach clause");
    };
    let LtlFormula::Atom(StatePredicate::IntLe(left, right)) = next_inner.as_ref() else {
        panic!("expected integer atom");
    };
    let IntExpr::TokensCount(places) = left else {
        panic!("expected tokens-count");
    };
    assert_eq!(places, &["p1"]);
    let IntExpr::Constant(value) = right else {
        panic!("expected constant");
    };
    assert_eq!(*value, 2);
}

#[test]
fn test_parse_properties_rejects_ltl_reachability_root() {
    let tempdir = TempDir::new().expect("tempdir should create");
    write_exam_file(
        &tempdir,
        "LTLCardinality",
        r#"      <exists-path>
        <finally>
          <integer-le>
            <tokens-count><place>p0</place></tokens-count>
            <integer-constant>1</integer-constant>
          </integer-le>
        </finally>
      </exists-path>"#,
    );

    let err = parse_properties(tempdir.path(), "LTLCardinality")
        .expect_err("reachability-shaped LTL formula should be rejected");
    assert!(err
        .to_string()
        .contains("LTL formula root must be <all-paths>"));
}

// --- Empty-operand rejection tests for CTL/LTL (#1258) ---

fn try_parse_ctl_root(xml: &str) -> Result<Formula, crate::error::PnmlError> {
    let doc = roxmltree::Document::parse(xml).expect("xml should parse");
    parse_ctl_root_formula(&doc.root_element())
}

fn try_parse_ltl_root(xml: &str) -> Result<Formula, crate::error::PnmlError> {
    let doc = roxmltree::Document::parse(xml).expect("xml should parse");
    parse_ltl_root_formula(&doc.root_element())
}

#[test]
fn test_reject_empty_ctl_conjunction() {
    let err = try_parse_ctl_root(
        r#"<formula>
  <conjunction/>
</formula>"#,
    )
    .expect_err("empty CTL conjunction should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("conjunction"),
        "error should mention conjunction: {msg}"
    );
}

#[test]
fn test_reject_empty_ctl_disjunction() {
    let err = try_parse_ctl_root(
        r#"<formula>
  <disjunction/>
</formula>"#,
    )
    .expect_err("empty CTL disjunction should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("disjunction"),
        "error should mention disjunction: {msg}"
    );
}

#[test]
fn test_reject_empty_ltl_conjunction() {
    let err = try_parse_ltl_root(
        r#"<formula>
  <all-paths>
    <conjunction/>
  </all-paths>
</formula>"#,
    )
    .expect_err("empty LTL conjunction should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("conjunction"),
        "error should mention conjunction: {msg}"
    );
}

#[test]
fn test_reject_empty_ltl_disjunction() {
    let err = try_parse_ltl_root(
        r#"<formula>
  <all-paths>
    <disjunction/>
  </all-paths>
</formula>"#,
    )
    .expect_err("empty LTL disjunction should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("disjunction"),
        "error should mention disjunction: {msg}"
    );
}

// --- Empty property document rejection tests (#1259) ---

#[test]
fn test_reject_empty_ctl_property_document_from_file() {
    let tempdir = TempDir::new().expect("tempdir should create");
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
</property-set>"#;
    fs::write(tempdir.path().join("CTLCardinality.xml"), xml).expect("write should succeed");

    let err = parse_properties(tempdir.path(), "CTLCardinality")
        .expect_err("empty CTL property document should fail");
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
fn test_reject_empty_ltl_property_document_from_file() {
    let tempdir = TempDir::new().expect("tempdir should create");
    let xml = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
</property-set>"#;
    fs::write(tempdir.path().join("LTLFireability.xml"), xml).expect("write should succeed");

    let err = parse_properties(tempdir.path(), "LTLFireability")
        .expect_err("empty LTL property document should fail");
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

// --- Over-arity rejection tests for CTL/LTL (#1260) ---

#[test]
fn test_reject_ctl_negation_with_two_children() {
    let err = try_parse_ctl_root(
        r#"<formula>
  <negation>
    <is-fireable><transition>t1</transition></is-fireable>
    <is-fireable><transition>t2</transition></is-fireable>
  </negation>
</formula>"#,
    )
    .expect_err("CTL negation with two children should fail");
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
fn test_reject_ltl_globally_with_two_children() {
    let err = try_parse_ltl_root(
        r#"<formula>
  <all-paths>
    <globally>
      <is-fireable><transition>t1</transition></is-fireable>
      <is-fireable><transition>t2</transition></is-fireable>
    </globally>
  </all-paths>
</formula>"#,
    )
    .expect_err("LTL globally with two children should fail");
    let msg = err.to_string();
    assert!(
        msg.contains("globally"),
        "error should mention globally: {msg}"
    );
    assert!(
        msg.contains("exactly one"),
        "error should say exactly one: {msg}"
    );
}

#[test]
fn test_reject_ctl_until_duplicate_before() {
    let err = try_parse_ctl_root(
        r#"<formula>
  <all-paths>
    <until>
      <before><is-fireable><transition>t0</transition></is-fireable></before>
      <before><is-fireable><transition>t1</transition></is-fireable></before>
      <reach><is-fireable><transition>t2</transition></is-fireable></reach>
    </until>
  </all-paths>
</formula>"#,
    )
    .expect_err("CTL until with duplicate before should fail");
    let msg = err.to_string();
    assert!(msg.contains("until"), "error should mention until: {msg}");
    assert!(
        msg.contains("<before>"),
        "error should mention <before>: {msg}"
    );
}

#[test]
fn test_reject_ctl_over_arity_from_file() {
    let tempdir = TempDir::new().expect("tempdir should create");
    write_exam_file(
        &tempdir,
        "CTLFireability",
        r#"      <all-paths>
        <globally>
          <is-fireable><transition>t1</transition></is-fireable>
          <is-fireable><transition>t2</transition></is-fireable>
        </globally>
      </all-paths>"#,
    );

    let err = parse_properties(tempdir.path(), "CTLFireability")
        .expect_err("over-arity CTL globally should fail via file entry");
    let msg = err.to_string();
    assert!(
        msg.contains("globally"),
        "error should mention globally: {msg}"
    );
    assert!(
        msg.contains("exactly one"),
        "error should say exactly one: {msg}"
    );
}

#[test]
fn test_reject_ctl_integer_le_over_arity_from_file() {
    let tempdir = TempDir::new().expect("tempdir should create");
    write_exam_file(
        &tempdir,
        "CTLCardinality",
        r#"      <all-paths>
        <until>
          <before>
            <is-fireable><transition>t0</transition></is-fireable>
          </before>
          <reach>
            <exists-path>
              <next>
                <integer-le>
                  <integer-constant>1</integer-constant>
                  <integer-constant>2</integer-constant>
                  <integer-constant>3</integer-constant>
                </integer-le>
              </next>
            </exists-path>
          </reach>
        </until>
      </all-paths>"#,
    );

    let err = parse_properties(tempdir.path(), "CTLCardinality")
        .expect_err("over-arity integer-le should fail via typed file entry");
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
