// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fs;

use tempfile::tempdir;

use super::super::{collect_examination_with_dir, Examination, ExaminationValue};
use super::fixtures::counting_net;
use crate::explorer::{CheckpointConfig, ExplorationConfig};
use crate::output::Verdict;

const REACHABILITY_CARDINALITY_XML: &str = r#"<?xml version="1.0"?>
<property-set xmlns="http://mcc.lip6.fr/">
  <property>
    <id>TestModel-ReachabilityCardinality-00</id>
    <formula>
      <all-paths>
        <globally>
          <disjunction>
            <is-fireable><transition>T0</transition></is-fireable>
            <integer-le>
              <integer-constant>3</integer-constant>
              <tokens-count><place>P1</place></tokens-count>
            </integer-le>
          </disjunction>
        </globally>
      </all-paths>
    </formula>
  </property>
</property-set>"#;

#[test]
fn collect_examination_reachability_can_resume_from_checkpoint() {
    let net = counting_net();
    let tempdir = tempdir().expect("tempdir");
    let checkpoint_dir = tempdir.path().join("reachability-checkpoint");
    fs::write(
        tempdir.path().join("ReachabilityCardinality.xml"),
        REACHABILITY_CARDINALITY_XML,
    )
    .expect("write ReachabilityCardinality.xml");

    let interrupted_config = ExplorationConfig::new(100).with_checkpoint(
        CheckpointConfig::new(checkpoint_dir.clone(), 1).with_stop_after_first_save(true),
    );
    let interrupted = collect_examination_with_dir(
        &net,
        "TestModel",
        tempdir.path(),
        Examination::ReachabilityCardinality,
        &interrupted_config,
    )
    .expect("interrupted reachability collection should succeed");
    assert_eq!(interrupted.len(), 1);
    assert_eq!(
        interrupted[0].value,
        ExaminationValue::Verdict(Verdict::CannotCompute)
    );

    let resume_config = ExplorationConfig::new(100)
        .with_checkpoint(CheckpointConfig::new(checkpoint_dir, 1).with_resume(true));
    let resumed = collect_examination_with_dir(
        &net,
        "TestModel",
        tempdir.path(),
        Examination::ReachabilityCardinality,
        &resume_config,
    )
    .expect("resumed reachability collection should succeed");

    let fresh = collect_examination_with_dir(
        &net,
        "TestModel",
        tempdir.path(),
        Examination::ReachabilityCardinality,
        &ExplorationConfig::new(100),
    )
    .expect("fresh reachability collection should succeed");

    assert_eq!(resumed, fresh);
    assert_eq!(fresh.len(), 1);
    assert_eq!(fresh[0].value, ExaminationValue::Verdict(Verdict::True));
}
