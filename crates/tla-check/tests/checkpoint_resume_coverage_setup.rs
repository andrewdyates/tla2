// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod common;

use tempfile::tempdir;
use tla_check::{CheckResult, Config, LimitType, ModelChecker};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn checkpoint_resume_initializes_coverage_setup() {
    let spec = r#"
---- MODULE ResumeCoverage ----
VARIABLES x, y
Init == x = 0 /\ y = 0
IncX == x < 2 /\ x' = x + 1 /\ y' = y
IncY == y < 2 /\ x' = x /\ y' = y + 1
Next == IncX \/ IncY
TypeOK == x \in 0..2 /\ y \in 0..2
====
"#;

    let module = common::parse_module_strict(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let checkpoint_dir = tempdir().expect("tempdir");
    let checkpoint_path = checkpoint_dir.path().join("checkpoint");

    {
        let mut checker = ModelChecker::new(&module, &config);
        checker.set_collect_coverage(true);
        checker.set_max_states(3);
        checker.set_checkpoint(checkpoint_path.clone(), std::time::Duration::from_secs(0));

        let result = checker.check();
        assert!(
            matches!(
                result,
                CheckResult::LimitReached {
                    limit_type: LimitType::States,
                    ..
                }
            ),
            "expected first run to stop at max state limit, got: {:?}",
            result
        );
    }

    let mut resumed_checker = ModelChecker::new(&module, &config);
    resumed_checker.set_collect_coverage(true);
    let resumed = resumed_checker
        .check_with_resume(&checkpoint_path)
        .expect("resume should load checkpoint");

    let stats = match resumed {
        CheckResult::Success(stats) => stats,
        other => panic!("expected resume run success, got: {:?}", other),
    };

    assert_eq!(
        stats.detected_actions,
        vec!["IncX".to_string(), "IncY".to_string()],
        "resume path should detect and retain action names from Next"
    );

    let coverage = stats
        .coverage
        .as_ref()
        .expect("coverage stats should be initialized for resumed runs");

    let ordered_names: Vec<String> = coverage
        .action_order
        .iter()
        .map(|id| {
            coverage
                .actions
                .get(id)
                .expect("registered coverage action should exist")
                .name
                .clone()
        })
        .collect();
    assert_eq!(
        ordered_names,
        vec!["IncX".to_string(), "IncY".to_string()],
        "coverage action order should match detected Next disjuncts after resume"
    );
}
