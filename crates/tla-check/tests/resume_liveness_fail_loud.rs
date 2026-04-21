// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod common;

use tempfile::tempdir;
use tla_check::LivenessCheckError;
use tla_check::{CheckError, CheckResult, Config, LimitType, ModelChecker};

const SPEC_SRC: &str = r#"
---- MODULE ResumeLiveness ----
VARIABLE x
Init == x = 0
Next == x' = x
Live == <> (x = 1)
====
"#;

fn make_config() -> Config {
    Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["Live".to_string()],
        check_deadlock: false,
        ..Default::default()
    }
}

#[derive(Clone, Copy, Debug)]
enum StorageMode {
    FullState,
    FingerprintOnly,
}

impl StorageMode {
    fn store_states(self) -> bool {
        matches!(self, Self::FullState)
    }
}

/// Sanity: a fresh run detects the liveness violation in both storage modes.
fn assert_baseline_detects_violation(
    module: &tla_core::ast::Module,
    config: &Config,
    mode: StorageMode,
) {
    let mut checker = ModelChecker::new(module, config);
    checker.set_store_states(mode.store_states());
    let baseline = checker.check();
    assert!(
        matches!(baseline, CheckResult::LivenessViolation { .. }),
        "expected baseline liveness violation in {mode:?} mode, got: {:?}",
        baseline,
    );
}

/// Create a partial checkpoint stopping after 1 state.
fn create_partial_checkpoint(
    module: &tla_core::ast::Module,
    config: &Config,
    checkpoint_path: &std::path::Path,
    mode: StorageMode,
) {
    let mut checker = ModelChecker::new(module, config);
    checker.set_store_states(mode.store_states());
    checker.set_max_states(1);
    checker.set_checkpoint(
        checkpoint_path.to_path_buf(),
        std::time::Duration::from_secs(0),
    );

    let first = checker.check();
    assert!(
        matches!(
            first,
            CheckResult::LimitReached {
                limit_type: LimitType::States,
                ..
            }
        ),
        "expected checkpointing run to stop at state limit, got: {:?}",
        first
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn resume_rejects_unchecked_liveness_properties() {
    let module = common::parse_module_strict(SPEC_SRC);
    let config = make_config();

    assert_baseline_detects_violation(&module, &config, StorageMode::FullState);

    let checkpoint_dir = tempdir().expect("tempdir");
    let checkpoint_path = checkpoint_dir.path().join("checkpoint");

    create_partial_checkpoint(&module, &config, &checkpoint_path, StorageMode::FullState);

    let mut resumed_checker = ModelChecker::new(&module, &config);
    resumed_checker.set_store_states(StorageMode::FullState.store_states());
    let resumed = resumed_checker
        .check_with_resume(&checkpoint_path)
        .expect("resume should load checkpoint");

    match resumed {
        CheckResult::Error {
            error: CheckError::Liveness(LivenessCheckError::Generic(msg)),
            ..
        } => {
            assert!(
                msg.contains("Temporal properties were NOT checked"),
                "expected explicit unchecked-liveness diagnostic, got: {msg}"
            );
            assert!(
                msg.contains("Live"),
                "expected diagnostic to name skipped property, got: {msg}"
            );
        }
        other => panic!(
            "expected Error(LivenessError) from resumed run, got: {:?}",
            other
        ),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn resume_rejects_unchecked_liveness_properties_in_fingerprint_only_mode() {
    let module = common::parse_module_strict(SPEC_SRC);
    let config = make_config();

    assert_baseline_detects_violation(&module, &config, StorageMode::FingerprintOnly);

    let checkpoint_dir = tempdir().expect("tempdir");
    let checkpoint_path = checkpoint_dir.path().join("checkpoint");

    create_partial_checkpoint(
        &module,
        &config,
        &checkpoint_path,
        StorageMode::FingerprintOnly,
    );

    let mut resumed_checker = ModelChecker::new(&module, &config);
    resumed_checker.set_store_states(StorageMode::FingerprintOnly.store_states());
    let resumed = resumed_checker
        .check_with_resume(&checkpoint_path)
        .expect("resume should load checkpoint");

    match resumed {
        CheckResult::Error {
            error: CheckError::Liveness(LivenessCheckError::Generic(msg)),
            ..
        } => {
            assert!(
                msg.contains("Temporal properties were NOT checked"),
                "expected explicit unchecked-liveness diagnostic, got: {msg}"
            );
            assert!(
                msg.contains("full-state or fingerprint-only mode"),
                "expected diagnostic to mention both unsupported resume modes, got: {msg}"
            );
            assert!(
                msg.contains("Live"),
                "expected diagnostic to name skipped property, got: {msg}"
            );
        }
        other => panic!(
            "expected Error(LivenessError) from resumed fp-only run, got: {:?}",
            other
        ),
    }
}
