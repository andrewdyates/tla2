// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::test_support::parse_module;

mod checkpoint_lifecycle;
mod checkpoint_resume_regressions;
mod terminal_states;
mod trace_modes;

/// Build a standard Init/Next config with optional invariants.
fn init_next_config(invariants: &[&str]) -> Config {
    Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: invariants.iter().map(|s| (*s).to_string()).collect(),
        ..Default::default()
    }
}

/// Run a model check stopping after `max_states` and saving a checkpoint.
fn save_checkpoint_stopping_at(
    module: &tla_core::ast::Module,
    config: &Config,
    checkpoint_path: &std::path::Path,
    max_states: usize,
) {
    let mut checker = ModelChecker::new(module, config);
    checker.set_deadlock_check(false);
    checker.set_max_states(max_states);
    checker.set_checkpoint(
        checkpoint_path.to_path_buf(),
        std::time::Duration::from_secs(0),
    );
    let result = checker.check();
    assert!(
        matches!(
            result,
            CheckResult::LimitReached {
                limit_type: LimitType::States,
                ..
            }
        ),
        "Expected LimitReached to trigger checkpoint, got {:?}",
        result
    );
}
