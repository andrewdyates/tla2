// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration test proving `CheckResult::stats()` is callable from outside the crate.

use tla_check::{CheckResult, CheckStats};

#[test]
fn checkresult_stats_public_accessor_exposes_stats() {
    let mut stats = CheckStats::default();
    stats.states_found = 42;
    stats.initial_states = 1;
    let result = CheckResult::Success(stats);
    let borrowed = result.stats();
    assert_eq!(borrowed.states_found, 42);
    assert_eq!(borrowed.initial_states, 1);
}
