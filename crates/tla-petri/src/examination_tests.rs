// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for MCC examination observers and output formatting.

#[path = "examination_tests/deadlock_one_safe_state_space.rs"]
mod deadlock_one_safe_state_space;
#[path = "examination_tests/fixtures.rs"]
mod fixtures;
#[path = "examination_tests/ibm5964_stable_marking_tests.rs"]
mod ibm5964_stable_marking_tests;
#[path = "examination_tests/one_safe_colored_tests.rs"]
mod one_safe_colored;
#[path = "examination_tests/one_safe_por.rs"]
mod one_safe_por;
#[path = "examination_tests/output_and_enum.rs"]
mod output_and_enum;
#[path = "examination_tests/property_budget_dispatch.rs"]
mod property_budget_dispatch;
#[path = "examination_tests/quasi_liveness.rs"]
mod quasi_liveness;
#[path = "examination_tests/reachability_checkpoint.rs"]
mod reachability_checkpoint;
#[path = "examination_tests/reduction_dispatch.rs"]
mod reduction_dispatch;
#[path = "examination_tests/reduction_property_dispatch.rs"]
mod reduction_property_dispatch;
#[path = "examination_tests/restore_self_loops_tests.rs"]
mod restore_self_loops_tests;
#[path = "examination_tests/stable_marking.rs"]
mod stable_marking;
