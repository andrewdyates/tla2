// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// CTL checker test hub — themed test modules live under checker_tests/.
// Explicit #[path] attributes required because this file is loaded via
// #[path = "checker_tests.rs"] from checker.rs, which changes Rust's
// default module resolution directory.

#[path = "checker_tests/fixpoint_semantics.rs"]
mod fixpoint_semantics;
#[path = "checker_tests/mcc_deep_trace.rs"]
mod mcc_deep_trace;
#[path = "checker_tests/mcc_reachability_validation.rs"]
mod mcc_reachability_validation;
#[path = "checker_tests/mcc_trace_diagnostics.rs"]
mod mcc_trace_diagnostics;
#[path = "checker_tests/naive_crosscheck.rs"]
mod naive_crosscheck;
#[path = "checker_tests/naive_eval.rs"]
mod naive_eval;
#[path = "checker_tests/performance.rs"]
mod performance;
#[path = "checker_tests/support.rs"]
mod support;
