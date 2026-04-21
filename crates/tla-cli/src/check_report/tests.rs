// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for check_report module.

use std::ffi::OsString;
use std::process::Command;
use std::sync::{LazyLock, Mutex, MutexGuard};
use std::time::Duration;

use tla_check::{
    CheckResult, CheckStats, PropertyViolationKind, State, StorageStats, Trace, Value,
};

use super::storage_stats_lines;
use super::trace_format::{
    build_liveness_trace_difftrace, build_liveness_trace_text, format_trace_difftrace,
    property_violation_presentation,
};
use crate::tlc_codes;

static ENV_LOCK: LazyLock<Mutex<()>> = LazyLock::new(|| Mutex::new(()));

fn env_lock() -> MutexGuard<'static, ()> {
    ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

struct EnvVarGuard {
    key: &'static str,
    prev: Option<OsString>,
    _lock: MutexGuard<'static, ()>,
}

impl EnvVarGuard {
    fn remove(key: &'static str) -> Self {
        let lock = env_lock();
        let prev = std::env::var_os(key);
        std::env::remove_var(key);
        Self {
            key,
            prev,
            _lock: lock,
        }
    }

    fn set(key: &'static str, value: &'static str) -> Self {
        let lock = env_lock();
        let prev = std::env::var_os(key);
        std::env::set_var(key, value);
        Self {
            key,
            prev,
            _lock: lock,
        }
    }
}

impl Drop for EnvVarGuard {
    fn drop(&mut self) {
        match self.prev.take() {
            Some(value) => std::env::set_var(self.key, value),
            None => std::env::remove_var(self.key),
        }
    }
}

fn run_report_check_human_case(case: &str) -> std::process::Output {
    let exe = std::env::current_exe().expect("current test binary");
    Command::new(exe)
        .arg("--nocapture")
        .arg("--exact")
        .arg("check_report::tests::test_report_check_human_capture_helper")
        .env("TLA2_CHECK_REPORT_CAPTURE_CASE", case)
        .env("TLA2_BYTECODE_VM_STATS", "1")
        .output()
        .expect("capture helper should run")
}

fn state_with_x(x: i64) -> State {
    State::from_pairs(vec![("x", Value::SmallInt(x))])
}

fn check_stats(states_found: usize, initial_states: usize) -> CheckStats {
    let mut stats = CheckStats::default();
    stats.states_found = states_found;
    stats.initial_states = initial_states;
    stats
}

#[test]
fn test_format_bytecode_vm_stats_line_uses_grouped_counts() {
    let line = super::format_bytecode_vm_stats_line((1_234, 56, 12));
    assert_eq!(
        line,
        "Bytecode VM: 1,234 executions, 56 fallbacks, 12 compile failures"
    );
}

#[test]
fn test_bytecode_vm_stats_line_respects_env_gate() {
    tla_check::eval::clear_for_test_reset();

    {
        let _guard = EnvVarGuard::remove("TLA2_BYTECODE_VM_STATS");
        assert_eq!(super::bytecode_vm_stats_line(), None);
    }

    {
        let _guard = EnvVarGuard::set("TLA2_BYTECODE_VM_STATS", "1");
        assert_eq!(
            super::bytecode_vm_stats_line(),
            Some("Bytecode VM: 0 executions, 0 fallbacks, 0 compile failures".to_string())
        );
    }
}

#[test]
fn test_report_check_human_success_emits_bytecode_vm_stats_to_stdout() {
    let output = run_report_check_human_case("success");
    assert!(
        output.status.success(),
        "capture helper failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("Bytecode VM: 0 executions, 0 fallbacks, 0 compile failures"),
        "expected Bytecode VM stats line in success report stdout, got:\n{stdout}"
    );
}

#[test]
fn test_report_check_human_invariant_violation_emits_bytecode_vm_stats_to_stderr() {
    let output = run_report_check_human_case("invariant");
    assert!(
        output.status.success(),
        "capture helper failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Error: Invariant TypeOK is violated."),
        "expected invariant violation header in stderr, got:\n{stderr}"
    );
    assert!(
        stderr.contains("Bytecode VM: 0 executions, 0 fallbacks, 0 compile failures"),
        "expected Bytecode VM stats line in violation report stderr, got:\n{stderr}"
    );
}

#[test]
fn test_report_check_human_capture_helper() {
    let Ok(case) = std::env::var("TLA2_CHECK_REPORT_CAPTURE_CASE") else {
        return;
    };

    tla_check::eval::clear_for_test_reset();

    match case.as_str() {
        "success" => {
            super::report_check_human(
                CheckResult::Success(check_stats(1, 1)),
                Duration::from_secs(1),
                0,
                0,
                crate::cli_schema::TraceFormat::Text,
                false,
                false,
            )
            .expect("success report should not error");
        }
        "invariant" => {
            let report = super::report_check_human(
                CheckResult::InvariantViolation {
                    invariant: "TypeOK".to_string(),
                    trace: Trace::from_states(vec![]),
                    stats: check_stats(2, 1),
                },
                Duration::from_secs(1),
                0,
                0,
                crate::cli_schema::TraceFormat::Text,
                false,
                false,
            );
            assert!(
                report.is_err(),
                "invariant violations should return an error"
            );
        }
        other => panic!("unknown capture case: {other}"),
    }
}

#[test]
fn test_stuttering_cycle_emits_stuttering_marker() {
    // Cycle with identical states → "Stuttering" annotation.
    let s0 = state_with_x(0);
    let s1 = state_with_x(1);
    let s2 = state_with_x(2);
    let prefix = Trace::from_states(vec![s0, s1]);
    // Cycle: two copies of x=2 (same fingerprint).
    let cycle = Trace::from_states(vec![s2.clone(), s2]);

    let text = build_liveness_trace_text(&prefix, &cycle);
    assert!(
        text.contains("Stuttering"),
        "expected 'Stuttering' marker in output:\n{text}"
    );
    // TLC format: "State N: Stuttering".
    assert!(
        text.contains("State 4: Stuttering"),
        "expected 'State 4: Stuttering' in output:\n{text}"
    );
    // The x=2 state should appear once, not twice.
    let x2_count = text.matches("x = 2").count();
    assert_eq!(x2_count, 1, "x=2 should appear once, got {x2_count}");
}

#[test]
fn test_back_to_state_cycle_emits_back_marker() {
    // Cycle closes by returning to its first state → "Back to state N: <label>".
    let s0 = state_with_x(0);
    let s1 = state_with_x(1);
    // Cycle: [x=0, x=1, x=0] — last matches first.
    let prefix = Trace::from_states(vec![]);
    let cycle = Trace::from_states(vec![s0.clone(), s1, s0]);

    let text = build_liveness_trace_text(&prefix, &cycle);
    assert!(
        text.contains("Back to state 1:"),
        "expected 'Back to state 1:' in output:\n{text}"
    );
    // x=0 should appear once (as state 1), not twice.
    let x0_count = text.matches("x = 0").count();
    assert_eq!(x0_count, 1, "x=0 should appear once, got {x0_count}");
}

#[test]
fn test_normal_cycle_no_special_markers() {
    // Cycle with distinct states → no stuttering or back-to-state.
    let s0 = state_with_x(0);
    let s1 = state_with_x(1);
    let s2 = state_with_x(2);
    let prefix = Trace::from_states(vec![s0]);
    let cycle = Trace::from_states(vec![s1, s2]);

    let text = build_liveness_trace_text(&prefix, &cycle);
    assert!(
        !text.contains("Stuttering"),
        "unexpected Stuttering in:\n{text}"
    );
    assert!(
        !text.contains("Back to state"),
        "unexpected Back to state in:\n{text}"
    );
    // All three states should appear (TLC format: "State N: <label>").
    assert!(text.contains("State 1: "), "missing state 1");
    assert!(text.contains("State 2: "), "missing state 2");
    assert!(text.contains("State 3: "), "missing state 3");
}

#[test]
fn test_prefix_with_back_to_state_cycle() {
    // Prefix + cycle with back-edge. State numbering is sequential.
    let s0 = state_with_x(0);
    let s1 = state_with_x(1);
    let s2 = state_with_x(2);
    let prefix = Trace::from_states(vec![s0]);
    // Cycle: [x=1, x=2, x=1] — back to cycle start.
    let cycle = Trace::from_states(vec![s1.clone(), s2, s1]);

    let text = build_liveness_trace_text(&prefix, &cycle);
    // Prefix is state 1, cycle starts at state 2.
    assert!(
        text.contains("Back to state 2:"),
        "expected 'Back to state 2:' in output:\n{text}"
    );
    assert!(text.contains("State 1: "), "missing state 1 (prefix)");
    assert!(text.contains("State 2: "), "missing state 2 (cycle start)");
    assert!(text.contains("State 3: "), "missing state 3 (cycle middle)");
}

#[test]
fn test_prefix_cycle_overlap_folds_duplicate() {
    // When last prefix state == first cycle state, TLC folds them.
    // Prefix: [x=0], Cycle: [x=0, x=1, x=0]
    // Expected: 1: x=0, 2: x=1, Back to state 1
    let s0 = state_with_x(0);
    let s1 = state_with_x(1);
    let prefix = Trace::from_states(vec![s0.clone()]);
    let cycle = Trace::from_states(vec![s0.clone(), s1, s0]);

    let text = build_liveness_trace_text(&prefix, &cycle);
    assert!(
        text.contains("Back to state 1:"),
        "expected 'Back to state 1:' in output:\n{text}"
    );
    // Only 2 numbered states (x=0 from prefix, x=1 from cycle).
    assert!(text.contains("State 1: "), "missing state 1");
    assert!(text.contains("State 2: "), "missing state 2");
    assert!(
        !text.contains("State 3: "),
        "unexpected state 3 — overlap should fold duplicate:\n{text}"
    );
    // x=0 appears only once (the prefix state covers the cycle entry).
    let x0_count = text.matches("x = 0").count();
    assert_eq!(
        x0_count, 1,
        "x=0 should appear once (folded), got {x0_count}:\n{text}"
    );
}

#[test]
fn test_prefix_cycle_overlap_stuttering() {
    // Prefix: [x=0, x=1], Cycle: [x=1, x=1] — last prefix == first cycle.
    // The cycle is all-same after skipping the overlapping entry.
    // Expected: 1: x=0, 2: x=1, 3: Stuttering
    let s0 = state_with_x(0);
    let s1 = state_with_x(1);
    let prefix = Trace::from_states(vec![s0, s1.clone()]);
    let cycle = Trace::from_states(vec![s1.clone(), s1]);

    let text = build_liveness_trace_text(&prefix, &cycle);
    assert!(
        text.contains("Stuttering"),
        "expected 'Stuttering' in output:\n{text}"
    );
    assert!(
        text.contains("State 3: Stuttering"),
        "expected 'State 3: Stuttering' in output:\n{text}"
    );
    // x=1 appears once (the prefix state, not duplicated by cycle).
    let x1_count = text.matches("x = 1").count();
    assert_eq!(
        x1_count, 1,
        "x=1 should appear once (folded), got {x1_count}:\n{text}"
    );
}

#[test]
fn test_liveness_trace_uses_tlc_var_format() {
    // Verify that liveness traces use /\ var = value format (not 2-space indent).
    let s0 = State::from_pairs(vec![("x", Value::SmallInt(0)), ("y", Value::SmallInt(1))]);
    let s1 = State::from_pairs(vec![("x", Value::SmallInt(1)), ("y", Value::SmallInt(0))]);
    let prefix = Trace::from_states(vec![s0]);
    let cycle = Trace::from_states(vec![s1]);

    let text = build_liveness_trace_text(&prefix, &cycle);
    assert!(
        text.contains("/\\ x = "),
        "expected '/\\ x = ' TLC format in output:\n{text}"
    );
    assert!(
        text.contains("/\\ y = "),
        "expected '/\\ y = ' TLC format in output:\n{text}"
    );
    // Should NOT contain old "  x = " format.
    assert!(
        !text.contains("  x = "),
        "unexpected 2-space indent format in output:\n{text}"
    );
}

// -----------------------------------------------------------------------
// --difftrace tests (Part of #2470 Step 5)
// -----------------------------------------------------------------------

fn state_xy(x: i64, y: i64) -> State {
    State::from_pairs(vec![("x", Value::SmallInt(x)), ("y", Value::SmallInt(y))])
}

#[test]
fn test_difftrace_first_state_shows_all_vars() {
    let trace = Trace::from_states(vec![state_xy(0, 1), state_xy(1, 1)]);
    let text = format_trace_difftrace(&trace);
    // First state must show both variables.
    assert!(text.contains("/\\ x = 0"), "first state missing x:\n{text}");
    assert!(text.contains("/\\ y = 1"), "first state missing y:\n{text}");
}

#[test]
fn test_difftrace_subsequent_state_shows_only_changed() {
    // Use 3 states so state 2 is an intermediate (not last) state.
    // The last state always shows all vars per TLC behavior.
    let trace = Trace::from_states(vec![
        state_xy(0, 1),
        state_xy(1, 1), // only x changed
        state_xy(2, 1), // last state — will show all vars
    ]);
    let text = format_trace_difftrace(&trace);
    // Second state (intermediate): only x changed (0→1), y stayed the same.
    let lines: Vec<&str> = text.lines().collect();
    let state2_start = lines
        .iter()
        .position(|l| l.starts_with("State 2:"))
        .unwrap();
    let state3_start = lines
        .iter()
        .position(|l| l.starts_with("State 3:"))
        .unwrap();
    let state2_vars = &lines[state2_start + 1..state3_start];
    assert_eq!(
        state2_vars[0], "x = 1",
        "difftrace should show only changed var:\n{text}"
    );
    // Should not have a y line in state 2 region.
    assert!(
        !state2_vars.iter().any(|l| l.contains("y =")),
        "difftrace should omit unchanged var y:\n{text}"
    );
}

#[test]
fn test_difftrace_multiple_changes() {
    let trace = Trace::from_states(vec![state_xy(0, 0), state_xy(1, 2)]);
    let text = format_trace_difftrace(&trace);
    // Both vars changed — should show both with /\ prefix.
    let lines: Vec<&str> = text.lines().collect();
    let state2_start = lines
        .iter()
        .position(|l| l.starts_with("State 2:"))
        .unwrap();
    let state2_lines = &lines[state2_start + 1..];
    assert!(
        state2_lines.iter().any(|l| l == &"/\\ x = 1"),
        "difftrace should show changed x:\n{text}"
    );
    assert!(
        state2_lines.iter().any(|l| l == &"/\\ y = 2"),
        "difftrace should show changed y:\n{text}"
    );
}

#[test]
fn test_difftrace_no_changes_emits_empty() {
    // If an intermediate state is identical to previous, no variable lines are emitted
    // (TLC behavior). Use 3 states so state 2 is intermediate, not last.
    // The last state always shows all vars per TLC behavior.
    let s = state_xy(0, 1);
    let trace = Trace::from_states(vec![s.clone(), s.clone(), state_xy(1, 1)]);
    let text = format_trace_difftrace(&trace);
    let lines: Vec<&str> = text.lines().collect();
    let state2_start = lines
        .iter()
        .position(|l| l.starts_with("State 2:"))
        .unwrap();
    let state3_start = lines
        .iter()
        .position(|l| l.starts_with("State 3:"))
        .unwrap();
    // After "2: <Action>", before "3:", there should be no var lines.
    let state2_region = &lines[state2_start + 1..state3_start];
    assert!(
        state2_region.is_empty() || state2_region.iter().all(|l| l.is_empty()),
        "difftrace should emit no vars when nothing changed:\n{text}"
    );
}

#[test]
fn test_difftrace_last_state_shows_all_vars() {
    // TLC always shows all variables on the last (violating) state in difftrace mode,
    // so users can see the complete state that caused the invariant violation.
    // Verified against TLC 2.20 with DifftraceTest.tla (6 variables).
    let trace = Trace::from_states(vec![
        state_xy(0, 1),
        state_xy(1, 1), // only x changed
        state_xy(2, 1), // only x changed — but this is the last (violating) state
    ]);
    let text = format_trace_difftrace(&trace);
    let lines: Vec<&str> = text.lines().collect();
    // State 2 (intermediate): should show only x (diff behavior).
    let state2_start = lines
        .iter()
        .position(|l| l.starts_with("State 2:"))
        .unwrap();
    assert_eq!(
        lines[state2_start + 1],
        "x = 1",
        "intermediate state should show only changed var:\n{text}"
    );
    // State 3 (last/violating): should show ALL variables, not just changed ones.
    let state3_start = lines
        .iter()
        .position(|l| l.starts_with("State 3:"))
        .unwrap();
    let state3_lines: Vec<&str> = lines[state3_start + 1..].to_vec();
    assert!(
        state3_lines.iter().any(|l| l.contains("x = 2")),
        "last state should show x:\n{text}"
    );
    assert!(
        state3_lines.iter().any(|l| l.contains("y = 1")),
        "last state should show y (even though unchanged):\n{text}"
    );
}

#[test]
fn test_liveness_difftrace_shows_diffs() {
    let prefix = Trace::from_states(vec![state_xy(0, 0), state_xy(1, 0)]);
    let s_cycle1 = state_xy(1, 1);
    let s_cycle2 = state_xy(1, 0); // same as prefix end for back-to-state
    let cycle = Trace::from_states(vec![s_cycle1, s_cycle2]);
    let text = build_liveness_trace_difftrace(&prefix, &cycle);
    // State 1 (initial): both vars shown.
    assert!(
        text.contains("/\\ x = 0"),
        "initial state should show all vars:\n{text}"
    );
    // State 2: only x changed (0→1).
    let lines: Vec<&str> = text.lines().collect();
    let state2_start = lines
        .iter()
        .position(|l| l.starts_with("State 2:"))
        .unwrap();
    assert_eq!(
        lines[state2_start + 1],
        "x = 1",
        "state 2 should show only x change:\n{text}"
    );
}

#[test]
fn test_storage_stats_lines_include_memory_only_stats() {
    let mut stats = StorageStats::default();
    stats.memory_count = 3;
    stats.memory_bytes = 8 * 1024 * 1024;

    let lines =
        storage_stats_lines(&stats).expect("mmap-style reserved memory should be reportable");

    assert!(lines.iter().any(|line| line == "Storage:"));
    assert!(lines.iter().any(|line| line == "  Memory states: 3"));
    assert!(lines.iter().any(|line| line == "  Disk states: 0"));
    assert!(lines.iter().any(|line| line == "  Memory reserved: 8.0 MB"));
    assert!(!lines.iter().any(|line| line.contains("Disk lookups:")));
    assert!(!lines.iter().any(|line| line.contains("Evictions:")));
}

#[test]
fn test_property_violation_presentation_state_level_uses_invariant_format() {
    let presentation = property_violation_presentation("AC1", PropertyViolationKind::StateLevel);

    assert_eq!(
        presentation.tlc_code,
        tlc_codes::ec::TLC_INVARIANT_VIOLATED_BEHAVIOR
    );
    assert_eq!(presentation.headline, "Invariant AC1 is violated.");
    assert_eq!(
        presentation.trace_intro,
        "The behavior up to this point is:"
    );
}

#[test]
fn test_property_violation_presentation_action_level_keeps_action_format() {
    let presentation = property_violation_presentation("Next", PropertyViolationKind::ActionLevel);

    assert_eq!(
        presentation.tlc_code,
        tlc_codes::ec::TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR
    );
    assert_eq!(presentation.headline, "Action property Next is violated.");
    assert_eq!(
        presentation.trace_intro,
        "The behavior up to this point is:"
    );
}
