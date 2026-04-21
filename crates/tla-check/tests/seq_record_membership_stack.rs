// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for stack overflow risk in `Seq(record)` membership checks.
//!
//! Part of #758: Evaluating kafka2_core-style type invariants can recurse deeply enough to
//! overflow constrained per-thread stacks (e.g. tests, embedded callers, worker threads).
//!
//! This test runs the checker in a subprocess so a stack overflow (which aborts the process)
//! becomes a clean test failure rather than hard-aborting the whole suite.

mod common;

use ntest::timeout;
use std::process::Command;
use tla_check::{CheckResult, Config, ModelChecker};

const CHILD_ENV: &str = "TLA2_SEQ_RECORD_MEMBERSHIP_CHILD";
const CHILD_SENTINEL: &str = "SEQ_RECORD_MEMBERSHIP_CHILD_RAN";

#[cfg_attr(test, timeout(10000))]
#[test]
fn seq_record_membership_child() {
    if std::env::var_os(CHILD_ENV).is_none() {
        return;
    }

    eprintln!("{CHILD_SENTINEL}");

    let stack_size = std::env::var("TLA2_SEQ_RECORD_MEMBERSHIP_STACK_SIZE_BYTES")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(1024 * 1024);

    let spec = r#"
---- MODULE Kafka2TypeInvariantRepro ----
EXTENDS Naturals, Sequences

MessageType == [key: Seq(Nat) \cup {<<>>}]

Keys == {<<>>, <<0>>, <<0, 1>>}

VARIABLE msgs

Init == msgs = << [key |-> <<>>] >>

Next ==
    \E k \in Keys:
        msgs' = << [key |-> k] >>

TypeInvariant == msgs \in Seq(MessageType)

====
"#;

    let result = std::thread::Builder::new()
        .name("seq_record_membership_child".to_string())
        .stack_size(stack_size)
        .spawn(move || {
            let module = common::parse_module(spec);
            let config = Config {
                init: Some("Init".to_string()),
                next: Some("Next".to_string()),
                invariants: vec!["TypeInvariant".to_string()],
                ..Default::default()
            };
            let mut checker = ModelChecker::new_with_extends(&module, &[], &config);
            checker.check()
        })
        .expect("failed to spawn child thread")
        .join();

    match result {
        Ok(check_result) => match check_result {
            CheckResult::Success(stats) => {
                assert_eq!(
                    stats.states_found, 3,
                    "Kafka2TypeInvariantRepro: expected 3 distinct states (one per key), got {}",
                    stats.states_found
                );
                assert_eq!(
                    stats.transitions, 9,
                    "Kafka2TypeInvariantRepro: expected 9 transitions (3 states * 3 successors), got {}",
                    stats.transitions
                );
            }
            CheckResult::InvariantViolation { invariant, .. } => {
                panic!(
                    "bug regression: invariant {invariant} violated (should hold for all reachable states)"
                );
            }
            other => panic!("unexpected result: {other:?}"),
        },
        Err(panic_payload) => std::panic::resume_unwind(panic_payload),
    }
}

#[cfg_attr(test, timeout(10000))]
#[test]
fn seq_record_membership_does_not_abort_on_small_stack() {
    let exe = std::env::current_exe().expect("current_exe");
    let output = Command::new(exe)
        .env(CHILD_ENV, "1")
        .env(
            "TLA2_SEQ_RECORD_MEMBERSHIP_STACK_SIZE_BYTES",
            (1024 * 1024).to_string(),
        )
        .arg("--exact")
        .arg("seq_record_membership_child")
        .arg("--nocapture")
        .output()
        .expect("failed to spawn child process");

    assert!(
        output.status.success(),
        "child process failed (status={:?})\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stdout.contains(CHILD_SENTINEL) || stderr.contains(CHILD_SENTINEL),
        "child process succeeded but did not run the expected child test.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
