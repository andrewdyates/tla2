// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![cfg(feature = "llvm2")]

mod common;

use std::path::PathBuf;
use std::time::Duration;

const TIMEOUT: Duration = Duration::from_secs(60);

fn external_mcl() -> Option<(PathBuf, PathBuf)> {
    let mut roots = Vec::new();
    if let Some(root) = std::env::var_os("TLAPLUS_EXAMPLES") {
        roots.push(PathBuf::from(root));
    }
    if let Some(home) = std::env::var_os("HOME") {
        roots.push(PathBuf::from(home).join("tlaplus-examples/specifications"));
    }

    for root in roots {
        for base in [&root, &root.join("specifications")] {
            let tla = base.join("lamport_mutex/MCLamportMutex.tla");
            let cfg = base.join("lamport_mutex/MCLamportMutex.cfg");
            if tla.is_file() && cfg.is_file() {
                return Some((tla, cfg));
            }
        }
    }
    None
}

fn skip_missing_external_mcl() -> Option<(PathBuf, PathBuf)> {
    let spec = external_mcl();
    if spec.is_none() {
        eprintln!(
            "skipping external MCLamportMutex native test: TLAPLUS_EXAMPLES/lamport_mutex or ~/tlaplus-examples/specifications/lamport_mutex missing"
        );
    }
    spec
}

fn mcl_args<'a>(tla: &'a str, cfg: &'a str) -> [&'a str; 11] {
    [
        "check",
        tla,
        "--config",
        cfg,
        "--workers",
        "1",
        "--force",
        "--max-depth",
        "1",
        "--backend",
        "llvm2",
    ]
}

fn base_native_env() -> Vec<(&'static str, &'static str)> {
    vec![
        ("TLA2_AUTO_POR", "0"),
        ("TLA2_BYTECODE_VM", "1"),
        ("TLA2_COMPILED_BFS", "1"),
        ("TLA2_FLAT_BFS", "1"),
        ("TLA2_LLVM2", "1"),
        ("TLA2_LLVM2_BFS", "1"),
        ("TLA2_LLVM2_EXISTS", "1"),
        ("TLA2_SKIP_LIVENESS", "1"),
        ("TLA2_DISABLE_ARTIFACT_CACHE", "1"),
        ("TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST", "strict"),
        ("TLA2_LLVM2_NATIVE_FUSED_STRICT", "1"),
        ("TLA2_LLVM2_DISABLE_POST_RA_OPT", "0"),
        ("TLA2_LLVM2_NATIVE_FUSED_DISABLE_LOCAL_DEDUP", "1"),
    ]
}

fn env_remove() -> &'static [&'static str] {
    &[
        "TLA2_NO_COMPILED_BFS",
        "TLA2_NO_FLAT_BFS",
        "TLA2_LLVM2_ENTRY_COUNTER_GATE",
        "TLA2_LLVM2_NATIVE_CALLOUT_SELFTEST_FAIL_CLOSED",
        "TLA2_LLVM2_NATIVE_FUSED_ENABLE_LOCAL_DEDUP",
    ]
}

fn run_external_mcl(
    callout_opt: &'static str,
    parent_loop_opt: &'static str,
) -> Option<(i32, String, String)> {
    let (tla, cfg) = skip_missing_external_mcl()?;
    let tla = tla.to_string_lossy().into_owned();
    let cfg = cfg.to_string_lossy().into_owned();
    let args = mcl_args(&tla, &cfg);
    let mut env = base_native_env();
    env.push(("TLA2_LLVM2_NATIVE_CALLOUT_OPT_LEVEL", callout_opt));
    env.push((
        "TLA2_LLVM2_NATIVE_FUSED_PARENT_LOOP_OPT_LEVEL",
        parent_loop_opt,
    ));

    Some(common::run_tla_parsed_with_env_timeout(
        &args,
        &env,
        env_remove(),
        TIMEOUT,
    ))
}

fn assert_success(code: i32, stdout: &str, stderr: &str, label: &str) {
    assert_eq!(
        code, 0,
        "{label} failed with exit code {code}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

fn assert_callout_selftest(stdout: &str, stderr: &str) {
    assert!(
        stdout.contains("Mode: sequential (1 worker)"),
        "expected sequential CLI mode\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("Max depth: 1"),
        "expected bounded depth output\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("SPECIFICATION: Spec (resolved to INIT: Init, NEXT: Next)"),
        "expected SPECIFICATION resolution output\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stdout.contains("INVARIANTS: TypeOK, BoundedNetwork, Mutex"),
        "expected MCL invariant list\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("[llvm2] compiled next-state for action 'Request__1_1'"),
        "expected Request__1_1 native action compile\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("[flat_state] inferred layout: 5 vars, 89 total slots"),
        "expected promoted 89-slot MCL flat layout\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("[llvm2-selftest] running native fused callout selftest on first real parent: state_len=89, actions=27, state_constraints=1, invariants=3, fail_closed=true"),
        "expected first-parent native callout selftest\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("name=Request__1_1 status=Ok"),
        "expected Request__1_1 standalone native callout to return Ok\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("[llvm2-selftest] native fused callout selftest complete"),
        "expected native callout selftest completion\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
fn external_mcl_request_1_1_callout_selftest_o1() {
    let Some((code, stdout, stderr)) = run_external_mcl("O1", "O1") else {
        return;
    };

    assert_success(
        code,
        &stdout,
        &stderr,
        "MCL Request__1_1 O1 callout selftest",
    );
    assert_callout_selftest(&stdout, &stderr);
}

#[test]
fn external_mcl_request_1_1_callout_selftest_o3() {
    let Some((code, stdout, stderr)) = run_external_mcl("O3", "O1") else {
        return;
    };

    assert_success(
        code,
        &stdout,
        &stderr,
        "MCL Request__1_1 O3 callout selftest",
    );
    assert_callout_selftest(&stdout, &stderr);
}

#[test]
fn external_mcl_native_fused_single_thread_launch_gate() {
    let Some((code, stdout, stderr)) = run_external_mcl("O3", "O3") else {
        return;
    };

    assert_success(
        code,
        &stdout,
        &stderr,
        "MCL native fused single-thread launch gate",
    );
    assert_callout_selftest(&stdout, &stderr);
    assert!(
        stderr.contains(
            "[llvm2] executable action coverage: llvm2_actions_compiled=27 llvm2_actions_total=27"
        ),
        "expected full MCL action coverage\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("[llvm2] CompiledBfsLevel built (state-constrained native fused LLVM2 parent loop): 27 action instances, 3 invariants, state_len=89"),
        "expected native fused CompiledBfsLevel build\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("llvm2_native_fused_level_active=true"),
        "expected native fused level telemetry\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("llvm2_native_fused_state_constraint_count=1"),
        "expected native fused state constraint telemetry\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("llvm2_native_fused_invariant_count=3"),
        "expected native fused invariant telemetry\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("llvm2_native_fused_regular_invariants_checked=true"),
        "expected native fused regular invariant backend telemetry\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("llvm2_native_fused_local_dedup=false"),
        "expected launch local dedup disabled telemetry\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("[compiled-bfs] starting compiled BFS level loop (1 initial states in arena, fused=true)"),
        "expected compiled BFS level loop launch\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
