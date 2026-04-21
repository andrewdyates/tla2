// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::Path;

mod common;
use common::TempDir;

fn write_counter_spec(path: &Path, module_name: &str) {
    let spec = format!(
        r#"
---- MODULE {module_name} ----
EXTENDS Integers

VARIABLE x

Init == x = 0
Next == x' = x + 1
====
"#
    );
    common::write_file(path, spec.as_bytes());
}

fn assert_limit_run_prints_mmap_storage_stats_to_stdout(
    workers: &str,
    temp_name: &str,
    module_name: &str,
    expected_summary: &str,
) {
    let dir = TempDir::new(temp_name);
    let spec = dir.path.join(format!("{module_name}.tla"));
    let cfg = dir.path.join(format!("{module_name}.cfg"));

    write_counter_spec(&spec, module_name);
    common::write_file(&cfg, b"INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n");

    let out = common::run_tla(&[
        "check",
        spec.to_str().expect("utf-8 spec path"),
        "--config",
        cfg.to_str().expect("utf-8 cfg path"),
        "--workers",
        workers,
        "--mmap-fingerprints",
        "1048576",
        "--max-states",
        "1",
    ]);

    assert!(
        out.status.success(),
        "expected state-limit exit code 0\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains(expected_summary),
        "expected limit-reached summary on stdout\nstdout:\n{}\nstderr:\n{}",
        stdout,
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        stdout.contains("Storage:"),
        "expected storage section on stdout for limit-reached runs\nstdout:\n{}\nstderr:\n{}",
        stdout,
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        stdout.contains("Memory reserved: 8.0 MB"),
        "expected mmap reserved-memory line on stdout for limit-reached runs\nstdout:\n{}\nstderr:\n{}",
        stdout,
        String::from_utf8_lossy(&out.stderr)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_human_invariant_violation_prints_mmap_storage_stats_to_stderr() {
    let dir = TempDir::new("tla2-storage-stats-human-invariant");
    let spec = dir.path.join("StorageStatsInvariant.tla");
    let cfg = dir.path.join("StorageStatsInvariant.cfg");

    common::write_file(
        &spec,
        br#"
---- MODULE StorageStatsInvariant ----
EXTENDS Integers

VARIABLE x

Init == x = 0
Next == x' = x + 1
Safe == x = 0
====
"#,
    );
    common::write_file(&cfg, b"INIT Init\nNEXT Next\nINVARIANT Safe\n");

    let out = common::run_tla(&[
        "check",
        spec.to_str().expect("utf-8 spec path"),
        "--config",
        cfg.to_str().expect("utf-8 cfg path"),
        "--workers",
        "1",
        "--mmap-fingerprints",
        "1048576",
    ]);

    assert!(
        !out.status.success(),
        "expected invariant violation\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("Storage:"),
        "expected storage section on stderr for invariant violations\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        stderr
    );
    assert!(
        stderr.contains("Memory reserved: 8.0 MB"),
        "expected mmap reserved-memory line on stderr for invariant violations\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        stderr
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_human_limit_reached_prints_mmap_storage_stats_to_stdout() {
    assert_limit_run_prints_mmap_storage_stats_to_stdout(
        "1",
        "tla2-storage-stats-human-limit",
        "StorageStatsLimit",
        "Model checking stopped: state limit reached.",
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_human_parallel_limit_reached_prints_mmap_storage_stats_to_stdout() {
    assert_limit_run_prints_mmap_storage_stats_to_stdout(
        "2",
        "tla2-storage-stats-human-parallel-limit",
        "StorageStatsParallelLimit",
        "Model checking stopped: state limit reached.",
    );
}
