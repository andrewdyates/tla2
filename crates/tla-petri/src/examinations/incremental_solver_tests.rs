// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fs;
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use tempfile::TempDir;

use super::{IncrementalSolver, SolverOutcome};

fn write_fake_solver_script(dir: &Path, name: &str, body: &str) -> PathBuf {
    let path = dir.join(name);
    let script = format!("#!/bin/sh\nset -eu\n{body}\n");
    fs::write(&path, script).expect("failed to write fake solver script");
    #[cfg(unix)]
    {
        let mut perms = fs::metadata(&path)
            .expect("script metadata should exist")
            .permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&path, perms).expect("failed to mark fake solver executable");
    }
    path
}

#[test]
fn test_incremental_solver_round_trips_sat_then_unsat() {
    let tempdir = TempDir::new().expect("tempdir should create");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-incremental",
        r#"probe_done=0
count=0
while IFS= read -r line; do
  case "$line" in
    "(check-sat)")
      if [ "$probe_done" -eq 0 ]; then
        probe_done=1
        printf 'sat\n'
      else
        count=$((count + 1))
        if [ "$count" -eq 1 ]; then
          printf 'sat\n'
        else
          printf 'unsat\n'
        fi
      fi
      ;;
    "(exit)")
      exit 0
      ;;
  esac
done"#,
    );

    let mut incremental = IncrementalSolver::new(&solver).expect("probe should succeed");
    assert!(incremental.send("(set-logic QF_LIA)\n"));
    assert!(incremental.push(), "push should succeed");
    assert_eq!(
        incremental.check_sat(Duration::from_secs(1)),
        SolverOutcome::Sat
    );
    assert!(incremental.pop(), "pop should succeed");
    assert_eq!(
        incremental.check_sat(Duration::from_secs(1)),
        SolverOutcome::Unsat
    );
}

#[test]
fn test_incremental_solver_times_out_without_blocking() {
    let tempdir = TempDir::new().expect("tempdir should create");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4-incremental-timeout",
        r#"probe_done=0
while IFS= read -r line; do
  case "$line" in
    "(check-sat)")
      if [ "$probe_done" -eq 0 ]; then
        probe_done=1
        printf 'sat\n'
      else
        sleep 5
      fi
      ;;
    "(exit)")
      exit 0
      ;;
  esac
done"#,
    );

    let mut incremental = IncrementalSolver::new(&solver).expect("probe should succeed");
    let start = Instant::now();
    assert_eq!(
        incremental.check_sat(Duration::from_millis(50)),
        SolverOutcome::Unknown
    );
    assert!(
        start.elapsed() < Duration::from_secs(1),
        "timeout-safe reads should fail closed quickly"
    );
}

#[test]
fn test_incremental_solver_real_z4_startup_fails_closed_quickly() {
    let Some(z4_path) = super::super::smt_encoding::find_z4() else {
        eprintln!("SKIP: z4 not available");
        return;
    };

    let start = Instant::now();
    let solver = IncrementalSolver::new(&z4_path);
    assert!(
        start.elapsed() < Duration::from_secs(3),
        "real-z4 startup probing should either succeed or fail closed quickly"
    );
    drop(solver);
}
