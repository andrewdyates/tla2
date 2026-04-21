// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Subprocess spawning, timeout waiting, and concurrency primitives for diagnose runner.

use std::path::Path;
use std::time::{Duration, Instant};

use super::super::types::DiagnoseCheckPolicy;

/// Spawn `tla2 check` or `tla2 simulate` depending on the spec's mode.
/// Part of #3076: simulation specs require `tla2 simulate` to pass.
/// Part of #3236: `continue_on_error` controls whether `--continue-on-error`
/// is passed; specs whose TLC baseline was collected at first-error use `false`.
/// Part of #4252 Stream 6: `backend` selects `interpreter` (default) or
/// `llvm2` (stub emitting `backend_unavailable` sentinel, exit code 3).
/// Only applies to `check` mode; simulation mode always uses the interpreter.
pub(super) fn spawn_tla2(
    exe: &Path,
    tla_path: &Path,
    cfg_path: &Path,
    mode: &str,
    checker_policy: DiagnoseCheckPolicy,
    continue_on_error: bool,
    backend: &str,
) -> std::io::Result<std::process::Child> {
    let mut cmd = std::process::Command::new(exe);
    match mode {
        "simulate" | "generate" => {
            // Part of #3448: Simulation-mode specs are probabilistic — invariant
            // violations depend on random seed and trace count. Diagnose tests whether
            // TLA2 can run the simulation without crashing, not whether it finds the
            // same probabilistic violations as TLC. Pass --no-invariants so that
            // invariant violations (which are the designed behavior of trace-export
            // specs like EWD998ChanID_export) don't cause false positives.
            cmd.arg("simulate")
                .arg(tla_path)
                .arg("--config")
                .arg(cfg_path)
                .arg("--no-invariants");
        }
        _ => {
            cmd.arg("check")
                .arg(tla_path)
                .arg("--config")
                .arg(cfg_path)
                .arg("--output")
                .arg("json")
                // Override per-instance memory auto-detection with a large
                // explicit limit. Auto-detection divides system RAM by
                // count_tla2_instances(), which over-restricts each subprocess
                // when unrelated tla2 processes are running. 131072 MB = 128 GB
                // effectively disables the limit on typical machines.
                .arg("--memory-limit")
                .arg("131072")
                .arg("--backend")
                .arg(backend);
            checker_policy.append_check_args(&mut cmd, continue_on_error);
        }
    }
    cmd.stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
}

/// Check if the process was killed by a signal (SIGKILL or SIGTERM), which
/// typically indicates the memory watchdog terminated it for OOM.
/// Part of #2927: previously these were misclassified as Crash.
pub(super) fn is_signal_killed(status: &std::process::ExitStatus) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        matches!(status.signal(), Some(9 | 15)) // SIGKILL, SIGTERM
    }
    #[cfg(not(unix))]
    {
        let _ = status;
        false
    }
}

pub(super) enum WaitResult {
    Completed(std::process::Output),
    Timeout,
    Error(std::io::Error),
}

/// Wait for a child process with a timeout. Reads stdout/stderr in background
/// threads to avoid pipe buffer deadlocks (~64KB OS buffer limit).
pub(super) fn wait_with_timeout(mut child: std::process::Child, timeout: Duration) -> WaitResult {
    use std::io::Read as _;

    let mut stdout_pipe = child.stdout.take();
    let mut stderr_pipe = child.stderr.take();

    let stdout_handle = std::thread::spawn(move || {
        let mut buf = Vec::new();
        if let Some(ref mut pipe) = stdout_pipe {
            let _ = pipe.read_to_end(&mut buf);
        }
        buf
    });
    let stderr_handle = std::thread::spawn(move || {
        let mut buf = Vec::new();
        if let Some(ref mut pipe) = stderr_pipe {
            let _ = pipe.read_to_end(&mut buf);
        }
        buf
    });

    let start = Instant::now();
    let poll_interval = Duration::from_millis(100);

    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let stdout = stdout_handle.join().unwrap_or_default();
                let stderr = stderr_handle.join().unwrap_or_default();
                return WaitResult::Completed(std::process::Output {
                    status,
                    stdout,
                    stderr,
                });
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    let _ = stdout_handle.join();
                    let _ = stderr_handle.join();
                    return WaitResult::Timeout;
                }
                std::thread::sleep(poll_interval);
            }
            Err(e) => {
                let _ = stdout_handle.join();
                let _ = stderr_handle.join();
                return WaitResult::Error(e);
            }
        }
    }
}

// ── Semaphore (std doesn't provide one) ─────────────────────────────────────

pub(in crate::cmd_diagnose) struct Semaphore {
    state: std::sync::Mutex<usize>,
    cvar: std::sync::Condvar,
}

pub(in crate::cmd_diagnose) struct SemaphorePermit<'a> {
    sem: &'a Semaphore,
}

impl Semaphore {
    pub(in crate::cmd_diagnose) fn new(permits: usize) -> Self {
        Self {
            state: std::sync::Mutex::new(permits),
            cvar: std::sync::Condvar::new(),
        }
    }

    pub(in crate::cmd_diagnose) fn acquire(&self) -> SemaphorePermit<'_> {
        let mut count = self.state.lock().expect("semaphore lock poisoned");
        while *count == 0 {
            count = self.cvar.wait(count).expect("semaphore condvar poisoned");
        }
        *count -= 1;
        SemaphorePermit { sem: self }
    }
}

impl Drop for SemaphorePermit<'_> {
    fn drop(&mut self) {
        let mut count = self.sem.state.lock().expect("semaphore lock poisoned");
        *count += 1;
        self.sem.cvar.notify_one();
    }
}
