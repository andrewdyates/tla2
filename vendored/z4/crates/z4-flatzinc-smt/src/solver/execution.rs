// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Run z4 on the given SMT-LIB script.
///
/// When the `z4-library` feature is enabled, uses the z4 library API directly
/// (parse + execute) which eliminates subprocess overhead (~13x faster per
/// call). When timeout is configured, the library path uses a watchdog thread
/// to set the executor's interrupt flag after the deadline.
pub(crate) fn run_z4(script: &str, config: &SolverConfig) -> Result<String, SolverError> {
    #[cfg(feature = "z4-library")]
    {
        #[allow(clippy::needless_return)]
        return run_z4_library(script, config.timeout_ms);
    }
    #[cfg(not(feature = "z4-library"))]
    run_z4_oneshot(script, config)
}

/// Run z4 via the library API: parse SMT-LIB text, then execute commands
/// directly in-process. Eliminates subprocess spawn overhead (~8ms per call)
/// and pipe serialization.
///
/// When `timeout_ms` is set, a watchdog thread sets the executor's interrupt
/// flag after the deadline, causing check-sat to return `unknown`.
#[cfg(feature = "z4-library")]
fn run_z4_library(script: &str, timeout_ms: Option<u64>) -> Result<String, SolverError> {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    let commands =
        z4_frontend::parse(script).map_err(|e| SolverError::SolverError(format!("parse: {e}")))?;
    let mut executor = z4_dpll::Executor::new();

    // Wire interrupt flag for cooperative timeout (#5931).
    // Timer thread uses park_timeout so it can be woken early when the
    // executor finishes, avoiding orphaned sleeping threads (#6231).
    let timer_handle = if let Some(ms) = timeout_ms {
        let flag = Arc::new(AtomicBool::new(false));
        executor.set_interrupt(flag.clone());
        let cancelled = Arc::new(AtomicBool::new(false));
        let cancel_flag = cancelled.clone();
        let handle = std::thread::spawn(move || {
            std::thread::park_timeout(Duration::from_millis(ms));
            if !cancel_flag.load(Ordering::Acquire) {
                flag.store(true, Ordering::SeqCst);
            }
        });
        Some((handle, cancelled))
    } else {
        None
    };

    let mut outputs = Vec::new();
    for cmd in &commands {
        match executor.execute(cmd) {
            Ok(Some(out)) => outputs.push(out),
            Ok(None) => {}
            Err(e) => {
                // Non-fatal after check-sat: get-info :reason-unknown may
                // fail when the result was sat/unsat (not unknown).
                // The critical outputs (check-sat, get-value) already captured.
                if outputs.is_empty() {
                    // Cancel timer before returning error.
                    if let Some((handle, cancelled)) = timer_handle {
                        cancelled.store(true, Ordering::Release);
                        handle.thread().unpark();
                    }
                    return Err(SolverError::SolverError(format!("{e}")));
                }
            }
        }
    }

    // Cancel the timer early — executor is done.
    if let Some((handle, cancelled)) = timer_handle {
        cancelled.store(true, Ordering::Release);
        handle.thread().unpark();
    }
    if outputs.is_empty() {
        Ok(String::new())
    } else {
        Ok(outputs.join("\n") + "\n")
    }
}

/// Run z4 as a subprocess with the given SMT-LIB script on stdin.
///
/// Uses process-level timeout instead of z4's `-t:` flag. The `-t:` flag
/// causes z4 to return `unknown` on problems it can otherwise solve (#327).
/// Process-level timeout kills the subprocess after the deadline, which
/// correctly preserves z4's default solving strategy.
#[cfg(not(feature = "z4-library"))]
pub(crate) fn run_z4_oneshot(script: &str, config: &SolverConfig) -> Result<String, SolverError> {
    let mut cmd = Command::new(&config.z4_path);
    cmd.arg("-in");
    cmd.stdin(Stdio::piped());
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::piped());

    let mut child = cmd.spawn().map_err(|e| SolverError::SpawnFailed {
        path: config.z4_path.clone(),
        source: e,
    })?;

    // Write script to stdin and close it to signal EOF.
    if let Some(ref mut stdin) = child.stdin {
        stdin.write_all(script.as_bytes())?;
    }
    drop(child.stdin.take());

    if let Some(timeout_ms) = config.timeout_ms {
        wait_with_timeout(&mut child, Duration::from_millis(timeout_ms))
    } else {
        wait_no_timeout(child)
    }
}

/// Wait for child process with a deadline, killing it on timeout.
///
/// Reads stdout/stderr in background threads to avoid pipe buffer deadlock.
/// Returns `"unknown\n"` if the process is killed after the deadline.
#[cfg(not(feature = "z4-library"))]
fn wait_with_timeout(child: &mut Child, timeout: Duration) -> Result<String, SolverError> {
    use std::io::Read as _;

    let start = Instant::now();

    let stdout_handle = child.stdout.take().expect("stdout piped");
    let stderr_handle = child.stderr.take().expect("stderr piped");

    let stdout_thread = std::thread::spawn(move || {
        let mut buf = String::new();
        let mut reader = io::BufReader::new(stdout_handle);
        reader.read_to_string(&mut buf).ok();
        buf
    });
    let stderr_thread = std::thread::spawn(move || {
        let mut buf = String::new();
        let mut reader = io::BufReader::new(stderr_handle);
        reader.read_to_string(&mut buf).ok();
        buf
    });

    loop {
        match child.try_wait().map_err(SolverError::IoError)? {
            Some(_status) => break,
            None => {
                if start.elapsed() > timeout {
                    child.kill().ok();
                    child.wait().ok();
                    let _ = stdout_thread.join();
                    let _ = stderr_thread.join();
                    return Ok("unknown\n".to_string());
                }
                std::thread::sleep(Duration::from_millis(50));
            }
        }
    }

    let stdout_output = stdout_thread.join().unwrap_or_default();
    let stderr_output = stderr_thread.join().unwrap_or_default();

    if !stderr_output.is_empty() && stdout_output.is_empty() {
        return Err(SolverError::SolverError(stderr_output));
    }

    Ok(stdout_output)
}

/// Wait for child process without timeout.
#[cfg(not(feature = "z4-library"))]
fn wait_no_timeout(child: Child) -> Result<String, SolverError> {
    let output = child.wait_with_output().map_err(SolverError::IoError)?;

    if !output.stderr.is_empty() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if output.stdout.is_empty() {
            return Err(SolverError::SolverError(stderr.into_owned()));
        }
    }

    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

/// Extract the reason for `unknown` from z4's `(get-info :reason-unknown)` response.
///
/// Scans remaining output lines for `(:reason-unknown "...")` and returns the
/// reason string (e.g., "timeout", "incomplete"). Returns `None` if no
/// reason-unknown response is found.
pub(crate) fn extract_reason_unknown(lines: &[String]) -> Option<String> {
    for line in lines {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("(:reason-unknown") {
            let rest = rest.trim();
            if let Some(inner) = rest.strip_suffix(')') {
                let reason = inner.trim().trim_matches('"');
                if !reason.is_empty() {
                    return Some(reason.to_string());
                }
            }
        }
    }
    None
}

/// Parse z4 output into check-sat result and remaining lines.
pub(crate) fn parse_z4_output(output: &str) -> Result<(CheckSatResult, Vec<String>), SolverError> {
    let mut lines: Vec<String> = output.lines().map(String::from).collect();
    if lines.is_empty() {
        return Err(SolverError::EmptyOutput);
    }

    let status_line = lines.remove(0).trim().to_string();
    let status = match status_line.as_str() {
        "sat" => CheckSatResult::Sat,
        "unsat" => CheckSatResult::Unsat,
        "unknown" => CheckSatResult::Unknown,
        other => return Err(SolverError::UnexpectedOutput(other.to_string())),
    };

    Ok((status, lines))
}
