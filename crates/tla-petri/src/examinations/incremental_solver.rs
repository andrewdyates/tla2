// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Persistent z4 process for incremental SMT queries.
//!
//! Keeps one z4 child process alive across the entire BMC depth ladder,
//! allowing transition-relation assertions to accumulate (learned clauses
//! carry forward) and per-property queries to use push/pop scoping.

use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use super::smt_encoding::SolverOutcome;

const STARTUP_MARKER: &str = "sat";
const STARTUP_PROBE: &str = "(push 1)\n(check-sat)\n(pop 1)\n";
const STARTUP_TIMEOUT: Duration = Duration::from_secs(2);

pub(super) struct IncrementalSolver {
    child: Child,
    stdin: ChildStdin,
    lines: Receiver<String>,
    reader_thread: Option<JoinHandle<()>>,
    terminated: bool,
}

impl IncrementalSolver {
    pub(super) fn new(z4_path: &Path) -> Option<Self> {
        let mut child = Command::new(z4_path)
            .arg("-smt2")
            .arg("-in")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .ok()?;

        let stdin = child.stdin.take()?;
        let stdout = child.stdout.take()?;
        let (line_tx, line_rx) = mpsc::channel();
        let reader_thread = thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            let mut line = String::new();
            loop {
                line.clear();
                match reader.read_line(&mut line) {
                    Ok(0) | Err(_) => break,
                    Ok(_) => {
                        if line_tx.send(line.clone()).is_err() {
                            break;
                        }
                    }
                }
            }
        });

        let mut solver = Self {
            child,
            stdin,
            lines: line_rx,
            reader_thread: Some(reader_thread),
            terminated: false,
        };

        if !solver.send(STARTUP_PROBE) || !solver.read_until_marker(STARTUP_TIMEOUT, STARTUP_MARKER)
        {
            solver.terminate();
            return None;
        }

        Some(solver)
    }

    /// Send SMT-LIB commands (no response expected).
    pub(super) fn send(&mut self, cmd: &str) -> bool {
        if self.terminated {
            return false;
        }
        self.stdin.write_all(cmd.as_bytes()).is_ok() && self.stdin.flush().is_ok()
    }

    /// Send `(check-sat)` and wait for one solver status line.
    pub(super) fn check_sat(&mut self, timeout: Duration) -> SolverOutcome {
        let timeout_ms = timeout.as_millis().max(1).min(u128::from(u64::MAX));
        if !self.send(&format!(
            "(set-option :timeout {timeout_ms})\n(check-sat)\n"
        )) {
            self.terminate();
            return SolverOutcome::Unknown;
        }
        self.read_outcome(timeout)
    }

    pub(super) fn push(&mut self) -> bool {
        self.send("(push 1)\n")
    }

    pub(super) fn pop(&mut self) -> bool {
        self.send("(pop 1)\n")
    }

    fn read_until_marker(&mut self, timeout: Duration, marker: &str) -> bool {
        let start = Instant::now();
        loop {
            let remaining = timeout.saturating_sub(start.elapsed());
            if remaining.is_zero() {
                return false;
            }

            match self.lines.recv_timeout(remaining) {
                Ok(line) => {
                    let trimmed = line.trim().trim_matches('"');
                    if trimmed == marker {
                        return true;
                    }
                    if trimmed.starts_with("(error") {
                        return false;
                    }
                }
                Err(RecvTimeoutError::Timeout) | Err(RecvTimeoutError::Disconnected) => {
                    return false;
                }
            }
        }
    }

    fn read_outcome(&mut self, timeout: Duration) -> SolverOutcome {
        let start = Instant::now();
        loop {
            let remaining = timeout.saturating_sub(start.elapsed());
            if remaining.is_zero() {
                self.terminate();
                return SolverOutcome::Unknown;
            }

            match self.lines.recv_timeout(remaining) {
                Ok(line) => match line.trim() {
                    "sat" => return SolverOutcome::Sat,
                    "unsat" => return SolverOutcome::Unsat,
                    "unknown" => return SolverOutcome::Unknown,
                    trimmed if trimmed.starts_with("(error") => return SolverOutcome::Unknown,
                    _ => {}
                },
                Err(RecvTimeoutError::Timeout) | Err(RecvTimeoutError::Disconnected) => {
                    self.terminate();
                    return SolverOutcome::Unknown;
                }
            }
        }
    }

    fn terminate(&mut self) {
        if self.terminated {
            return;
        }
        let _ = self.child.kill();
        let _ = self.child.wait();
        self.terminated = true;
    }
}

impl Drop for IncrementalSolver {
    fn drop(&mut self) {
        if !self.terminated {
            let _ = self.stdin.write_all(b"(exit)\n");
            let _ = self.stdin.flush();
            let _ = self.child.wait();
            self.terminated = true;
        }
        if let Some(reader_thread) = self.reader_thread.take() {
            let _ = reader_thread.join();
        }
    }
}

#[cfg(test)]
#[path = "incremental_solver_tests.rs"]
mod tests;
