// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Persistent z4 subprocess for incremental SMT queries in TLA+ BMC.
//!
//! Keeps one z4 child process alive across the entire BMC depth ladder so that
//! learned clauses carry forward across depths. Per-depth property queries use
//! `(push)`/`(pop)` scoping to retract depth-specific assertions while retaining
//! the accumulated transition-relation knowledge.
//!
//! Ported from `tla-petri/src/examinations/incremental_solver.rs` and adapted
//! for TLA+ bounded model checking. Part of #3724.

use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

/// Result of a `(check-sat)` query against the incremental solver.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SatResult {
    Sat,
    Unsat,
    Unknown,
}

const STARTUP_TIMEOUT: Duration = Duration::from_secs(5);

/// Persistent z4 subprocess for incremental SMT solving.
///
/// The solver is spawned once and reused across multiple BMC depths. Declarations
/// (sorts, functions, constants) are tracked so the process can be restarted and
/// replayed on crash.
pub(crate) struct IncrementalSolver {
    child: Child,
    stdin: ChildStdin,
    lines: Receiver<String>,
    reader_thread: Option<JoinHandle<()>>,
    terminated: bool,
    /// z4 binary path for restart.
    z4_path: String,
    /// Accumulated declarations for crash recovery replay.
    declarations: Vec<String>,
}

impl IncrementalSolver {
    /// Spawn a new z4 subprocess in incremental SMT-LIB2 mode.
    ///
    /// `z4_path` is the path to the z4 binary (or just `"z4"` to search PATH).
    /// Returns `None` if the subprocess cannot be spawned or fails the startup probe.
    pub(crate) fn new(z4_path: &str) -> Option<Self> {
        let (child, stdin, lines, reader_thread) = Self::spawn_process(z4_path)?;

        let mut solver = Self {
            child,
            stdin,
            lines,
            reader_thread: Some(reader_thread),
            terminated: false,
            z4_path: z4_path.to_string(),
            declarations: Vec::new(),
        };

        // Startup probe: verify the process responds to a trivial check-sat.
        if !solver.send_raw("(check-sat)\n") {
            solver.terminate();
            return None;
        }
        match solver.read_line_timeout(STARTUP_TIMEOUT) {
            Some(line) if line.trim() == "sat" => {}
            _ => {
                solver.terminate();
                return None;
            }
        }

        Some(solver)
    }

    /// Send a persistent declaration (sort, function, constant).
    ///
    /// The declaration is recorded so it can be replayed on crash recovery.
    pub(crate) fn declare(&mut self, smt_cmd: &str) -> bool {
        if self.send_raw(smt_cmd) {
            self.declarations.push(smt_cmd.to_string());
            true
        } else {
            false
        }
    }

    /// Send an assertion that persists (not retracted by `pop`).
    ///
    /// This is recorded for crash recovery replay.
    pub(crate) fn assert_persistent(&mut self, smt_cmd: &str) -> bool {
        if self.send_raw(smt_cmd) {
            self.declarations.push(smt_cmd.to_string());
            true
        } else {
            false
        }
    }

    /// Send raw SMT-LIB2 commands without recording for replay.
    pub(crate) fn assert_smt(&mut self, smt_cmd: &str) -> bool {
        self.send_raw(smt_cmd)
    }

    /// Push a new assertion scope.
    pub(crate) fn push(&mut self) -> bool {
        self.send_raw("(push 1)\n")
    }

    /// Pop the most recent assertion scope.
    pub(crate) fn pop(&mut self) -> bool {
        self.send_raw("(pop 1)\n")
    }

    /// Send `(check-sat)` and wait for a result within `timeout`.
    pub(crate) fn check_sat(&mut self, timeout: Duration) -> SatResult {
        let timeout_ms = timeout.as_millis().max(1);
        let set_timeout = format!("(set-option :timeout {timeout_ms})\n(check-sat)\n");
        if !self.send_raw(&set_timeout) {
            self.terminate();
            return SatResult::Unknown;
        }
        self.read_sat_result(timeout)
    }

    /// Returns `true` if the solver subprocess has been terminated.
    pub(crate) fn is_terminated(&self) -> bool {
        self.terminated
    }

    /// Attempt to restart the solver after a crash, replaying all declarations.
    ///
    /// Returns `true` if restart succeeded and all declarations were replayed.
    pub(crate) fn restart(&mut self) -> bool {
        // Clean up the old process.
        self.terminate();

        let Some((child, stdin, lines, reader_thread)) = Self::spawn_process(&self.z4_path) else {
            return false;
        };

        self.child = child;
        self.stdin = stdin;
        self.lines = lines;
        self.reader_thread = Some(reader_thread);
        self.terminated = false;

        // Startup probe.
        if !self.send_raw("(check-sat)\n") {
            self.terminate();
            return false;
        }
        match self.read_line_timeout(STARTUP_TIMEOUT) {
            Some(line) if line.trim() == "sat" => {}
            _ => {
                self.terminate();
                return false;
            }
        }

        // Replay all persistent declarations.
        let decls = self.declarations.clone();
        for decl in &decls {
            if !self.send_raw(decl) {
                self.terminate();
                return false;
            }
        }

        true
    }

    // -- Internal helpers --

    fn spawn_process(
        z4_path: &str,
    ) -> Option<(Child, ChildStdin, Receiver<String>, JoinHandle<()>)> {
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
        let (tx, rx) = mpsc::channel();

        let reader_thread = thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            let mut line = String::new();
            loop {
                line.clear();
                match reader.read_line(&mut line) {
                    Ok(0) | Err(_) => break,
                    Ok(_) => {
                        if tx.send(line.clone()).is_err() {
                            break;
                        }
                    }
                }
            }
        });

        Some((child, stdin, rx, reader_thread))
    }

    fn send_raw(&mut self, cmd: &str) -> bool {
        if self.terminated {
            return false;
        }
        self.stdin.write_all(cmd.as_bytes()).is_ok() && self.stdin.flush().is_ok()
    }

    fn read_line_timeout(&mut self, timeout: Duration) -> Option<String> {
        let start = Instant::now();
        loop {
            let remaining = timeout.saturating_sub(start.elapsed());
            if remaining.is_zero() {
                return None;
            }
            match self.lines.recv_timeout(remaining) {
                Ok(line) => return Some(line),
                Err(RecvTimeoutError::Timeout) | Err(RecvTimeoutError::Disconnected) => {
                    return None;
                }
            }
        }
    }

    fn read_sat_result(&mut self, timeout: Duration) -> SatResult {
        let start = Instant::now();
        loop {
            let remaining = timeout.saturating_sub(start.elapsed());
            if remaining.is_zero() {
                self.terminate();
                return SatResult::Unknown;
            }

            match self.lines.recv_timeout(remaining) {
                Ok(line) => match line.trim() {
                    "sat" => return SatResult::Sat,
                    "unsat" => return SatResult::Unsat,
                    "unknown" => return SatResult::Unknown,
                    trimmed if trimmed.starts_with("(error") => return SatResult::Unknown,
                    _ => { /* skip info/warning lines, keep reading */ }
                },
                Err(RecvTimeoutError::Timeout) | Err(RecvTimeoutError::Disconnected) => {
                    self.terminate();
                    return SatResult::Unknown;
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
        if let Some(handle) = self.reader_thread.take() {
            let _ = handle.join();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Find z4 binary for tests. Checks Z4_PATH env, ~/z4/target/release/z4, then PATH.
    fn find_z4_for_test() -> Option<String> {
        if let Ok(path) = std::env::var("Z4_PATH") {
            if std::path::Path::new(&path).is_file() {
                return Some(path);
            }
        }
        if let Ok(home) = std::env::var("HOME") {
            let home_path = std::path::PathBuf::from(home).join("z4/target/release/z4");
            if home_path.is_file() {
                return Some(home_path.to_string_lossy().into_owned());
            }
        }
        // Try PATH
        if Command::new("z4")
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok()
        {
            return Some("z4".to_string());
        }
        None
    }

    #[test]
    fn test_incremental_solver_basic_sat() {
        let Some(z4) = find_z4_for_test() else {
            eprintln!("z4 binary not found, skipping test");
            return;
        };
        let mut solver = IncrementalSolver::new(&z4).expect("solver should spawn");

        solver.declare("(declare-const x Int)\n");
        solver.assert_smt("(assert (= x 42))\n");

        let result = solver.check_sat(Duration::from_secs(5));
        assert_eq!(result, SatResult::Sat);
    }

    #[test]
    fn test_incremental_solver_push_pop() {
        let Some(z4) = find_z4_for_test() else {
            eprintln!("z4 binary not found, skipping test");
            return;
        };
        let mut solver = IncrementalSolver::new(&z4).expect("solver should spawn");

        solver.declare("(declare-const x Int)\n");
        solver.assert_smt("(assert (>= x 0))\n");

        // Push and add conflicting constraint.
        solver.push();
        solver.assert_smt("(assert (< x 0))\n");
        let result = solver.check_sat(Duration::from_secs(5));
        assert_eq!(result, SatResult::Unsat, "x >= 0 AND x < 0 should be unsat");

        // Pop should retract the conflicting constraint.
        solver.pop();
        let result = solver.check_sat(Duration::from_secs(5));
        assert_eq!(result, SatResult::Sat, "x >= 0 alone should be sat");
    }

    #[test]
    fn test_incremental_solver_learned_clauses_persist() {
        let Some(z4) = find_z4_for_test() else {
            eprintln!("z4 binary not found, skipping test");
            return;
        };
        let mut solver = IncrementalSolver::new(&z4).expect("solver should spawn");

        // Declare persistent variables and constraints (simulating BMC transition).
        solver.declare("(declare-const x0 Int)\n");
        solver.declare("(declare-const x1 Int)\n");
        solver.assert_persistent("(assert (= x0 0))\n");
        solver.assert_persistent("(assert (= x1 (+ x0 1)))\n");

        // Depth 1: check if x1 > 5 (should be unsat since x1 = 1).
        solver.push();
        solver.assert_smt("(assert (> x1 5))\n");
        let result = solver.check_sat(Duration::from_secs(5));
        assert_eq!(result, SatResult::Unsat);
        solver.pop();

        // Add more transition steps.
        solver.declare("(declare-const x2 Int)\n");
        solver.assert_persistent("(assert (= x2 (+ x1 1)))\n");

        // Depth 2: x2 > 5 still unsat since x2 = 2.
        solver.push();
        solver.assert_smt("(assert (> x2 5))\n");
        let result = solver.check_sat(Duration::from_secs(5));
        assert_eq!(result, SatResult::Unsat);
        solver.pop();

        // Depth 2: x2 = 2 should be sat.
        solver.push();
        solver.assert_smt("(assert (= x2 2))\n");
        let result = solver.check_sat(Duration::from_secs(5));
        assert_eq!(result, SatResult::Sat);
        solver.pop();
    }

    #[test]
    fn test_incremental_solver_restart_replays_declarations() {
        let Some(z4) = find_z4_for_test() else {
            eprintln!("z4 binary not found, skipping test");
            return;
        };
        let mut solver = IncrementalSolver::new(&z4).expect("solver should spawn");

        solver.declare("(declare-const x Int)\n");
        solver.assert_persistent("(assert (= x 42))\n");

        // Verify it works before restart.
        solver.push();
        solver.assert_smt("(assert (= x 42))\n");
        let result = solver.check_sat(Duration::from_secs(5));
        assert_eq!(result, SatResult::Sat);
        solver.pop();

        // Force restart (simulates crash recovery).
        assert!(solver.restart(), "restart should succeed");

        // Declarations should have been replayed.
        solver.push();
        solver.assert_smt("(assert (= x 42))\n");
        let result = solver.check_sat(Duration::from_secs(5));
        assert_eq!(result, SatResult::Sat, "replayed declarations should work");
        solver.pop();
    }
}
