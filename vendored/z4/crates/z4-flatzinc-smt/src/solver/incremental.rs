// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// --- Incremental solver (persistent z4 process with push/pop) ---

/// State for pipe-based incremental solver (subprocess with PTY).
#[cfg_attr(feature = "z4-library", allow(dead_code))]
struct PipeState {
    child: Child,
    stdin: io::BufWriter<Box<dyn Write + Send>>,
    stdout: io::BufReader<ChildStdout>,
    sync_counter: u64,
}

/// Backend for the incremental solver.
#[cfg_attr(feature = "z4-library", allow(dead_code))]
enum IncrementalBackend {
    /// Pipe-based: subprocess with PTY + echo sync markers.
    Pipe(PipeState),
    /// Library-based: z4 Solver API in-process (no subprocess, no pipes).
    /// Uses the native Solver API for push/pop/check-sat with timeout support.
    /// Boxed to avoid large enum variant size difference vs PipeState.
    #[cfg(feature = "z4-library")]
    Library(Box<z4_dpll::api::Solver>),
}

/// Incremental SMT solver with push/pop for backtracking search.
///
/// With `z4-library` feature: uses in-process z4 Executor (no subprocess).
/// Without: spawns a z4 subprocess with PTY and echo sync markers.
///
/// Benefit: declarations are sent once, z4 reuses learned clauses across calls,
/// and process spawn overhead (~5ms per call) is eliminated.
pub(crate) struct IncrementalSolver {
    backend: IncrementalBackend,
}

// --- PipeState: all pipe-specific methods ---

#[cfg_attr(feature = "z4-library", allow(dead_code))]
impl PipeState {
    /// Spawn z4 with a PTY as stdin so it enters interactive mode.
    #[cfg(unix)]
    fn new_with_pty(config: &SolverConfig, declarations: &str) -> Result<Self, SolverError> {
        use nix::pty::openpty;
        use nix::sys::termios;

        let pty = openpty(None, None)
            .map_err(|e| SolverError::IoError(io::Error::other(format!("openpty: {e}"))))?;

        let mut attrs = termios::tcgetattr(&pty.slave)
            .map_err(|e| SolverError::IoError(io::Error::other(format!("tcgetattr: {e}"))))?;
        attrs.local_flags.remove(termios::LocalFlags::ECHO);
        termios::tcsetattr(&pty.slave, termios::SetArg::TCSANOW, &attrs)
            .map_err(|e| SolverError::IoError(io::Error::other(format!("tcsetattr: {e}"))))?;

        let mut cmd = Command::new(&config.z4_path);
        cmd.arg("-in");
        cmd.stdin(Stdio::from(pty.slave));
        cmd.stdout(Stdio::piped());
        cmd.stderr(Stdio::piped());

        let mut child = cmd.spawn().map_err(|e| SolverError::SpawnFailed {
            path: config.z4_path.clone(),
            source: e,
        })?;

        let master_file = std::fs::File::from(pty.master);
        let stdin: Box<dyn Write + Send> = Box::new(master_file);
        let stdin = io::BufWriter::new(stdin);
        let stdout = io::BufReader::new(child.stdout.take().expect("stdout piped"));

        let mut state = Self {
            child,
            stdin,
            stdout,
            sync_counter: 0,
        };

        state.send(declarations)?;
        state.verify_incremental_support()?;
        Ok(state)
    }

    /// Spawn z4 with piped stdin (non-Unix fallback).
    #[cfg(not(unix))]
    fn new_with_pipe(config: &SolverConfig, declarations: &str) -> Result<Self, SolverError> {
        let mut cmd = Command::new(&config.z4_path);
        cmd.arg("-in");
        cmd.stdin(Stdio::piped());
        cmd.stdout(Stdio::piped());
        cmd.stderr(Stdio::piped());

        let mut child = cmd.spawn().map_err(|e| SolverError::SpawnFailed {
            path: config.z4_path.clone(),
            source: e,
        })?;

        let stdin: Box<dyn Write + Send> = Box::new(child.stdin.take().expect("stdin piped"));
        let stdin = io::BufWriter::new(stdin);
        let stdout = io::BufReader::new(child.stdout.take().expect("stdout piped"));

        let mut state = Self {
            child,
            stdin,
            stdout,
            sync_counter: 0,
        };

        state.send(declarations)?;
        state.verify_incremental_support()?;
        Ok(state)
    }

    #[cfg(unix)]
    #[allow(unsafe_code)] // libc::poll FFI call requires unsafe
    fn poll_readable(&self, timeout_ms: i32) -> bool {
        use std::os::unix::io::AsRawFd;
        let fd = self.stdout.get_ref().as_raw_fd();
        let mut pfd = libc::pollfd {
            fd,
            events: libc::POLLIN,
            revents: 0,
        };
        // SAFETY: `pfd` is a valid stack-local `pollfd` with a valid fd from
        // `as_raw_fd()`, `nfds` is 1 matching the single-element array, and
        // `timeout_ms` is a plain integer. No aliasing or lifetime issues.
        let result = unsafe { libc::poll(&raw mut pfd, 1, timeout_ms) };
        result > 0 && (pfd.revents & libc::POLLIN) != 0
    }

    fn verify_incremental_support(&mut self) -> Result<(), SolverError> {
        let marker = self.next_marker();
        self.send(&format!("(echo \"{marker}\")\n"))?;

        #[cfg(unix)]
        {
            if !self.poll_readable(3000) {
                return Err(SolverError::PipeBuffering);
            }
        }

        let _lines = self.read_until_marker(&marker)?;
        Ok(())
    }

    fn send(&mut self, cmd: &str) -> Result<(), SolverError> {
        self.stdin.write_all(cmd.as_bytes())?;
        self.stdin.flush()?;
        Ok(())
    }

    fn next_marker(&mut self) -> String {
        self.sync_counter += 1;
        format!("SYNC_{}", self.sync_counter)
    }

    fn read_until_marker(&mut self, marker: &str) -> Result<Vec<String>, SolverError> {
        let mut lines = Vec::new();
        let marker_quoted = format!("\"{marker}\"");
        loop {
            let mut line = String::new();
            let n = self
                .stdout
                .read_line(&mut line)
                .map_err(SolverError::IoError)?;
            if n == 0 {
                return Err(SolverError::EmptyOutput);
            }
            let trimmed = line.trim();
            if trimmed == marker || trimmed == marker_quoted {
                break;
            }
            if !trimmed.is_empty() {
                lines.push(trimmed.to_string());
            }
        }
        Ok(lines)
    }

    fn check_sat_incremental(&mut self, assertions: &str) -> Result<CheckSatResult, SolverError> {
        let marker = self.next_marker();
        self.send("(push 1)\n")?;
        self.send(assertions)?;
        self.send("(check-sat)\n")?;
        self.send(&format!("(echo \"{marker}\")\n"))?;

        let lines = self.read_until_marker(&marker)?;

        if lines.is_empty() {
            return Err(SolverError::EmptyOutput);
        }

        match lines[0].as_str() {
            "sat" => Ok(CheckSatResult::Sat),
            "unsat" => Ok(CheckSatResult::Unsat),
            "unknown" => Ok(CheckSatResult::Unknown),
            other => Err(SolverError::UnexpectedOutput(other.to_string())),
        }
    }

    fn pop(&mut self) -> Result<(), SolverError> {
        self.send("(pop 1)\n")?;
        Ok(())
    }

    fn get_value(&mut self, vars: &str) -> Result<HashMap<String, String>, SolverError> {
        let marker = self.next_marker();
        self.send(&format!("(get-value ({vars}))\n"))?;
        self.send(&format!("(echo \"{marker}\")\n"))?;

        let lines = self.read_until_marker(&marker)?;
        parse_get_value(&lines)
    }

    fn shutdown(&mut self) {
        let _ = self.stdin.write_all(b"(exit)\n");
        let _ = self.stdin.flush();
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

// --- IncrementalSolver: dispatches to pipe or library backend ---

impl IncrementalSolver {
    /// Create incremental solver. With `z4-library` feature, uses in-process
    /// z4 Solver API with timeout support. Otherwise, spawns a subprocess with PTY.
    pub(crate) fn new(config: &SolverConfig, declarations: &str) -> Result<Self, SolverError> {
        #[cfg(feature = "z4-library")]
        {
            Self::new_library(config, declarations)
        }
        #[cfg(not(feature = "z4-library"))]
        {
            Self::new_pipe(config, declarations)
        }
    }

    /// Create pipe-based solver (subprocess with PTY on Unix).
    #[cfg_attr(feature = "z4-library", allow(dead_code))]
    fn new_pipe(config: &SolverConfig, declarations: &str) -> Result<Self, SolverError> {
        #[cfg(unix)]
        let pipe = PipeState::new_with_pty(config, declarations)?;
        #[cfg(not(unix))]
        let pipe = PipeState::new_with_pipe(config, declarations)?;
        Ok(Self {
            backend: IncrementalBackend::Pipe(pipe),
        })
    }

    /// Create library-based solver (in-process z4 Solver API).
    ///
    /// Uses the native `Solver` API which provides:
    /// - Direct push/pop/check-sat without SMT-LIB text reparsing
    /// - Timeout support via `Solver::set_timeout()`
    /// - Interrupt handle for cancellation from other threads
    #[cfg(feature = "z4-library")]
    #[allow(deprecated)]
    fn new_library(config: &SolverConfig, declarations: &str) -> Result<Self, SolverError> {
        use z4_dpll::api::{Logic, Solver};

        // Create solver with permissive logic; parse_smtlib2 will override
        // with the actual logic from the declarations (set-logic is idempotent).
        let mut solver = Solver::new(Logic::All);

        // Set timeout from config so all check_sat calls respect it
        if let Some(ms) = config.timeout_ms {
            solver.set_timeout(Some(Duration::from_millis(ms)));
        }

        // Load declarations (set-logic, declare-const, assert, etc.)
        // Skips query commands (check-sat, get-model, etc.)
        solver
            .parse_smtlib2(declarations)
            .map_err(|e| SolverError::SolverError(format!("parse error: {e}")))?;

        Ok(Self {
            backend: IncrementalBackend::Library(Box::new(solver)),
        })
    }

    /// Push a scope, send assertions, check satisfiability.
    pub(crate) fn check_sat_incremental(
        &mut self,
        assertions: &str,
    ) -> Result<CheckSatResult, SolverError> {
        match &mut self.backend {
            IncrementalBackend::Pipe(pipe) => pipe.check_sat_incremental(assertions),
            #[cfg(feature = "z4-library")]
            IncrementalBackend::Library(solver) => {
                use z4_dpll::api::SolveResult;

                // Native push — no text parsing needed
                solver
                    .try_push()
                    .map_err(|e| SolverError::SolverError(format!("{e}")))?;

                // Parse and assert the bound constraint (still text since the
                // optimization loop constructs assertions as SMT-LIB strings)
                if !assertions.trim().is_empty() {
                    solver
                        .parse_smtlib2(assertions)
                        .map_err(|e| SolverError::SolverError(format!("parse error: {e}")))?;
                }

                // Native check-sat — respects Solver::set_timeout()
                match solver.check_sat().result() {
                    SolveResult::Sat => Ok(CheckSatResult::Sat),
                    SolveResult::Unsat => Ok(CheckSatResult::Unsat),
                    SolveResult::Unknown | _ => Ok(CheckSatResult::Unknown),
                }
            }
        }
    }

    /// Pop the most recent scope.
    pub(crate) fn pop(&mut self) -> Result<(), SolverError> {
        match &mut self.backend {
            IncrementalBackend::Pipe(pipe) => pipe.pop(),
            #[cfg(feature = "z4-library")]
            IncrementalBackend::Library(solver) => solver
                .try_pop()
                .map_err(|e| SolverError::SolverError(format!("{e}"))),
        }
    }

    /// Query variable values after a successful check-sat.
    pub(crate) fn get_value(&mut self, vars: &str) -> Result<HashMap<String, String>, SolverError> {
        match &mut self.backend {
            IncrementalBackend::Pipe(pipe) => pipe.get_value(vars),
            #[cfg(feature = "z4-library")]
            IncrementalBackend::Library(solver) => {
                // Use the native Model API to extract values without text
                // round-tripping through (get-value (...)) serialization.
                let verified_model = solver.model().ok_or(SolverError::EmptyOutput)?;
                let model = verified_model.model();

                let mut result = HashMap::new();
                for var_name in vars.split_whitespace() {
                    if let Some(val) = model.int_val(var_name) {
                        // Format as SMT-LIB integer for compatibility with
                        // parse_smt_int: negative uses (- N) syntax.
                        use num_traits::Signed;
                        if val.is_negative() {
                            result.insert(var_name.to_string(), format!("(- {})", val.abs()));
                        } else {
                            result.insert(var_name.to_string(), val.to_string());
                        }
                    } else if let Some(val) = model.bool_val(var_name) {
                        result.insert(var_name.to_string(), val.to_string());
                    } else if let Some(val) = model.real_val(var_name) {
                        // Format BigRational for SMT-LIB
                        use num_traits::ToPrimitive;
                        if let Some(f) = val.to_f64() {
                            result.insert(var_name.to_string(), format!("{f}"));
                        }
                    }
                    // Skip variables not in model (solver may assign defaults)
                }
                Ok(result)
            }
        }
    }
}

impl Drop for IncrementalSolver {
    fn drop(&mut self) {
        match &mut self.backend {
            IncrementalBackend::Pipe(pipe) => pipe.shutdown(),
            #[cfg(feature = "z4-library")]
            IncrementalBackend::Library(_) => {} // no cleanup needed
        }
    }
}
