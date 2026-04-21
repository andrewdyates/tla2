// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// SMT solver driver for FlatZinc solving (Phase 4: optimization loop)

use std::collections::HashMap;
use std::io::{self, BufRead, Write};
use std::process::{Child, ChildStdout, Command, Stdio};
use std::time::{Duration, Instant};

use crate::output::format_dzn_solution;
use crate::translate::{SmtInt, TranslationResult, VarDomain};

mod error;
mod execution;
mod incremental;
mod optimization;
mod parse;
mod satisfaction;
#[cfg(test)]
mod tests;

pub use error::SolverError;
pub use parse::{parse_get_value, parse_smt_int};

pub(crate) use execution::{extract_reason_unknown, parse_z4_output, run_z4};
pub(crate) use incremental::IncrementalSolver;
use satisfaction::build_output_get_value;

/// Configuration for the SMT solver subprocess.
pub struct SolverConfig {
    /// Path to z4 binary.
    pub z4_path: String,
    /// Timeout per check-sat call in milliseconds (None = no timeout).
    pub timeout_ms: Option<u64>,
    /// Enumerate all solutions for satisfaction problems (MiniZinc `-a` flag).
    /// For optimization problems this has no additional effect.
    pub all_solutions: bool,
    /// Global wall-clock deadline for the entire solve (set from `-t` flag).
    /// When set, optimization loops check remaining time before each probe
    /// and stop when the deadline is reached.
    pub global_deadline: Option<Instant>,
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            z4_path: "z4".into(),
            timeout_ms: None,
            all_solutions: false,
            global_deadline: None,
        }
    }
}

/// Maximum per-call timeout cap (60 seconds) for optimization probes
/// when a global deadline is set.
const MAX_PER_CALL_TIMEOUT_MS: u64 = 60_000;

impl SolverConfig {
    /// Check if the global deadline has been reached.
    pub(crate) fn deadline_expired(&self) -> bool {
        self.global_deadline.is_some_and(|d| Instant::now() >= d)
    }

    /// Compute a per-call timeout that respects the global deadline.
    ///
    /// Returns a config with `timeout_ms` set to `min(remaining_time / 2, 60s)`.
    /// If no global deadline is set, returns the original timeout_ms unchanged.
    pub(crate) fn with_deadline_timeout(&self) -> Self {
        let timeout_ms = match self.global_deadline {
            Some(deadline) => {
                let remaining = deadline.saturating_duration_since(Instant::now());
                let half_remaining = remaining.as_millis() as u64 / 2;
                let capped = half_remaining.min(MAX_PER_CALL_TIMEOUT_MS);
                // Use the tighter of the two: original timeout or deadline-based
                match self.timeout_ms {
                    Some(orig) => Some(orig.min(capped)),
                    None => Some(capped),
                }
            }
            None => self.timeout_ms,
        };
        Self {
            z4_path: self.z4_path.clone(),
            timeout_ms,
            all_solutions: self.all_solutions,
            global_deadline: self.global_deadline,
        }
    }
}

/// Outcome of a single check-sat call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckSatResult {
    Sat,
    Unsat,
    Unknown,
}

/// Solve a FlatZinc model via z4 and print solutions to stdout.
///
/// For satisfaction problems: prints one solution + "----------".
/// For optimization problems: iteratively tightens the bound,
/// printing each improving solution + "----------", then "==========" when
/// optimality is proved (or best-found if interrupted).
///
/// Returns the number of solutions found.
pub fn solve(
    result: &TranslationResult,
    config: &SolverConfig,
    out: &mut dyn Write,
) -> Result<usize, SolverError> {
    if result.objective.is_some() {
        optimization::solve_optimization(result, config, out)
    } else {
        satisfaction::solve_satisfaction(result, config, out)
    }
}
