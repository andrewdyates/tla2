// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Solver driver: thin wrapper around z4_flatzinc_smt::solve().
//
// MiniZinc competition protocol:
//   - Print each solution followed by "----------"
//   - Print "==========" when optimality is proved or all solutions found
//   - Print "=====UNSATISFIABLE=====" if no solution exists
//   - Print "=====UNKNOWN=====" on timeout or inconclusive result
//   - Flush stdout after each solution (scoring uses best-found)

use std::io;
use std::time::{Duration, Instant};

use anyhow::Result;
use z4_flatzinc_smt::{SolverConfig, TranslationResult};

/// Solve a translated FlatZinc model by piping SMT-LIB2 to z4.
///
/// When `fd_search` is true, uses the branching solver that follows
/// FlatZinc search annotations (FD Search track). Otherwise uses the
/// one-shot solver (Free Search track).
///
/// When `all_solutions` is true and the problem is a satisfaction problem,
/// enumerates all solutions by adding blocking clauses after each one.
/// For optimization problems, `-a` has no additional effect (intermediate
/// solutions are already printed).
pub(crate) fn cmd_solve(
    result: &TranslationResult,
    z4_bin: &str,
    timeout_ms: Option<u64>,
    fd_search: bool,
    all_solutions: bool,
) -> Result<()> {
    let global_deadline = timeout_ms.map(|ms| Instant::now() + Duration::from_millis(ms));
    let config = SolverConfig {
        z4_path: z4_bin.to_string(),
        timeout_ms,
        all_solutions,
        global_deadline,
    };
    let mut out = io::stdout().lock();
    if fd_search {
        z4_flatzinc_smt::solve_branching(result, &config, &mut out)
            .map_err(|e| anyhow::anyhow!("solver error: {e}"))?;
    } else {
        z4_flatzinc_smt::solve(result, &config, &mut out)
            .map_err(|e| anyhow::anyhow!("solver error: {e}"))?;
    }
    Ok(())
}
