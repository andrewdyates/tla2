// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Optimization loop for the solve-cp subcommand: binary-probe-guided
// incremental search over the objective domain.

use std::io::Write;
use std::time::{Duration, Instant};

use anyhow::Result;
use z4_cp::engine::CpSolveResult;
use z4_flatzinc_parser::ast::*;

use super::search_annotations::apply_search_annotations;
use super::CpContext;

/// Minimum objective range width to trigger binary search probing.
/// Below this threshold, linear search is more efficient.
const BINARY_PROBE_THRESHOLD: i64 = 20;

/// Maximum number of binary search probing steps per solution.
const MAX_BINARY_PROBES: usize = 15;

/// Per-probe timeout in milliseconds (short to avoid wasting time on hard probes).
const PROBE_TIMEOUT_MS: u64 = 200;

/// Solve an optimization model using binary-probe-guided incremental search.
///
/// After finding each solution, uses SAT-level binary probing to establish
/// a proven lower bound on the optimal value, then narrows the search range
/// with permanent constraints before resuming full CP-SAT optimization.
///
/// The binary probing uses SAT-level assumptions (without the CP extension)
/// to temporarily test bounds. UNSAT results from probing are sound (the
/// bound is definitely infeasible), while SAT results are used heuristically.
/// This lets us skip large swaths of the objective domain that are provably
/// infeasible, converting O(range) linear iterations into O(log range) probes
/// + a shorter linear tail.
///
/// Uses `deadline` as a global wall-clock limit: before each iteration,
/// checks remaining time and stops if expired, outputting the best solution
/// found so far.
pub(super) fn solve_optimization(
    model: &FznModel,
    obj_expr: &Expr,
    minimize: bool,
    deadline: Option<Instant>,
    out: &mut impl Write,
    err: &mut impl Write,
) -> Result<()> {
    let _ = writeln!(
        err,
        "info: {} objective via binary-probe-guided search",
        if minimize { "minimizing" } else { "maximizing" }
    );

    let mut ctx = CpContext::new();
    ctx.build_model(model)?;
    apply_search_annotations(&mut ctx, &model.solve.annotations);
    let obj_var = ctx.resolve_var(obj_expr)?;

    // Pre-compile constraints before setting timeout so encoding
    // overhead doesn't eat into the solve budget.
    ctx.engine.pre_compile();

    // Use set_deadline so the timer starts AFTER encoding inside each
    // solve() call, not during model building (#5683).
    if let Some(d) = deadline {
        ctx.engine.set_deadline(d);
    }

    // Register objective for persistent phase guidance via suggest_phase().
    // The CP extension will suggest optimal-direction phases for the objective
    // variable on every SAT decision, overriding phase-saving.
    ctx.engine.set_objective(obj_var, minimize);

    // Also set initial phase bias for the first solve (belt and suspenders:
    // suggest_phase handles subsequent decisions, but bias_objective_phase
    // sets the phase-save values that pick_phase uses as fallback).
    ctx.engine.bias_objective_phase(obj_var, minimize);

    let mut found_any = false;

    loop {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            if !found_any {
                writeln!(out, "=====UNKNOWN=====")?;
            }
            // Don't print ========== on timeout — optimality is not proven.
            // MiniZinc uses the last ---------- separated solution as best-known.
            return Ok(());
        }

        match ctx.engine.solve() {
            CpSolveResult::Sat(assignment) => {
                let obj_val = assignment
                    .iter()
                    .find(|(v, _)| *v == obj_var)
                    .map(|(_, val)| *val)
                    .expect("objective variable must be in assignment");

                found_any = true;
                let dzn = ctx.format_solution(&assignment);
                write!(out, "{dzn}")?;
                writeln!(out, "----------")?;

                if objective_reached_global_extreme(obj_val, minimize) {
                    writeln!(out, "==========")?;
                    return Ok(());
                }
                tighten_search_after_solution(&mut ctx, obj_var, obj_val, minimize);

                // Binary probing: narrow the search range using SAT-level
                // assumptions to quickly identify infeasible objective regions.
                // Only probe when the remaining range is large enough to benefit.
                let (domain_lb, domain_ub) = ctx.engine.var_bounds(obj_var);
                let remaining_range = if minimize {
                    obj_val - 1 - domain_lb
                } else {
                    domain_ub - (obj_val + 1)
                };

                if remaining_range >= BINARY_PROBE_THRESHOLD {
                    binary_probe_and_commit(
                        &mut ctx, obj_var, obj_val, minimize, deadline, domain_lb, domain_ub, err,
                    );
                }

                // Phase 2 optimization: boost objective variable activity,
                // biasing CDCL decisions toward the objective frontier where
                // improvements are most likely found.
                ctx.engine.boost_objective(obj_var, obj_val, minimize);

                // Phase 2 optimization: solution-guided phase saving.
                // Set SAT variable phases to match the current best solution
                // so that on restarts, the solver first tries values from the
                // best-known solution and then branches away to explore
                // improvements — focusing search near known-good regions.
                ctx.engine.set_solution_phases(&assignment);

                // The deadline is stored in the engine; solve() handles
                // clearing the interrupt and setting a fresh timer after
                // encoding on each iteration (#5683).
            }
            CpSolveResult::Unsat => {
                if found_any {
                    // Tightened bound is infeasible — previous solution is optimal.
                    writeln!(out, "==========")?;
                } else {
                    writeln!(out, "=====UNSATISFIABLE=====")?;
                }
                return Ok(());
            }
            CpSolveResult::Unknown | _ => {
                if !found_any {
                    writeln!(out, "=====UNKNOWN=====")?;
                }
                // Don't print ========== on Unknown — optimality is not proven.
                return Ok(());
            }
        }
    }
}

/// Run binary probing and commit proven bounds.
fn binary_probe_and_commit(
    ctx: &mut CpContext,
    obj_var: z4_cp::variable::IntVarId,
    obj_val: i64,
    minimize: bool,
    deadline: Option<Instant>,
    domain_lb: i64,
    domain_ub: i64,
    err: &mut impl Write,
) {
    // Spend up to 10% of remaining time on probing, or use
    // the fixed probe timeout — whichever is smaller.
    let probe_timeout = if let Some(dl) = deadline {
        let remaining = dl.saturating_duration_since(Instant::now());
        let budget = remaining / 10;
        Duration::from_millis(PROBE_TIMEOUT_MS).min(budget)
    } else {
        Duration::from_millis(PROBE_TIMEOUT_MS)
    };

    if probe_timeout.is_zero() {
        return;
    }

    let proven = ctx.engine.binary_probe_lower_bound(
        obj_var,
        obj_val,
        minimize,
        MAX_BINARY_PROBES,
        probe_timeout,
    );

    // Commit the proven bound to permanently narrow the range.
    if minimize && proven > domain_lb {
        ctx.engine.add_lower_bound(obj_var, proven);
        let _ = writeln!(
            err,
            "info: binary probe: obj >= {proven} (narrowed from {domain_lb})",
        );
    } else if !minimize && proven < domain_ub {
        ctx.engine.add_upper_bound(obj_var, proven);
        let _ = writeln!(
            err,
            "info: binary probe: obj <= {proven} (narrowed from {domain_ub})",
        );
    }
}

fn objective_reached_global_extreme(obj_val: i64, minimize: bool) -> bool {
    (minimize && obj_val == i64::MIN) || (!minimize && obj_val == i64::MAX)
}

fn tighten_search_after_solution(
    ctx: &mut CpContext,
    obj_var: z4_cp::variable::IntVarId,
    obj_val: i64,
    minimize: bool,
) {
    if minimize {
        if let Some(next) = obj_val.checked_sub(1) {
            ctx.engine.add_upper_bound(obj_var, next);
        }
    } else if let Some(next) = obj_val.checked_add(1) {
        ctx.engine.add_lower_bound(obj_var, next);
    }
}
