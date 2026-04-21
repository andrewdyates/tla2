// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Optimization via binary search on the objective bound.
///
/// Strategy: find first feasible solution, then binary-search between the
/// domain bound and the current best to minimize (or maximize) efficiently.
/// Optimization via exponential tightening + binary search.
///
/// Tries IncrementalSolver first (push/pop reuses declarations and learned
/// clauses across probes). Falls back to one-shot solving when the incremental
/// backend is unavailable (PipeBuffering on non-library builds).
pub(super) fn solve_optimization(
    result: &TranslationResult,
    config: &SolverConfig,
    out: &mut dyn Write,
) -> Result<usize, SolverError> {
    match IncrementalSolver::new(config, &result.declarations) {
        Ok(solver) => solve_optimization_incremental(result, config, solver, out),
        Err(SolverError::PipeBuffering) => solve_optimization_oneshot(result, config, out),
        Err(e) => Err(e),
    }
}

/// Incremental optimization: declarations loaded once, each probe uses push/pop.
///
/// Benefits over oneshot:
/// - Declarations parsed once (not re-sent per probe)
/// - z4 reuses learned clauses across bound-tightening probes
/// - With z4-library: eliminates subprocess overhead (~8ms per call)
fn solve_optimization_incremental(
    result: &TranslationResult,
    config: &SolverConfig,
    mut solver: IncrementalSolver,
    out: &mut dyn Write,
) -> Result<usize, SolverError> {
    let obj = result
        .objective
        .as_ref()
        .expect("called solve_optimization without objective");

    // Combined get-value variable list: output vars + objective.
    let mut query_vars = result.output_smt_names.clone();
    if !query_vars.contains(&obj.smt_expr) {
        query_vars.push(obj.smt_expr.clone());
    }
    let vars_str = query_vars.join(" ");

    let mut solutions_found = 0;

    // Phase 1: Find first feasible solution (no objective bound).
    let status = solver.check_sat_incremental("")?;
    let first_obj_val = match status {
        CheckSatResult::Sat => {
            let values = solver.get_value(&vars_str)?;
            solver.pop()?;

            let dzn = format_dzn_solution(&values, &result.output_vars);
            write!(out, "{dzn}")?;
            writeln!(out, "----------")?;
            out.flush()?;
            solutions_found += 1;

            let obj_val = values
                .get(&obj.smt_expr)
                .ok_or_else(|| SolverError::MissingObjective(obj.smt_expr.clone()))?;
            parse_smt_int(obj_val)?
        }
        CheckSatResult::Unsat => {
            solver.pop()?;
            writeln!(out, "=====UNSATISFIABLE=====")?;
            out.flush()?;
            return Ok(0);
        }
        CheckSatResult::Unknown => {
            solver.pop()?;
            writeln!(out, "=====UNKNOWN=====")?;
            out.flush()?;
            return Ok(0);
        }
    };

    let mut best_val = first_obj_val;
    let (domain_lo, domain_hi) = objective_domain_bounds(result, obj);
    let mut step: i64 = 1;
    let mut optimality_proven = false;

    'outer: loop {
        // Check global deadline before each probe.
        if config.deadline_expired() {
            break;
        }

        let target = if obj.minimize {
            best_val.saturating_sub(step).max(domain_lo)
        } else {
            best_val.saturating_add(step).min(domain_hi)
        };

        if (obj.minimize && target >= best_val) || (!obj.minimize && target <= best_val) {
            optimality_proven = true;
            break;
        }

        let bound_assertion = if obj.minimize {
            format!("(assert (<= {} {}))\n", obj.smt_expr, SmtInt(target))
        } else {
            format!("(assert (>= {} {}))\n", obj.smt_expr, SmtInt(target))
        };

        let status = solver.check_sat_incremental(&bound_assertion)?;
        match status {
            CheckSatResult::Sat => {
                let values = solver.get_value(&vars_str)?;
                solver.pop()?;

                let obj_val = values
                    .get(&obj.smt_expr)
                    .ok_or_else(|| SolverError::MissingObjective(obj.smt_expr.clone()))?;
                let found_val = parse_smt_int(obj_val)?;

                if (obj.minimize && found_val < best_val) || (!obj.minimize && found_val > best_val)
                {
                    best_val = found_val;
                    let dzn = format_dzn_solution(&values, &result.output_vars);
                    write!(out, "{dzn}")?;
                    writeln!(out, "----------")?;
                    out.flush()?;
                    solutions_found += 1;
                }

                step = step.saturating_mul(2);
            }
            CheckSatResult::Unsat => {
                solver.pop()?;

                // Binary search in [target+1, best-1] (minimize) or
                // [best+1, target-1] (maximize). Skip already-proven UNSAT target.
                let (mut lo, mut hi) = if obj.minimize {
                    (target + 1, best_val - 1)
                } else {
                    (best_val + 1, target - 1)
                };

                while lo <= hi {
                    // Check deadline before each binary search probe.
                    if config.deadline_expired() {
                        break 'outer;
                    }

                    let mid = lo + (hi - lo) / 2;
                    let bound = if obj.minimize {
                        format!("(assert (<= {} {}))\n", obj.smt_expr, SmtInt(mid))
                    } else {
                        format!("(assert (>= {} {}))\n", obj.smt_expr, SmtInt(mid))
                    };

                    let status = solver.check_sat_incremental(&bound)?;
                    match status {
                        CheckSatResult::Sat => {
                            let values = solver.get_value(&vars_str)?;
                            solver.pop()?;

                            let obj_val = values.get(&obj.smt_expr).ok_or_else(|| {
                                SolverError::MissingObjective(obj.smt_expr.clone())
                            })?;
                            let found_val = parse_smt_int(obj_val)?;

                            if (obj.minimize && found_val < best_val)
                                || (!obj.minimize && found_val > best_val)
                            {
                                best_val = found_val;
                                let dzn = format_dzn_solution(&values, &result.output_vars);
                                write!(out, "{dzn}")?;
                                writeln!(out, "----------")?;
                                out.flush()?;
                                solutions_found += 1;
                            }
                            if obj.minimize {
                                hi = found_val - 1;
                            } else {
                                lo = found_val + 1;
                            }
                        }
                        CheckSatResult::Unsat => {
                            solver.pop()?;
                            if obj.minimize {
                                lo = mid + 1;
                            } else {
                                hi = mid - 1;
                            }
                        }
                        CheckSatResult::Unknown => {
                            solver.pop()?;
                            break 'outer;
                        }
                    }
                }
                optimality_proven = true;
                break;
            }
            CheckSatResult::Unknown => {
                solver.pop()?;
                break;
            }
        }
    }

    if optimality_proven {
        writeln!(out, "==========")?;
        out.flush()?;
    }

    Ok(solutions_found)
}

/// One-shot optimization fallback: each probe sends full declarations + bound.
///
/// Used when IncrementalSolver is unavailable (PipeBuffering error on
/// non-library builds where z4 buffers all stdin before processing).
fn solve_optimization_oneshot(
    result: &TranslationResult,
    config: &SolverConfig,
    out: &mut dyn Write,
) -> Result<usize, SolverError> {
    let obj = result
        .objective
        .as_ref()
        .expect("called solve_optimization without objective");

    let get_value_cmd = build_output_get_value(result);
    let obj_get_value = format!("(get-value ({}))\n", obj.smt_expr);

    let mut solutions_found = 0;
    let mut buf = String::with_capacity(result.declarations.len() + 4096);

    // Phase 1: Find first feasible solution (no objective bound).
    let first_obj_val;
    {
        buf.clear();
        buf.push_str(&result.declarations);
        buf.push_str("(check-sat)\n");
        buf.push_str(&get_value_cmd);
        buf.push_str(&obj_get_value);
        buf.push_str("(get-info :reason-unknown)\n");

        let output = run_z4(&buf, config)?;
        let (status, lines) = parse_z4_output(&output)?;

        match status {
            CheckSatResult::Sat => {
                let values = parse_get_value(&lines)?;
                let dzn = format_dzn_solution(&values, &result.output_vars);
                write!(out, "{dzn}")?;
                writeln!(out, "----------")?;
                out.flush()?;
                solutions_found += 1;

                let obj_val = values
                    .get(&obj.smt_expr)
                    .ok_or_else(|| SolverError::MissingObjective(obj.smt_expr.clone()))?;
                first_obj_val = parse_smt_int(obj_val)?;
            }
            CheckSatResult::Unsat => {
                writeln!(out, "=====UNSATISFIABLE=====")?;
                out.flush()?;
                return Ok(0);
            }
            CheckSatResult::Unknown => {
                let reason = extract_reason_unknown(&lines);
                writeln!(out, "=====UNKNOWN=====")?;
                if let Some(r) = reason {
                    writeln!(out, "% reason-unknown: {r}")?;
                }
                out.flush()?;
                return Ok(0);
            }
        }
    }

    let mut best_val = first_obj_val;

    let (domain_lo, domain_hi) = objective_domain_bounds(result, obj);
    let mut step: i64 = 1;
    let mut optimality_proven = false;

    'outer: loop {
        // Check global deadline before each probe.
        if config.deadline_expired() {
            break;
        }

        let target = if obj.minimize {
            best_val.saturating_sub(step).max(domain_lo)
        } else {
            best_val.saturating_add(step).min(domain_hi)
        };

        if (obj.minimize && target >= best_val) || (!obj.minimize && target <= best_val) {
            optimality_proven = true;
            break;
        }

        let bound_assertion = if obj.minimize {
            format!("(assert (<= {} {}))\n", obj.smt_expr, SmtInt(target))
        } else {
            format!("(assert (>= {} {}))\n", obj.smt_expr, SmtInt(target))
        };

        buf.clear();
        buf.push_str(&result.declarations);
        buf.push_str(&bound_assertion);
        buf.push_str("(check-sat)\n");
        buf.push_str(&get_value_cmd);
        buf.push_str(&obj_get_value);
        buf.push_str("(get-info :reason-unknown)\n");

        // Use deadline-aware per-call timeout: min(remaining/2, 60s).
        let probe_config = config.with_deadline_timeout();
        let output = run_z4(&buf, &probe_config)?;
        let (status, lines) = parse_z4_output(&output)?;

        match status {
            CheckSatResult::Sat => {
                let values = parse_get_value(&lines)?;
                let obj_val = values
                    .get(&obj.smt_expr)
                    .ok_or_else(|| SolverError::MissingObjective(obj.smt_expr.clone()))?;
                let found_val = parse_smt_int(obj_val)?;

                let is_better = if obj.minimize {
                    found_val < best_val
                } else {
                    found_val > best_val
                };
                if is_better {
                    best_val = found_val;
                    let dzn = format_dzn_solution(&values, &result.output_vars);
                    write!(out, "{dzn}")?;
                    writeln!(out, "----------")?;
                    out.flush()?;
                    solutions_found += 1;
                }

                step = step.saturating_mul(2);
            }
            CheckSatResult::Unsat => {
                // Skip already-proven UNSAT target value.
                let (mut lo, mut hi) = if obj.minimize {
                    (target + 1, best_val - 1)
                } else {
                    (best_val + 1, target - 1)
                };

                while lo <= hi {
                    // Check deadline before each binary search probe.
                    if config.deadline_expired() {
                        break 'outer;
                    }

                    let mid = lo + (hi - lo) / 2;

                    let bound = if obj.minimize {
                        format!("(assert (<= {} {}))\n", obj.smt_expr, SmtInt(mid))
                    } else {
                        format!("(assert (>= {} {}))\n", obj.smt_expr, SmtInt(mid))
                    };

                    buf.clear();
                    buf.push_str(&result.declarations);
                    buf.push_str(&bound);
                    buf.push_str("(check-sat)\n");
                    buf.push_str(&get_value_cmd);
                    buf.push_str(&obj_get_value);
                    buf.push_str("(get-info :reason-unknown)\n");

                    let probe_config = config.with_deadline_timeout();
                    let output = run_z4(&buf, &probe_config)?;
                    let (status, lines) = parse_z4_output(&output)?;

                    match status {
                        CheckSatResult::Sat => {
                            let values = parse_get_value(&lines)?;
                            let obj_val = values.get(&obj.smt_expr).ok_or_else(|| {
                                SolverError::MissingObjective(obj.smt_expr.clone())
                            })?;
                            let found_val = parse_smt_int(obj_val)?;

                            if (obj.minimize && found_val < best_val)
                                || (!obj.minimize && found_val > best_val)
                            {
                                best_val = found_val;
                                let dzn = format_dzn_solution(&values, &result.output_vars);
                                write!(out, "{dzn}")?;
                                writeln!(out, "----------")?;
                                out.flush()?;
                                solutions_found += 1;
                            }
                            if obj.minimize {
                                hi = found_val - 1;
                            } else {
                                lo = found_val + 1;
                            }
                        }
                        CheckSatResult::Unsat => {
                            if obj.minimize {
                                lo = mid + 1;
                            } else {
                                hi = mid - 1;
                            }
                        }
                        CheckSatResult::Unknown => break 'outer,
                    }
                }
                optimality_proven = true;
                break;
            }
            CheckSatResult::Unknown => {
                let reason = extract_reason_unknown(&lines);
                if let Some(r) = reason {
                    writeln!(out, "% reason-unknown: {r}")?;
                    out.flush()?;
                }
                break;
            }
        }
    }

    if optimality_proven {
        writeln!(out, "==========")?;
        out.flush()?;
    }

    Ok(solutions_found)
}

/// Get the lower and upper domain bounds for the objective variable.
///
/// Looks up the objective's SMT expression in `var_domains`. Falls back to
/// conservative defaults (i32 range) if no domain info is available.
fn objective_domain_bounds(
    result: &TranslationResult,
    obj: &crate::translate::ObjectiveInfo,
) -> (i64, i64) {
    if let Some(domain) = result.var_domains.get(&obj.smt_expr) {
        match domain {
            VarDomain::IntRange(lo, hi) => (*lo, *hi),
            VarDomain::IntSet(vals) => {
                let lo = vals.iter().copied().min().unwrap_or(i64::from(i32::MIN));
                let hi = vals.iter().copied().max().unwrap_or(i64::from(i32::MAX));
                (lo, hi)
            }
            VarDomain::Bool => (0, 1),
            VarDomain::IntUnbounded => (i64::from(i32::MIN), i64::from(i32::MAX)),
        }
    } else {
        // No domain info — use conservative range.
        (i64::from(i32::MIN), i64::from(i32::MAX))
    }
}
