// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// solve-cp: Direct CP-SAT solving of FlatZinc models via z4-cp.
//
// Translates FlatZinc constraints directly to z4-cp's Constraint types
// and solves using the Lazy Clause Generation CP-SAT engine, bypassing
// the SMT-LIB translation layer entirely.

use std::collections::HashMap;
use std::io::{self, Write};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use anyhow::Result;
use z4_cp::engine::CpSolveResult;
use z4_cp::search::{SearchStrategy, ValueChoice};
use z4_cp::variable::IntVarId;
use z4_cp::{CpSatEngine, Domain};
use z4_flatzinc_parser::ast::*;

mod constraints;
mod constraints_circuit;
mod constraints_counting;
mod constraints_global;
mod constraints_lex;
mod constraints_nonlinear;
mod constraints_reif;
mod constraints_set;
mod constraints_table;
mod detect_disjunctive;
mod opt_loop;
mod output;
mod search_annotations;
mod variables;

use search_annotations::apply_search_annotations;

#[derive(Clone, Copy)]
struct PortfolioWorkerConfig {
    strategy: Option<SearchStrategy>,
    value_choice: Option<ValueChoice>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SolveCpStatus {
    Sat,
    Unsat,
    Unknown,
}

struct SolveCpReport {
    status: SolveCpStatus,
    stdout: Vec<u8>,
}

const PORTFOLIO_WORKERS: [PortfolioWorkerConfig; 5] = [
    PortfolioWorkerConfig {
        strategy: None,
        value_choice: None,
    },
    PortfolioWorkerConfig {
        strategy: Some(SearchStrategy::Activity),
        value_choice: Some(ValueChoice::IndomainSplit),
    },
    PortfolioWorkerConfig {
        strategy: Some(SearchStrategy::FirstFail),
        value_choice: Some(ValueChoice::IndomainMin),
    },
    PortfolioWorkerConfig {
        strategy: Some(SearchStrategy::InputOrder),
        value_choice: Some(ValueChoice::IndomainMin),
    },
    PortfolioWorkerConfig {
        strategy: Some(SearchStrategy::DomWDeg),
        value_choice: Some(ValueChoice::IndomainReverseSplit),
    },
];

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_benchmarks;
#[cfg(test)]
mod tests_false_unsat;
#[cfg(test)]
mod tests_global;
#[cfg(test)]
mod tests_nonlinear;
#[cfg(test)]
mod tests_ordering;

/// Entry point for the `solve-cp` subcommand.
pub(crate) fn cmd_solve_cp(
    model: &FznModel,
    timeout_ms: Option<u64>,
    all_solutions: bool,
    parallel_workers: usize,
    prechecked_unsupported: Option<&[String]>,
) -> Result<()> {
    // Reuse a caller-provided probe when the CLI already performed one.
    if let Some(unsupported) = prechecked_unsupported {
        if !unsupported.is_empty() {
            let mut out = io::stdout().lock();
            let mut err = io::stderr().lock();
            for name in unsupported {
                let _ = writeln!(err, "warning: unsupported constraint: {name}");
            }
            writeln!(out, "=====UNKNOWN=====")?;
            return Ok(());
        }
    } else {
        let unsupported = unsupported_constraints(model)?;
        if !unsupported.is_empty() {
            let mut out = io::stdout().lock();
            let mut err = io::stderr().lock();
            for name in &unsupported {
                let _ = writeln!(err, "warning: unsupported constraint: {name}");
            }
            writeln!(out, "=====UNKNOWN=====")?;
            return Ok(());
        }
    }

    let deadline = timeout_ms.map(|ms| Instant::now() + Duration::from_millis(ms));
    let mut out = io::stdout().lock();
    let mut err = io::stderr().lock();

    match &model.solve.kind {
        SolveKind::Satisfy => {
            if parallel_workers > 1 && !all_solutions {
                solve_satisfaction_parallel(model, deadline, parallel_workers, &mut out)?;
                return Ok(());
            }
            if parallel_workers > 1 && all_solutions {
                writeln!(
                    err,
                    "info: solve-cp -p uses a single worker when -a/--all-solutions is set"
                )?;
            }
            let mut ctx = CpContext::new();
            ctx.build_model(model)?;
            apply_search_annotations(&mut ctx, &model.solve.annotations);
            ctx.set_default_search_vars_if_missing();
            // Pre-compile constraints before setting timeout so encoding
            // overhead doesn't eat into the solve budget.
            ctx.engine.pre_compile();
            if let Some(dl) = deadline {
                // Use set_deadline so the timer starts AFTER encoding,
                // not during model building (#5683).
                ctx.engine.set_deadline(dl);
            }
            let _ = solve_satisfaction(&mut ctx, all_solutions, deadline, &mut out)?;
        }
        SolveKind::Minimize(ref expr) | SolveKind::Maximize(ref expr) => {
            if parallel_workers > 1 {
                writeln!(
                    err,
                    "info: solve-cp -p currently parallelizes only satisfaction models; using a single worker for optimization"
                )?;
            }
            let minimize = matches!(model.solve.kind, SolveKind::Minimize(_));
            opt_loop::solve_optimization(model, expr, minimize, deadline, &mut out, &mut err)?;
        }
    }

    Ok(())
}

pub(crate) fn unsupported_constraints(model: &FznModel) -> Result<Vec<String>> {
    let mut probe = CpContext::new();
    probe.build_model(model)?;
    Ok(probe.unsupported)
}

/// Solve a satisfaction model, optionally enumerating all solutions.
fn solve_satisfaction(
    ctx: &mut CpContext,
    all_solutions: bool,
    deadline: Option<Instant>,
    out: &mut impl Write,
) -> Result<SolveCpStatus> {
    let mut found_any = false;

    loop {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            if !found_any {
                writeln!(out, "=====UNKNOWN=====")?;
                return Ok(SolveCpStatus::Unknown);
            }
            // Don't print ========== on timeout during all-solutions:
            // we haven't proven all solutions were enumerated.
            return Ok(SolveCpStatus::Sat);
        }

        match ctx.engine.solve() {
            CpSolveResult::Sat(assignment) => {
                found_any = true;
                let dzn = ctx.format_solution(&assignment);
                write!(out, "{dzn}")?;
                writeln!(out, "----------")?;

                if !all_solutions {
                    writeln!(out, "==========")?;
                    return Ok(SolveCpStatus::Sat);
                }

                // Block this solution and search for the next one.
                // Use only output variables for the blocking clause so
                // internal auxiliary variables don't overconstrain.
                let output_assignment: Vec<_> = ctx
                    .output_var_ids()
                    .iter()
                    .filter_map(|&id| {
                        assignment
                            .iter()
                            .find(|(v, _)| *v == id)
                            .map(|&(v, val)| (v, val))
                    })
                    .collect();
                ctx.engine.block_assignment(&output_assignment);
            }
            CpSolveResult::Unsat => {
                if found_any {
                    // All solutions enumerated — search exhausted.
                    writeln!(out, "==========")?;
                    return Ok(SolveCpStatus::Sat);
                } else {
                    writeln!(out, "=====UNSATISFIABLE=====")?;
                    return Ok(SolveCpStatus::Unsat);
                }
            }
            CpSolveResult::Unknown | _ => {
                if !found_any {
                    writeln!(out, "=====UNKNOWN=====")?;
                    return Ok(SolveCpStatus::Unknown);
                }
                // Don't print ========== on Unknown — search is incomplete.
                return Ok(SolveCpStatus::Sat);
            }
        }
    }
}

fn apply_portfolio_config(ctx: &mut CpContext, config: PortfolioWorkerConfig) {
    if let Some(strategy) = config.strategy {
        ctx.engine.set_search_strategy(strategy);
    }
    if let Some(value_choice) = config.value_choice {
        ctx.engine.set_value_choice(value_choice);
    }
}

fn run_satisfaction_worker(
    model: &FznModel,
    deadline: Option<Instant>,
    config: PortfolioWorkerConfig,
) -> Result<SolveCpReport> {
    let mut ctx = CpContext::new();
    ctx.build_model(model)?;
    apply_search_annotations(&mut ctx, &model.solve.annotations);
    ctx.set_default_search_vars_if_missing();
    apply_portfolio_config(&mut ctx, config);
    ctx.engine.pre_compile();
    if let Some(dl) = deadline {
        ctx.engine.set_deadline(dl);
    }
    let mut stdout = Vec::new();
    let status = solve_satisfaction(&mut ctx, false, deadline, &mut stdout)?;
    Ok(SolveCpReport { status, stdout })
}

fn solve_satisfaction_parallel(
    model: &FznModel,
    deadline: Option<Instant>,
    parallel_workers: usize,
    out: &mut impl Write,
) -> Result<()> {
    let worker_count = parallel_workers.min(PORTFOLIO_WORKERS.len());
    let (tx, rx) = mpsc::channel();

    for &config in PORTFOLIO_WORKERS.iter().take(worker_count) {
        let tx = tx.clone();
        let model = model.clone();
        thread::spawn(move || {
            let _ = tx.send(run_satisfaction_worker(&model, deadline, config));
        });
    }
    drop(tx);

    let mut first_unknown: Option<SolveCpReport> = None;
    let mut first_err: Option<anyhow::Error> = None;

    for _ in 0..worker_count {
        match rx.recv() {
            Ok(Ok(report)) => match report.status {
                SolveCpStatus::Sat | SolveCpStatus::Unsat => {
                    out.write_all(&report.stdout)?;
                    return Ok(());
                }
                SolveCpStatus::Unknown => {
                    if first_unknown.is_none() {
                        first_unknown = Some(report);
                    }
                }
            },
            Ok(Err(err)) => {
                if first_err.is_none() {
                    first_err = Some(err);
                }
            }
            Err(_) => break,
        }
    }

    if let Some(report) = first_unknown {
        out.write_all(&report.stdout)?;
        return Ok(());
    }

    if let Some(err) = first_err {
        return Err(err);
    }

    writeln!(out, "=====UNKNOWN=====")?;
    Ok(())
}

/// Output variable info for DZN formatting.
pub(super) struct CpOutputVar {
    pub(super) fzn_name: String,
    pub(super) var_ids: Vec<IntVarId>,
    pub(super) is_array: bool,
    pub(super) array_range: Option<(i64, i64)>,
    pub(super) is_bool: bool,
    /// For set outputs: names of set variables (looked up in set_var_map).
    pub(super) set_var_names: Vec<String>,
}

/// Translation context: FlatZinc model → z4-cp constraints.
pub(super) struct CpContext {
    pub(super) engine: CpSatEngine,
    /// FlatZinc variable name → CP variable ID
    pub(super) var_map: HashMap<String, IntVarId>,
    /// FlatZinc array variable name → element CP variable IDs
    pub(super) array_var_map: HashMap<String, Vec<IntVarId>>,
    /// Integer parameter values
    pub(super) par_ints: HashMap<String, i64>,
    /// Integer array parameter values
    pub(super) par_int_arrays: HashMap<String, Vec<i64>>,
    /// Set parameter values (name → set expression: IntRange, SetLit, EmptySet)
    pub(super) par_sets: HashMap<String, Expr>,
    /// Cached singleton variables for constants
    pub(super) const_vars: HashMap<i64, IntVarId>,
    /// Variable domain bounds for Big-M reification encoding
    pub(super) var_bounds: HashMap<IntVarId, (i64, i64)>,
    /// Output variables for DZN formatting
    pub(super) output_vars: Vec<CpOutputVar>,
    /// Set variable: name → (lo_element, boolean indicator var IDs)
    pub(super) set_var_map: HashMap<String, (i64, Vec<IntVarId>)>,
    /// Parameter arrays of constant sets: name → list of element vectors
    pub(super) par_set_arrays: HashMap<String, Vec<Vec<i64>>>,
    /// Unsupported constraint names encountered
    pub(super) unsupported: Vec<String>,
}

impl CpContext {
    fn new() -> Self {
        Self {
            engine: CpSatEngine::new(),
            var_map: HashMap::new(),
            array_var_map: HashMap::new(),
            par_ints: HashMap::new(),
            par_int_arrays: HashMap::new(),
            par_sets: HashMap::new(),
            const_vars: HashMap::new(),
            var_bounds: HashMap::new(),
            output_vars: Vec::new(),
            set_var_map: HashMap::new(),
            par_set_arrays: HashMap::new(),
            unsupported: Vec::new(),
        }
    }

    fn build_model(&mut self, model: &FznModel) -> Result<()> {
        for par in &model.parameters {
            self.register_parameter(par);
        }
        for var in &model.variables {
            self.create_variable(var)?;
        }
        // Pre-scan for disjunctive scheduling patterns (jobshop).
        // Adds Constraint::Disjunctive propagators for each detected machine.
        // The int_lin_le_reif constraints are still translated normally below.
        self.detect_disjunctive(model);
        for constraint in &model.constraints {
            self.translate_constraint(constraint)?;
        }
        Ok(())
    }

    fn eval_const_int(&self, expr: &Expr) -> Option<i64> {
        match expr {
            Expr::Int(n) => Some(*n),
            Expr::Bool(b) => Some(i64::from(*b)),
            Expr::Ident(name) => self.par_ints.get(name).copied(),
            _ => None,
        }
    }

    /// Resolve an expression to an IntVarId (creates fixed vars for constants).
    fn resolve_var(&mut self, expr: &Expr) -> Result<IntVarId> {
        match expr {
            Expr::Ident(name) => {
                if let Some(&id) = self.var_map.get(name) {
                    Ok(id)
                } else if let Some(&v) = self.par_ints.get(name) {
                    Ok(self.get_const_var(v))
                } else {
                    anyhow::bail!("unknown variable or parameter: {name}")
                }
            }
            Expr::Int(n) => Ok(self.get_const_var(*n)),
            Expr::Bool(b) => Ok(self.get_const_var(i64::from(*b))),
            _ => anyhow::bail!("cannot resolve expression to variable: {expr:?}"),
        }
    }

    /// Resolve an expression to an array of IntVarIds.
    fn resolve_var_array(&mut self, expr: &Expr) -> Result<Vec<IntVarId>> {
        match expr {
            Expr::ArrayLit(elems) => elems.iter().map(|e| self.resolve_var(e)).collect(),
            Expr::Ident(name) => {
                if let Some(ids) = self.array_var_map.get(name).cloned() {
                    Ok(ids)
                } else if let Some(vals) = self.par_int_arrays.get(name).cloned() {
                    Ok(vals.iter().map(|&v| self.get_const_var(v)).collect())
                } else {
                    anyhow::bail!("cannot resolve identifier as array: {name}")
                }
            }
            _ => anyhow::bail!("expected array expression, got {expr:?}"),
        }
    }

    /// Resolve an expression to a constant integer.
    fn resolve_const_int(&self, expr: &Expr) -> Result<i64> {
        self.eval_const_int(expr)
            .ok_or_else(|| anyhow::anyhow!("expected constant integer, got {expr:?}"))
    }

    /// Resolve an expression to a constant integer array.
    fn resolve_const_int_array(&self, expr: &Expr) -> Result<Vec<i64>> {
        match expr {
            Expr::ArrayLit(elems) => elems.iter().map(|e| self.resolve_const_int(e)).collect(),
            Expr::Ident(name) => self
                .par_int_arrays
                .get(name)
                .cloned()
                .ok_or_else(|| anyhow::anyhow!("unknown int array parameter: {name}")),
            _ => anyhow::bail!("expected constant int array, got {expr:?}"),
        }
    }

    fn get_const_var(&mut self, val: i64) -> IntVarId {
        if let Some(&id) = self.const_vars.get(&val) {
            return id;
        }
        let id = self.engine.new_int_var(Domain::singleton(val), None);
        self.const_vars.insert(val, id);
        self.var_bounds.insert(id, (val, val));
        id
    }

    /// Get bounds for a variable (for Big-M reification encoding).
    pub(super) fn get_var_bounds(&self, var: IntVarId) -> (i64, i64) {
        self.var_bounds
            .get(&var)
            .copied()
            .unwrap_or((-1_000_000, 1_000_000))
    }

    /// Collect all output variable IDs for blocking clause construction.
    fn output_var_ids(&self) -> Vec<IntVarId> {
        let mut ids = Vec::new();
        for ov in &self.output_vars {
            ids.extend_from_slice(&ov.var_ids);
        }
        ids
    }

    /// When no search annotation is provided, use output variables as default
    /// search_vars. Without this, DomWDeg falls back to scanning ALL trail
    /// variables (including internal auxiliary vars), causing 100x+ slowdown
    /// on MiniZinc-compiled models that lack int_search annotations.
    pub(super) fn set_default_search_vars_if_missing(&mut self) {
        if self.engine.search_vars().is_empty() {
            let mut vars = Vec::new();
            for ov in &self.output_vars {
                if !ov.is_bool {
                    vars.extend_from_slice(&ov.var_ids);
                }
            }
            if !vars.is_empty() {
                self.engine.set_search_vars(vars);
            }
        }
    }

    fn mark_unsupported(&mut self, name: &str) {
        if !self.unsupported.contains(&name.to_string()) {
            self.unsupported.push(name.to_string());
        }
    }
}
