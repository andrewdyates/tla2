// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Z4-based symbolic simulation for TLA+ specs (Apalache Gap 9).
//!
//! Symbolic simulation explores state trajectories using z4 SMT solving to
//! resolve nondeterministic choices, rather than explicit-state enumeration.
//! Unlike BMC (which explores ALL paths up to depth k), symbolic simulation
//! follows ONE path per run, extracting a concrete witness at each step.
//!
//! # Algorithm
//!
//! For each simulation run:
//! 1. Encode `Init(s0)` and solve. Extract a concrete initial state.
//! 2. For step `i` (0..max_depth):
//!    a. Assert `Next(si, si+1)` symbolically.
//!    b. Ask the solver for a satisfying assignment (a concrete next-state).
//!    c. Check `Safety(si+1)`. If violated, return a counterexample.
//!    d. Assert the concrete state at step `i+1` to seed the next step.
//! 3. If no violation after `max_depth` steps, report "no violation in this run."
//!
//! # Key Difference from BMC
//!
//! BMC formula: `Init(s0) /\ Next(s0,s1) /\ ... /\ Next(sk-1,sk) /\ (NOT Safety(s0) \/ ... \/ NOT Safety(sk))`
//! (explores all k-deep paths simultaneously)
//!
//! Symbolic simulation: step-by-step solve-extract-advance loop
//! (follows one path, multiple runs with different solver choices find different paths)
//!
//! # Usage
//!
//! ```text
//! let config = SymbolicSimConfig { num_runs: 10, max_depth: 100, .. };
//! let result = symbolic_simulate(module, config, ctx, bmc_config)?;
//! ```
//!
//! Part of #3757 (Apalache Gap 9).

use rustc_hash::FxHashMap;
use std::collections::HashMap;
use std::time::{Duration, Instant};

use tla_core::ast::Module;
use tla_z4::{BmcState, BmcTranslator, BmcValue, Model, SolveResult, TlaSort, Z4Error};

use crate::check::CheckError;
use crate::config::Config;
use crate::eval::EvalCtx;
use crate::z4_pdr::expand_operators_for_chc;
use crate::z4_shared;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for symbolic simulation.
#[derive(Debug, Clone)]
pub struct SymbolicSimConfig {
    /// Number of independent simulation runs.
    pub num_runs: usize,
    /// Maximum depth (steps) per simulation run.
    pub max_depth: usize,
    /// Timeout for each individual solver call.
    pub solve_timeout: Option<Duration>,
    /// Overall wall-clock timeout for the entire simulation session.
    pub session_timeout: Option<Duration>,
    /// Enable debug logging to stderr.
    pub debug: bool,
}

impl Default for SymbolicSimConfig {
    fn default() -> Self {
        let timeout_secs: u64 = std::env::var("TLA2_SYMSIM_TIMEOUT_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(300);

        let num_runs: usize = std::env::var("TLA2_SYMSIM_RUNS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(10);

        let max_depth: usize = std::env::var("TLA2_SYMSIM_DEPTH")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(100);

        Self {
            num_runs,
            max_depth,
            solve_timeout: Some(Duration::from_secs(timeout_secs)),
            session_timeout: Some(Duration::from_secs(timeout_secs)),
            debug: debug_z4_symsim_enabled(),
        }
    }
}

debug_flag!(debug_z4_symsim_enabled, "TLA2_DEBUG_Z4_SYMSIM");

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

/// Result of a symbolic simulation session (multiple runs).
#[derive(Debug)]
pub enum SymbolicSimResult {
    /// At least one run found a safety violation.
    Violation {
        /// The simulation run index (0-based) that found the violation.
        run_index: usize,
        /// Depth at which the violation was found.
        depth: usize,
        /// Concrete counterexample trace.
        trace: Vec<BmcState>,
    },
    /// All runs completed without finding a violation.
    NoViolation {
        /// Number of runs completed.
        runs_completed: usize,
        /// Maximum depth reached across all runs.
        max_depth_reached: usize,
        /// Total number of states explored (sum across all runs).
        total_states: usize,
    },
    /// Session timed out before completing all runs.
    Timeout {
        /// Number of runs completed before timeout.
        runs_completed: usize,
        /// Total states explored before timeout.
        total_states: usize,
        /// Human-readable timeout reason.
        reason: String,
    },
}

/// Errors specific to symbolic simulation.
#[derive(Debug, thiserror::Error)]
pub enum SymbolicSimError {
    /// Missing Init or Next definition.
    #[error("Missing specification: {0}")]
    MissingSpec(String),
    /// No invariants configured.
    #[error("No invariants configured for symbolic simulation")]
    NoInvariants,
    /// Failed to translate the TLA+ expression.
    #[error("Translation failed: {0}")]
    TranslationError(String),
    /// Solver setup or execution failed.
    #[error("Solver failed: {0}")]
    SolverFailed(String),
    /// General checker error.
    #[error("Check error: {0:?}")]
    CheckError(#[from] CheckError),
}

impl From<Z4Error> for SymbolicSimError {
    fn from(err: Z4Error) -> Self {
        match err {
            Z4Error::Solver(inner) => SymbolicSimError::SolverFailed(inner.to_string()),
            other => SymbolicSimError::TranslationError(other.to_string()),
        }
    }
}

// ---------------------------------------------------------------------------
// Internal: single-step simulation state
// ---------------------------------------------------------------------------

/// Extract a concrete state from a BMC model at a given step.
///
/// Reads variable assignments from the SAT model and returns them as
/// `(name, BmcValue)` pairs suitable for `assert_concrete_state`.
fn extract_state_at_step(
    translator: &BmcTranslator,
    model: &Model,
    var_sorts: &[(String, TlaSort)],
    step: usize,
) -> BmcState {
    let trace = translator.extract_trace(model);
    // extract_trace returns states for all steps 0..=bound_k.
    // We need only the state at `step`.
    if step < trace.len() {
        trace.into_iter().nth(step).unwrap_or(BmcState {
            step,
            assignments: HashMap::new(),
        })
    } else {
        // Fallback: manually read from model using var_sorts.
        let mut assignments = HashMap::new();
        for (name, sort) in var_sorts {
            let step_name = format!("{name}__{step}");
            match sort {
                TlaSort::Bool => {
                    if let Some(val) = model.bool_val(&step_name) {
                        assignments.insert(name.clone(), BmcValue::Bool(val));
                    } else {
                        eprintln!(
                            "Warning: symbolic sim fallback: Bool variable '{name}' \
                             not found in model at step {step}"
                        );
                    }
                }
                TlaSort::Int | TlaSort::String => {
                    if let Some(val) = model.int_val(&step_name) {
                        if let Ok(v) = i64::try_from(val) {
                            assignments.insert(name.clone(), BmcValue::Int(v));
                        } else {
                            assignments.insert(name.clone(), BmcValue::BigInt(val.clone()));
                        }
                    } else {
                        eprintln!(
                            "Warning: symbolic sim fallback: Int variable '{name}' \
                             not found in model at step {step}"
                        );
                    }
                }
                _ => {
                    eprintln!(
                        "Warning: symbolic sim fallback: variable '{name}' has \
                         compound sort {sort} which is not yet supported (step {step})"
                    );
                }
            }
        }
        BmcState { step, assignments }
    }
}

// ---------------------------------------------------------------------------
// Single simulation run
// ---------------------------------------------------------------------------

/// Result of a single simulation run.
enum SingleRunResult {
    /// Found a violation at this depth with this trace.
    Violation { depth: usize, trace: Vec<BmcState> },
    /// Completed all steps without violation.
    NoViolation {
        max_depth_reached: usize,
        states_explored: usize,
    },
    /// Deadlock: Next has no satisfying successor.
    Deadlock {
        depth: usize,
        #[allow(dead_code)]
        trace: Vec<BmcState>,
    },
    /// Solver returned unknown or error.
    SolverInconclusive { depth: usize, reason: String },
}

/// Run a single symbolic simulation trace.
///
/// Creates a fresh solver for each run. Uses a 2-step sliding window:
/// at each depth, creates a translator with bound=1, seeds step 0 with
/// the current concrete state, translates Next(s0,s1), solves, extracts
/// the next concrete state at step 1, and repeats.
fn run_single_simulation(
    var_sorts: &[(String, TlaSort)],
    init_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    next_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    safety_expanded: &tla_core::Spanned<tla_core::ast::Expr>,
    config: &SymbolicSimConfig,
    run_index: usize,
) -> Result<SingleRunResult, SymbolicSimError> {
    let mut trace: Vec<BmcState> = Vec::new();

    // Phase 1: Find an initial state satisfying Init.
    let init_state = {
        let mut translator = z4_shared::make_translator(var_sorts, 0)?;
        translator.set_timeout(config.solve_timeout);
        for (name, sort) in var_sorts {
            translator.declare_var(name, sort.clone())?;
        }
        let init_term = translator.translate_init(init_expanded)?;
        translator.assert(init_term);

        match translator.try_check_sat()? {
            SolveResult::Sat => {
                let model = translator.try_get_model()?;
                extract_state_at_step(&translator, &model, var_sorts, 0)
            }
            SolveResult::Unsat(_) => {
                return Ok(SingleRunResult::SolverInconclusive {
                    depth: 0,
                    reason: "Init predicate is unsatisfiable".to_string(),
                });
            }
            _ => {
                return Ok(SingleRunResult::SolverInconclusive {
                    depth: 0,
                    reason: "Solver returned unknown for Init".to_string(),
                });
            }
        }
    };

    if config.debug {
        eprintln!(
            "[z4-symsim] run {}: init state has {} vars",
            run_index,
            init_state.assignments.len()
        );
    }

    trace.push(init_state);

    // Phase 2: Check if init state violates safety.
    {
        let mut checker = z4_shared::make_translator(var_sorts, 0)?;
        checker.set_timeout(config.solve_timeout);
        for (name, sort) in var_sorts {
            checker.declare_var(name, sort.clone())?;
        }
        let concrete: Vec<(String, BmcValue)> = trace[0]
            .assignments
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        checker.assert_concrete_state(&concrete, 0)?;
        let not_safety = checker.translate_not_safety_at_step(safety_expanded, 0)?;
        checker.assert(not_safety);

        if let SolveResult::Sat = checker.try_check_sat()? {
            return Ok(SingleRunResult::Violation { depth: 0, trace });
        }
    }

    // Phase 3: Step-by-step symbolic simulation.
    for depth in 0..config.max_depth {
        // Create a fresh translator with bound=1 for this single step.
        let mut translator = z4_shared::make_translator(var_sorts, 1)?;
        translator.set_timeout(config.solve_timeout);
        for (name, sort) in var_sorts {
            translator.declare_var(name, sort.clone())?;
        }

        // Assert the current concrete state at step 0.
        let current_state = trace.last().expect("trace non-empty");
        let concrete: Vec<(String, BmcValue)> = current_state
            .assignments
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        translator.assert_concrete_state(&concrete, 0)?;

        // Assert Next(s0, s1).
        let next_term = translator.translate_next(next_expanded, 0)?;
        translator.assert(next_term);

        // Solve for a next state.
        match translator.try_check_sat()? {
            SolveResult::Sat => {
                let model = translator.try_get_model()?;
                let mut next_state = extract_state_at_step(&translator, &model, var_sorts, 1);
                next_state.step = depth + 1;
                trace.push(next_state);
            }
            SolveResult::Unsat(_) => {
                // Deadlock: no successor exists from the current state.
                if config.debug {
                    eprintln!("[z4-symsim] run {}: deadlock at depth {}", run_index, depth);
                }
                return Ok(SingleRunResult::Deadlock { depth, trace });
            }
            _ => {
                return Ok(SingleRunResult::SolverInconclusive {
                    depth,
                    reason: format!("Solver returned unknown at depth {depth}"),
                });
            }
        }

        // Check if the new state violates safety.
        {
            let mut checker = z4_shared::make_translator(var_sorts, 0)?;
            checker.set_timeout(config.solve_timeout);
            for (name, sort) in var_sorts {
                checker.declare_var(name, sort.clone())?;
            }
            let new_state = trace.last().expect("just pushed");
            let concrete: Vec<(String, BmcValue)> = new_state
                .assignments
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
            checker.assert_concrete_state(&concrete, 0)?;
            let not_safety = checker.translate_not_safety_at_step(safety_expanded, 0)?;
            checker.assert(not_safety);

            if let SolveResult::Sat = checker.try_check_sat()? {
                if config.debug {
                    eprintln!(
                        "[z4-symsim] run {}: violation at depth {}",
                        run_index,
                        depth + 1
                    );
                }
                return Ok(SingleRunResult::Violation {
                    depth: depth + 1,
                    trace,
                });
            }
        }

        if config.debug && (depth + 1) % 10 == 0 {
            eprintln!("[z4-symsim] run {}: reached depth {}", run_index, depth + 1);
        }
    }

    Ok(SingleRunResult::NoViolation {
        max_depth_reached: config.max_depth,
        states_explored: trace.len(),
    })
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Run symbolic simulation on a TLA+ spec.
///
/// Executes `config.num_runs` independent simulation runs, each exploring
/// up to `config.max_depth` steps. Returns as soon as any run finds a
/// safety violation, or after all runs complete.
///
/// Part of #3757 (Apalache Gap 9).
pub fn symbolic_simulate(
    module: &Module,
    config: &Config,
    ctx: &EvalCtx,
    sim_config: SymbolicSimConfig,
) -> Result<SymbolicSimResult, SymbolicSimError> {
    let symbolic_ctx =
        z4_shared::symbolic_ctx_with_config(ctx, config).map_err(SymbolicSimError::MissingSpec)?;
    let vars = z4_shared::collect_state_vars(module);
    if vars.is_empty() {
        return Err(SymbolicSimError::MissingSpec(
            "No state variables declared".to_string(),
        ));
    }

    if config.invariants.is_empty() {
        return Err(SymbolicSimError::NoInvariants);
    }

    let resolved = z4_shared::resolve_init_next(config, &symbolic_ctx)
        .map_err(SymbolicSimError::MissingSpec)?;

    let init_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.init)
        .map_err(SymbolicSimError::MissingSpec)?;
    let next_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.next)
        .map_err(SymbolicSimError::MissingSpec)?;
    let safety_expr = z4_shared::build_safety_conjunction(&symbolic_ctx, &config.invariants)
        .map_err(SymbolicSimError::TranslationError)?;

    let init_expanded = expand_operators_for_chc(&symbolic_ctx, &init_expr, false);
    let next_expanded = expand_operators_for_chc(&symbolic_ctx, &next_expr, true);
    let safety_expanded = expand_operators_for_chc(&symbolic_ctx, &safety_expr, false);

    let var_sorts =
        z4_shared::infer_var_sorts(&vars, &init_expanded, &config.invariants, &symbolic_ctx);

    if sim_config.debug {
        eprintln!(
            "[z4-symsim] {} vars, {} runs, max depth {}, {} invariants",
            var_sorts.len(),
            sim_config.num_runs,
            sim_config.max_depth,
            config.invariants.len(),
        );
    }

    let session_start = Instant::now();
    let mut runs_completed = 0;
    let mut max_depth_reached = 0;
    let mut total_states = 0;

    for run_index in 0..sim_config.num_runs {
        // Check session timeout.
        if let Some(session_timeout) = sim_config.session_timeout {
            if session_start.elapsed() >= session_timeout {
                return Ok(SymbolicSimResult::Timeout {
                    runs_completed,
                    total_states,
                    reason: format!(
                        "Session timeout ({:.1}s) after {} runs",
                        session_timeout.as_secs_f64(),
                        runs_completed,
                    ),
                });
            }
        }

        let result = run_single_simulation(
            &var_sorts,
            &init_expanded,
            &next_expanded,
            &safety_expanded,
            &sim_config,
            run_index,
        )?;

        match result {
            SingleRunResult::Violation { depth, trace } => {
                if sim_config.debug {
                    eprintln!(
                        "[z4-symsim] violation found in run {} at depth {}",
                        run_index, depth
                    );
                }
                return Ok(SymbolicSimResult::Violation {
                    run_index,
                    depth,
                    trace,
                });
            }
            SingleRunResult::NoViolation {
                max_depth_reached: d,
                states_explored: s,
            } => {
                runs_completed += 1;
                max_depth_reached = max_depth_reached.max(d);
                total_states += s;
            }
            SingleRunResult::Deadlock { depth, trace: _ } => {
                // Deadlock is not a safety violation for simulation purposes.
                // Log it and continue to the next run.
                runs_completed += 1;
                max_depth_reached = max_depth_reached.max(depth);
                total_states += depth + 1;
                if sim_config.debug {
                    eprintln!(
                        "[z4-symsim] run {} deadlocked at depth {}",
                        run_index, depth
                    );
                }
            }
            SingleRunResult::SolverInconclusive { depth, reason } => {
                // Solver inconclusive — count the run but log the issue.
                runs_completed += 1;
                max_depth_reached = max_depth_reached.max(depth);
                total_states += depth;
                if sim_config.debug {
                    eprintln!(
                        "[z4-symsim] run {} inconclusive at depth {}: {}",
                        run_index, depth, reason
                    );
                }
            }
        }
    }

    Ok(SymbolicSimResult::NoViolation {
        runs_completed,
        max_depth_reached,
        total_states,
    })
}

// ---------------------------------------------------------------------------
// Pipeline integration: SymbolicSimRunner
// ---------------------------------------------------------------------------

/// Pipeline runner wrapping symbolic simulation for the verification pipeline.
///
/// Maps:
/// - `SymbolicSimResult::Violation` -> `PropertyVerdict::Violated`
/// - `SymbolicSimResult::NoViolation` / `Timeout` -> `Unknown` (simulation
///   cannot prove safety, only find bugs)
///
/// Part of #3757.
pub struct SymbolicSimRunner<'a> {
    module: &'a Module,
    config: &'a Config,
    ctx: &'a EvalCtx,
    sim_config: SymbolicSimConfig,
}

impl<'a> SymbolicSimRunner<'a> {
    /// Construct a symbolic simulation pipeline runner.
    pub fn new(
        module: &'a Module,
        config: &'a Config,
        ctx: &'a EvalCtx,
        sim_config: SymbolicSimConfig,
    ) -> Self {
        Self {
            module,
            config,
            ctx,
            sim_config,
        }
    }
}

impl std::fmt::Debug for SymbolicSimRunner<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SymbolicSimRunner")
            .field("module", &self.module.name.node)
            .field("num_runs", &self.sim_config.num_runs)
            .field("max_depth", &self.sim_config.max_depth)
            .finish()
    }
}

impl crate::check::pipeline::PhaseRunner for SymbolicSimRunner<'_> {
    fn run(
        &mut self,
        unresolved: &[crate::check::pipeline::PropertyId],
        time_budget: Duration,
    ) -> FxHashMap<crate::check::pipeline::PropertyId, crate::check::pipeline::PropertyVerdict> {
        use crate::check::pipeline::PropertyVerdict;

        let mut sim_config = self.sim_config.clone();
        sim_config.session_timeout = Some(time_budget);

        let mut verdicts = FxHashMap::default();
        match symbolic_simulate(self.module, self.config, self.ctx, sim_config) {
            Ok(SymbolicSimResult::Violation { .. }) => {
                // Symbolic simulation found a counterexample.
                for prop in unresolved {
                    verdicts.insert(prop.clone(), PropertyVerdict::Violated);
                }
            }
            Ok(SymbolicSimResult::NoViolation { .. }) | Ok(SymbolicSimResult::Timeout { .. }) => {
                // Simulation cannot prove safety — leave as Unknown.
            }
            Err(e) => {
                eprintln!("Pipeline symbolic simulation error: {e}");
            }
        }
        verdicts
    }

    fn phase(&self) -> crate::check::pipeline::VerificationPhase {
        crate::check::pipeline::VerificationPhase::SymbolicSim
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::Config;
    use crate::eval::EvalCtx;
    use crate::test_support::parse_module;

    fn config_with_invariants(init: &str, next: &str, invariants: &[&str]) -> Config {
        Config {
            init: Some(init.to_string()),
            next: Some(next.to_string()),
            invariants: invariants.iter().map(|s| s.to_string()).collect(),
            ..Default::default()
        }
    }

    fn default_sim_config() -> SymbolicSimConfig {
        SymbolicSimConfig {
            num_runs: 3,
            max_depth: 20,
            solve_timeout: Some(Duration::from_secs(10)),
            session_timeout: Some(Duration::from_secs(30)),
            debug: false,
        }
    }

    #[test]
    fn test_symbolic_sim_safe_spec() {
        let src = r#"
---- MODULE SymSimSafe ----
VARIABLE x
Init == x \in {0, 1, 2}
Next == x' = x
TypeOK == x \in {0, 1, 2}
====
"#;
        let module = parse_module(src);
        let config = config_with_invariants("Init", "Next", &["TypeOK"]);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);

        let sim_config = default_sim_config();
        let result = symbolic_simulate(&module, &config, &ctx, sim_config)
            .expect("simulation should succeed");

        match result {
            SymbolicSimResult::NoViolation {
                runs_completed,
                total_states,
                ..
            } => {
                assert!(runs_completed > 0, "should complete at least one run");
                assert!(total_states > 0, "should explore at least one state");
            }
            SymbolicSimResult::Violation { .. } => {
                panic!("should not find violation in safe spec");
            }
            SymbolicSimResult::Timeout { .. } => {
                panic!("should not timeout on trivial spec");
            }
        }
    }

    #[test]
    fn test_symbolic_sim_finds_violation() {
        let src = r#"
---- MODULE SymSimUnsafe ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Bound == x < 5
====
"#;
        let module = parse_module(src);
        let config = config_with_invariants("Init", "Next", &["Bound"]);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);

        let sim_config = SymbolicSimConfig {
            num_runs: 1,
            max_depth: 20,
            solve_timeout: Some(Duration::from_secs(10)),
            session_timeout: Some(Duration::from_secs(30)),
            debug: false,
        };
        let result = symbolic_simulate(&module, &config, &ctx, sim_config)
            .expect("simulation should succeed");

        match result {
            SymbolicSimResult::Violation { depth, trace, .. } => {
                assert_eq!(depth, 5, "violation should occur at depth 5 (x reaches 5)");
                assert_eq!(trace.len(), 6, "trace should have 6 states (0..5)");
            }
            other => {
                panic!("expected violation, got: {other:?}");
            }
        }
    }

    #[test]
    fn test_symbolic_sim_missing_invariants() {
        let src = r#"
---- MODULE SymSimNoInv ----
VARIABLE x
Init == x = 0
Next == x' = x
====
"#;
        let module = parse_module(src);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec![],
            ..Default::default()
        };
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);

        let result = symbolic_simulate(&module, &config, &ctx, default_sim_config());
        assert!(result.is_err(), "should error with no invariants");
    }

    #[test]
    fn test_symbolic_sim_deadlock() {
        // Spec where Next becomes unsatisfiable after one step.
        let src = r#"
---- MODULE SymSimDeadlock ----
VARIABLE x
Init == x = 0
Next == x = 0 /\ x' = 1
TypeOK == x \in {0, 1}
====
"#;
        let module = parse_module(src);
        let config = config_with_invariants("Init", "Next", &["TypeOK"]);
        let mut ctx = EvalCtx::new();
        ctx.load_module(&module);

        let sim_config = SymbolicSimConfig {
            num_runs: 1,
            max_depth: 10,
            solve_timeout: Some(Duration::from_secs(10)),
            session_timeout: Some(Duration::from_secs(30)),
            debug: false,
        };
        let result = symbolic_simulate(&module, &config, &ctx, sim_config)
            .expect("simulation should succeed");

        // Should complete without violation (deadlock is not a safety violation
        // in simulation mode).
        match result {
            SymbolicSimResult::NoViolation { runs_completed, .. } => {
                assert_eq!(runs_completed, 1);
            }
            other => {
                panic!("expected NoViolation (deadlock handled), got: {other:?}");
            }
        }
    }

    #[test]
    fn test_symbolic_sim_config_defaults() {
        let config = SymbolicSimConfig::default();
        assert_eq!(config.num_runs, 10);
        assert_eq!(config.max_depth, 100);
        assert!(config.solve_timeout.is_some());
    }

    #[test]
    fn test_symbolic_sim_runner_phase() {
        assert_eq!(
            crate::check::pipeline::VerificationPhase::SymbolicSim.to_string(),
            "SymbolicSim"
        );
    }
}
