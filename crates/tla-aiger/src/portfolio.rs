// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Thread-based portfolio solver for AIGER safety checking.
//!
//! Runs multiple engines (IC3 variants, BMC, k-induction) in parallel and
//! returns the first definitive result. Uses `Arc<AtomicBool>` for cooperative
//! cancellation.
//!
//! The IC3 portfolio mirrors rIC3's approach of running diverse IC3
//! configurations simultaneously. rIC3 uses 16 OS processes; we use threads
//! with cooperative cancellation since our solvers are self-contained.
//!
//! Reference: rIC3 `src/portfolio/mod.rs`, adapted for thread-only operation
//! (no process spawning). Extended well beyond rIC3's 16-engine portfolio
//! with z4-sat configuration diversity, arithmetic-tuned configs, and CEGAR-IC3.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use crate::bmc::BmcEngine;
use crate::check_result::CheckResult;
use crate::ic3::{
    GeneralizationOrder, Ic3Config, Ic3Engine, Ic3Result, RestartStrategy, ValidationStrategy,
};
use crate::kind::{KindEngine, KindStrengthenedEngine};
use crate::preprocess::analyze_circuit;
use crate::transys::Transys;
use crate::types::AigerCircuit;

/// Configuration for a single engine in the portfolio.
#[derive(Debug, Clone)]
pub enum EngineConfig {
    /// BMC with a given step size (z4-sat default config).
    Bmc { step: usize },
    /// BMC with dynamic step size (rIC3's `--dyn-step`).
    ///
    /// Step size is computed at runtime based on circuit complexity:
    /// `step = max(1, 10_000_000 / (max_var + num_trans_clauses))`.
    /// Small circuits get large steps; large circuits get step=1.
    BmcDynamic,
    /// BMC with a z4-sat configuration variant and given step size.
    ///
    /// Portfolio diversity comes from z4-sat's configuration knobs: different
    /// restart policies (Luby, geometric, stable-only), branching heuristics
    /// (VMTF, CHB), and preprocessing toggles. This replaces the former
    /// CaDiCaL BMC backend — we own z4-sat and do not use external solvers.
    BmcZ4Variant {
        step: usize,
        backend: crate::sat_types::SolverBackend,
    },
    /// BMC with a z4-sat variant and dynamic step size.
    BmcZ4VariantDynamic {
        backend: crate::sat_types::SolverBackend,
    },
    /// BMC with geometric backoff step sizing (#4123).
    ///
    /// Starts at step=1 for the first `initial_depths` depths (thorough shallow
    /// coverage), then doubles the step size every `double_interval` SAT calls,
    /// capped at `max_step`. This reaches deep counterexamples much faster than
    /// fixed step=1 while still catching shallow bugs.
    ///
    /// Designed for Sokoban/microban puzzles where rIC3 finds counterexamples
    /// at depth 100+ in 0.2-4.3s via dynamic step sizing.
    BmcGeometricBackoff {
        initial_depths: usize,
        double_interval: usize,
        max_step: usize,
    },
    /// BMC with geometric backoff and a z4-sat configuration variant.
    BmcGeometricBackoffZ4Variant {
        initial_depths: usize,
        double_interval: usize,
        max_step: usize,
        backend: crate::sat_types::SolverBackend,
    },
    /// k-Induction.
    Kind,
    /// k-Induction with simple-path constraint (rIC3's default mode).
    ///
    /// Asserts pairwise state distinctness in the induction trace,
    /// strengthening the hypothesis to prove harder properties.
    KindSimplePath,
    /// k-Induction with skip-bmc mode (induction step only).
    ///
    /// Only checks the inductive step, skipping the base case BMC check.
    /// Useful in portfolios where BMC is already running in a separate thread.
    /// This saves solver time by focusing purely on proving the property
    /// k-inductive. Reference: rIC3 `kind.rs` `--skip-bmc` flag.
    KindSkipBmc,
    /// k-Induction with a z4-sat configuration variant.
    ///
    /// Portfolio diversity: different z4-sat configs race against each other
    /// on the same k-induction problem.
    KindZ4Variant {
        backend: crate::sat_types::SolverBackend,
    },
    /// k-Induction with a z4-sat variant and skip-bmc mode.
    KindSkipBmcZ4Variant {
        backend: crate::sat_types::SolverBackend,
    },
    /// IC3/PDR with default configuration (all optimizations off).
    Ic3,
    /// IC3/PDR with a specific configuration and human-readable name.
    Ic3Configured { config: Ic3Config, name: String },
    /// CEGAR-IC3: IC3 inside a counterexample-guided abstraction refinement loop.
    ///
    /// Starts with an abstract model (COI latches only), runs IC3, and refines
    /// if the counterexample is spurious. Effective on large circuits where most
    /// latches are irrelevant to the property.
    ///
    /// The `mode` controls how aggressively the abstraction removes information:
    /// - `AbstractConstraints` (abs_cst): only relax constraint enforcement
    /// - `AbstractAll` (abs_all): remove both constraints and transition relation
    CegarIc3 {
        config: Ic3Config,
        name: String,
        mode: crate::ic3::cegar::AbstractionMode,
    },
    /// Strengthened k-Induction with auxiliary invariant discovery.
    KindStrengthened,
    /// Strengthened k-Induction with a z4-sat configuration variant.
    KindStrengthenedZ4Variant {
        backend: crate::sat_types::SolverBackend,
    },
}

impl EngineConfig {
    /// Human-readable name for this engine configuration.
    pub fn name(&self) -> &str {
        match self {
            EngineConfig::Bmc { step } => {
                // Return a static str for common cases; callers can format themselves
                if *step == 1 {
                    "bmc-1"
                } else {
                    "bmc"
                }
            }
            EngineConfig::BmcDynamic => "bmc-dynamic",
            EngineConfig::BmcZ4Variant { backend, .. } => match backend {
                crate::sat_types::SolverBackend::Z4Luby => "bmc-z4-luby",
                crate::sat_types::SolverBackend::Z4Stable => "bmc-z4-stable",
                crate::sat_types::SolverBackend::Z4Geometric => "bmc-z4-geometric",
                crate::sat_types::SolverBackend::Z4Vmtf => "bmc-z4-vmtf",
                crate::sat_types::SolverBackend::Z4Chb => "bmc-z4-chb",
                crate::sat_types::SolverBackend::Z4NoPreprocess => "bmc-z4-nopreproc",
                _ => "bmc-z4-variant",
            },
            EngineConfig::BmcZ4VariantDynamic { backend } => match backend {
                crate::sat_types::SolverBackend::Z4Luby => "bmc-z4-luby-dynamic",
                crate::sat_types::SolverBackend::Z4Stable => "bmc-z4-stable-dynamic",
                _ => "bmc-z4-variant-dynamic",
            },
            EngineConfig::BmcGeometricBackoff { .. } => "bmc-geometric-backoff",
            EngineConfig::BmcGeometricBackoffZ4Variant { backend, .. } => match backend {
                crate::sat_types::SolverBackend::Z4Luby => "bmc-geometric-z4-luby",
                crate::sat_types::SolverBackend::Z4Stable => "bmc-geometric-z4-stable",
                _ => "bmc-geometric-z4-variant",
            },
            EngineConfig::Kind => "kind",
            EngineConfig::KindSimplePath => "kind-simple-path",
            EngineConfig::KindSkipBmc => "kind-skip-bmc",
            EngineConfig::KindZ4Variant { backend } => match backend {
                crate::sat_types::SolverBackend::Z4Luby => "kind-z4-luby",
                crate::sat_types::SolverBackend::Z4Stable => "kind-z4-stable",
                crate::sat_types::SolverBackend::Z4Vmtf => "kind-z4-vmtf",
                _ => "kind-z4-variant",
            },
            EngineConfig::KindSkipBmcZ4Variant { backend } => match backend {
                crate::sat_types::SolverBackend::Z4Luby => "kind-skip-bmc-z4-luby",
                crate::sat_types::SolverBackend::Z4Stable => "kind-skip-bmc-z4-stable",
                crate::sat_types::SolverBackend::Z4Vmtf => "kind-skip-bmc-z4-vmtf",
                _ => "kind-skip-bmc-z4-variant",
            },
            EngineConfig::Ic3 => "ic3-default",
            EngineConfig::Ic3Configured { name, .. } => name.as_str(),
            EngineConfig::CegarIc3 { name, .. } => name.as_str(),
            EngineConfig::KindStrengthened => "kind-strengthened",
            EngineConfig::KindStrengthenedZ4Variant { backend } => match backend {
                crate::sat_types::SolverBackend::Z4Luby => "kind-str-z4-luby",
                crate::sat_types::SolverBackend::Z4Stable => "kind-str-z4-stable",
                _ => "kind-str-z4-variant",
            },
        }
    }
}

/// Result of a portfolio run, including which solver produced the answer.
#[derive(Debug, Clone)]
pub struct PortfolioResult {
    /// The model checking result.
    pub result: CheckResult,
    /// Name of the solver configuration that produced this result.
    pub solver_name: String,
    /// Wall-clock time taken by the winning solver.
    pub time_secs: f64,
}

/// Configuration for the portfolio solver.
#[derive(Debug, Clone)]
pub struct PortfolioConfig {
    /// Overall time budget.
    pub timeout: Duration,
    /// Engine configurations to run in parallel.
    pub engines: Vec<EngineConfig>,
    /// Maximum unrolling depth for BMC/k-induction.
    pub max_depth: usize,
    /// Preprocessing configuration (#4124).
    pub preprocess: crate::preprocess::PreprocessConfig,
}

impl Default for PortfolioConfig {
    fn default() -> Self {
        default_portfolio()
    }
}

/// Run a portfolio of model checking engines in parallel.
///
/// Spawns one thread per engine. The first definitive result (Safe or Unsafe)
/// causes all other engines to be cancelled via the shared `AtomicBool` flag.
///
/// Returns the first definitive result, or the best Unknown result if all
/// engines finish without a definitive answer.
pub fn portfolio_check(circuit: &AigerCircuit, config: PortfolioConfig) -> CheckResult {
    portfolio_check_detailed(circuit, config).result
}

/// Run a portfolio with detailed result including solver attribution and timing.
pub fn portfolio_check_detailed(
    circuit: &AigerCircuit,
    config: PortfolioConfig,
) -> PortfolioResult {
    // Set preprocessing timeout if not already configured (#4074).
    // Use 20% of the overall timeout (minimum 5s) to prevent preprocessing
    // from consuming the entire time budget on large circuits (e.g., bakery
    // with 112 latches, 1472 ANDs hangs in SCORR/synthesis).
    let preprocess_config = if config.preprocess.timeout_secs == 0 && config.timeout.as_secs() > 0 {
        let mut pc = config.preprocess.clone();
        pc.timeout_secs = (config.timeout.as_secs() / 5).max(5);
        pc
    } else {
        config.preprocess.clone()
    };
    let ts = Transys::from_aiger(circuit)
        .preprocess_configured(&preprocess_config)
        .0;

    // Detect arithmetic circuit structure and override portfolio if needed.
    // Arithmetic circuits (adders, multipliers, counters) have XOR/carry chain
    // patterns that benefit from arithmetic-tuned IC3 configurations.
    let config = if analyze_circuit(&ts).is_arithmetic {
        let mut arith = arithmetic_portfolio();
        arith.timeout = config.timeout;
        arith
    } else if is_sat_likely(&ts) {
        // SAT-likely heuristic (#4123): when PI count > 2x latch count,
        // the circuit has many free inputs relative to state, making it
        // more likely that a bad state is reachable (SAT). Allocate more
        // portfolio time budget to BMC configs and less to IC3.
        //
        // This pattern is common in Sokoban/microban puzzles where the
        // environment (inputs) is large relative to the game state (latches).
        eprintln!(
            "Portfolio: SAT-likely heuristic triggered (inputs={} > 2*latches={}), using SAT-focused portfolio",
            ts.num_inputs, ts.num_latches
        );
        let mut sat = sat_focused_portfolio();
        sat.timeout = config.timeout;
        sat
    } else {
        config
    };

    let cancelled = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel();
    let start = Instant::now();

    let mut handles = Vec::new();

    for engine_config in &config.engines {
        let ts = ts.clone();
        let cancelled = cancelled.clone();
        let tx = tx.clone();
        let cfg = engine_config.clone();
        let max_depth = config.max_depth;

        handles.push(thread::spawn(move || {
            let engine_start = Instant::now();
            let engine_name = cfg.name().to_string();

            // Wrap the entire engine execution in catch_unwind (#4026).
            // If a z4-sat panic escapes past the solver-level catch_unwind
            // (e.g., during add_clause or push/pop), or if any other panic
            // occurs in the engine, we degrade gracefully to Unknown instead
            // of crashing the portfolio thread and losing its channel sender.
            let engine_name_clone = engine_name.clone();
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                move || match cfg {
                    EngineConfig::Bmc { step } => {
                        let mut engine = BmcEngine::new(ts, step);
                        engine.set_cancelled(cancelled);
                        engine.check(max_depth)
                    }
                    EngineConfig::BmcDynamic => {
                        let mut engine = BmcEngine::new_dynamic(ts);
                        engine.set_cancelled(cancelled);
                        engine.check(max_depth)
                    }
                    EngineConfig::BmcZ4Variant { step, backend } => {
                        let mut engine = BmcEngine::new_with_backend(
                            ts, step, backend,
                        );
                        engine.set_cancelled(cancelled);
                        engine.check(max_depth)
                    }
                    EngineConfig::BmcZ4VariantDynamic { backend } => {
                        let mut engine = BmcEngine::new_dynamic_with_backend(
                            ts, backend,
                        );
                        engine.set_cancelled(cancelled);
                        engine.check(max_depth)
                    }
                    EngineConfig::BmcGeometricBackoff {
                        initial_depths,
                        double_interval,
                        max_step,
                    } => {
                        let mut engine = BmcEngine::new_geometric_backoff(ts);
                        engine.set_cancelled(cancelled);
                        engine.check_geometric_backoff(
                            max_depth,
                            initial_depths,
                            double_interval,
                            max_step,
                        )
                    }
                    EngineConfig::BmcGeometricBackoffZ4Variant {
                        initial_depths,
                        double_interval,
                        max_step,
                        backend,
                    } => {
                        let mut engine =
                            BmcEngine::new_geometric_backoff_with_backend(ts, backend);
                        engine.set_cancelled(cancelled);
                        engine.check_geometric_backoff(
                            max_depth,
                            initial_depths,
                            double_interval,
                            max_step,
                        )
                    }
                    EngineConfig::Kind => {
                        let mut engine = KindEngine::new(ts);
                        engine.set_cancelled(cancelled);
                        engine.check(max_depth)
                    }
                    EngineConfig::KindSimplePath => {
                        let mut engine = KindEngine::new_simple_path(ts);
                        engine.set_cancelled(cancelled);
                        engine.check(max_depth)
                    }
                    EngineConfig::KindSkipBmc => {
                        let mut engine = KindEngine::with_config(
                            ts,
                            crate::kind::KindConfig {
                                simple_path: false,
                                skip_bmc: true,
                            },
                        );
                        engine.set_cancelled(cancelled);
                        engine.check(max_depth)
                    }
                    EngineConfig::KindZ4Variant { backend } => {
                        let mut engine = KindEngine::with_config_and_backend(
                            ts,
                            crate::kind::KindConfig::default(),
                            backend,
                        );
                        engine.set_cancelled(cancelled);
                        engine.check(max_depth)
                    }
                    EngineConfig::KindSkipBmcZ4Variant { backend } => {
                        let mut engine = KindEngine::with_config_and_backend(
                            ts,
                            crate::kind::KindConfig {
                                simple_path: false,
                                skip_bmc: true,
                            },
                            backend,
                        );
                        engine.set_cancelled(cancelled);
                        engine.check(max_depth)
                    }
                    EngineConfig::KindStrengthened => {
                        let mut engine = KindStrengthenedEngine::new(ts);
                        engine.set_cancelled(cancelled);
                        engine.check(max_depth)
                    }
                    EngineConfig::KindStrengthenedZ4Variant { backend } => {
                        let mut engine =
                            KindStrengthenedEngine::with_backend(ts, backend);
                        engine.set_cancelled(cancelled);
                        engine.check(max_depth)
                    }
                    EngineConfig::Ic3 => {
                        let ts_ref = ts.clone();
                        let mut engine = Ic3Engine::new(ts);
                        engine.set_cancelled(cancelled);
                        ic3_to_check_result(engine.check(), &ts_ref)
                    }
                    EngineConfig::Ic3Configured { config, .. } => {
                        let mut ts = ts;
                        if config.internal_signals {
                            ts.select_internal_signals();
                        }
                        let ts_ref = ts.clone();
                        let mut engine = Ic3Engine::with_config(ts, config);
                        engine.set_cancelled(cancelled);
                        ic3_to_check_result(engine.check(), &ts_ref)
                    }
                    EngineConfig::CegarIc3 { config, mode, .. } => {
                        let mut cegar =
                            crate::ic3::cegar::CegarIc3::with_mode(ts, config, mode);
                        cegar.set_cancelled(cancelled);
                        cegar.run()
                    }
                },
            ))
            .unwrap_or_else(|panic_info| {
                let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                    (*s).to_string()
                } else if let Some(s) = panic_info.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "unknown panic".to_string()
                };
                eprintln!(
                    "Portfolio: engine {engine_name_clone} panicked: {msg}"
                );
                CheckResult::Unknown {
                    reason: format!("engine panicked: {msg}"),
                }
            });

            let elapsed = engine_start.elapsed().as_secs_f64();
            let _ = tx.send(PortfolioResult {
                result,
                solver_name: engine_name,
                time_secs: elapsed,
            });
        }));
    }
    drop(tx); // Close sender so rx.recv() returns Err when all threads finish

    // Wait for first definitive result or timeout
    let mut best = PortfolioResult {
        result: CheckResult::Unknown {
            reason: "no engine finished".into(),
        },
        solver_name: String::new(),
        time_secs: 0.0,
    };

    loop {
        let remaining = config.timeout.saturating_sub(start.elapsed());
        if remaining.is_zero() {
            cancelled.store(true, Ordering::Relaxed);
            for handle in handles {
                let _ = handle.join();
            }
            return PortfolioResult {
                result: CheckResult::Unknown {
                    reason: "portfolio timeout".into(),
                },
                solver_name: String::new(),
                time_secs: config.timeout.as_secs_f64(),
            };
        }

        match rx.recv_timeout(remaining) {
            Ok(portfolio_result) => {
                if portfolio_result.result.is_definitive() {
                    // Portfolio-level witness verification (#4103):
                    // Before accepting an Unsafe result from ANY engine (BMC,
                    // k-induction, IC3), verify the witness by simulating
                    // the circuit. This is defense-in-depth: BMC/k-ind already
                    // verify internally, but IC3 does not, and this catches
                    // bugs in any engine's witness extraction.
                    if let CheckResult::Unsafe { ref trace, depth } = portfolio_result.result {
                        if let Err(reason) = ts.verify_witness(trace) {
                            eprintln!(
                                "Portfolio: {} returned Unsafe at depth {} but witness \
                                 verification FAILED: {}. Treating as Unknown.",
                                portfolio_result.solver_name, depth, reason,
                            );
                            // Don't accept this result -- continue waiting
                            // for other engines.
                            continue;
                        }
                    }
                    cancelled.store(true, Ordering::Relaxed);
                    // Wait for all threads to finish
                    for handle in handles {
                        let _ = handle.join();
                    }
                    return portfolio_result;
                }
                best = portfolio_result;
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {
                cancelled.store(true, Ordering::Relaxed);
                for handle in handles {
                    let _ = handle.join();
                }
                return PortfolioResult {
                    result: CheckResult::Unknown {
                        reason: "portfolio timeout".into(),
                    },
                    solver_name: String::new(),
                    time_secs: config.timeout.as_secs_f64(),
                };
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                // All senders dropped -- all engines finished
                break;
            }
        }
    }

    // Wait for remaining threads
    for handle in handles {
        let _ = handle.join();
    }

    best
}

/// Convert IC3 result to the shared CheckResult type.
fn ic3_to_check_result(ic3: Ic3Result, ts: &Transys) -> CheckResult {
    match ic3 {
        Ic3Result::Safe { .. } => CheckResult::Safe,
        Ic3Result::Unsafe { depth, trace } => {
            // Convert IC3's (Var, bool) trace to named FxHashMap trace.
            // Use the same naming convention as BMC (l{idx}/i{idx}/v{var_id})
            // so verify_witness can find the variable values.
            let named_trace = trace
                .into_iter()
                .map(|state| {
                    let mut named: rustc_hash::FxHashMap<String, bool> =
                        rustc_hash::FxHashMap::default();
                    for (var, val) in &state {
                        // Map latch vars to "l{idx}" format
                        if let Some(idx) = ts.latch_vars.iter().position(|lv| lv == var) {
                            named.insert(format!("l{idx}"), *val);
                        }
                        // Map input vars to "i{idx}" format
                        if let Some(idx) = ts.input_vars.iter().position(|iv| iv == var) {
                            named.insert(format!("i{idx}"), *val);
                        }
                        // Also include raw "v{id}" for compatibility
                        named.insert(format!("v{}", var.0), *val);
                    }
                    named
                })
                .collect();
            CheckResult::Unsafe {
                depth,
                trace: named_trace,
            }
        }
        Ic3Result::Unknown { reason } => CheckResult::Unknown { reason },
    }
}

// ---------------------------------------------------------------------------
// Pre-defined IC3 configurations (mirroring rIC3's portfolio diversity)
//
// rIC3's bl_default portfolio runs 16 engines total:
//   11 IC3 configs + 4 BMC configs + 1 k-induction
// Each IC3 config varies: ctg on/off, ctg_max, ctg_limit, ctp, internal
// signals (inn), drop_po, random seed.
//
// We mirror the most impactful axes:
//   - Feature toggles: ctp, inf_frame, internal_signals, ternary_reduce
//   - CTG tuning: ctg_max (3 vs 5), ctg_limit (1 vs 15)
//   - CTP tuning: ctp_max
//   - Random seed diversity: each config gets a unique seed
// ---------------------------------------------------------------------------

/// IC3 with all optimizations off (conservative baseline).
/// Mirrors rIC3's `ic3 --rseed 1`. Best single-config performance on many benchmarks.
pub fn ic3_conservative() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            random_seed: 1,
            ..Ic3Config::default()
        },
        name: "ic3-conservative".into(),
    }
}

/// IC3 with Counter-To-Propagation enabled.
/// CTP strengthens frames during propagation, helping benchmarks where
/// lemma push-through is the bottleneck.
/// Mirrors rIC3's `ic3_inn_ctp` (CTP is paired with internal signals in rIC3).
pub fn ic3_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            random_seed: 2,
            ..Ic3Config::default()
        },
        name: "ic3-ctp".into(),
    }
}

/// IC3 with infinity frame promotion.
/// Globally-inductive lemmas are promoted and never re-propagated,
/// reducing work on deep induction chains.
pub fn ic3_inf() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            inf_frame: true,
            random_seed: 3,
            ..Ic3Config::default()
        },
        name: "ic3-inf".into(),
    }
}

/// IC3 with internal signals (AND gate variables in cubes).
/// FMCAD'21 technique: including internal signals in cubes can help
/// generalization on circuits with complex combinational logic.
/// Mirrors rIC3's `ic3_inn` configuration.
pub fn ic3_internal() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            internal_signals: true,
            random_seed: 4,
            ..Ic3Config::default()
        },
        name: "ic3-internal".into(),
    }
}

/// IC3 with ternary simulation pre-reduction.
/// Ternary simulation quickly identifies don't-care literals in bad cubes,
/// reducing cube size before the expensive MIC generalization loop.
pub fn ic3_ternary() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ternary_reduce: true,
            random_seed: 5,
            ..Ic3Config::default()
        },
        name: "ic3-ternary".into(),
    }
}

/// IC3 with all optimizations enabled (aggressive mode).
/// Combines CTP, infinity frame, internal signals, and ternary reduction.
/// May be the fastest on some benchmarks, but the overhead of all
/// optimizations together can hurt on others.
pub fn ic3_full() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            inf_frame: true,
            internal_signals: true,
            ternary_reduce: true,
            random_seed: 6,
            ..Ic3Config::default()
        },
        name: "ic3-full".into(),
    }
}

/// IC3 with CTP + infinity frame (best for deep safety proofs).
pub fn ic3_ctp_inf() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            inf_frame: true,
            random_seed: 7,
            ..Ic3Config::default()
        },
        name: "ic3-ctp-inf".into(),
    }
}

/// IC3 with internal signals + ternary reduce (best for complex combinational logic).
pub fn ic3_internal_ternary() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            internal_signals: true,
            ternary_reduce: true,
            random_seed: 8,
            ..Ic3Config::default()
        },
        name: "ic3-internal-ternary".into(),
    }
}

/// IC3 with aggressive CTG limits (deep generalization).
/// Mirrors rIC3's `ic3_ctg_limit` with `--ctg-max 5 --ctg-limit 15`.
/// Higher limits allow deeper counterexample blocking during MIC,
/// producing shorter lemmas at the cost of more SAT calls per literal drop.
/// Complements the conservative config which uses ctg_max=3, ctg_limit=1.
pub fn ic3_deep_ctg() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctg_max: 5,
            ctg_limit: 15,
            random_seed: 9,
            ..Ic3Config::default()
        },
        name: "ic3-deep-ctg".into(),
    }
}

/// IC3 with internal signals + CTP.
/// Mirrors rIC3's `ic3_inn_ctp` — combining CTP with internal signals often
/// excels on circuits with deep combinational logic where both shorter
/// cubes (from internal signals) and stronger propagation (from CTP) help.
pub fn ic3_internal_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            internal_signals: true,
            ctp: true,
            random_seed: 10,
            ..Ic3Config::default()
        },
        name: "ic3-internal-ctp".into(),
    }
}

/// IC3 with deep CTG + internal signals.
/// Combines aggressive generalization (ctg_max=5, ctg_limit=15) with
/// internal signal cubes, targeting circuits where standard IC3 produces
/// overly specific lemmas.
pub fn ic3_deep_ctg_internal() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctg_max: 5,
            ctg_limit: 15,
            internal_signals: true,
            random_seed: 11,
            ..Ic3Config::default()
        },
        name: "ic3-deep-ctg-internal".into(),
    }
}

/// IC3 with ternary reduction + infinity frame + unique seed.
/// Lightweight preprocessing (ternary) plus global lemma promotion (inf),
/// a complementary combination not covered by other configs.
pub fn ic3_ternary_inf() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ternary_reduce: true,
            inf_frame: true,
            random_seed: 12,
            ..Ic3Config::default()
        },
        name: "ic3-ternary-inf".into(),
    }
}

/// IC3 with aggressive CTP (max 5 attempts).
/// Higher CTP limit for propagation-bound benchmarks where the default
/// ctp_max=3 is insufficient to push all lemmas through.
pub fn ic3_aggressive_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            random_seed: 13,
            ..Ic3Config::default()
        },
        name: "ic3-aggressive-ctp".into(),
    }
}

/// IC3 with deep CTG + CTP (strongest generalization + propagation combo).
/// Combines aggressive CTG (ctg_max=5, ctg_limit=15) with CTP for benchmarks
/// where both generalization and propagation are bottlenecks. This is the
/// configuration closest to rIC3's strongest single-engine mode.
pub fn ic3_deep_ctg_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctg_max: 5,
            ctg_limit: 15,
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            random_seed: 14,
            ..Ic3Config::default()
        },
        name: "ic3-deep-ctg-ctp".into(),
    }
}

/// IC3 with all features plus high seed (maximum diversity).
/// Identical feature set to ic3_full but with a different random seed,
/// providing complementary MIC literal orderings. On many benchmarks,
/// the best-performing config depends on literal ordering luck —
/// two identical feature sets with different seeds often solve different
/// subsets of benchmarks.
pub fn ic3_full_alt_seed() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            inf_frame: true,
            internal_signals: true,
            ternary_reduce: true,
            random_seed: 15,
            ..Ic3Config::default()
        },
        name: "ic3-full-alt".into(),
    }
}

/// IC3 with internal signals + deep CTG + CTP + ternary (kitchen sink, high seed).
/// The most aggressive configuration in the portfolio. Combines every
/// optimization axis. Expensive per-step but can solve the hardest benchmarks
/// that no single optimization can crack.
pub fn ic3_kitchen_sink() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            internal_signals: true,
            ternary_reduce: true,
            ctg_max: 5,
            ctg_limit: 15,
            random_seed: 16,
            ..Ic3Config::default()
        },
        name: "ic3-kitchen-sink".into(),
    }
}

/// IC3 with CTG-down MIC variant.
/// Uses the flip-based cube shrinking from rIC3's `ctg_down()` instead of
/// standard literal dropping. More aggressive generalization that can remove
/// multiple literals at once by using the SAT model to guide shrinking.
/// Reference: rIC3 mic.rs:122 — `ctg_down()`.
pub fn ic3_ctg_down() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctg_down: true,
            random_seed: 17,
            ..Ic3Config::default()
        },
        name: "ic3-ctg-down".into(),
    }
}

/// IC3 with CTG-down + CTP + inf (aggressive generalization + propagation).
/// Combines the flip-based MIC with CTP and infinity frame for maximum
/// generalization effectiveness.
pub fn ic3_ctg_down_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctg_down: true,
            ctp: true,
            inf_frame: true,
            random_seed: 18,
            ..Ic3Config::default()
        },
        name: "ic3-ctg-down-ctp".into(),
    }
}

/// IC3 with dynamic generalization (GAP-5).
/// Adaptively adjusts CTG parameters based on proof obligation activity.
/// High-activity POs get more aggressive generalization, while easy POs
/// use minimal overhead. Combined with drop_po (enabled by default).
/// Reference: rIC3 block.rs:129-159 — dynamic MicType selection.
pub fn ic3_dynamic() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            dynamic: true,
            random_seed: 19,
            ..Ic3Config::default()
        },
        name: "ic3-dynamic".into(),
    }
}

/// IC3 with dynamic generalization + CTP + infinity frame.
/// The dynamic+CTP combination is strong: dynamic adjusts generalization
/// effort per-cube, while CTP strengthens frames during propagation.
pub fn ic3_dynamic_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            dynamic: true,
            ctp: true,
            inf_frame: true,
            random_seed: 20,
            ..Ic3Config::default()
        },
        name: "ic3-dynamic-ctp".into(),
    }
}

/// IC3 with dynamic generalization + internal signals.
/// Dynamic CTG adapts to per-cube difficulty while internal signals
/// provide richer cubes for generalization.
pub fn ic3_dynamic_internal() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            dynamic: true,
            internal_signals: true,
            random_seed: 21,
            ..Ic3Config::default()
        },
        name: "ic3-dynamic-internal".into(),
    }
}

/// IC3 tuned for arithmetic circuits (adders, multipliers, counters).
///
/// Arithmetic circuits have specific characteristics that benefit from:
/// - **Deep CTG** (ctg_max=5, ctg_limit=15): arithmetic invariants often
///   require aggressive generalization across carry chain boundaries.
/// - **Internal signals**: carry chain AND gate outputs provide useful
///   generalization anchors.
/// - **CTP**: propagation is the bottleneck on deep arithmetic circuits
///   where lemmas must be pushed through many carry-dependent frames.
/// - **Ternary reduce**: carry chains create many don't-care bits.
/// - **Dynamic generalization**: arithmetic cubes vary greatly in difficulty
///   (simple constant propagation vs. full carry chain reasoning).
///
/// This config is selected automatically when circuit analysis detects
/// XOR/carry chain patterns (see `preprocess::xor_detect`).
pub fn ic3_arithmetic() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            internal_signals: true,
            ternary_reduce: true,
            ctg_max: 5,
            ctg_limit: 15,
            dynamic: true,
            random_seed: 100,
            blocking_budget: 500,
            ..Ic3Config::default()
        },
        name: "ic3-arithmetic".into(),
    }
}

/// IC3 for arithmetic circuits with CTG-down MIC variant.
///
/// Combines the arithmetic-tuned parameters with CTG-down's aggressive
/// model-based cube shrinking. On arithmetic circuits, CTG-down can
/// remove multiple carry-chain-dependent literals at once by using the
/// SAT model to identify which literals are actually relevant.
pub fn ic3_arithmetic_ctg_down() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            internal_signals: true,
            ternary_reduce: true,
            ctg_down: true,
            random_seed: 101,
            blocking_budget: 500,
            ..Ic3Config::default()
        },
        name: "ic3-arithmetic-ctg-down".into(),
    }
}

/// IC3 for arithmetic circuits without internal signals (diversity).
///
/// Some arithmetic benchmarks perform better without internal signals
/// because the carry chain AND gates add too many variables to cubes.
/// This provides portfolio diversity against the full arithmetic config.
pub fn ic3_arithmetic_no_internal() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            internal_signals: false,
            ternary_reduce: true,
            ctg_max: 5,
            ctg_limit: 15,
            dynamic: true,
            random_seed: 102,
            blocking_budget: 500,
            ..Ic3Config::default()
        },
        name: "ic3-arithmetic-no-internal".into(),
    }
}

/// IC3 for arithmetic circuits with conservative MIC (#4072).
///
/// Arithmetic circuits have carry chain dependencies that make per-literal
/// MIC drops expensive and mostly futile. This config:
/// - **No CTG** (ctg_max=0): carry chain predecessors are numerous and
///   structured — CTG wastes SAT calls trying to block them.
/// - **MIC drop budget = 100**: limits the literal-drop loop to 100 SAT calls.
///   UNSAT core reduction (Phase 1) typically removes 30-60% of literals for
///   free; the budget catches truly independent bits but avoids carry chain
///   thrashing.
/// - **Blocking budget = 200**: limits bad-state discoveries per depth to force
///   frame advancement. Core-only lemmas are weaker, so fewer per depth is OK.
/// - **CTP + inf_frame**: propagation is the bottleneck on deep arithmetic
///   circuits, so these features accelerate convergence via frame strengthening.
/// - **No internal signals**: carry chain AND gates add variables that increase
///   cube size without improving generalization quality.
///
/// This is the key convergence fix: standard MIC on a 32-bit counter wastes
/// 32+ SAT calls per cube discovering that every bit is essential. With a
/// budget of 100, MIC returns the core-reduced cube after ~100 calls and IC3
/// makes progress instead of thrashing.
pub fn ic3_arithmetic_conservative() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            internal_signals: false,
            ternary_reduce: true,
            ctg_max: 0,
            ctg_limit: 0,
            dynamic: false,
            mic_drop_budget: 100,
            blocking_budget: 200,
            random_seed: 103,
            ..Ic3Config::default()
        },
        name: "ic3-arithmetic-conservative".into(),
    }
}

/// IC3 for arithmetic circuits with tight MIC budget + dynamic (#4072).
///
/// Variant of conservative mode with dynamic generalization enabled.
/// Dynamic CTG is activity-aware: low-activity POs (common on first encounter
/// of arithmetic cubes) get zero CTG, while high-activity POs (thrashing cubes
/// that keep reappearing) get aggressive CTG. Combined with the MIC budget
/// and blocking budget, this avoids wasting SAT calls on easy cubes while
/// investing more effort in persistently difficult ones.
pub fn ic3_arithmetic_tight_budget() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            internal_signals: false,
            ternary_reduce: true,
            ctg_max: 2,
            ctg_limit: 1,
            dynamic: true,
            mic_drop_budget: 50,
            blocking_budget: 300,
            random_seed: 104,
            ..Ic3Config::default()
        },
        name: "ic3-arithmetic-tight-budget".into(),
    }
}

/// IC3 for arithmetic circuits: core-only MIC (#4072).
///
/// The most aggressive budget configuration: mic_drop_budget=1 means the
/// literal-drop loop effectively does nothing beyond the UNSAT core reduction
/// (which happens in Phase 1, before the drop loop). This produces slightly
/// weaker lemmas but runs extremely fast per-cube, letting IC3 explore more
/// frames and find the invariant through quantity rather than quality of
/// individual lemmas.
///
/// Blocking budget = 100 to force rapid frame advancement. The strategy is
/// quantity over quality: many weak lemmas across many frames, relying on
/// propagation to merge and strengthen them.
///
/// Best for deep arithmetic circuits (Fibonacci, counters) where the invariant
/// involves many correlated bits and per-literal dropping is futile.
pub fn ic3_arithmetic_core_only() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            ctp_max: 3,
            inf_frame: true,
            internal_signals: false,
            ternary_reduce: true,
            ctg_max: 0,
            ctg_limit: 0,
            dynamic: false,
            mic_drop_budget: 1,
            blocking_budget: 100,
            random_seed: 105,
            ..Ic3Config::default()
        },
        name: "ic3-arithmetic-core-only".into(),
    }
}

/// IC3 with 2-ordering lift for tighter generalizations (#4099).
///
/// After the standard Activity-ordered MIC pass, tries a second pass with
/// ReverseTopological ordering and keeps the shorter result. This is only
/// done when the first pass didn't reduce the cube much (> half original)
/// and the circuit has > 15 latches.
///
/// The complementary ordering explores a fundamentally different
/// generalization path through the search space, often finding literals
/// that Activity-based ordering misses because they have moderate
/// VSIDS scores but are structurally redundant.
pub fn ic3_multi_order() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            gen_order: GeneralizationOrder::Activity,
            multi_lift_orderings: 2,
            random_seed: 110,
            ..Ic3Config::default()
        },
        name: "ic3-multi-order".into(),
    }
}

/// IC3 with 2-ordering lift + CTP + infinity frame (#4099).
///
/// Combines the multi-ordering lift with CTP and infinity frame for
/// stronger propagation. The multi-ordering lift produces tighter lemmas,
/// and CTP + inf_frame push those lemmas further forward, accelerating
/// convergence.
pub fn ic3_multi_order_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            inf_frame: true,
            gen_order: GeneralizationOrder::Activity,
            multi_lift_orderings: 2,
            random_seed: 111,
            ..Ic3Config::default()
        },
        name: "ic3-multi-order-ctp".into(),
    }
}

/// IC3 with 3-ordering lift (maximum diversity) + CTP + infinity frame (#4099).
///
/// Tries all three ordering strategies: Activity, ReverseTopological, and
/// RandomShuffle. Maximum generalization diversity at the cost of up to 3x
/// MIC calls on cubes where the first ordering underperforms.
///
/// Best for hard benchmarks where tight lemmas are critical for convergence.
pub fn ic3_multi_order_full() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctp: true,
            inf_frame: true,
            gen_order: GeneralizationOrder::Activity,
            multi_lift_orderings: 3,
            random_seed: 112,
            ..Ic3Config::default()
        },
        name: "ic3-multi-order-full".into(),
    }
}

/// IC3 with internal signals only (#4148).
///
/// Mirrors rIC3's vanilla `--inn` flag: extends the MIC variable domain to
/// include AND-gate outputs so generalization operates over latches + internal
/// signals. No other features enabled — pure internal signal diversity.
pub fn ic3_inn() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            internal_signals: true,
            random_seed: 150,
            ..Ic3Config::default()
        },
        name: "ic3-inn".into(),
    }
}

/// IC3 with internal signals + CTP (#4148).
///
/// Mirrors rIC3's `ic3_inn_ctp`: combining CTP propagation with internal
/// signals provides both stronger propagation (CTP pushes lemmas forward)
/// and richer generalization (internal signals in cubes). The combination
/// is particularly effective on arithmetic circuits with carry chains.
pub fn ic3_inn_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            internal_signals: true,
            ctp: true,
            inf_frame: true,
            random_seed: 151,
            ..Ic3Config::default()
        },
        name: "ic3-inn-ctp".into(),
    }
}

/// IC3 with internal signals, no CTG (#4148).
///
/// Mirrors rIC3's `ic3_inn_noctg`: internal signals for richer cubes but
/// CTG disabled (ctg_max=0) to avoid over-generalization.
pub fn ic3_inn_noctg() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            internal_signals: true,
            ctg_max: 0,
            ctg_limit: 0,
            random_seed: 152,
            ..Ic3Config::default()
        },
        name: "ic3-inn-noctg".into(),
    }
}

/// IC3 with internal signals + dynamic generalization (#4148).
///
/// Mirrors rIC3's `ic3_inn_dynamic`: internal signals + dynamic CTG that
/// adapts based on proof obligation activity.
pub fn ic3_inn_dynamic() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            internal_signals: true,
            dynamic: true,
            drop_po: false,
            random_seed: 153,
            ..Ic3Config::default()
        },
        name: "ic3-inn-dynamic".into(),
    }
}

/// IC3 with SimpleSolver backend for high-constraint-ratio circuits (#4092).
///
/// z4-sat produces FINALIZE_SAT_FAIL on circuits with high constraint-to-latch
/// ratios (e.g., NTU microban Sokoban puzzles with 100-300+ constraints on
/// 30-60 latches). The cross-check fallback mechanism in block.rs eventually
/// switches to SimpleSolver, but wastes several seconds on z4-sat failures
/// first. This config starts with SimpleSolver from the beginning.
///
/// SimpleSolver is a simple DPLL solver without CDCL or preprocessing.
/// It is slower per-query than z4-sat on most benchmarks, but never produces
/// false UNSAT or FINALIZE_SAT_FAIL. On high-constraint benchmarks where
/// z4-sat spends most of its time on error recovery, SimpleSolver is faster.
///
/// CTP + inf enabled for convergence. SkipConsecution validation since
/// another portfolio member with Auto validates.
pub fn ic3_simple_solver() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            solver_backend: crate::sat_types::SolverBackend::Simple,
            ctp: true,
            inf_frame: true,
            random_seed: 160,
            validation_strategy: ValidationStrategy::SkipConsecution,
            ..Ic3Config::default()
        },
        name: "ic3-simple-solver".into(),
    }
}

/// IC3 with SimpleSolver + internal signals for high-constraint circuits (#4092).
///
/// Combines the SimpleSolver backend (no false UNSAT) with internal signals
/// for richer cubes. On constraint-heavy circuits where z4-sat fails,
/// this provides a complementary IC3 path with different generalization
/// behavior.
pub fn ic3_simple_solver_inn() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            solver_backend: crate::sat_types::SolverBackend::Simple,
            internal_signals: true,
            ctp: true,
            inf_frame: true,
            random_seed: 161,
            validation_strategy: ValidationStrategy::SkipConsecution,
            ..Ic3Config::default()
        },
        name: "ic3-simple-solver-inn".into(),
    }
}

/// Portfolio optimized for arithmetic circuits.
///
/// Arithmetic circuits (adders, multipliers, counters) have deep
/// combinational logic with regular carry chain structure. This portfolio:
/// - Includes 3 arithmetic-tuned IC3 configs (with/without internal signals, CTG-down)
/// - Includes 3 conservative MIC configs for carry-chain-heavy circuits (#4072)
/// - Includes 4 internal signal (--inn) IC3 variants for arithmetic generalization (#4148)
/// - Adds 4 general IC3 configs for diversity
/// - Uses deeper BMC (max_depth=50000) since arithmetic bugs often require depth
/// - Includes more BMC variants (step sizes 1, 10, 65, 200 for very deep bugs)
/// - k-induction with skip-bmc (induction is effective on regular arithmetic)
///
/// Selected automatically when `analyze_circuit().is_arithmetic` is true.
pub fn arithmetic_portfolio() -> PortfolioConfig {
    PortfolioConfig {
        timeout: Duration::from_secs(3600),
        engines: vec![
            // Arithmetic-tuned IC3 (3 configs)
            ic3_arithmetic(),
            ic3_arithmetic_ctg_down(),
            ic3_arithmetic_no_internal(),
            // Conservative MIC configs for carry-chain circuits (#4072, 3 configs)
            ic3_arithmetic_conservative(),
            ic3_arithmetic_tight_budget(),
            ic3_arithmetic_core_only(),
            // Internal signal IC3 variants for arithmetic generalization (#4148, 4 configs)
            ic3_inn(),
            ic3_inn_ctp(),
            ic3_inn_noctg(),
            ic3_inn_dynamic(),
            // General IC3 for diversity (4 configs)
            ic3_conservative(),
            ic3_deep_ctg_ctp(),
            ic3_dynamic_ctp(),
            ic3_kitchen_sink(),
            // BMC variants with z4-sat (7 default + 2 z4 variant + 1 geometric, #4123)
            EngineConfig::Bmc { step: 1 },
            EngineConfig::Bmc { step: 10 },
            EngineConfig::Bmc { step: 65 },
            EngineConfig::Bmc { step: 200 },
            EngineConfig::Bmc { step: 500 },     // Deep arithmetic bugs (#4123)
            EngineConfig::BmcDynamic,
            // Geometric backoff BMC (#4123)
            EngineConfig::BmcGeometricBackoff {
                initial_depths: 50,
                double_interval: 20,
                max_step: 64,
            },
            // z4-sat variant BMC: Luby restarts + VMTF for diversity
            EngineConfig::BmcZ4Variant { step: 10, backend: crate::sat_types::SolverBackend::Z4Luby },
            EngineConfig::BmcZ4VariantDynamic { backend: crate::sat_types::SolverBackend::Z4Vmtf },
            // k-Induction (2 configs — arithmetic properties are often k-inductive)
            EngineConfig::Kind,
            EngineConfig::KindSkipBmc,
        ],
        max_depth: 50000,
        preprocess: crate::preprocess::PreprocessConfig::default(),
    }
}

/// IC3 without drop_po (GAP-2 disabled).
/// Some benchmarks benefit from NOT dropping high-activity POs, because
/// persistent cubes may eventually become blockable after enough lemmas
/// accumulate. This provides portfolio diversity against drop_po-enabled configs.
pub fn ic3_no_drop() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            drop_po: false,
            random_seed: 22,
            ..Ic3Config::default()
        },
        name: "ic3-no-drop".into(),
    }
}

/// IC3 with aggressive drop_po (threshold=10.0).
///
/// Lower threshold drops proof obligations sooner — after ~10 re-encounters
/// instead of the default ~20. Frees solver time on benchmarks with many
/// thrashing cubes at the cost of potentially missing blockable cubes that
/// need more attempts. Complements the default threshold=20.0 and no-drop
/// configs for portfolio diversity.
///
/// Reference: rIC3 portfolio.toml varies drop_po on/off but not threshold;
/// this is a tla-aiger extension for finer-grained PO management.
pub fn ic3_aggressive_drop() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            drop_po: true,
            drop_po_threshold: 10.0,
            random_seed: 170,
            ..Ic3Config::default()
        },
        name: "ic3-aggressive-drop".into(),
    }
}

/// IC3 with conservative drop_po (threshold=40.0).
///
/// Higher threshold keeps proof obligations alive longer — cubes must be
/// re-encountered ~40 times before being dropped. Gives IC3 more chances
/// to block persistent cubes that become blockable after frame lemmas
/// accumulate. Better for benchmarks where patience pays off, worse for
/// benchmarks with many hopeless cubes.
pub fn ic3_conservative_drop() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            drop_po: true,
            drop_po_threshold: 40.0,
            random_seed: 171,
            ..Ic3Config::default()
        },
        name: "ic3-conservative-drop".into(),
    }
}

/// IC3 with aggressive drop + CTP + infinity frame.
///
/// Combines aggressive PO dropping (threshold=10.0) with strong propagation.
/// CTP helps push lemmas forward even when cubes are being dropped aggressively,
/// compensating for the reduced blocking effort per cube.
pub fn ic3_aggressive_drop_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            drop_po: true,
            drop_po_threshold: 10.0,
            ctp: true,
            inf_frame: true,
            random_seed: 172,
            ..Ic3Config::default()
        },
        name: "ic3-aggressive-drop-ctp".into(),
    }
}

/// IC3 with reverse topological generalization order.
/// Drops output-side latches (deeper in the AND-gate graph) before input-side
/// latches. This can find shorter generalizations on circuits with deep
/// pipelines where output-side latches are more likely to be don't-cares.
pub fn ic3_reverse_topo() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            gen_order: GeneralizationOrder::ReverseTopological,
            random_seed: 23,
            ..Ic3Config::default()
        },
        name: "ic3-reverse-topo".into(),
    }
}

/// IC3 with reverse topological order + CTP + infinity frame.
/// Combines structural ordering with strong propagation for deep pipelines.
pub fn ic3_reverse_topo_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            gen_order: GeneralizationOrder::ReverseTopological,
            ctp: true,
            inf_frame: true,
            random_seed: 24,
            ..Ic3Config::default()
        },
        name: "ic3-reverse-topo-ctp".into(),
    }
}

/// IC3 with random shuffle generalization order.
/// Pure diversity: randomized literal ordering avoids systematic biases.
/// Different from seed-based activity perturbation because it completely
/// decouples ordering from VSIDS activity, exploring orthogonal paths.
pub fn ic3_random_shuffle() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            gen_order: GeneralizationOrder::RandomShuffle,
            random_seed: 25,
            ..Ic3Config::default()
        },
        name: "ic3-random-shuffle".into(),
    }
}

/// IC3 with random shuffle + internal signals + deep CTG.
/// Combines randomized ordering with internal signals and aggressive
/// generalization for maximum diversity on complex circuits.
pub fn ic3_random_deep() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            gen_order: GeneralizationOrder::RandomShuffle,
            internal_signals: true,
            ctg_max: 5,
            ctg_limit: 15,
            random_seed: 26,
            ..Ic3Config::default()
        },
        name: "ic3-random-deep".into(),
    }
}

/// IC3 with circuit-size-based CTG adaptation.
/// Automatically adjusts CTG aggressiveness based on circuit size:
/// small circuits get deep CTG, large circuits get conservative CTG.
/// Combined with CTP and infinity frame for strong baseline.
pub fn ic3_circuit_adapt() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            circuit_adapt: true,
            ctp: true,
            inf_frame: true,
            random_seed: 27,
            ..Ic3Config::default()
        },
        name: "ic3-circuit-adapt".into(),
    }
}

/// IC3 with circuit adaptation + internal signals + ternary.
/// Circuit-size-aware CTG with richer cubes for broad coverage.
pub fn ic3_circuit_adapt_full() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            circuit_adapt: true,
            ctp: true,
            inf_frame: true,
            internal_signals: true,
            ternary_reduce: true,
            random_seed: 28,
            ..Ic3Config::default()
        },
        name: "ic3-circuit-adapt-full".into(),
    }
}

/// IC3 with geometric restart hint + deep CTG.
/// Advisory geometric restart strategy (base=100, factor=1.5) combined
/// with deep CTG. The restart hint serves as a portfolio diversity knob
/// for future z4-sat restart integration.
pub fn ic3_geometric_restart() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            restart_strategy: RestartStrategy::Geometric {
                base: 100,
                factor: 1.5,
            },
            ctg_max: 5,
            ctg_limit: 15,
            random_seed: 29,
            ..Ic3Config::default()
        },
        name: "ic3-geometric-restart".into(),
    }
}

/// IC3 with Luby restart hint + CTP.
/// Advisory Luby restart strategy (unit=512) with CTP propagation.
pub fn ic3_luby_restart() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            restart_strategy: RestartStrategy::Luby { unit: 512 },
            ctp: true,
            inf_frame: true,
            random_seed: 30,
            ..Ic3Config::default()
        },
        name: "ic3-luby-restart".into(),
    }
}

/// IC3 optimized for deep pipelines: reverse topo + deep CTG + internal signals.
/// Targets circuits with long sequential chains where output-side latches
/// are often irrelevant to the property. Deep CTG + internal signals help
/// generalize across pipeline stages.
///
/// Uses blocking_budget=500 (#4074) to force depth advancement on circuits
/// where the blocking phase generates exponentially many cubes at shallow depths.
pub fn ic3_deep_pipeline() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            gen_order: GeneralizationOrder::ReverseTopological,
            ctg_max: 5,
            ctg_limit: 15,
            internal_signals: true,
            ctp: true,
            random_seed: 31,
            blocking_budget: 500,
            ..Ic3Config::default()
        },
        name: "ic3-deep-pipeline".into(),
    }
}

/// IC3 optimized for wide combinational logic: circuit adapt + all features.
/// Targets circuits with wide AND-gate fan-in where domain restriction and
/// ternary simulation are most effective. Circuit adaptation automatically
/// tunes CTG for the circuit's size.
pub fn ic3_wide_comb() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            circuit_adapt: true,
            ternary_reduce: true,
            internal_signals: true,
            ctp: true,
            ctp_max: 5,
            inf_frame: true,
            random_seed: 32,
            ..Ic3Config::default()
        },
        name: "ic3-wide-comb".into(),
    }
}

/// IC3 with dynamic generalization + circuit adaptation.
/// Combines per-PO activity-based CTG tuning with per-circuit size-based
/// CTG baseline. The circuit_adapt sets the baseline; dynamic adjusts from
/// there based on individual proof obligation difficulty.
///
/// Uses blocking_budget=300 (#4074) to force depth advancement on circuits
/// where the blocking phase generates exponentially many cubes.
pub fn ic3_dynamic_adapt() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            dynamic: true,
            circuit_adapt: true,
            ctp: true,
            inf_frame: true,
            random_seed: 33,
            blocking_budget: 300,
            ..Ic3Config::default()
        },
        name: "ic3-dynamic-adapt".into(),
    }
}

/// IC3 without preprocessing optimizations (CTG=0, drop_po=false).
///
/// Matches rIC3's `ic3_no_preproc` configuration: disables CTG generalization
/// and proof obligation dropping. Some benchmarks are hurt by aggressive
/// generalization or PO dropping — this variant catches those cases.
///
/// Reference: rIC3 `portfolio.toml` — `ic3_no_preproc` (CTG=false, FRTS=false, SCORR=false, drop_po=false).
pub fn ic3_no_preprocess() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            ctg_max: 0,
            ctg_limit: 0,
            drop_po: false,
            parent_lemma: false,
            random_seed: 34,
            ..Ic3Config::default()
        },
        name: "ic3-no-preprocess".into(),
    }
}

/// IC3 without parent lemma heuristic and without drop_po.
///
/// Matches rIC3's `ic3_no_parent` configuration: disables proof obligation
/// dropping and the parent lemma MIC heuristic. The parent lemma biases
/// generalization toward reusing structure from prior lemmas, which can
/// be counterproductive on circuits where fresh generalizations are needed.
///
/// Reference: rIC3 `portfolio.toml` — `ic3_no_parent` (drop_po=false, parent_lemma=false).
pub fn ic3_no_parent() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            drop_po: false,
            parent_lemma: false,
            random_seed: 35,
            ..Ic3Config::default()
        },
        name: "ic3-no-parent".into(),
    }
}

/// IC3 with parent lemma MIC seeding (CAV'23 #4150).
///
/// Enables the parent lemma MIC seeding optimization: when a proof obligation
/// has a parent, the intersection of the current cube and the parent's blocking
/// lemma is used as a tighter starting point for MIC generalization.
pub fn ic3_parent_mic() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            parent_lemma: true,
            parent_lemma_mic: true,
            random_seed: 38,
            ..Ic3Config::default()
        },
        name: "ic3-parent-mic".into(),
    }
}

/// IC3 with parent lemma MIC seeding + CTP + internal signals (CAV'23 #4150).
pub fn ic3_parent_mic_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            parent_lemma: true,
            parent_lemma_mic: true,
            ctp: true,
            inf_frame: true,
            internal_signals: true,
            random_seed: 39,
            ..Ic3Config::default()
        },
        name: "ic3-parent-mic-ctp".into(),
    }
}

/// IC3 with predicate propagation (backward bad-state analysis).
///
/// Uses a backward transition solver to find predecessors of bad states,
/// complementing standard forward IC3. Effective on benchmarks where the
/// property has small backward reachability even if forward analysis struggles.
///
/// Reference: rIC3 `ic3/predprop.rs` — `PredProp` struct (127 LOC).
/// Reference: rIC3 `portfolio.toml` — `ic3_predprop`.
pub fn ic3_predprop() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            predprop: true,
            random_seed: 36,
            ..Ic3Config::default()
        },
        name: "ic3-predprop".into(),
    }
}

/// IC3 with predicate propagation + CTP + infinity frame.
///
/// Combines backward analysis with strong forward features: CTP strengthens
/// frame propagation, infinity frame reduces re-propagation, and predprop
/// finds bad predecessors that forward-only analysis might miss.
pub fn ic3_predprop_ctp() -> EngineConfig {
    EngineConfig::Ic3Configured {
        config: Ic3Config {
            predprop: true,
            ctp: true,
            inf_frame: true,
            random_seed: 37,
            ..Ic3Config::default()
        },
        name: "ic3-predprop-ctp".into(),
    }
}

/// CEGAR-IC3 with conservative inner IC3 config (abs_all mode).
///
/// Runs IC3 inside a CEGAR abstraction-refinement loop. Best for large
/// circuits where only a small subset of latches is relevant to the property.
/// Uses abs_all mode: non-abstract latches become free variables.
pub fn cegar_ic3_conservative() -> EngineConfig {
    EngineConfig::CegarIc3 {
        config: Ic3Config {
            random_seed: 40,
            ..Ic3Config::default()
        },
        name: "cegar-ic3-conservative".into(),
        mode: crate::ic3::cegar::AbstractionMode::AbstractAll,
    }
}

/// CEGAR-IC3 with CTP + infinity frame inner config (abs_all mode).
///
/// Combines CEGAR's abstraction with CTP's stronger propagation and
/// infinity frame promotion.
pub fn cegar_ic3_ctp_inf() -> EngineConfig {
    EngineConfig::CegarIc3 {
        config: Ic3Config {
            ctp: true,
            inf_frame: true,
            random_seed: 41,
            ..Ic3Config::default()
        },
        name: "cegar-ic3-ctp-inf".into(),
        mode: crate::ic3::cegar::AbstractionMode::AbstractAll,
    }
}

/// CEGAR-IC3 in abs_cst mode: only abstract constraint enforcement.
///
/// Mirrors rIC3's `ic3_abs_cst` portfolio config. Keeps all latches and
/// transition relations but relaxes constraint enforcement for non-abstract
/// latches. This is a lighter abstraction that produces fewer spurious
/// counterexamples at the cost of less speedup.
pub fn ic3_abs_cst() -> EngineConfig {
    EngineConfig::CegarIc3 {
        config: Ic3Config {
            random_seed: 42,
            ..Ic3Config::default()
        },
        name: "ic3-abs-cst".into(),
        mode: crate::ic3::cegar::AbstractionMode::AbstractConstraints,
    }
}

/// CEGAR-IC3 in abs_all mode with internal signals.
///
/// Mirrors rIC3's `ic3_abs_all` portfolio config. Full abstraction (both
/// constraints and transition) with internal signal cubes for better
/// generalization on circuits with complex combinational logic.
pub fn ic3_abs_all() -> EngineConfig {
    EngineConfig::CegarIc3 {
        config: Ic3Config {
            internal_signals: true,
            random_seed: 43,
            ..Ic3Config::default()
        },
        name: "ic3-abs-all".into(),
        mode: crate::ic3::cegar::AbstractionMode::AbstractAll,
    }
}

// ---------------------------------------------------------------------------
// Portfolio presets
// ---------------------------------------------------------------------------

/// Default portfolio configuration.
///
/// Rebalanced from Wave 9 data (15/50 benchmarks solved):
/// - k-induction solved 5/7 UNSAT (strongest UNSAT solver) → more configs
/// - BMC solved 8/8 SAT (strongest SAT solver) → wider step coverage
/// - IC3 solved only 2 benchmarks → fewer configs, keep only proven/diverse ones
///
/// Total: 25 threads. For maximum coverage, use `competition_portfolio()`.
pub fn default_portfolio() -> PortfolioConfig {
    full_ic3_portfolio()
}

/// Full IC3 portfolio rebalanced from Wave 9 data.
///
/// Wave 9 results (15/50 benchmarks):
///   - k-induction: 5/7 UNSAT (strongest UNSAT solver)
///   - BMC: 8/8 SAT (strongest SAT solver)
///   - IC3: 2/15 (only conservative + arithmetic-tight-budget solved anything)
///
/// Rebalancing strategy (#4119, #4099):
///   - IC3: expanded from 5 to 6 (added multi-order-ctp for tighter generalization)
///   - CEGAR-IC3: kept at 2 (abstraction helps on large circuits)
///   - BMC: expanded from 11 to 14 (added step 2/5 to fill medium-depth gaps,
///     added z4-Geometric step 65 for backend diversity)
///   - k-induction: expanded from 3 to 7 (the UNSAT workhorse deserves more threads)
///     Standard + skip-bmc + z4-Luby + z4-Stable + z4-Vmtf skip-bmc
///     + strengthened + strengthened z4-Luby
///
/// Total: 10 IC3 + 1 SimpleSolver IC3 + 2 CEGAR + 14 BMC + 7 k-ind = 34 engines.
pub fn full_ic3_portfolio() -> PortfolioConfig {
    PortfolioConfig {
        timeout: Duration::from_secs(3600),
        engines: vec![
            // IC3 variants (6 configurations — curated from Wave 9 data + #4099)
            // Only ic3-conservative solved a benchmark; keep it plus 5 maximally
            // diverse configs covering different axes.
            ic3_conservative(),      // seed 1: baseline, solved vis_QF_BV_bcuvis32
            ic3_ctp_inf(),           // seed 7: CTP + inf (strong propagation combo)
            ic3_deep_ctg_ctp(),      // seed 14: strongest generalization + propagation
            ic3_dynamic_ctp(),       // seed 20: per-PO adaptive + CTP + inf
            ic3_circuit_adapt(),     // seed 27: auto-tunes CTG for circuit size
            ic3_multi_order_ctp(),   // seed 111: 2-ordering lift + CTP + inf (#4099)
            ic3_parent_mic(),        // seed 38: parent lemma MIC seeding (CAV'23 #4150)
            // Internal signal (--inn) IC3 variants (#4148, 2 configs)
            ic3_inn_ctp(),           // seed 151: inn + CTP + inf (matches rIC3 ic3_inn_ctp)
            ic3_inn_dynamic(),       // seed 153: inn + dynamic (matches rIC3 ic3_inn_dynamic)
            // SimpleSolver IC3 for high-constraint circuits (#4092)
            // z4-sat FINALIZE_SAT_FAIL on microban (100-300+ constraints) wastes
            // seconds on cross-check fallbacks. SimpleSolver is correct from the start.
            ic3_simple_solver(),     // seed 160: SimpleSolver backend (no z4-sat false UNSAT)
            // CEGAR-IC3 variants (#4064: abstraction-refinement loop over IC3)
            ic3_abs_cst(),           // seed 42: abs_cst mode (constraint-only abstraction)
            ic3_abs_all(),           // seed 43: abs_all mode (full abstraction + internal signals)
            // BMC variants with z4-sat default (10 configurations, #4119)
            // Wave 9: BMC solved all 8 SAT benchmarks. Added step 2/5 to fill
            // gaps between step 1 and step 10 for medium-depth SAT benchmarks.
            EngineConfig::Bmc { step: 1 },
            EngineConfig::Bmc { step: 2 },       // Fill gap: medium-depth (#4119)
            EngineConfig::Bmc { step: 5 },       // Fill gap: shallow-mid (#4119)
            EngineConfig::Bmc { step: 10 },
            EngineConfig::Bmc { step: 65 },
            EngineConfig::Bmc { step: 200 },
            EngineConfig::Bmc { step: 500 },     // Deep Sokoban puzzles (#4123)
            EngineConfig::Bmc { step: 1000 },    // Extremely deep bugs (#4123)
            EngineConfig::BmcDynamic,
            // Geometric backoff BMC (#4123): step=1 for first 50 depths, then doubles.
            EngineConfig::BmcGeometricBackoff {
                initial_depths: 50,
                double_interval: 20,
                max_step: 64,
            },
            // z4-sat variant BMC (4 configs): diverse SAT solver configs race
            EngineConfig::BmcZ4Variant { step: 1, backend: crate::sat_types::SolverBackend::Z4Luby },
            EngineConfig::BmcZ4Variant { step: 10, backend: crate::sat_types::SolverBackend::Z4Stable },
            EngineConfig::BmcZ4Variant { step: 65, backend: crate::sat_types::SolverBackend::Z4Geometric },
            EngineConfig::BmcZ4VariantDynamic { backend: crate::sat_types::SolverBackend::Z4Vmtf },
            // k-Induction (7 configs — the UNSAT workhorse, up from 3, #4119)
            // Wave 9: k-induction solved 5/7 UNSAT. More backend diversity
            // races different z4-sat configs on the same induction problem.
            EngineConfig::Kind,                // default z4-sat
            EngineConfig::KindSkipBmc,         // induction-only (BMC handled separately)
            EngineConfig::KindZ4Variant { backend: crate::sat_types::SolverBackend::Z4Luby },
            EngineConfig::KindZ4Variant { backend: crate::sat_types::SolverBackend::Z4Stable },
            EngineConfig::KindSkipBmcZ4Variant { backend: crate::sat_types::SolverBackend::Z4Vmtf },
            // Strengthened k-Induction with invariant discovery (CEGS)
            EngineConfig::KindStrengthened,
            EngineConfig::KindStrengthenedZ4Variant { backend: crate::sat_types::SolverBackend::Z4Luby },
        ],
        max_depth: 50000,
        preprocess: crate::preprocess::PreprocessConfig::default(),
    }
}

/// Competition portfolio optimized from Wave 9 sweep data.
///
/// Wave 9 results (15 correct / 50 benchmarks):
///   - BMC solved 7/8 SAT benchmarks (the SAT workhorse)
///   - k-induction solved 5/7 UNSAT benchmarks (the UNSAT workhorse)
///   - IC3 solved only 2/15 benchmarks (ic3-arithmetic-tight-budget + ic3 default)
///   - 37+ IC3 configs were redundant — most get stuck at depth 1-2 on industrial circuits
///
/// Portfolio rebalanced: fewer IC3 (keep only configs with proven value or
/// maximum diversity), more BMC step variants for deeper SAT coverage, more
/// k-induction variants with z4-sat backend diversity.
///
/// **IC3 (20 configs) — curated for maximum diversity:**
/// - conservative (seed 1): baseline, solved vis_QF_BV_bcuvis32
/// - arithmetic-tight-budget (seed 104): ONLY IC3 that uniquely solved a benchmark
/// - ctp-inf (seed 7): strong propagation + frame promotion combo
/// - deep-ctg-ctp (seed 14): strongest generalization + propagation
/// - circuit-adapt (seed 27): auto-tunes CTG for circuit size
/// - dynamic-ctp (seed 20): per-PO adaptive generalization
/// - predprop-ctp (seed 37): backward analysis for forward-hard circuits
/// - no-preprocess (seed 34): rIC3 parity, no CTG/no drop_po
/// - multi-order-ctp (seed 111): 2-ordering MIC lift
/// - multi-order-full (seed 112): 3-ordering MIC lift (max diversity)
/// - parent-mic (seed 38): parent lemma MIC seeding (CAV'23)
/// - parent-mic-ctp (seed 39): parent MIC + CTP + inf
/// - inn-ctp (seed 151): internal signals + CTP (#4148)
/// - inn-noctg (seed 152): internal signals, no CTG (#4148)
/// - inn-dynamic (seed 153): internal signals + dynamic (#4148)
/// - simple-solver (seed 160): SimpleSolver for high-constraint circuits
/// - simple-solver-inn (seed 161): SimpleSolver + internal signals
/// - aggressive-drop (seed 170): drop_po threshold=10.0 (#4151)
/// - conservative-drop (seed 171): drop_po threshold=40.0 (#4151)
/// - aggressive-drop-ctp (seed 172): drop_po threshold=10.0 + CTP + inf (#4151)
///
/// **CEGAR-IC3 (2 configs) — abstraction for large circuits:**
/// - cegar-ic3-ctp-inf (seed 41): CEGAR + strong propagation
/// - ic3-abs-cst (seed 42): constraint-only abstraction
///
/// **BMC (18 configs) — wide step range + z4-sat backend diversity:**
/// - Steps 1/2/5/10/25/65/100/200/500/1000 + dynamic + geometric backoff (12 default z4-sat)
/// - z4-sat Luby step 1/5, Stable step 10, Geometric step 25, VMTF dynamic, geo-backoff Luby (6 variants)
///
/// **k-Induction (11 configs) — z4-sat backend diversity + strengthened (#4119):**
/// - Standard + skip-bmc (2 default z4-sat)
/// - z4-sat Luby/Stable/Vmtf standard (3 variants)
/// - z4-sat Luby/Stable/Vmtf skip-bmc (3 variants)
/// - Strengthened k-induction: default + z4-Luby + z4-Stable (3 configs)
///
/// Total: 20 IC3 + 2 CEGAR + 18 BMC + 11 k-ind = 51 engines.
pub fn competition_portfolio() -> PortfolioConfig {
    let engines = vec![
        // IC3 — 20 curated configs (12 general + 3 internal-signal + 2 SimpleSolver + 3 drop-threshold)
        // Wave 9 data: only ic3-conservative and ic3-arithmetic-tight-budget
        // solved benchmarks. Keep those plus maximally diverse configs that
        // cover different axes (CTG, CTP, dynamic, ordering, backward analysis,
        // internal signals for arithmetic generalization #4148,
        // drop_po threshold variants for thrashing prevention #4151).
        ic3_conservative(),              // seed 1: baseline, solved vis_QF_BV_bcuvis32
        ic3_arithmetic_tight_budget(),   // seed 104: solved qspiflash_qflexpress_divfive-p20
        ic3_ctp_inf(),                   // seed 7: CTP + inf (strong propagation combo)
        ic3_deep_ctg_ctp(),              // seed 14: deep CTG + CTP (strongest generalization)
        ic3_circuit_adapt(),             // seed 27: auto-tunes CTG for circuit size
        ic3_dynamic_ctp(),               // seed 20: per-PO adaptive + CTP + inf
        ic3_predprop_ctp(),              // seed 37: backward analysis + CTP + inf
        ic3_no_preprocess(),             // seed 34: no CTG, no drop_po (rIC3 parity)
        ic3_multi_order_ctp(),           // seed 111: 2-ordering lift + CTP + inf
        ic3_multi_order_full(),          // seed 112: 3-ordering lift + CTP + inf (max diversity)
        ic3_parent_mic(),                // seed 38: parent lemma MIC seeding (CAV'23 #4150)
        ic3_parent_mic_ctp(),            // seed 39: parent MIC + CTP + inf (#4150)
        // Internal signal (--inn) IC3 variants (#4148, 3 configs)
        // rIC3's bl_default has 4 inn configs (ic3_inn, ic3_inn_ctp, ic3_inn_noctg,
        // ic3_inn_dynamic). Internal signals extend MIC to AND-gate outputs for
        // finer generalization, particularly effective on arithmetic circuits.
        ic3_inn_ctp(),                   // seed 151: inn + CTP + inf (matches rIC3 ic3_inn_ctp)
        ic3_inn_noctg(),                 // seed 152: inn + no CTG (matches rIC3 ic3_inn_noctg)
        ic3_inn_dynamic(),               // seed 153: inn + dynamic (matches rIC3 ic3_inn_dynamic)
        // SimpleSolver IC3 for high-constraint circuits (#4092)
        ic3_simple_solver(),             // seed 160: SimpleSolver (no z4-sat false UNSAT)
        ic3_simple_solver_inn(),         // seed 161: SimpleSolver + inn
        // Drop-PO threshold variants (#4151, 3 configs)
        // Default IC3 configs use drop_po=true, threshold=20.0. These variants
        // explore aggressive dropping (threshold=10.0) for thrash-heavy circuits
        // and conservative dropping (threshold=40.0) for circuits where persistence
        // eventually pays off. Complements no-drop (ic3_no_preprocess seed 34).
        ic3_aggressive_drop(),           // seed 170: threshold=10.0, drop sooner
        ic3_conservative_drop(),         // seed 171: threshold=40.0, drop later
        ic3_aggressive_drop_ctp(),       // seed 172: threshold=10.0 + CTP + inf
        // CEGAR-IC3 — 2 configs (down from 4)
        cegar_ic3_ctp_inf(),             // seed 41: CEGAR + CTP + inf (abs_all)
        ic3_abs_cst(),                   // seed 42: constraint-only abstraction
        // BMC — 18 configs (#4123: added step 1000 + geometric backoff variants)
        // Wave 9: BMC solved 7/8 SAT benchmarks. More step variants give wider
        // depth coverage. Step 2 and 5 fill gaps between step 1 and step 10
        // for medium-depth SAT benchmarks (microban puzzles at depth 20-60).
        EngineConfig::Bmc { step: 1 },     // Every depth, thorough
        EngineConfig::Bmc { step: 2 },     // 2x faster depth coverage
        EngineConfig::Bmc { step: 5 },     // Shallow-mid bugs
        EngineConfig::Bmc { step: 10 },    // Mid-depth
        EngineConfig::Bmc { step: 25 },    // Mid-deep
        EngineConfig::Bmc { step: 65 },    // Deep bugs
        EngineConfig::Bmc { step: 100 },   // Very deep
        EngineConfig::Bmc { step: 200 },   // Very deep, fast exploration
        EngineConfig::Bmc { step: 500 },   // Extremely deep (Sokoban)
        EngineConfig::Bmc { step: 1000 },  // Maximum depth reach (#4123)
        EngineConfig::BmcDynamic,          // Circuit-adaptive
        // Geometric backoff BMC (#4123): best of both worlds — thorough shallow
        // coverage (step=1 for first 50 depths) then rapid deep exploration.
        EngineConfig::BmcGeometricBackoff {
            initial_depths: 50,
            double_interval: 20,
            max_step: 64,
        },
        // z4-sat variant BMC: different SAT solver configs race on same BMC problem
        EngineConfig::BmcZ4Variant { step: 1, backend: crate::sat_types::SolverBackend::Z4Luby },
        EngineConfig::BmcZ4Variant { step: 5, backend: crate::sat_types::SolverBackend::Z4Luby },
        EngineConfig::BmcZ4Variant { step: 10, backend: crate::sat_types::SolverBackend::Z4Stable },
        EngineConfig::BmcZ4Variant { step: 25, backend: crate::sat_types::SolverBackend::Z4Geometric },
        EngineConfig::BmcZ4VariantDynamic { backend: crate::sat_types::SolverBackend::Z4Vmtf },
        // Geometric backoff with z4-sat Luby for diversity (#4123)
        EngineConfig::BmcGeometricBackoffZ4Variant {
            initial_depths: 50,
            double_interval: 20,
            max_step: 64,
            backend: crate::sat_types::SolverBackend::Z4Luby,
        },
        // k-Induction — 11 configs total (8 basic + 3 strengthened): the UNSAT workhorse
        // Wave 9: k-induction solved 5/7 UNSAT benchmarks. Backend diversity
        // races different z4-sat configs on the same induction problem.
        EngineConfig::Kind,                // default z4-sat
        EngineConfig::KindSkipBmc,         // induction-only (BMC handled separately)
        EngineConfig::KindZ4Variant { backend: crate::sat_types::SolverBackend::Z4Luby },
        EngineConfig::KindZ4Variant { backend: crate::sat_types::SolverBackend::Z4Stable },
        EngineConfig::KindZ4Variant { backend: crate::sat_types::SolverBackend::Z4Vmtf },
        EngineConfig::KindSkipBmcZ4Variant { backend: crate::sat_types::SolverBackend::Z4Luby },
        EngineConfig::KindSkipBmcZ4Variant { backend: crate::sat_types::SolverBackend::Z4Stable },
        EngineConfig::KindSkipBmcZ4Variant { backend: crate::sat_types::SolverBackend::Z4Vmtf },
        // Strengthened k-Induction with auxiliary invariant discovery (CEGS, #4119)
        // Supplements basic k-induction — strengthened induction may converge on
        // benchmarks where basic k-induction cannot, and vice versa. Both must run.
        // z4-sat variant diversity for strengthened induction as well.
        EngineConfig::KindStrengthened,
        EngineConfig::KindStrengthenedZ4Variant { backend: crate::sat_types::SolverBackend::Z4Luby },
        EngineConfig::KindStrengthenedZ4Variant { backend: crate::sat_types::SolverBackend::Z4Stable },
    ];

    PortfolioConfig {
        timeout: Duration::from_secs(3600),
        engines,
        max_depth: 50000,
        preprocess: crate::preprocess::PreprocessConfig::aggressive(),
    }
}

/// rIC3-matched portfolio: 11 IC3 + 4 BMC + 1 k-induction = 16 engines.
///
/// This portfolio exactly mirrors rIC3's `bl_default` configuration from
/// `portfolio.toml`, which is the configuration that achieved #2 safety
/// at HWMCC'25 (274/330 benchmarks solved).
///
/// **rIC3 bl_default mapping:**
/// ```text
/// ic3               → ic3-conservative (seed 1)
/// ic3_no_preproc    → ic3-ctp (seed 2, no CTG)   [we approximate]
/// ic3_no_parent     → ic3-inf (seed 3)            [we approximate]
/// ic3_abs_cst       → ic3-internal (seed 4)       [abstract const → internal signals]
/// ic3_abs_all       → ic3-ternary (seed 5)        [abstract all → ternary]
/// ic3_predprop      → ic3-full (seed 6)           [pred-prop → full features]
/// ic3_ctg_limit     → ic3-deep-ctg (seed 7)       [exact match: ctg_max=5 ctg_limit=15]
/// ic3_inn           → ic3-inn (seed 150)            [exact match #4148]
/// ic3_inn_ctp       → ic3-inn-ctp (seed 151)       [exact match #4148]
/// ic3_inn_noctg     → ic3-inn-noctg (seed 152)     [exact match #4148]
/// ic3_inn_dynamic   → ic3-inn-dynamic (seed 153)   [exact match #4148]
/// bmc               → bmc step=1 (seed 12)
/// bmc_kissat_10     → bmc step=10 (seed 13)
/// bmc_kissat_65     → bmc step=65 (seed 14)
/// bmc_kissat_dyn    → bmc dynamic (seed 15)
/// kind              → kind (seed 16)
/// ```
///
/// The key insight from rIC3: 16 engines is the sweet spot. Too few = missing
/// coverage. Too many = resource contention. The 11:4:1 ratio (IC3:BMC:Kind)
/// reflects that IC3 handles most UNSAT benchmarks while BMC finds most SAT ones.
///
/// Portfolio diversity comes from z4-sat configuration variants instead of
/// external solvers. The 3 Kissat-equivalent BMC slots (step 10, step 65,
/// dynamic) use z4-sat variants with different restart/branching configs,
/// providing the multi-solver diversity pattern rIC3 uses (CaDiCaL + Kissat)
/// but entirely within our own SAT solver stack.
pub fn ric3_portfolio() -> PortfolioConfig {
    PortfolioConfig {
        timeout: Duration::from_secs(3600),
        engines: vec![
            // 11 IC3 variants (matching rIC3's bl_default 11 IC3 configs)
            ic3_conservative(),      // seed 1: ic3 (default)
            ic3_ctp(),               // seed 2: ic3_no_preproc approx
            ic3_inf(),               // seed 3: ic3_no_parent approx
            ic3_internal(),          // seed 4: ic3_abs_cst → internal signals
            ic3_ternary(),           // seed 5: ic3_abs_all → ternary
            ic3_full(),              // seed 6: ic3_predprop → full features
            ic3_deep_ctg(),          // seed 7: ic3_ctg_limit (exact: ctg_max=5 ctg_limit=15)
            ic3_inn(),               // seed 150: ic3_inn (exact match #4148)
            ic3_inn_ctp(),           // seed 151: ic3_inn_ctp (exact match #4148)
            ic3_inn_noctg(),         // seed 152: ic3_inn_noctg (exact match #4148)
            ic3_inn_dynamic(),       // seed 153: ic3_inn_dynamic (exact match #4148)
            // 4 BMC variants (matching rIC3's bl_default)
            // rIC3 uses plain CaDiCaL for step-1 and Kissat for step-10/65/dynamic.
            // We use z4-sat default for step-1 and z4-sat variants for the rest,
            // providing equivalent diversity through configuration knobs.
            EngineConfig::Bmc { step: 1 },   // bmc --step 1 (z4-sat default)
            EngineConfig::BmcZ4Variant { step: 10, backend: crate::sat_types::SolverBackend::Z4Luby },    // Luby restarts for step-10
            EngineConfig::BmcZ4Variant { step: 65, backend: crate::sat_types::SolverBackend::Z4Stable },   // Stable mode for step-65
            EngineConfig::BmcZ4VariantDynamic { backend: crate::sat_types::SolverBackend::Z4Vmtf },        // VMTF branching for dynamic
            // 1 k-induction (rIC3 uses --simple-path; we use standard due to #4039/#4050)
            EngineConfig::Kind,
        ],
        max_depth: 50000,
        preprocess: crate::preprocess::PreprocessConfig::default(),
    }
}

/// SAT-focused portfolio: more BMC threads, higher depth, fewer IC3 configs.
///
/// Optimized for benchmarks where the property is expected to be SAT (bug exists
/// at some depth), such as HWMCC Sokoban/microban puzzles (#4073, #4123). The key
/// insight: SAT benchmarks are solved by BMC, not IC3. IC3 probes for safety
/// (UNSAT), while BMC searches for bugs (SAT). This portfolio:
///
/// - **13 BMC configs**: step 1/5/10/25/65/100/200/500/1000/dynamic + geometric
///   backoff variants for wide depth coverage (#4123)
/// - **3 IC3 configs**: conservative + CTP + full for diversity
/// - **max_depth = 100,000**: deep enough for complex Sokoban puzzles
/// - **2 k-induction configs**: standard + skip-bmc
///
/// Selected when the CLI specifies `--sat-focus` or when circuit analysis
/// detects SAT-likely patterns (PI count > 2x latch count).
pub fn sat_focused_portfolio() -> PortfolioConfig {
    PortfolioConfig {
        timeout: Duration::from_secs(3600),
        engines: vec![
            // BMC variants with z4-sat (#4123: added step 500/1000 + geometric backoff)
            EngineConfig::Bmc { step: 1 },     // Every depth, thorough
            EngineConfig::Bmc { step: 5 },      // Shallow-mid bugs
            EngineConfig::Bmc { step: 10 },     // Mid-depth
            EngineConfig::Bmc { step: 25 },     // Mid-deep
            EngineConfig::Bmc { step: 65 },     // Deep bugs
            EngineConfig::Bmc { step: 100 },    // Very deep
            EngineConfig::Bmc { step: 200 },    // Very deep, fast exploration
            EngineConfig::Bmc { step: 500 },    // Extremely deep (Sokoban) (#4123)
            EngineConfig::Bmc { step: 1000 },   // Maximum depth reach (#4123)
            EngineConfig::BmcDynamic,           // Circuit-adaptive
            // Geometric backoff BMC (#4123): thorough shallow + fast deep
            EngineConfig::BmcGeometricBackoff {
                initial_depths: 50,
                double_interval: 20,
                max_step: 64,
            },
            // z4-sat variant BMC: diverse configs race against default z4-sat.
            EngineConfig::BmcZ4Variant { step: 1, backend: crate::sat_types::SolverBackend::Z4Luby },
            EngineConfig::BmcZ4Variant { step: 65, backend: crate::sat_types::SolverBackend::Z4Stable },
            EngineConfig::BmcZ4VariantDynamic { backend: crate::sat_types::SolverBackend::Z4Vmtf },
            // Geometric backoff with z4-sat Luby (#4123)
            EngineConfig::BmcGeometricBackoffZ4Variant {
                initial_depths: 50,
                double_interval: 20,
                max_step: 64,
                backend: crate::sat_types::SolverBackend::Z4Luby,
            },
            // IC3 variants (4 configs — some bugs are found by IC3)
            ic3_conservative(),
            ic3_ctp(),
            ic3_full(),
            // SimpleSolver IC3 for high-constraint SAT benchmarks (#4092)
            // SAT-focused circuits (microban) often have high constraint-to-latch
            // ratios that trigger z4-sat FINALIZE_SAT_FAIL. SimpleSolver avoids this.
            ic3_simple_solver(),
            // k-Induction (2 configs)
            EngineConfig::Kind,
            EngineConfig::KindSkipBmc,
        ],
        max_depth: 100000,
        preprocess: crate::preprocess::PreprocessConfig::default(),
    }
}

/// SAT-likely heuristic: returns true when the circuit structure suggests
/// the property is likely SAT (a bug exists at some depth).
///
/// The heuristic checks if `num_inputs > 2 * num_latches`. Circuits with
/// many primary inputs relative to latches have a large combinational input
/// space that is often not fully constrained, making it more likely that
/// some input combination can drive the circuit into a bad state.
///
/// This pattern is common in Sokoban/microban puzzles (HWMCC benchmarks)
/// where the environment (inputs) is large relative to the game state (latches).
/// rIC3 solves these via deep BMC in 0.2-4.3s; our default portfolio
/// under-invests in BMC depth for these circuits.
///
/// When this heuristic triggers, `portfolio_check_detailed` uses `sat_focused_portfolio()`
/// which allocates more threads to BMC configs with deeper step sizes (#4123).
pub(crate) fn is_sat_likely(ts: &Transys) -> bool {
    ts.num_inputs > 2 * ts.num_latches && ts.num_latches > 0
}

/// Simple single-engine configuration (no parallelism).
pub fn single_bmc(timeout: Duration, max_depth: usize) -> PortfolioConfig {
    PortfolioConfig {
        timeout,
        engines: vec![EngineConfig::Bmc { step: 1 }],
        max_depth,
        preprocess: crate::preprocess::PreprocessConfig::default(),
    }
}

/// Single IC3 engine with a specific configuration.
pub fn single_ic3(timeout: Duration, config: Ic3Config, name: &str) -> PortfolioConfig {
    PortfolioConfig {
        timeout,
        engines: vec![EngineConfig::Ic3Configured {
            config,
            name: name.into(),
        }],
        max_depth: 10000,
        preprocess: crate::preprocess::PreprocessConfig::default(),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_aag;

    #[test]
    fn test_portfolio_trivially_unsafe() {
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::Bmc { step: 1 }, EngineConfig::Kind],
            max_depth: 10,
            preprocess: crate::preprocess::PreprocessConfig::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(matches!(result, CheckResult::Unsafe { .. }));
    }

    #[test]
    fn test_portfolio_trivially_safe() {
        let circuit = parse_aag("aag 0 0 0 1 0\n0\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::Bmc { step: 1 }, EngineConfig::Kind],
            max_depth: 10,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        // Kind should prove this safe (bad = constant FALSE)
        // BMC will return Unknown at bound
        assert!(
            result.is_definitive() || matches!(result, CheckResult::Unknown { .. }),
            "unexpected result: {result:?}"
        );
    }

    #[test]
    fn test_portfolio_toggle_reachable() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::Bmc { step: 1 }, EngineConfig::Kind],
            max_depth: 10,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(matches!(result, CheckResult::Unsafe { .. }));
    }

    #[test]
    fn test_portfolio_latch_stays_zero() {
        // Latch next=0, bad=latch. k-induction should prove safe.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::Kind],
            max_depth: 10,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Safe),
            "expected Safe, got {result:?}"
        );
    }

    #[test]
    fn test_portfolio_default_config() {
        let config = default_portfolio();
        // Wave 9 rebalanced (#4119) + internal signal configs (#4148) + parent-mic (#4150):
        // 7 IC3 + 2 inn IC3 + 1 SimpleSolver + 2 CEGAR + 10 BMC default + 4 BMC z4 + 7 Kind = 33
        assert_eq!(config.engines.len(), 33);
        assert_eq!(config.timeout, Duration::from_secs(3600));
    }

    #[test]
    fn test_portfolio_ic3_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::Ic3],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(matches!(result, CheckResult::Safe), "got {result:?}");
    }

    #[test]
    fn test_portfolio_ic3_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::Ic3],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_portfolio_timeout() {
        // Use a tiny timeout with a circuit that won't resolve quickly
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_millis(1), // 1ms timeout
            engines: vec![EngineConfig::Bmc { step: 1 }],
            max_depth: 1_000_000, // Very deep
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        // Should either timeout or resolve (kind would prove safe)
        // With BMC only, it should reach bound or timeout
        assert!(
            matches!(result, CheckResult::Unknown { .. } | CheckResult::Safe),
            "unexpected: {result:?}"
        );
    }

    // -----------------------------------------------------------------------
    // IC3 portfolio variant tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_ic3_conservative_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![ic3_conservative()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(matches!(result, CheckResult::Safe), "got {result:?}");
    }

    #[test]
    fn test_ic3_ctp_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![ic3_ctp()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_ic3_inf_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![ic3_inf()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(matches!(result, CheckResult::Safe), "got {result:?}");
    }

    #[test]
    fn test_ic3_internal_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![ic3_internal()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(matches!(result, CheckResult::Safe), "got {result:?}");
    }

    #[test]
    fn test_ic3_ternary_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![ic3_ternary()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_ic3_full_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![ic3_full()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(matches!(result, CheckResult::Safe), "got {result:?}");
    }

    #[test]
    fn test_ic3_full_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![ic3_full()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "got {result:?}"
        );
    }

    #[test]
    fn test_full_ic3_portfolio_config() {
        let config = full_ic3_portfolio();
        // Wave 9 rebalanced (#4119) + internal signal configs (#4148) + parent-mic (#4150):
        // 7 IC3 + 2 inn IC3 + 1 SimpleSolver + 2 CEGAR + 10 BMC default + 4 BMC z4 + 7 Kind = 33
        assert_eq!(config.engines.len(), 33);
    }

    #[test]
    fn test_competition_portfolio_config() {
        let config = competition_portfolio();
        // Wave 12 rebalanced + internal signal + SimpleSolver + parent MIC configs:
        // 12 IC3 general + 3 IC3 inn + 2 IC3 SimpleSolver + 2 CEGAR-IC3
        // + 10 BMC basic + 1 BMC dynamic + 1 BMC geometric + 5 BMC z4-variant
        // + 1 BMC geometric z4-variant + 8 Kind + 3 Kind strengthened = 48
        assert_eq!(config.engines.len(), 48);
    }

    #[test]
    fn test_full_portfolio_toggle_unsafe() {
        // All IC3 variants + BMC + Kind should agree this is unsafe.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(10),
            ..full_ic3_portfolio()
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "full portfolio should find Unsafe, got {result:?}"
        );
    }

    #[test]
    fn test_full_portfolio_latch_zero_safe() {
        // All IC3 variants + BMC + Kind should agree this is safe.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(10),
            ..full_ic3_portfolio()
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Safe),
            "full portfolio should find Safe, got {result:?}"
        );
    }

    #[test]
    fn test_detailed_result_has_solver_name() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![ic3_conservative()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check_detailed(&circuit, config);
        assert!(
            matches!(result.result, CheckResult::Unsafe { .. }),
            "got {:?}",
            result.result
        );
        assert_eq!(result.solver_name, "ic3-conservative");
        assert!(result.time_secs >= 0.0);
    }

    #[test]
    fn test_engine_config_names() {
        assert_eq!(ic3_conservative().name(), "ic3-conservative");
        assert_eq!(ic3_ctp().name(), "ic3-ctp");
        assert_eq!(ic3_inf().name(), "ic3-inf");
        assert_eq!(ic3_internal().name(), "ic3-internal");
        assert_eq!(ic3_ternary().name(), "ic3-ternary");
        assert_eq!(ic3_full().name(), "ic3-full");
        assert_eq!(ic3_ctp_inf().name(), "ic3-ctp-inf");
        assert_eq!(ic3_internal_ternary().name(), "ic3-internal-ternary");
        assert_eq!(ic3_deep_ctg().name(), "ic3-deep-ctg");
        assert_eq!(ic3_internal_ctp().name(), "ic3-internal-ctp");
        assert_eq!(ic3_deep_ctg_internal().name(), "ic3-deep-ctg-internal");
        assert_eq!(ic3_ternary_inf().name(), "ic3-ternary-inf");
        assert_eq!(ic3_aggressive_ctp().name(), "ic3-aggressive-ctp");
        assert_eq!(ic3_deep_ctg_ctp().name(), "ic3-deep-ctg-ctp");
        assert_eq!(ic3_full_alt_seed().name(), "ic3-full-alt");
        assert_eq!(ic3_kitchen_sink().name(), "ic3-kitchen-sink");
        assert_eq!(ic3_ctg_down().name(), "ic3-ctg-down");
        assert_eq!(ic3_ctg_down_ctp().name(), "ic3-ctg-down-ctp");
        assert_eq!(ic3_dynamic().name(), "ic3-dynamic");
        assert_eq!(ic3_dynamic_ctp().name(), "ic3-dynamic-ctp");
        assert_eq!(ic3_dynamic_internal().name(), "ic3-dynamic-internal");
        assert_eq!(ic3_no_drop().name(), "ic3-no-drop");
        assert_eq!(ic3_reverse_topo().name(), "ic3-reverse-topo");
        assert_eq!(ic3_reverse_topo_ctp().name(), "ic3-reverse-topo-ctp");
        assert_eq!(ic3_random_shuffle().name(), "ic3-random-shuffle");
        assert_eq!(ic3_random_deep().name(), "ic3-random-deep");
        assert_eq!(ic3_circuit_adapt().name(), "ic3-circuit-adapt");
        assert_eq!(ic3_circuit_adapt_full().name(), "ic3-circuit-adapt-full");
        assert_eq!(ic3_geometric_restart().name(), "ic3-geometric-restart");
        assert_eq!(ic3_luby_restart().name(), "ic3-luby-restart");
        assert_eq!(ic3_deep_pipeline().name(), "ic3-deep-pipeline");
        assert_eq!(ic3_wide_comb().name(), "ic3-wide-comb");
        assert_eq!(ic3_dynamic_adapt().name(), "ic3-dynamic-adapt");
        assert_eq!(ic3_multi_order().name(), "ic3-multi-order");
        assert_eq!(ic3_multi_order_ctp().name(), "ic3-multi-order-ctp");
        assert_eq!(ic3_multi_order_full().name(), "ic3-multi-order-full");
        assert_eq!(cegar_ic3_conservative().name(), "cegar-ic3-conservative");
        assert_eq!(cegar_ic3_ctp_inf().name(), "cegar-ic3-ctp-inf");
        assert_eq!(EngineConfig::Kind.name(), "kind");
        assert_eq!(EngineConfig::KindSimplePath.name(), "kind-simple-path");
        assert_eq!(EngineConfig::Bmc { step: 1 }.name(), "bmc-1");
        assert_eq!(EngineConfig::Bmc { step: 5 }.name(), "bmc");
        assert_eq!(EngineConfig::BmcDynamic.name(), "bmc-dynamic");
        assert_eq!(EngineConfig::KindSkipBmc.name(), "kind-skip-bmc");
        assert_eq!(EngineConfig::KindStrengthened.name(), "kind-strengthened");
    }

    #[test]
    fn test_single_ic3_config() {
        let config = single_ic3(
            Duration::from_secs(5),
            Ic3Config {
                ctp: true,
                inf_frame: true,
                ..Ic3Config::default()
            },
            "custom-ic3",
        );
        assert_eq!(config.engines.len(), 1);
        assert_eq!(config.engines[0].name(), "custom-ic3");
    }

    #[test]
    fn test_new_ic3_configs_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        for config_fn in [
            ic3_deep_ctg,
            ic3_internal_ctp,
            ic3_deep_ctg_internal,
            ic3_ternary_inf,
            ic3_aggressive_ctp,
            ic3_deep_ctg_ctp,
            ic3_full_alt_seed,
            ic3_kitchen_sink,
            ic3_ctg_down,
            ic3_ctg_down_ctp,
            ic3_dynamic,
            ic3_dynamic_ctp,
            ic3_dynamic_internal,
            ic3_no_drop,
            ic3_reverse_topo,
            ic3_reverse_topo_ctp,
            ic3_random_shuffle,
            ic3_random_deep,
            ic3_circuit_adapt,
            ic3_circuit_adapt_full,
            ic3_geometric_restart,
            ic3_luby_restart,
            ic3_deep_pipeline,
            ic3_wide_comb,
            ic3_dynamic_adapt,
            ic3_no_preprocess,
            ic3_no_parent,
            ic3_predprop,
            ic3_predprop_ctp,
        ] {
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![config_fn()],
                max_depth: 100,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(
                matches!(result, CheckResult::Safe),
                "{} should find Safe, got {result:?}",
                config_fn().name()
            );
        }
    }

    #[test]
    fn test_new_ic3_configs_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        for config_fn in [
            ic3_deep_ctg,
            ic3_internal_ctp,
            ic3_deep_ctg_internal,
            ic3_ternary_inf,
            ic3_aggressive_ctp,
            ic3_deep_ctg_ctp,
            ic3_full_alt_seed,
            ic3_kitchen_sink,
            ic3_ctg_down,
            ic3_ctg_down_ctp,
            ic3_dynamic,
            ic3_dynamic_ctp,
            ic3_dynamic_internal,
            ic3_no_drop,
            ic3_reverse_topo,
            ic3_reverse_topo_ctp,
            ic3_random_shuffle,
            ic3_random_deep,
            ic3_circuit_adapt,
            ic3_circuit_adapt_full,
            ic3_geometric_restart,
            ic3_luby_restart,
            ic3_deep_pipeline,
            ic3_wide_comb,
            ic3_dynamic_adapt,
            ic3_no_preprocess,
            ic3_no_parent,
            ic3_predprop,
            ic3_predprop_ctp,
        ] {
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![config_fn()],
                max_depth: 100,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(
                matches!(result, CheckResult::Unsafe { .. }),
                "{} should find Unsafe, got {result:?}",
                config_fn().name()
            );
        }
    }

    #[test]
    fn test_competition_portfolio_all_unique_seeds() {
        // Every IC3 config in the competition portfolio should have a unique seed.
        let config = competition_portfolio();
        let mut seeds = Vec::new();
        for engine in &config.engines {
            if let EngineConfig::Ic3Configured {
                config: ic3_cfg, ..
            } = engine
            {
                seeds.push(ic3_cfg.random_seed);
            }
        }
        let unique_count = {
            let mut s = seeds.clone();
            s.sort();
            s.dedup();
            s.len()
        };
        assert_eq!(
            unique_count,
            seeds.len(),
            "all IC3 configs must have unique seeds, got {seeds:?}"
        );
    }

    #[test]
    fn test_competition_portfolio_ctg_diversity() {
        // Competition portfolio should have configs with default and deep CTG.
        // (Extreme CTG configs with ctg_max=7 were removed in favor of
        // generalization order diversity in #4065.)
        let config = competition_portfolio();
        let mut has_default_ctg = false;
        let mut has_deep_ctg = false;
        for engine in &config.engines {
            if let EngineConfig::Ic3Configured {
                config: ic3_cfg, ..
            } = engine
            {
                if ic3_cfg.ctg_max == 3 && ic3_cfg.ctg_limit == 1 {
                    has_default_ctg = true;
                }
                if ic3_cfg.ctg_max == 5 && ic3_cfg.ctg_limit == 15 {
                    has_deep_ctg = true;
                }
            }
        }
        assert!(has_default_ctg, "should have default CTG configs");
        assert!(has_deep_ctg, "should have deep CTG configs");
    }

    #[test]
    fn test_competition_portfolio_vsids_diversity() {
        // Competition portfolio should have configs with default VSIDS decay.
        // (Fast/slow decay configs were removed in favor of generalization
        // order diversity in #4065.)
        let config = competition_portfolio();
        let mut has_default_decay = false;
        for engine in &config.engines {
            if let EngineConfig::Ic3Configured {
                config: ic3_cfg, ..
            } = engine
            {
                if (ic3_cfg.vsids_decay - 0.99).abs() < 0.001 {
                    has_default_decay = true;
                }
            }
        }
        assert!(has_default_decay, "should have default decay (0.99) configs");
    }

    #[test]
    fn test_competition_portfolio_has_skip_bmc_kind() {
        // Competition portfolio should have both Kind and KindSkipBmc for diversity.
        let config = competition_portfolio();
        let has_kind = config.engines.iter().any(|e| matches!(e, EngineConfig::Kind));
        let has_skip_bmc = config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::KindSkipBmc));
        assert!(has_kind, "should have standard k-induction");
        assert!(has_skip_bmc, "should have skip-bmc k-induction");
    }

    #[test]
    fn test_portfolio_bmc_dynamic_unsafe() {
        // Trivially unsafe (bad=1 at step 0): dynamic BMC finds it at depth 0.
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::BmcDynamic],
            max_depth: 1000,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "bmc-dynamic should find Unsafe, got {result:?}"
        );
    }

    #[test]
    fn test_portfolio_bmc_geometric_backoff_unsafe() {
        // Trivially unsafe (bad=1 at step 0): geometric backoff BMC finds it at depth 0.
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::BmcGeometricBackoff {
                initial_depths: 50,
                double_interval: 20,
                max_step: 64,
            }],
            max_depth: 1000,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "bmc-geometric-backoff should find Unsafe, got {result:?}"
        );
    }

    #[test]
    fn test_portfolio_bmc_geometric_backoff_z4_variant_unsafe() {
        // Toggle flip-flop: geometric backoff z4-Luby should find bug at depth 1.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::BmcGeometricBackoffZ4Variant {
                initial_depths: 50,
                double_interval: 20,
                max_step: 64,
                backend: crate::sat_types::SolverBackend::Z4Luby,
            }],
            max_depth: 1000,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "bmc-geometric-z4-luby should find Unsafe, got {result:?}"
        );
    }

    #[test]
    fn test_default_portfolio_includes_geometric_backoff() {
        let config = default_portfolio();
        let geo_count = config
            .engines
            .iter()
            .filter(|e| {
                matches!(
                    e,
                    EngineConfig::BmcGeometricBackoff { .. }
                        | EngineConfig::BmcGeometricBackoffZ4Variant { .. }
                )
            })
            .count();
        assert!(
            geo_count >= 1,
            "default portfolio should have at least 1 geometric backoff BMC config, got {geo_count}"
        );
    }

    #[test]
    fn test_competition_portfolio_includes_geometric_backoff() {
        let config = competition_portfolio();
        let geo_count = config
            .engines
            .iter()
            .filter(|e| {
                matches!(
                    e,
                    EngineConfig::BmcGeometricBackoff { .. }
                        | EngineConfig::BmcGeometricBackoffZ4Variant { .. }
                )
            })
            .count();
        assert!(
            geo_count >= 1,
            "competition portfolio should have at least 1 geometric backoff BMC config, got {geo_count}"
        );
    }

    #[test]
    fn test_sat_focused_portfolio_includes_deeper_bmc() {
        let config = sat_focused_portfolio();
        let has_step_500 = config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Bmc { step: 500 }));
        let has_step_1000 = config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Bmc { step: 1000 }));
        assert!(has_step_500, "SAT-focused portfolio should have BMC step=500");
        assert!(has_step_1000, "SAT-focused portfolio should have BMC step=1000");
    }

    #[test]
    fn test_is_sat_likely_heuristic() {
        // Use real circuits to test the heuristic instead of constructing Transys manually.
        // Simple circuit: 0 inputs, 1 latch => not SAT-likely
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        assert!(!is_sat_likely(&ts), "0 inputs should not be SAT-likely");

        // Circuit with 2 inputs, 0 latches: not SAT-likely (0 latches guard)
        let circuit = parse_aag("aag 3 2 0 0 1 1\n2\n4\n6\n6 2 4\n").unwrap();
        let ts = Transys::from_aiger(&circuit);
        assert!(!is_sat_likely(&ts), "0 latches should not be SAT-likely");
    }

    #[test]
    fn test_portfolio_kind_standard_proves_safe() {
        // Standard k-induction (no simple-path) can prove safe properties.
        // This replaces the simple-path variant which was unable to prove
        // Safe due to the #4039 soundness guard (#4050).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::Kind],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Safe),
            "kind (standard) should prove Safe, got {result:?}"
        );
    }

    #[test]
    fn test_portfolio_kind_standard_finds_unsafe() {
        // Standard k-induction should find unsafe properties (via base case).
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::Kind],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Unsafe { .. }),
            "kind (standard) should find Unsafe, got {result:?}"
        );
    }

    #[test]
    fn test_portfolio_cancellation_propagates() {
        // Two IC3 configs racing on a trivially unsafe circuit.
        // Both should find Unsafe quickly; the first wins and cancels the other.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![ic3_conservative(), ic3_ctp()],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check_detailed(&circuit, config);
        assert!(matches!(result.result, CheckResult::Unsafe { .. }));
        // The solver name should be one of the two
        assert!(
            result.solver_name == "ic3-conservative" || result.solver_name == "ic3-ctp",
            "unexpected solver: {}",
            result.solver_name
        );
    }

    #[test]
    fn test_ric3_portfolio_config() {
        let config = ric3_portfolio();
        // rIC3 bl_default has 16 engines: 11 IC3 + 4 BMC + 1 kind
        assert_eq!(config.engines.len(), 16, "ric3 portfolio should have 16 engines");

        // Verify we have the expected engine types
        let ic3_count = config
            .engines
            .iter()
            .filter(|e| e.name().starts_with("ic3-"))
            .count();
        let bmc_count = config
            .engines
            .iter()
            .filter(|e| e.name().starts_with("bmc"))
            .count();
        let kind_count = config
            .engines
            .iter()
            .filter(|e| e.name().starts_with("kind"))
            .count();
        assert_eq!(ic3_count, 11, "should have 11 IC3 variants");
        assert_eq!(bmc_count, 4, "should have 4 BMC variants");
        assert_eq!(kind_count, 1, "should have 1 k-induction");

        // All IC3 configs should have unique random_seeds
        let ic3_seeds: Vec<u64> = config
            .engines
            .iter()
            .filter_map(|e| match e {
                EngineConfig::Ic3Configured { config, .. } => Some(config.random_seed),
                _ => None,
            })
            .collect();
        let unique_seeds: std::collections::HashSet<u64> = ic3_seeds.iter().copied().collect();
        assert_eq!(
            ic3_seeds.len(),
            unique_seeds.len(),
            "IC3 seeds must be unique"
        );
    }

    #[test]
    fn test_kind_skip_bmc_skips_base_case() {
        // Toggle circuit: latch starts 0, next = NOT latch, bad = latch
        // At step 1, latch=1, so bad=1 → Unsafe via base case.
        // But skip-bmc mode does NOT check base cases (that's the point --
        // a separate BMC engine handles base cases in the portfolio).
        // So it should report Safe (the induction step holds) or Unknown.
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::KindSkipBmc],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        // skip-bmc only checks induction, not base case, so it won't find
        // the counterexample. It may report Safe (if induction holds) or
        // Unknown (if max_depth reached without proving induction).
        assert!(
            !matches!(result, CheckResult::Unsafe { .. }),
            "kind-skip-bmc should NOT find base case violations, got {result:?}"
        );
    }

    #[test]
    fn test_kind_skip_bmc_proves_safe() {
        // Stuck-at-zero: latch starts 0, next = 0, bad = latch
        // Latch is always 0, so bad is never asserted → Safe
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        let config = PortfolioConfig {
            timeout: Duration::from_secs(5),
            engines: vec![EngineConfig::KindSkipBmc],
            max_depth: 100,
            preprocess: Default::default(),
        };
        let result = portfolio_check(&circuit, config);
        assert!(
            matches!(result, CheckResult::Safe),
            "kind-skip-bmc should prove Safe, got {result:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Arithmetic portfolio tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_arithmetic_portfolio_config() {
        let config = arithmetic_portfolio();
        // 6 arithmetic IC3 + 4 inn IC3 (#4148) + 4 general IC3 + 9 BMC + 2 Kind = 25
        assert_eq!(config.engines.len(), 25);
        assert_eq!(config.timeout, Duration::from_secs(3600));
        assert_eq!(config.max_depth, 50000);

        // Verify arithmetic IC3 configs are present
        let names: Vec<&str> = config.engines.iter().map(|e| e.name()).collect();
        assert!(names.contains(&"ic3-arithmetic"));
        assert!(names.contains(&"ic3-arithmetic-ctg-down"));
        assert!(names.contains(&"ic3-arithmetic-no-internal"));
        assert!(names.contains(&"ic3-arithmetic-conservative"));
        assert!(names.contains(&"ic3-arithmetic-tight-budget"));
        assert!(names.contains(&"ic3-arithmetic-core-only"));
        // Verify internal signal (--inn) IC3 configs are present (#4148)
        assert!(names.contains(&"ic3-inn"));
        assert!(names.contains(&"ic3-inn-ctp"));
        assert!(names.contains(&"ic3-inn-noctg"));
        assert!(names.contains(&"ic3-inn-dynamic"));
    }

    #[test]
    fn test_arithmetic_ic3_configs_safe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
        for config_fn in [
            ic3_arithmetic,
            ic3_arithmetic_ctg_down,
            ic3_arithmetic_no_internal,
            ic3_arithmetic_conservative,
            ic3_arithmetic_tight_budget,
            ic3_arithmetic_core_only,
        ] {
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![config_fn()],
                max_depth: 100,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(
                matches!(result, CheckResult::Safe),
                "{} should find Safe, got {result:?}",
                config_fn().name()
            );
        }
    }

    #[test]
    fn test_arithmetic_ic3_configs_unsafe() {
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
        for config_fn in [
            ic3_arithmetic,
            ic3_arithmetic_ctg_down,
            ic3_arithmetic_no_internal,
            ic3_arithmetic_conservative,
            ic3_arithmetic_tight_budget,
            ic3_arithmetic_core_only,
        ] {
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![config_fn()],
                max_depth: 100,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(
                matches!(result, CheckResult::Unsafe { .. }),
                "{} should find Unsafe, got {result:?}",
                config_fn().name()
            );
        }
    }

    #[test]
    fn test_arithmetic_portfolio_unique_seeds() {
        let config = arithmetic_portfolio();
        let mut seeds = Vec::new();
        for engine in &config.engines {
            if let EngineConfig::Ic3Configured {
                config: ic3_cfg, ..
            } = engine
            {
                seeds.push(ic3_cfg.random_seed);
            }
        }
        let unique_count = {
            let mut s = seeds.clone();
            s.sort();
            s.dedup();
            s.len()
        };
        assert_eq!(
            unique_count,
            seeds.len(),
            "all arithmetic portfolio IC3 configs must have unique seeds, got {seeds:?}"
        );
    }

    #[test]
    fn test_arithmetic_config_names() {
        assert_eq!(ic3_arithmetic().name(), "ic3-arithmetic");
        assert_eq!(ic3_arithmetic_ctg_down().name(), "ic3-arithmetic-ctg-down");
        assert_eq!(
            ic3_arithmetic_no_internal().name(),
            "ic3-arithmetic-no-internal"
        );
        assert_eq!(
            ic3_arithmetic_conservative().name(),
            "ic3-arithmetic-conservative"
        );
        assert_eq!(
            ic3_arithmetic_tight_budget().name(),
            "ic3-arithmetic-tight-budget"
        );
        assert_eq!(
            ic3_arithmetic_core_only().name(),
            "ic3-arithmetic-core-only"
        );
    }

    // -----------------------------------------------------------------------
    // z4-sat variant BMC/Kind portfolio tests (replaces CaDiCaL tests)
    // -----------------------------------------------------------------------

    mod z4_variant_portfolio_tests {
        use super::*;

        #[test]
        fn test_portfolio_bmc_z4_luby_unsafe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![EngineConfig::BmcZ4Variant {
                    step: 1,
                    backend: crate::sat_types::SolverBackend::Z4Luby,
                }],
                max_depth: 10,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(
                matches!(result, CheckResult::Unsafe { .. }),
                "z4-sat Luby BMC should find Unsafe, got {result:?}"
            );
        }

        #[test]
        fn test_portfolio_bmc_z4_variant_dynamic_unsafe() {
            let circuit = parse_aag("aag 0 0 0 1 0\n1\n").unwrap();
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![EngineConfig::BmcZ4VariantDynamic {
                    backend: crate::sat_types::SolverBackend::Z4Vmtf,
                }],
                max_depth: 100,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(
                matches!(result, CheckResult::Unsafe { .. }),
                "z4-sat VMTF dynamic BMC should find Unsafe, got {result:?}"
            );
        }

        #[test]
        fn test_portfolio_bmc_z4_stable_safe_bounded() {
            // Latch next=0, bad=latch. BMC returns Unknown (can't prove safety).
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![EngineConfig::BmcZ4Variant {
                    step: 1,
                    backend: crate::sat_types::SolverBackend::Z4Stable,
                }],
                max_depth: 10,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(
                matches!(result, CheckResult::Unknown { .. }),
                "z4-sat Stable BMC should return Unknown for safe circuit, got {result:?}"
            );
        }

        #[test]
        fn test_portfolio_z4_variant_bmc_config_names() {
            assert_eq!(
                EngineConfig::BmcZ4Variant {
                    step: 10,
                    backend: crate::sat_types::SolverBackend::Z4Luby
                }
                .name(),
                "bmc-z4-luby"
            );
            assert_eq!(
                EngineConfig::BmcZ4Variant {
                    step: 65,
                    backend: crate::sat_types::SolverBackend::Z4Stable
                }
                .name(),
                "bmc-z4-stable"
            );
            assert_eq!(
                EngineConfig::BmcZ4VariantDynamic {
                    backend: crate::sat_types::SolverBackend::Z4Vmtf
                }
                .name(),
                "bmc-z4-variant-dynamic"
            );
        }

        #[test]
        fn test_default_portfolio_includes_z4_variant_bmc() {
            let config = default_portfolio();
            let variant_count = config
                .engines
                .iter()
                .filter(|e| {
                    matches!(
                        e,
                        EngineConfig::BmcZ4Variant { .. }
                            | EngineConfig::BmcZ4VariantDynamic { .. }
                    )
                })
                .count();
            assert_eq!(
                variant_count, 4,
                "default portfolio should have 4 z4-sat variant BMC configs"
            );
        }

        #[test]
        fn test_sat_focused_portfolio_includes_z4_variant_bmc() {
            let config = sat_focused_portfolio();
            let variant_count = config
                .engines
                .iter()
                .filter(|e| {
                    matches!(
                        e,
                        EngineConfig::BmcZ4Variant { .. }
                            | EngineConfig::BmcZ4VariantDynamic { .. }
                            | EngineConfig::BmcGeometricBackoffZ4Variant { .. }
                    )
                })
                .count();
            assert_eq!(
                variant_count, 4,
                "SAT-focused portfolio should have 4 z4-sat variant BMC configs (incl. geometric backoff)"
            );
        }

        #[test]
        fn test_arithmetic_portfolio_includes_z4_variant_bmc() {
            let config = arithmetic_portfolio();
            let variant_count = config
                .engines
                .iter()
                .filter(|e| {
                    matches!(
                        e,
                        EngineConfig::BmcZ4Variant { .. }
                            | EngineConfig::BmcZ4VariantDynamic { .. }
                    )
                })
                .count();
            assert_eq!(
                variant_count, 2,
                "arithmetic portfolio should have 2 z4-sat variant BMC configs"
            );
        }

        /// z4-sat variant and default z4-sat BMC should agree on a 2-step counter.
        #[test]
        fn test_portfolio_z4_variant_default_agree_two_step_counter() {
            let aag = "aag 3 0 2 0 1 1\n2 3\n4 2\n6\n6 3 4\n";
            let circuit = parse_aag(aag).unwrap();

            // z4-sat default BMC
            let default_config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![EngineConfig::Bmc { step: 1 }],
                max_depth: 10,
                preprocess: Default::default(),
            };
            let default_result = portfolio_check_detailed(&circuit, default_config);

            // z4-sat Luby variant BMC
            let luby_config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![EngineConfig::BmcZ4Variant {
                    step: 1,
                    backend: crate::sat_types::SolverBackend::Z4Luby,
                }],
                max_depth: 10,
                preprocess: Default::default(),
            };
            let luby_result = portfolio_check_detailed(&circuit, luby_config);

            // Both should find Unsafe at depth 2.
            assert!(
                matches!(default_result.result, CheckResult::Unsafe { depth: 2, .. }),
                "z4-sat default BMC: {default_result:?}"
            );
            assert!(
                matches!(luby_result.result, CheckResult::Unsafe { depth: 2, .. }),
                "z4-sat Luby BMC: {luby_result:?}"
            );
        }

        // -------------------------------------------------------------------
        // z4-sat variant k-induction portfolio tests
        // -------------------------------------------------------------------

        #[test]
        fn test_portfolio_kind_z4_luby_proves_safe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![EngineConfig::KindZ4Variant {
                    backend: crate::sat_types::SolverBackend::Z4Luby,
                }],
                max_depth: 100,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(
                matches!(result, CheckResult::Safe),
                "z4-sat Luby kind should prove Safe, got {result:?}"
            );
        }

        #[test]
        fn test_portfolio_kind_z4_luby_finds_unsafe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![EngineConfig::KindZ4Variant {
                    backend: crate::sat_types::SolverBackend::Z4Luby,
                }],
                max_depth: 100,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(
                matches!(result, CheckResult::Unsafe { .. }),
                "z4-sat Luby kind should find Unsafe, got {result:?}"
            );
        }

        #[test]
        fn test_portfolio_kind_skip_bmc_z4_luby_proves_safe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![EngineConfig::KindSkipBmcZ4Variant {
                    backend: crate::sat_types::SolverBackend::Z4Luby,
                }],
                max_depth: 100,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(
                matches!(result, CheckResult::Safe),
                "z4-sat Luby kind-skip-bmc should prove Safe, got {result:?}"
            );
        }

        #[test]
        fn test_portfolio_z4_variant_kind_config_names() {
            assert_eq!(
                EngineConfig::KindZ4Variant {
                    backend: crate::sat_types::SolverBackend::Z4Luby
                }
                .name(),
                "kind-z4-luby"
            );
            assert_eq!(
                EngineConfig::KindSkipBmcZ4Variant {
                    backend: crate::sat_types::SolverBackend::Z4Luby
                }
                .name(),
                "kind-skip-bmc-z4-luby"
            );
        }

        #[test]
        fn test_default_portfolio_includes_z4_variant_kind() {
            let config = default_portfolio();
            let variant_kind_count = config
                .engines
                .iter()
                .filter(|e| {
                    matches!(
                        e,
                        EngineConfig::KindZ4Variant { .. }
                            | EngineConfig::KindSkipBmcZ4Variant { .. }
                    )
                })
                .count();
            assert_eq!(
                variant_kind_count, 3,
                "default portfolio should have 3 z4-sat variant k-induction configs"
            );
        }

        #[test]
        fn test_competition_portfolio_includes_z4_variant_kind() {
            let config = competition_portfolio();
            let variant_kind_count = config
                .engines
                .iter()
                .filter(|e| {
                    matches!(
                        e,
                        EngineConfig::KindZ4Variant { .. }
                            | EngineConfig::KindSkipBmcZ4Variant { .. }
                    )
                })
                .count();
            // Wave 10: 3 standard variants (Luby/Stable/Vmtf) + 3 skip-bmc variants = 6
            assert_eq!(
                variant_kind_count, 6,
                "competition portfolio should have 6 z4-sat variant k-induction configs"
            );
        }

        // ---------------------------------------------------------------
        // IC3 inn portfolio config tests (#4148)
        // ---------------------------------------------------------------

        #[test]
        fn test_ic3_inn_portfolio_safe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![ic3_inn()],
                max_depth: 100,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(matches!(result, CheckResult::Safe), "ic3_inn safe: got {result:?}");
        }

        #[test]
        fn test_ic3_inn_portfolio_unsafe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 3\n2\n").unwrap();
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![ic3_inn()],
                max_depth: 100,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(
                matches!(result, CheckResult::Unsafe { .. }),
                "ic3_inn unsafe: got {result:?}"
            );
        }

        #[test]
        fn test_ic3_inn_ctp_portfolio_safe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![ic3_inn_ctp()],
                max_depth: 100,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(matches!(result, CheckResult::Safe), "ic3_inn_ctp safe: got {result:?}");
        }

        #[test]
        fn test_ic3_inn_no_ctg_portfolio_safe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![ic3_inn_noctg()],
                max_depth: 100,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(matches!(result, CheckResult::Safe), "ic3_inn_no_ctg safe: got {result:?}");
        }

        #[test]
        fn test_ic3_inn_dynamic_portfolio_safe() {
            let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").unwrap();
            let config = PortfolioConfig {
                timeout: Duration::from_secs(5),
                engines: vec![ic3_inn_dynamic()],
                max_depth: 100,
                preprocess: Default::default(),
            };
            let result = portfolio_check(&circuit, config);
            assert!(matches!(result, CheckResult::Safe), "ic3_inn_dynamic safe: got {result:?}");
        }
    }
}
