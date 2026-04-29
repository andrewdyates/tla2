// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Portfolio runner: parallel engine execution with cooperative cancellation.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use crate::bmc::{BmcEngine, RandomSimEngine};
use crate::check_result::CheckResult;
use crate::ic3::{Ic3Engine, Ic3Result};
use crate::kind::{KindEngine, KindStrengthenedEngine};
use crate::preprocess::analyze_circuit;
use crate::transys::Transys;
use crate::types::AigerCircuit;

use super::config::{EngineConfig, PortfolioConfig, PortfolioResult};
use super::factory::{arithmetic_portfolio, is_sat_likely, sat_focused_portfolio};
use super::safe_witness::{validate_safe, SafeValidation, SafeWitness};

/// Internal channel payload: pairs the public `PortfolioResult` with the
/// optional `SafeWitness` produced by the engine so the aggregation loop can
/// cross-validate `Safe` verdicts (#4315) without changing the public API.
struct EngineOutcome {
    result: PortfolioResult,
    /// `Some(_)` for every engine; encodes how the engine backs up a `Safe`
    /// verdict (InductiveInvariant / Trivial / Unwitnessed). `None` is reserved
    /// for future use and treated the same as `Unwitnessed`.
    witness: Option<SafeWitness>,
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

    // Detect circuit structure and override portfolio if needed.
    //
    // Priority order (#4149): SAT-likely FIRST, then arithmetic.
    // Sokoban/microban puzzles have deep combinational logic (game rule constraints)
    // that triggers the arithmetic heuristic, but they need BMC (SAT-focused portfolio)
    // not IC3 (arithmetic portfolio). SAT-likely check must take priority.
    let config = if is_sat_likely(&ts) {
        eprintln!(
            "Portfolio: SAT-likely heuristic triggered (inputs={} latches={} constraints={}), using SAT-focused portfolio",
            ts.num_inputs, ts.num_latches, ts.constraint_lits.len(),
        );
        let mut sat = sat_focused_portfolio();
        sat.timeout = config.timeout;
        sat
    } else if analyze_circuit(&ts).is_arithmetic {
        let mut arith = arithmetic_portfolio();
        arith.timeout = config.timeout;
        arith
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
            let (result, witness) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                move || -> (CheckResult, SafeWitness) {
                    match cfg {
                        EngineConfig::Bmc { step } => {
                            let mut engine = BmcEngine::new(ts, step);
                            engine.set_cancelled(cancelled);
                            wrap_unwitnessed(engine.check(max_depth))
                        }
                        EngineConfig::BmcDynamic => {
                            let mut engine = BmcEngine::new_dynamic(ts);
                            engine.set_cancelled(cancelled);
                            wrap_unwitnessed(engine.check(max_depth))
                        }
                        EngineConfig::BmcZ4Variant { step, backend } => {
                            let mut engine = BmcEngine::new_with_backend(ts, step, backend);
                            engine.set_cancelled(cancelled);
                            wrap_unwitnessed(engine.check(max_depth))
                        }
                        EngineConfig::BmcZ4VariantDynamic { backend } => {
                            let mut engine = BmcEngine::new_dynamic_with_backend(ts, backend);
                            engine.set_cancelled(cancelled);
                            wrap_unwitnessed(engine.check(max_depth))
                        }
                        EngineConfig::BmcGeometricBackoff {
                            initial_depths,
                            double_interval,
                            max_step,
                        } => {
                            let mut engine = BmcEngine::new_geometric_backoff(ts);
                            engine.set_cancelled(cancelled);
                            wrap_unwitnessed(engine.check_geometric_backoff(
                                max_depth,
                                initial_depths,
                                double_interval,
                                max_step,
                            ))
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
                            wrap_unwitnessed(engine.check_geometric_backoff(
                                max_depth,
                                initial_depths,
                                double_interval,
                                max_step,
                            ))
                        }
                        EngineConfig::BmcLinearOffset {
                            start_depth,
                            step,
                            max_depth: config_max_depth,
                        } => {
                            // Use step=1 as the construction parameter; the
                            // linear-offset runner drives step internally and
                            // relies on unroll_step_no_accumulator for the skip
                            // region. Cap max_depth at the portfolio's overall
                            // cap to stay honest about the budget.
                            let mut engine = BmcEngine::new(ts, 1);
                            engine.set_cancelled(cancelled);
                            wrap_unwitnessed(engine.check_linear_offset(
                                start_depth,
                                step,
                                config_max_depth.min(max_depth),
                            ))
                        }
                        EngineConfig::Kind => {
                            let mut engine = KindEngine::new(ts);
                            engine.set_cancelled(cancelled);
                            wrap_unwitnessed(engine.check(max_depth))
                        }
                        EngineConfig::KindSimplePath => {
                            let mut engine = KindEngine::new_simple_path(ts);
                            engine.set_cancelled(cancelled);
                            wrap_unwitnessed(engine.check(max_depth))
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
                            wrap_unwitnessed(engine.check(max_depth))
                        }
                        EngineConfig::KindZ4Variant { backend } => {
                            let mut engine = KindEngine::with_config_and_backend(
                                ts,
                                crate::kind::KindConfig::default(),
                                backend,
                            );
                            engine.set_cancelled(cancelled);
                            wrap_unwitnessed(engine.check(max_depth))
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
                            wrap_unwitnessed(engine.check(max_depth))
                        }
                        EngineConfig::KindStrengthened => {
                            let mut engine = KindStrengthenedEngine::new(ts);
                            engine.set_cancelled(cancelled);
                            wrap_unwitnessed(engine.check(max_depth))
                        }
                        EngineConfig::KindStrengthenedZ4Variant { backend } => {
                            let mut engine = KindStrengthenedEngine::with_backend(ts, backend);
                            engine.set_cancelled(cancelled);
                            wrap_unwitnessed(engine.check(max_depth))
                        }
                        EngineConfig::Ic3 => {
                            let ts_ref = ts.clone();
                            let mut engine = Ic3Engine::new(ts);
                            engine.set_cancelled(cancelled);
                            ic3_to_check_result(engine.check(), &ts_ref)
                        }
                        EngineConfig::Ic3Configured { config, .. } => {
                            let mut ts = ts;
                            // inn-proper: promote internal signals to first-class latches BEFORE
                            // IC3 engine construction (#4308). Mutually exclusive with the
                            // cube-extension `internal_signals` variant.
                            if config.inn_proper && !config.internal_signals {
                                ts = crate::inn_proper::promote_internal_signals_to_latches(&ts);
                            }
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
                            wrap_unwitnessed(cegar.run())
                        }
                        EngineConfig::RandomSim {
                            steps_per_walk,
                            num_walks,
                            seed,
                        } => {
                            let mut engine =
                                RandomSimEngine::new(ts, steps_per_walk, num_walks, seed);
                            engine.set_cancelled(cancelled);
                            wrap_unwitnessed(engine.check())
                        }
                    }
                },
            ))
            .unwrap_or_else(|panic_info: Box<dyn std::any::Any + Send>| {
                let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                    (*s).to_string()
                } else if let Some(s) = panic_info.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "unknown panic".to_string()
                };
                eprintln!("Portfolio: engine {engine_name_clone} panicked: {msg}");
                (
                    CheckResult::Unknown {
                        reason: format!("engine panicked: {msg}"),
                    },
                    SafeWitness::Unwitnessed,
                )
            });

            let elapsed = engine_start.elapsed().as_secs_f64();
            let _ = tx.send(EngineOutcome {
                result: PortfolioResult {
                    result,
                    solver_name: engine_name,
                    time_secs: elapsed,
                },
                witness: Some(witness),
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
            join_with_grace_period(handles, PORTFOLIO_GRACE_PERIOD);
            return PortfolioResult {
                result: CheckResult::Unknown {
                    reason: "portfolio timeout".into(),
                },
                solver_name: String::new(),
                time_secs: config.timeout.as_secs_f64(),
            };
        }

        match rx.recv_timeout(remaining) {
            Ok(outcome) => {
                let EngineOutcome {
                    result: portfolio_result,
                    witness,
                } = outcome;
                if portfolio_result.result.is_definitive() {
                    match &portfolio_result.result {
                        // Portfolio-level witness verification (#4103):
                        // Before accepting an Unsafe result from ANY engine (BMC,
                        // k-induction, IC3), verify the witness by simulating
                        // the circuit. This is defense-in-depth: BMC/k-ind already
                        // verify internally, but IC3 does not, and this catches
                        // bugs in any engine's witness extraction.
                        CheckResult::Unsafe { .. } => {
                            if !verify_portfolio_unsafe_witness(&ts, &portfolio_result) {
                                // Don't accept this result -- continue waiting
                                // for other engines.
                                continue;
                            }
                            cancelled.store(true, Ordering::Relaxed);
                            join_with_grace_period(handles, PORTFOLIO_GRACE_PERIOD);
                            return portfolio_result;
                        }
                        CheckResult::Safe => {
                            // Symmetric Safe cross-validator (#4315).
                            // Run the independent witness checker BEFORE taking
                            // the cancellation shortcut. On Rejected / Downgrade
                            // we log a SOUNDNESS ALERT and keep waiting for
                            // sibling engines — we do NOT accept the result.
                            let witness_ref = witness.as_ref().unwrap_or(&SafeWitness::Unwitnessed);
                            match validate_safe(witness_ref, &ts) {
                                SafeValidation::Accepted => {}
                                SafeValidation::Indeterminate { reason } => {
                                    eprintln!(
                                        "Portfolio: validate_safe indeterminate \
                                         for {} (#4315): {}. Treating as \
                                         unverified; continuing.",
                                        portfolio_result.solver_name.as_str(),
                                        reason,
                                    );
                                    continue;
                                }
                                SafeValidation::Rejected { reason } => {
                                    eprintln!(
                                        "Portfolio: SOUNDNESS ALERT (#4315) — \
                                         Safe verdict from {} REJECTED by \
                                         independent validator: {}. Continuing \
                                         to wait for other engines.",
                                        portfolio_result.solver_name.as_str(),
                                        reason,
                                    );
                                    continue;
                                }
                                SafeValidation::Downgrade { reason } => {
                                    eprintln!(
                                        "Portfolio: SOUNDNESS ALERT (#4315) — \
                                         Safe verdict from {} has no proof \
                                         witness ({}). Downgrading to \
                                         unverified; continuing.",
                                        portfolio_result.solver_name.as_str(),
                                        reason,
                                    );
                                    continue;
                                }
                            }

                            cancelled.store(true, Ordering::Relaxed);

                            let mut competing = Vec::new();
                            if let Ok(drained) = rx.recv_timeout(SAFE_CROSS_VALIDATION_GRACE) {
                                if verify_portfolio_unsafe_witness(&ts, &drained.result) {
                                    competing.push(drained.result);
                                }
                            }

                            loop {
                                match rx.try_recv() {
                                    Ok(drained) => {
                                        if verify_portfolio_unsafe_witness(&ts, &drained.result) {
                                            competing.push(drained.result);
                                        }
                                    }
                                    Err(mpsc::TryRecvError::Empty)
                                    | Err(mpsc::TryRecvError::Disconnected) => {
                                        break;
                                    }
                                }
                            }

                            let winner = cross_validate_safe_result(portfolio_result, competing);
                            join_with_grace_period(handles, PORTFOLIO_GRACE_PERIOD);
                            return winner;
                        }
                        CheckResult::Unknown { .. } => {
                            unreachable!("definitive result must be Safe or Unsafe")
                        }
                    }
                }
                best = portfolio_result;
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {
                cancelled.store(true, Ordering::Relaxed);
                join_with_grace_period(handles, PORTFOLIO_GRACE_PERIOD);
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
    join_with_grace_period(handles, PORTFOLIO_GRACE_PERIOD);

    best
}

fn verify_portfolio_unsafe_witness(ts: &Transys, portfolio_result: &PortfolioResult) -> bool {
    if let CheckResult::Unsafe { trace, depth } = &portfolio_result.result {
        if let Err(reason) = ts.verify_witness(trace) {
            eprintln!(
                "Portfolio: {} returned Unsafe at depth {} but witness \
                 verification FAILED: {}. Treating as Unknown.",
                portfolio_result.solver_name.as_str(),
                depth,
                reason,
            );
            return false;
        }
    }

    true
}

/// Cross-validate a candidate Safe winner against other completed worker results (#4315).
///
/// In HWMCC, `Unsafe` (SAT) is always ground truth — the counterexample is
/// the witness. If a candidate Safe result is about to be returned but any
/// competing worker result (already drained from the channel) is Unsafe,
/// prefer Unsafe and log an ERROR citing the disagreement.
///
/// If two workers both return Safe with different `solver_name` (so
/// independent confirmation), log an INFO noting the agreement. If only
/// one Safe is present, this is a no-op wrapper.
///
/// Callers MUST have already verified any Unsafe witnesses in `competing`
/// before calling this helper (the helper trusts Unsafe results).
pub(super) fn cross_validate_safe_result(
    candidate_safe: PortfolioResult,
    competing: Vec<PortfolioResult>,
) -> PortfolioResult {
    debug_assert!(matches!(&candidate_safe.result, CheckResult::Safe));

    if let Some(unsafe_result) = competing
        .iter()
        .find(|result| matches!(&result.result, CheckResult::Unsafe { .. }))
    {
        eprintln!(
            "Portfolio: SOUNDNESS ALERT (#4315) — Safe result from {} ({:.3}s) \
             disagreed with Unsafe result from {} ({:.3}s); preferring Unsafe witness.",
            candidate_safe.solver_name.as_str(),
            candidate_safe.time_secs,
            unsafe_result.solver_name.as_str(),
            unsafe_result.time_secs,
        );
        return unsafe_result.clone();
    }

    if let Some(confirming_safe) = competing.iter().find(|result| {
        matches!(&result.result, CheckResult::Safe)
            && result.solver_name.as_str() != candidate_safe.solver_name.as_str()
    }) {
        eprintln!(
            "Portfolio: INFO (#4315) — Safe result from {} ({:.3}s) \
             independently confirmed by {} ({:.3}s).",
            candidate_safe.solver_name.as_str(),
            candidate_safe.time_secs,
            confirming_safe.solver_name.as_str(),
            confirming_safe.time_secs,
        );
    }

    candidate_safe
}

/// Grace period for thread joins after cancellation (#4096).
///
/// After the cancellation flag is set, each engine thread should check
/// `is_cancelled()` at its next cancellation point and exit. The grace
/// period is how long the portfolio waits for threads to respond before
/// detaching them (letting them finish in the background without blocking
/// the caller).
///
/// 3 seconds is generous — well-instrumented threads should exit within
/// milliseconds of seeing the cancellation flag. The only case where
/// threads take longer is if a SAT solver query is in progress and the
/// solver doesn't check its own cancellation flag frequently enough.
pub(super) const PORTFOLIO_GRACE_PERIOD: Duration = Duration::from_secs(3);

/// Grace period for draining competing results after a candidate Safe arrives (#4315).
pub(super) const SAFE_CROSS_VALIDATION_GRACE: Duration = Duration::from_millis(500);

/// Join threads with a grace period (#4096).
///
/// Waits up to `grace` for all threads to finish. If any threads are
/// still running after the grace period, they are detached (the
/// JoinHandle is dropped without joining, allowing the thread to run
/// in the background until it finishes on its own).
///
/// This prevents the portfolio from hanging indefinitely when a thread
/// is stuck in a long SAT solver query that doesn't respect the
/// cancellation flag.
pub(super) fn join_with_grace_period(handles: Vec<thread::JoinHandle<()>>, grace: Duration) {
    let deadline = Instant::now() + grace;
    let mut remaining_handles: Vec<Option<thread::JoinHandle<()>>> =
        handles.into_iter().map(Some).collect();

    // Poll for thread completion until deadline.
    loop {
        let now = Instant::now();
        if now >= deadline {
            break;
        }

        let all_done = remaining_handles.iter().all(|h| h.is_none());
        if all_done {
            return;
        }

        // Check each handle. JoinHandle doesn't have a timed join in std,
        // so we use is_finished() (stable since Rust 1.61) to poll.
        for slot in &mut remaining_handles {
            if let Some(handle) = slot {
                if handle.is_finished() {
                    let h = slot.take().expect("just checked Some");
                    let _ = h.join();
                }
            }
        }

        // Brief sleep to avoid busy-spinning. 10ms is fine for a grace period.
        let remaining_wait = deadline.saturating_duration_since(Instant::now());
        thread::sleep(remaining_wait.min(Duration::from_millis(10)));
    }

    // Grace period exceeded: detach any still-running threads by dropping
    // their JoinHandles. The threads will continue running in the background
    // but won't block the caller.
    let detached_count = remaining_handles.iter().filter(|h| h.is_some()).count();
    if detached_count > 0 {
        eprintln!(
            "Portfolio: {} thread(s) still running after {}s grace period — detaching (#4096)",
            detached_count,
            grace.as_secs_f64(),
        );
    }
    // Dropping the remaining JoinHandles detaches the threads.
    drop(remaining_handles);
}

/// Convert IC3 result to the shared CheckResult type plus the `SafeWitness`
/// attached to any `Safe` verdict (#4315). IC3 is currently the only engine
/// that emits an inductive-invariant witness; other engines are wrapped via
/// [`wrap_unwitnessed`] below.
pub(super) fn ic3_to_check_result(ic3: Ic3Result, ts: &Transys) -> (CheckResult, SafeWitness) {
    match ic3 {
        Ic3Result::Safe { depth, lemmas } => (
            CheckResult::Safe,
            SafeWitness::InductiveInvariant { lemmas, depth },
        ),
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
            (
                CheckResult::Unsafe {
                    depth,
                    trace: named_trace,
                },
                // Unsafe results don't need a Safe witness; Unwitnessed is
                // harmless because validate_safe is only invoked on Safe.
                SafeWitness::Unwitnessed,
            )
        }
        Ic3Result::Unknown { reason } => {
            (CheckResult::Unknown { reason }, SafeWitness::Unwitnessed)
        }
    }
}

/// Wrap an engine result that has no formal witness but passed its own
/// internal verification (#4315).
///
/// For `Safe`: emits `SafeWitness::EngineVerified { engine }`. The validator
/// accepts this without independent re-verification but logs that no
/// symmetric check was performed. Engines that CAN produce a formal invariant
/// (currently only IC3 variants) should emit
/// `SafeWitness::InductiveInvariant` through [`ic3_to_check_result`] so the
/// independent validator can catch #4310-class soundness bugs.
///
/// For `Unsafe`/`Unknown`: the witness is unused — we thread `Unwitnessed`
/// through as a neutral default.
pub(super) fn wrap_engine_verified(
    result: CheckResult,
    engine: &'static str,
) -> (CheckResult, SafeWitness) {
    let witness = match &result {
        CheckResult::Safe => SafeWitness::EngineVerified { engine },
        _ => SafeWitness::Unwitnessed,
    };
    (result, witness)
}

/// Back-compat shim: wraps a result with a generic `EngineVerified` for
/// `Safe` and `Unwitnessed` otherwise. Prefer [`wrap_engine_verified`] with
/// a specific engine label so audit logs identify the source.
pub(super) fn wrap_unwitnessed(result: CheckResult) -> (CheckResult, SafeWitness) {
    wrap_engine_verified(result, "engine")
}
