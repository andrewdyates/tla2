// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Engine scheduling for the CHC portfolio.
//!
//! Handles spawning solver threads, parallel execution with cancellation,
//! and sequential execution with per-engine timeouts.

use super::accept::AcceptDecision;
use super::engines::run_engine;
use super::{PortfolioResult, PortfolioSolver};
use crate::blackboard::{BlackboardHintProvider, SharedBlackboard};
use crate::cancellation::CancellationToken;
#[cfg(test)]
use std::cell::Cell;
use std::sync::{mpsc, Arc};
use std::thread;
use std::time::Duration;

/// Stack size for portfolio solver threads (128 MB).
///
/// Solver threads build deep expression trees during PDKind iterations
/// and PDR generalization. The default 8 MB thread stack overflows on
/// benchmarks like s_multipl_17 and half_true_modif_m. 128 MB gives
/// ample headroom while stacker handles extreme cases via heap growth.
const SOLVER_THREAD_STACK_SIZE: usize = 128 * 1024 * 1024;

/// Grace period after the parallel timeout fires (#7899).
///
/// When the portfolio timeout expires, engines are cooperatively cancelled.
/// However, an engine may be in the final stage of its proof (e.g., the last
/// SMT check before returning Safe) when the timeout fires. Without a grace
/// period, the portfolio returns Unknown even though a definitive result is
/// milliseconds away. This is the primary source of verdict non-determinism:
/// identical harnesses return PROOF on one run and UNKNOWN on the next,
/// depending on whether the winning engine finishes just before or just after
/// the timeout.
///
/// The grace period drains the result channel for this duration after
/// cancellation, accepting any definitive result that arrives.
///
/// Why 2000ms (#7899): The previous 500ms grace was insufficient for zani
/// harnesses where PDR's final SMT check (inductive invariant verification)
/// takes 500-1500ms depending on OS scheduling and memory pressure. 2000ms
/// captures >99% of "just barely missed the timeout" cases based on
/// empirical measurement of zani probe_pop_each_field harnesses. The cost
/// is at most 2s added to the total solve time, which is acceptable for a
/// 27-30s budget (the portfolio already timed out, so the extra 2s is within
/// the 3s margin between the 27s solve budget and 30s wall-clock limit).
const PARALLEL_TIMEOUT_GRACE_PERIOD: Duration = Duration::from_millis(2000);

/// Grace period for sequential engine timeouts (#7899).
///
/// When a sequential engine's budget expires, the engine is cooperatively
/// cancelled. This grace period allows it to finish if it was already in
/// its final computation. Shorter than the parallel grace because sequential
/// mode retries with the next engine, so over-waiting here steals budget
/// from subsequent engines. 500ms is enough to capture final SMT checks
/// without significantly impacting the remaining budget.
const SEQUENTIAL_ENGINE_GRACE_PERIOD: Duration = Duration::from_millis(500);

#[cfg(test)]
std::thread_local! {
    pub(super) static FORCE_SOLVER_THREAD_SPAWN_FAILURE: Cell<bool> = const { Cell::new(false) };
}

/// Extract a human-readable message from a panic payload.
pub(super) fn panic_message(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "unknown panic".to_string()
    }
}

impl PortfolioSolver {
    pub(super) fn spawn_solver_thread<F, T>(task: F) -> std::io::Result<thread::JoinHandle<T>>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        #[cfg(test)]
        if FORCE_SOLVER_THREAD_SPAWN_FAILURE.with(Cell::get) {
            return Err(std::io::Error::other(
                "forced solver thread spawn failure for test",
            ));
        }

        thread::Builder::new()
            .stack_size(SOLVER_THREAD_STACK_SIZE)
            .spawn(task)
    }

    /// Prepare an engine config with cross-engine sharing infrastructure.
    ///
    /// Injects blackboard, lemma cache, and hint providers into the engine
    /// config. This is the single preparation path used by both parallel
    /// and sequential schedulers (#7946).
    fn prepare_engine(
        engine_config: &mut super::types::EngineConfig,
        blackboard: &Arc<SharedBlackboard>,
        lemma_cache: Option<&crate::lemma_cache::LemmaCache>,
        idx: usize,
    ) {
        engine_config.inject_blackboard(blackboard.clone(), idx);
        if let Some(cache) = lemma_cache {
            engine_config.inject_lemma_cache(cache);
            engine_config.seed_from_lemma_cache(cache);
        }
        if let super::types::EngineConfig::Pdr(ref mut pdr) = engine_config {
            let provider = BlackboardHintProvider::new(blackboard.clone(), idx);
            pdr.user_hint_providers.0.push(Arc::new(provider));
        }
    }

    /// Run an engine with panic recovery (#2723, #7946).
    ///
    /// Wraps `run_engine` in `catch_unwind` with backtrace capture.
    /// On panic, returns the engine's `unknown_result()` variant so
    /// the portfolio can continue with remaining engines.
    fn run_engine_guarded(
        engine_config: super::types::EngineConfig,
        problem: crate::ChcProblem,
        idx: usize,
        verbose: bool,
    ) -> super::types::EngineResult {
        let engine_name = engine_config.name();
        let panic_result = engine_config.unknown_result();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            run_engine(engine_config, problem, idx, verbose)
        }));

        match result {
            Ok(engine_result) => engine_result,
            Err(payload) => {
                let bt = std::backtrace::Backtrace::force_capture();
                safe_eprintln!(
                    "Portfolio: Engine {} ({}) panicked: {}\nBacktrace:\n{}",
                    idx,
                    engine_name,
                    panic_message(&*payload),
                    bt
                );
                panic_result
            }
        }
    }

    /// Run engines in parallel, return first definitive result
    pub(super) fn solve_parallel(&self) -> PortfolioResult {
        // Reset global term memory counter for this solve invocation (#2769).
        // Each engine creates its own TermStore; the global counter tracks aggregate
        // allocation so engines can detect OOM conditions cooperatively.
        z4_core::TermStore::reset_global_term_bytes();

        let engine_problem = self.engine_problem().clone();
        let (tx, rx) = mpsc::channel();

        // Create shared cancellation token for cooperative engine stopping
        let cancellation_token = CancellationToken::new();

        if self.config.verbose {
            safe_eprintln!(
                "Portfolio: Starting {} engines in parallel",
                self.config.engines.len()
            );
            if self.should_run_engines_on_original_problem() {
                safe_eprintln!(
                    "Portfolio: Preprocessing erased all predicates but original problem still has them — running engines on original problem"
                );
            }
        }

        // Create cooperative blackboard for cross-engine lemma sharing (#7910).
        // All PDR engines get a BlackboardHintProvider so they can consume lemmas
        // published by other engines during hint application.
        let blackboard = SharedBlackboard::new();

        // Spawn threads for each engine
        let handles: Vec<_> =
            self.config
                .engines
                .iter()
                .enumerate()
                .filter_map(|(idx, engine_config)| {
                    let tx = tx.clone();
                    let problem = engine_problem.clone();
                    let mut engine_config = engine_config.clone();

                    // Prepare engine with cross-engine sharing (#7946).
                    Self::prepare_engine(&mut engine_config, &blackboard, None, idx);

                    let verbose = self.config.verbose;
                    let token = cancellation_token.clone();
                    let engine_name = engine_config.name();

                    match Self::spawn_solver_thread(move || {
                        let mut config = engine_config;
                        config.inject_cancellation_token(token);
                        let result = Self::run_engine_guarded(config, problem, idx, verbose);
                        // Ignore send errors - receiver might have dropped if another engine won
                        let _ = tx.send((idx, result));
                    }) {
                        Ok(handle) => Some(handle),
                        Err(err) => {
                            safe_eprintln!(
                            "Portfolio: Failed to spawn engine {} ({}): {}, treating as Unknown",
                            idx, engine_name, err
                        );
                            None
                        }
                    }
                })
                .collect();

        if handles.is_empty() {
            if self.config.verbose {
                safe_eprintln!("Portfolio: Failed to spawn all engines, returning Unknown");
            }
            return PortfolioResult::Unknown;
        }

        // Drop original sender so channel closes when all threads finish
        drop(tx);

        // Wait for results with optional timeout
        let start_time = std::time::Instant::now();
        let best_result = PortfolioResult::Unknown;
        let mut timed_out = false;
        let mut memory_exceeded = false;

        loop {
            // Calculate remaining timeout (if any)
            let recv_result = if let Some(timeout) = self.config.parallel_timeout {
                let elapsed = start_time.elapsed();
                if elapsed >= timeout {
                    // Timeout expired - cancel all engines and return Unknown
                    cancellation_token.cancel();
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Timeout ({:?}) expired, cancelling all engines",
                            timeout
                        );
                    }
                    timed_out = true;
                    break;
                }
                let remaining = timeout.saturating_sub(elapsed);
                if remaining.is_zero() {
                    cancellation_token.cancel();
                    timed_out = true;
                    break;
                }
                rx.recv_timeout(remaining)
            } else {
                // No timeout - blocking recv
                rx.recv().map_err(|_| mpsc::RecvTimeoutError::Disconnected)
            };

            match recv_result {
                Ok((idx, result)) => {
                    let (portfolio_result, needs_validation, engine_name) =
                        self.convert_engine_result(result);

                    if matches!(
                        &portfolio_result,
                        PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_)
                    ) {
                        match self.accept_or_reject(
                            portfolio_result,
                            needs_validation,
                            engine_name,
                            idx,
                        ) {
                            AcceptDecision::Accept(accepted) => {
                                cancellation_token.cancel();
                                if self.config.verbose {
                                    safe_eprintln!("Portfolio: Engine {} returned definitive result, cancelling others", idx);
                                }
                                return accepted;
                            }
                            AcceptDecision::Reject => continue,
                        }
                    } else {
                        // Unknown/NotApplicable: if global memory is exceeded,
                        // cancel all remaining engines rather than waiting for
                        // each to discover it independently (#2771).
                        if z4_core::TermStore::global_memory_exceeded() {
                            cancellation_token.cancel();
                            if self.config.verbose {
                                safe_eprintln!(
                                    "Portfolio: Global memory exceeded after engine {} returned Unknown, cancelling remaining",
                                    idx
                                );
                            }
                            memory_exceeded = true;
                            break;
                        }
                    }
                }
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    // Timeout expired - cancel all engines and return Unknown
                    cancellation_token.cancel();
                    if self.config.verbose {
                        safe_eprintln!("Portfolio: Timeout expired, cancelling all engines");
                    }
                    timed_out = true;
                    break;
                }
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    // All engines finished without definitive result
                    break;
                }
            }
        }

        // Grace period drain (#7899): after the main loop exits early (timeout
        // or memory exceeded), drain the channel briefly to capture definitive
        // results from engines that already completed. This eliminates verdict
        // non-determinism caused by:
        // 1. Timeout: engines finishing milliseconds after the deadline.
        // 2. Memory exceeded: a definitive result already queued in the channel
        //    from an engine that finished before the OOM-triggering Unknown was
        //    received. Without this drain, the arrival order of mpsc messages
        //    determines whether the portfolio returns Safe or Unknown (#7899).
        if timed_out || memory_exceeded {
            let grace = if memory_exceeded {
                // Memory exceeded: results are already in the channel buffer
                // (no engine is still computing a final answer after OOM), so
                // a non-blocking sweep via Duration::ZERO suffices.
                Duration::ZERO
            } else {
                // Timeout: engines may still be finishing their final SMT check.
                PARALLEL_TIMEOUT_GRACE_PERIOD
            };
            let grace_result = self.drain_channel_for_grace_period(&rx, grace);
            if let Some(accepted) = grace_result {
                if self.config.verbose {
                    let reason = if memory_exceeded {
                        "memory-exceeded drain"
                    } else {
                        "grace period"
                    };
                    safe_eprintln!("Portfolio: Accepted definitive result during {}", reason);
                }
                return accepted;
            }
        }

        // When neither timed out nor memory-exceeded, joining is cheap because
        // all senders have already disconnected. When timed out or OOM, skip
        // joining: engines may be stuck in SMT queries and never observe
        // cancellation. Joining here would violate the portfolio timeout
        // contract and cause the caller to be killed by the outer benchmark
        // timeout.
        if !timed_out && !memory_exceeded {
            for (idx, handle) in handles.into_iter().enumerate() {
                if let Err(payload) = handle.join() {
                    // Engine thread panicked outside catch_unwind (double panic,
                    // FFI unwind, or panic during backtrace capture). Log it so
                    // crashes are visible rather than silently absorbed (#5565).
                    let msg = panic_message(&*payload);
                    safe_eprintln!(
                        "Portfolio: Engine {} thread panicked outside catch_unwind: {}",
                        idx,
                        msg,
                    );
                }
            }
        }

        best_result
    }

    /// Drain the result channel after the main loop exits early (#7899).
    ///
    /// Accepts the first definitive (Safe/Unsafe) result already buffered in
    /// the channel or arriving within `grace` duration.
    ///
    /// Two calling modes:
    /// - **Timeout** (`grace > 0`): engines may be finishing their final SMT
    ///   check. Wait up to `grace` for a definitive result to arrive.
    /// - **Memory exceeded** (`grace == 0`): engines have already sent their
    ///   results. Do a non-blocking sweep of all buffered messages via
    ///   `try_recv` to catch definitive results that lost the mpsc delivery
    ///   race against the Unknown that triggered the OOM break.
    ///
    /// Returns `Some(result)` if a definitive result was found, `None`
    /// otherwise.
    fn drain_channel_for_grace_period(
        &self,
        rx: &mpsc::Receiver<(usize, super::types::EngineResult)>,
        grace: Duration,
    ) -> Option<PortfolioResult> {
        if grace.is_zero() {
            // Non-blocking sweep: drain all already-buffered messages.
            // This is the memory-exceeded path where results are already
            // in the channel; we just need to check them without waiting.
            loop {
                match rx.try_recv() {
                    Ok((idx, result)) => {
                        let (portfolio_result, needs_validation, engine_name) =
                            self.convert_engine_result(result);
                        if matches!(
                            &portfolio_result,
                            PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_)
                        ) {
                            match self.accept_or_reject(
                                portfolio_result,
                                needs_validation,
                                engine_name,
                                idx,
                            ) {
                                AcceptDecision::Accept(accepted) => {
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "Portfolio: Engine {} returned definitive result during channel drain",
                                            idx
                                        );
                                    }
                                    return Some(accepted);
                                }
                                AcceptDecision::Reject => continue,
                            }
                        }
                        // Unknown/NotApplicable: skip, keep draining.
                    }
                    Err(_) => return None, // Empty or disconnected
                }
            }
        }

        // Timed drain: wait up to `grace` for results to arrive.
        let grace_start = std::time::Instant::now();
        loop {
            let remaining = grace.saturating_sub(grace_start.elapsed());
            if remaining.is_zero() {
                return None;
            }
            match rx.recv_timeout(remaining) {
                Ok((idx, result)) => {
                    let (portfolio_result, needs_validation, engine_name) =
                        self.convert_engine_result(result);
                    if matches!(
                        &portfolio_result,
                        PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_)
                    ) {
                        match self.accept_or_reject(
                            portfolio_result,
                            needs_validation,
                            engine_name,
                            idx,
                        ) {
                            AcceptDecision::Accept(accepted) => {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "Portfolio: Engine {} returned definitive result during grace period ({:.0}ms after timeout)",
                                        idx,
                                        grace_start.elapsed().as_secs_f64() * 1000.0
                                    );
                                }
                                return Some(accepted);
                            }
                            AcceptDecision::Reject => continue,
                        }
                    }
                    // Unknown/NotApplicable results are ignored during grace period.
                }
                Err(mpsc::RecvTimeoutError::Timeout) => return None,
                Err(mpsc::RecvTimeoutError::Disconnected) => return None,
            }
        }
    }

    /// Compute the per-engine timeout for sequential budget splitting (#7932).
    ///
    /// Splits the remaining wall-clock budget equally across engines still to
    /// run. Each engine receives `remaining / engines_remaining`, capped by
    /// the configured per-engine timeout. If an engine finishes early, its
    /// unused time is automatically available to subsequent engines because
    /// the function re-measures remaining time on each call.
    ///
    /// Previous approach (50% halving) caused exponential budget decay:
    /// with 11 engines, engine 8+ received <0.2% of the total budget,
    /// causing timeout starvation and ERROR harness results (#7932).
    ///
    /// Equal-share allocation guarantees every engine gets at least
    /// `total_budget / N` seconds, while engines that finish early
    /// donate their surplus to the remaining pool.
    ///
    /// Returns the per-engine timeout for the current engine given:
    /// - `total_timeout`: the configured per-engine timeout (portfolio-level)
    /// - `deadline`: absolute wall-clock deadline for the entire sequential solve
    /// - `engines_remaining`: number of engines left to run (including current)
    pub(super) fn budget_for_engine(
        total_timeout: Duration,
        deadline: std::time::Instant,
        engines_remaining: usize,
    ) -> Duration {
        let now = std::time::Instant::now();
        let remaining = deadline.saturating_duration_since(now);
        if remaining.is_zero() {
            return Duration::ZERO;
        }

        if engines_remaining <= 1 {
            // Last engine gets all remaining budget.
            return remaining.min(total_timeout);
        }

        // Equal share: divide remaining budget evenly across remaining engines.
        // This ensures every engine gets a fair share. If earlier engines finish
        // early, their unused time redistributes automatically because we
        // re-measure `remaining` on each call (#7932).
        let equal_share = remaining / (engines_remaining as u32);

        // Cap at the configured per-engine timeout (don't exceed what the
        // caller requested even if there's plenty of wall-clock budget left).
        equal_share.min(total_timeout)
    }

    /// Run engines sequentially, stopping on first definitive result
    pub(super) fn solve_sequential(&self) -> PortfolioResult {
        // Reset global term memory counter for this solve invocation (#2769).
        z4_core::TermStore::reset_global_term_bytes();

        let engine_problem = self.engine_problem().clone();

        if self.config.verbose {
            safe_eprintln!(
                "Portfolio: Running {} engines sequentially",
                self.config.engines.len()
            );
            if self.should_run_engines_on_original_problem() {
                safe_eprintln!(
                    "Portfolio: Preprocessing erased all predicates but original problem still has them — running engines on original problem"
                );
            }
        }

        // Cross-engine lemma transfer cache (#7919).
        // PDR engines that return Unknown export their learned lemmas here.
        // Subsequent PDR engines receive accumulated lemmas at startup via
        // `PdrConfig::lemma_hints`, seeding their search with prior knowledge.
        let lemma_cache = crate::lemma_cache::LemmaCache::new();

        // Create blackboard for cross-engine information sharing (#7910).
        // In sequential mode, BMC publishes its discovered bounds (safe depths,
        // counterexample depths) and PDR reads them to skip redundant work.
        let blackboard = SharedBlackboard::new();

        // Compute a wall-clock deadline for the entire sequential solve (#7932).
        // When `self.config.timeout` is set, the total budget is used to split
        // time across engines so fallbacks get a fair share. Without a timeout,
        // `deadline` is None and engines run without wall-clock limits.
        let deadline = self.config.timeout.map(|t| std::time::Instant::now() + t);
        let num_engines = self.config.engines.len();

        for (idx, engine_config) in self.config.engines.iter().enumerate() {
            // Check global memory budget before launching next engine (#2771).
            // Previous engine may have exhausted memory and returned Unknown;
            // starting another engine with memory already over budget wastes time.
            if z4_core::TermStore::global_memory_exceeded() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Global memory budget exceeded before engine {}, returning Unknown",
                        idx
                    );
                }
                break;
            }

            // Track which engine type for validation
            let (result, needs_validation, engine_name) = if let Some(timeout) = self.config.timeout
            {
                // Compute this engine's budget share (#7932).
                // `budget_for_engine` splits remaining wall-clock budget equally
                // across remaining engines, ensuring fair allocation (#7932).
                let engines_remaining = num_engines - idx;
                let engine_budget =
                    Self::budget_for_engine(timeout, deadline.unwrap(), engines_remaining);

                if engine_budget.is_zero() {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: No budget remaining for engine {} ({}), skipping",
                            idx,
                            engine_config.name()
                        );
                    }
                    break;
                }

                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Engine {} ({}) budget: {:.1}s of {:.1}s remaining",
                        idx,
                        engine_config.name(),
                        engine_budget.as_secs_f64(),
                        deadline
                            .unwrap()
                            .saturating_duration_since(std::time::Instant::now())
                            .as_secs_f64()
                    );
                }

                // Run each engine in a thread so we can enforce a wall-clock timeout without
                // risking a hang (e.g., stuck SMT queries).
                let (tx, rx) = mpsc::channel();

                let mut engine_config = engine_config.clone();

                // Prepare engine with cross-engine sharing (#7946).
                Self::prepare_engine(&mut engine_config, &blackboard, Some(&lemma_cache), idx);

                let cancellation_token = engine_config.ensure_cancellation_token();

                let problem = engine_problem.clone();
                let verbose = self.config.verbose;
                let engine_name = engine_config.name();

                if verbose && !lemma_cache.is_empty() {
                    safe_eprintln!(
                        "Portfolio: Engine {} ({}) seeded with {} cached lemmas (#7907)",
                        idx,
                        engine_name,
                        lemma_cache.len()
                    );
                }

                if let Err(err) = Self::spawn_solver_thread(move || {
                    let result = Self::run_engine_guarded(engine_config, problem, idx, verbose);
                    // Ignore send errors: receiver might stop waiting due to timeout.
                    let _ = tx.send(result);
                }) {
                    safe_eprintln!(
                        "Portfolio: Failed to spawn engine {} ({}): {}, treating as Unknown",
                        idx,
                        engine_name,
                        err
                    );
                    continue;
                }

                let engine_result = match rx.recv_timeout(engine_budget) {
                    Ok(result) => result,
                    Err(mpsc::RecvTimeoutError::Timeout) => {
                        // Sequential grace period (#7899): the engine may be in
                        // its final SMT check when the budget expires. Cancel
                        // cooperatively, then wait briefly for the result.
                        // This eliminates the same non-determinism pattern as
                        // the parallel grace period: an engine that finishes
                        // 50ms after its budget would return Unknown without
                        // the grace window, but Safe/Unsafe with it.
                        cancellation_token.cancel();
                        match rx.recv_timeout(SEQUENTIAL_ENGINE_GRACE_PERIOD) {
                            Ok(result) => {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "Portfolio: Engine {} completed during grace period after {:.1}s budget",
                                        idx,
                                        engine_budget.as_secs_f64()
                                    );
                                }
                                result
                            }
                            Err(_) => {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "Portfolio: Engine {} timed out after {:.1}s budget + grace, trying next",
                                        idx,
                                        engine_budget.as_secs_f64()
                                    );
                                }
                                continue;
                            }
                        }
                    }
                    Err(mpsc::RecvTimeoutError::Disconnected) => {
                        // Channel disconnected = sender thread exited without sending.
                        // This typically means a double panic (panic inside catch_unwind's
                        // error handler) or FFI unwind. Always log — this is a bug (#5565).
                        safe_eprintln!(
                            "Portfolio: Engine {} channel disconnected without result (possible double panic), trying next",
                            idx
                        );
                        continue;
                    }
                };

                self.convert_engine_result(engine_result)
            } else {
                let engine_name = engine_config.name();

                // Prepare engine with cross-engine sharing (#7946).
                let mut engine_config = engine_config.clone();
                Self::prepare_engine(&mut engine_config, &blackboard, Some(&lemma_cache), idx);

                if self.config.verbose && !lemma_cache.is_empty() {
                    safe_eprintln!(
                        "Portfolio: Engine {} ({}) seeded with {} cached lemmas (#7919)",
                        idx,
                        engine_name,
                        lemma_cache.len()
                    );
                }

                let result = Self::run_engine_guarded(
                    engine_config,
                    engine_problem.clone(),
                    idx,
                    self.config.verbose,
                );
                self.convert_engine_result(result)
            };

            if matches!(
                &result,
                PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_)
            ) {
                match self.accept_or_reject(result, needs_validation, engine_name, idx) {
                    AcceptDecision::Accept(accepted) => {
                        if self.config.verbose {
                            safe_eprintln!("Portfolio: Engine {} returned definitive result", idx);
                        }
                        return accepted;
                    }
                    AcceptDecision::Reject => continue,
                }
            } else if self.config.verbose {
                safe_eprintln!(
                    "Portfolio: Engine {} returned Unknown, trying next (lemma cache: {} lemmas)",
                    idx,
                    lemma_cache.len()
                );
            }
        }

        PortfolioResult::Unknown
    }
}
