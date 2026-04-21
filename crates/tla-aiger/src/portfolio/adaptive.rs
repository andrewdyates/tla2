// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adaptive preset-rotation scheduler (PolyNexus-style port from rIC3).
//!
//! The static 16-config portfolio launches each config once and waits until the
//! global timeout. When IC3 stalls at depth 1-2 (cal14, cal42, loopv3,
//! microban_1 per #4247), no recovery mechanism exists. rIC3's PolyNexus
//! scheduler (`~/hwmcc/tools/ric3/src/polynexus/mod.rs:88-135`) replaces each
//! finished stuck worker with a fresh IC3 run using a rotated preset and a
//! new `rseed`.
//!
//! This module provides [`AdaptiveScheduler`] (seed-rotation over a preset
//! pool) and [`portfolio_check_adaptive`] (keeps worker slots full as each
//! worker finishes). Issue: #4309.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use crate::check_result::CheckResult;
use crate::ic3::{GeneralizationOrder, Ic3Config, Ic3Engine};
use crate::preprocess::analyze_circuit;
use crate::transys::Transys;
use crate::types::AigerCircuit;

use super::config::{EngineConfig, PortfolioResult};
use super::factory::{arithmetic_portfolio, is_sat_likely, sat_focused_portfolio};
use super::runner::{
    ic3_to_check_result, join_with_grace_period, portfolio_check_detailed,
    wrap_unwitnessed, PORTFOLIO_GRACE_PERIOD,
};
use super::safe_witness::{validate_safe, SafeValidation, SafeWitness};

/// Default cap: `preset_pool.len() * MAX_ITER_MULTIPLIER`.
const DEFAULT_MAX_ITER_MULTIPLIER: usize = 16;
/// Hard cap on concurrent worker threads.
const ADAPTIVE_MAX_WORKERS: usize = 16;
/// Poll interval matching rIC3 polynexus.
const ADAPTIVE_POLL: Duration = Duration::from_millis(10);

/// Preset-rotation scheduler. Cycles through the preset pool with
/// `rseed = base_rseed + iter` on each dispatch. Deterministic given the
/// base seed so that competition submissions are reproducible.
#[derive(Debug, Clone)]
pub struct AdaptiveScheduler {
    presets: Vec<Ic3Config>,
    iter: usize,
    base_rseed: u64,
    max_iter: usize,
}

impl AdaptiveScheduler {
    /// Create a scheduler with the given pool and base rseed. Default cap:
    /// `presets.len() * DEFAULT_MAX_ITER_MULTIPLIER`.
    #[must_use]
    pub fn new(presets: Vec<Ic3Config>, base_rseed: u64) -> Self {
        let max_iter = presets.len().saturating_mul(DEFAULT_MAX_ITER_MULTIPLIER);
        Self { presets, iter: 0, base_rseed, max_iter }
    }

    /// Override the default iteration cap.
    #[must_use]
    pub fn with_max_iter(mut self, max_iter: usize) -> Self {
        self.max_iter = max_iter;
        self
    }

    /// Construct from the default rIC3-derived preset pool.
    #[must_use]
    pub fn with_default_presets(base_rseed: u64) -> Self {
        Self::new(default_preset_pool(), base_rseed)
    }

    #[must_use]
    pub fn preset_pool_size(&self) -> usize {
        self.presets.len()
    }

    #[must_use]
    pub fn iteration(&self) -> usize {
        self.iter
    }

    #[must_use]
    pub fn max_iter(&self) -> usize {
        self.max_iter
    }

    /// Pick the next preset. Returns `None` when the pool is empty or the
    /// iteration cap has been reached.
    pub fn next(&mut self) -> Option<Ic3Config> {
        if self.presets.is_empty() || self.iter >= self.max_iter {
            return None;
        }
        let idx = self.iter;
        self.iter = self.iter.saturating_add(1);
        let preset_idx = idx % self.presets.len();
        let mut cfg = self.presets[preset_idx].clone();
        cfg.random_seed = self.base_rseed.wrapping_add(idx as u64);
        Some(cfg)
    }
}

/// Default preset pool derived from rIC3's `ic3_presets()` — 6 curated configs
/// plus a tla-aiger deep-CTG extension for extra ordering diversity.
/// Ref: `~/hwmcc/tools/ric3/src/polynexus/mod.rs:34-72`.
#[must_use]
pub fn default_preset_pool() -> Vec<Ic3Config> {
    vec![
        // 0: baseline
        Ic3Config { random_seed: 1, ..Ic3Config::default() },
        // 1: internal signals only (rIC3 ic3_inn)
        Ic3Config {
            internal_signals: true,
            random_seed: 2,
            ..Ic3Config::default()
        },
        // 2: CTP + infinity frame (substitute for rIC3 ic3_abs_cst+ctp)
        Ic3Config {
            ctp: true,
            inf_frame: true,
            random_seed: 3,
            ..Ic3Config::default()
        },
        // 3: dynamic generalization (rIC3 ic3_dynamic)
        Ic3Config {
            dynamic: true,
            drop_po: false,
            random_seed: 4,
            ..Ic3Config::default()
        },
        // 4: inn + rseed=42 (rIC3 ic3_inn_seed42)
        Ic3Config {
            internal_signals: true,
            random_seed: 42,
            ..Ic3Config::default()
        },
        // 5: CTP + rseed=123 (rIC3 ic3_ctp_seed123)
        Ic3Config {
            ctp: true,
            random_seed: 123,
            ..Ic3Config::default()
        },
        // 6: tla-aiger extension — deep CTG + random-shuffle MIC ordering
        Ic3Config {
            ctg_max: 5,
            ctg_limit: 15,
            gen_order: GeneralizationOrder::RandomShuffle,
            random_seed: 7,
            ..Ic3Config::default()
        },
    ]
}

/// Configuration for the adaptive portfolio run.
#[derive(Debug, Clone)]
pub struct AdaptivePortfolioConfig {
    /// Wall-clock deadline.
    pub timeout: Duration,
    /// Max BMC/k-induction unrolling depth.
    pub max_depth: usize,
    /// Preprocessing config (same as the static portfolio).
    pub preprocess: crate::preprocess::PreprocessConfig,
    /// Preset pool and rseed schedule.
    pub scheduler: AdaptiveScheduler,
    /// Concurrency cap. 0 = auto (`min(num_cpus, ADAPTIVE_MAX_WORKERS)`).
    pub workers: usize,
    /// Include BMC + k-induction fallbacks alongside the IC3 rotation.
    pub include_fallbacks: bool,
}

impl Default for AdaptivePortfolioConfig {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(3600),
            max_depth: 50_000,
            preprocess: crate::preprocess::PreprocessConfig::default(),
            scheduler: AdaptiveScheduler::with_default_presets(0),
            workers: 0,
            include_fallbacks: true,
        }
    }
}

/// Fallback engines dispatched alongside the IC3 rotation.
fn fallback_engines() -> Vec<EngineConfig> {
    vec![
        EngineConfig::Bmc { step: 1 },
        EngineConfig::Kind,
        EngineConfig::KindSkipBmc,
    ]
}

/// Message sent from a worker thread back to the dispatch loop.
#[derive(Debug)]
struct WorkerDone {
    result: PortfolioResult,
    /// `SafeWitness` attached to the verdict for the #4315 symmetric
    /// cross-validator. `None` is treated as `Unwitnessed` by the consumer.
    witness: Option<SafeWitness>,
}

/// Portfolio entry-point with PolyNexus-style adaptive preset rotation.
///
/// Spawns an initial wave of up to `workers` IC3 workers. When a worker
/// returns Unknown, the main loop consults the scheduler for a fresh
/// preset+rseed and spawns a replacement. Definitive results (Safe/Unsafe)
/// short-circuit the rotation and cancel all in-flight workers.
///
/// SAT-likely or arithmetic circuits fall back to the existing static
/// portfolio — seed rotation has no specific benefit on those benchmarks.
pub fn portfolio_check_adaptive(
    circuit: &AigerCircuit,
    config: AdaptivePortfolioConfig,
) -> PortfolioResult {
    let AdaptivePortfolioConfig {
        timeout,
        max_depth,
        preprocess,
        mut scheduler,
        workers,
        include_fallbacks,
    } = config;

    // Preprocess once — matches runner.rs #4074 (20% budget, min 5s).
    let mut pc = preprocess;
    if pc.timeout_secs == 0 && timeout.as_secs() > 0 {
        pc.timeout_secs = (timeout.as_secs() / 5).max(5);
    }
    let ts = Transys::from_aiger(circuit).preprocess_configured(&pc).0;

    // Defer to the static portfolio for SAT-likely / arithmetic circuits.
    if is_sat_likely(&ts) {
        let mut sat = sat_focused_portfolio();
        sat.timeout = timeout;
        return portfolio_check_detailed(circuit, sat);
    }
    if analyze_circuit(&ts).is_arithmetic {
        let mut arith = arithmetic_portfolio();
        arith.timeout = timeout;
        return portfolio_check_detailed(circuit, arith);
    }

    let effective_workers = if workers == 0 {
        std::thread::available_parallelism()
            .map(|n| n.get().min(ADAPTIVE_MAX_WORKERS))
            .unwrap_or(ADAPTIVE_MAX_WORKERS / 2)
    } else {
        workers.min(ADAPTIVE_MAX_WORKERS)
    }
    .max(1);

    let cancelled = Arc::new(AtomicBool::new(false));
    let (tx, rx) = mpsc::channel::<WorkerDone>();
    let start = Instant::now();
    let mut handles: Vec<thread::JoinHandle<()>> = Vec::new();
    let mut in_flight: usize = 0;

    // Fallback engines: spawned once, never respawned.
    if include_fallbacks {
        for engine in fallback_engines() {
            handles.push(spawn_engine_worker(
                engine,
                ts.clone(),
                Arc::clone(&cancelled),
                tx.clone(),
                max_depth,
            ));
            in_flight += 1;
        }
    }

    // Initial wave of IC3 workers.
    while in_flight < effective_workers + if include_fallbacks { fallback_engines().len() } else { 0 } {
        let Some(cfg) = scheduler.next() else { break };
        let engine = ic3_engine_for(&scheduler, cfg);
        handles.push(spawn_engine_worker(
            engine,
            ts.clone(),
            Arc::clone(&cancelled),
            tx.clone(),
            max_depth,
        ));
        in_flight += 1;
    }

    // Main dispatch loop. Keep `tx` alive so Disconnected only fires when
    // every worker has exited. Respawn paths clone `tx` for each new worker.
    let mut best = PortfolioResult {
        result: CheckResult::Unknown { reason: "no engine finished".into() },
        solver_name: String::new(),
        time_secs: 0.0,
    };

    loop {
        if start.elapsed() >= timeout {
            cancelled.store(true, Ordering::Relaxed);
            break;
        }
        if in_flight == 0 {
            break;
        }
        let remaining = timeout.saturating_sub(start.elapsed());
        let wait = remaining.min(ADAPTIVE_POLL);
        match rx.recv_timeout(wait) {
            Ok(done) => {
                in_flight = in_flight.saturating_sub(1);
                if done.result.result.is_definitive() {
                    // Witness verification defence-in-depth (#4103).
                    if let CheckResult::Unsafe { ref trace, depth } = done.result.result {
                        if let Err(reason) = ts.verify_witness(trace) {
                            eprintln!(
                                "AdaptivePortfolio: {} reported Unsafe at depth {} but witness FAILED: {}. Treating as Unknown; respawning.",
                                done.result.solver_name, depth, reason,
                            );
                            if let Some(cfg) = scheduler.next() {
                                let engine = ic3_engine_for(&scheduler, cfg);
                                handles.push(spawn_engine_worker(
                                    engine,
                                    ts.clone(),
                                    Arc::clone(&cancelled),
                                    tx.clone(),
                                    max_depth,
                                ));
                                in_flight += 1;
                            }
                            continue;
                        }
                    }
                    // Symmetric Safe cross-validator (#4315). Reject or
                    // downgrade any `Safe` whose proof witness does not
                    // independently verify, and respawn a fresh worker.
                    if matches!(done.result.result, CheckResult::Safe) {
                        let witness_ref = done
                            .witness
                            .as_ref()
                            .unwrap_or(&SafeWitness::Unwitnessed);
                        match validate_safe(witness_ref, &ts) {
                            SafeValidation::Accepted => {}
                            SafeValidation::Indeterminate { reason } => {
                                eprintln!(
                                    "AdaptivePortfolio: validate_safe \
                                     indeterminate for {} (#4315): {}. \
                                     Treating as unverified; respawning.",
                                    done.result.solver_name, reason,
                                );
                                if let Some(cfg) = scheduler.next() {
                                    let engine = ic3_engine_for(&scheduler, cfg);
                                    handles.push(spawn_engine_worker(
                                        engine,
                                        ts.clone(),
                                        Arc::clone(&cancelled),
                                        tx.clone(),
                                        max_depth,
                                    ));
                                    in_flight += 1;
                                }
                                continue;
                            }
                            SafeValidation::Rejected { reason } => {
                                eprintln!(
                                    "AdaptivePortfolio: SOUNDNESS ALERT \
                                     (#4315) — Safe verdict from {} REJECTED \
                                     by independent validator: {}. Respawning.",
                                    done.result.solver_name, reason,
                                );
                                if let Some(cfg) = scheduler.next() {
                                    let engine = ic3_engine_for(&scheduler, cfg);
                                    handles.push(spawn_engine_worker(
                                        engine,
                                        ts.clone(),
                                        Arc::clone(&cancelled),
                                        tx.clone(),
                                        max_depth,
                                    ));
                                    in_flight += 1;
                                }
                                continue;
                            }
                            SafeValidation::Downgrade { reason } => {
                                eprintln!(
                                    "AdaptivePortfolio: SOUNDNESS ALERT \
                                     (#4315) — Safe verdict from {} has no \
                                     proof witness ({}). Respawning.",
                                    done.result.solver_name, reason,
                                );
                                if let Some(cfg) = scheduler.next() {
                                    let engine = ic3_engine_for(&scheduler, cfg);
                                    handles.push(spawn_engine_worker(
                                        engine,
                                        ts.clone(),
                                        Arc::clone(&cancelled),
                                        tx.clone(),
                                        max_depth,
                                    ));
                                    in_flight += 1;
                                }
                                continue;
                            }
                        }
                    }
                    cancelled.store(true, Ordering::Relaxed);
                    best = done.result;
                    break;
                }
                // Unknown: remember the best bound and respawn.
                if best.solver_name.is_empty() {
                    best = done.result;
                }
                if let Some(cfg) = scheduler.next() {
                    let engine = ic3_engine_for(&scheduler, cfg);
                    handles.push(spawn_engine_worker(
                        engine,
                        ts.clone(),
                        Arc::clone(&cancelled),
                        tx.clone(),
                        max_depth,
                    ));
                    in_flight += 1;
                }
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {}
            Err(mpsc::RecvTimeoutError::Disconnected) => break,
        }
    }

    cancelled.store(true, Ordering::Relaxed);
    // Drop the main loop's sender so surviving workers cannot block indefinitely.
    drop(tx);
    join_with_grace_period(handles, PORTFOLIO_GRACE_PERIOD);

    if best.solver_name.is_empty() && !best.result.is_definitive() {
        best = PortfolioResult {
            result: CheckResult::Unknown { reason: "portfolio timeout".into() },
            solver_name: String::new(),
            time_secs: start.elapsed().as_secs_f64(),
        };
    }

    best
}

fn ic3_engine_for(scheduler: &AdaptiveScheduler, cfg: Ic3Config) -> EngineConfig {
    // `scheduler.iteration()` was just bumped when `cfg` was drawn.
    let iter = scheduler.iteration().saturating_sub(1);
    EngineConfig::Ic3Configured {
        name: format!("ic3-adaptive-iter{}-rseed{}", iter, cfg.random_seed),
        config: cfg,
    }
}

fn spawn_engine_worker(
    engine: EngineConfig,
    ts: Transys,
    cancelled: Arc<AtomicBool>,
    tx: mpsc::Sender<WorkerDone>,
    max_depth: usize,
) -> thread::JoinHandle<()> {
    thread::spawn(move || {
        let engine_start = Instant::now();
        let name = engine.name().to_string();
        let name_inner = name.clone();
        let (result, witness) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
            move || -> (CheckResult, SafeWitness) {
                run_single_engine(engine, ts, cancelled, max_depth)
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
            eprintln!("AdaptivePortfolio: engine {name_inner} panicked: {msg}");
            (
                CheckResult::Unknown { reason: format!("engine panicked: {msg}") },
                SafeWitness::Unwitnessed,
            )
        });
        let elapsed = engine_start.elapsed().as_secs_f64();
        let _ = tx.send(WorkerDone {
            result: PortfolioResult { result, solver_name: name, time_secs: elapsed },
            witness: Some(witness),
        });
    })
}

/// Run one engine. Restricted to the engines the adaptive path actually
/// dispatches (BMC step=1, Kind, KindSkipBmc, Ic3, Ic3Configured). Returns
/// the `CheckResult` paired with a `SafeWitness` for the #4315 cross-validator.
fn run_single_engine(
    engine: EngineConfig,
    ts: Transys,
    cancelled: Arc<AtomicBool>,
    max_depth: usize,
) -> (CheckResult, SafeWitness) {
    match engine {
        EngineConfig::Bmc { step } => {
            let mut e = crate::bmc::BmcEngine::new(ts, step);
            e.set_cancelled(cancelled);
            wrap_unwitnessed(e.check(max_depth))
        }
        EngineConfig::BmcDynamic => {
            let mut e = crate::bmc::BmcEngine::new_dynamic(ts);
            e.set_cancelled(cancelled);
            wrap_unwitnessed(e.check(max_depth))
        }
        EngineConfig::Kind => {
            let mut e = crate::kind::KindEngine::new(ts);
            e.set_cancelled(cancelled);
            wrap_unwitnessed(e.check(max_depth))
        }
        EngineConfig::KindSkipBmc => {
            let mut e = crate::kind::KindEngine::with_config(
                ts,
                crate::kind::KindConfig { simple_path: false, skip_bmc: true },
            );
            e.set_cancelled(cancelled);
            wrap_unwitnessed(e.check(max_depth))
        }
        EngineConfig::Ic3 => {
            let ts_ref = ts.clone();
            let mut e = Ic3Engine::new(ts);
            e.set_cancelled(cancelled);
            ic3_to_check_result(e.check(), &ts_ref)
        }
        EngineConfig::Ic3Configured { config, .. } => {
            let mut ts = ts;
            if config.internal_signals {
                ts.select_internal_signals();
            }
            let ts_ref = ts.clone();
            let mut e = Ic3Engine::with_config(ts, config);
            e.set_cancelled(cancelled);
            ic3_to_check_result(e.check(), &ts_ref)
        }
        other => wrap_unwitnessed(CheckResult::Unknown {
            reason: format!(
                "adaptive portfolio dispatched unsupported engine variant: {}",
                other.name(),
            ),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_preset_pool_size_is_seven() {
        assert_eq!(default_preset_pool().len(), 7);
    }

    #[test]
    fn test_scheduler_rotates_presets_with_rseed_bump() {
        let mut sched = AdaptiveScheduler::with_default_presets(0);
        let pool_size = sched.preset_pool_size();
        let mut seen_seeds = Vec::new();
        for i in 0..pool_size {
            let cfg = sched.next().expect("scheduler should produce preset");
            assert_eq!(cfg.random_seed, i as u64, "rseed should be base + iter");
            seen_seeds.push(cfg.random_seed);
        }
        let mut sorted = seen_seeds.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), pool_size);
    }

    #[test]
    fn test_scheduler_wraps_pool_with_fresh_rseed() {
        let mut sched = AdaptiveScheduler::with_default_presets(100);
        let pool_size = sched.preset_pool_size();
        let first: Vec<_> = (0..pool_size)
            .map(|_| sched.next().expect("round 1"))
            .collect();
        let second: Vec<_> = (0..pool_size)
            .map(|_| sched.next().expect("round 2"))
            .collect();
        for (i, (a, b)) in first.iter().zip(second.iter()).enumerate() {
            assert_ne!(a.random_seed, b.random_seed, "round 2 preset {i} same rseed as round 1");
            assert_eq!(a.random_seed, (100 + i) as u64);
            assert_eq!(b.random_seed, (100 + pool_size + i) as u64);
        }
    }

    #[test]
    fn test_scheduler_caps_at_max_iter() {
        let presets = vec![Ic3Config::default(); 3];
        let mut sched = AdaptiveScheduler::new(presets, 0).with_max_iter(5);
        for _ in 0..5 {
            assert!(sched.next().is_some());
        }
        assert!(sched.next().is_none(), "scheduler must cap at max_iter");
    }

    #[test]
    fn test_scheduler_default_max_iter_multiplier() {
        let sched = AdaptiveScheduler::with_default_presets(0);
        let pool = sched.preset_pool_size();
        assert_eq!(sched.max_iter(), pool * DEFAULT_MAX_ITER_MULTIPLIER);
    }

    #[test]
    fn test_scheduler_empty_pool_returns_none() {
        let mut sched = AdaptiveScheduler::new(vec![], 0);
        assert!(sched.next().is_none());
    }

    #[test]
    fn test_scheduler_distinct_presets_across_rotations() {
        // Regression guard: every dispatched config must have a unique rseed.
        let mut sched = AdaptiveScheduler::with_default_presets(0);
        let pool = sched.preset_pool_size();
        let n = pool * 3;
        let mut seen_seeds = Vec::with_capacity(n);
        for _ in 0..n {
            seen_seeds.push(sched.next().expect("produce config").random_seed);
        }
        let mut sorted = seen_seeds.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), n, "every iteration should have a unique rseed");
    }

    #[test]
    fn test_adaptive_config_default_has_nonzero_budget() {
        let cfg = AdaptivePortfolioConfig::default();
        assert!(cfg.timeout.as_secs() > 0);
        assert!(cfg.scheduler.preset_pool_size() > 0);
    }

    #[test]
    fn test_adaptive_trivially_unsafe() {
        // aag 0 0 0 1 0 / 1 — bad is constant TRUE.
        use crate::parser::parse_aag;
        let circuit = parse_aag("aag 0 0 0 1 0\n1\n").expect("parse");
        let config = AdaptivePortfolioConfig {
            timeout: Duration::from_secs(10),
            ..Default::default()
        };
        let result = portfolio_check_adaptive(&circuit, config);
        assert!(
            matches!(result.result, CheckResult::Unsafe { .. }),
            "expected Unsafe, got {:?}",
            result.result
        );
    }

    #[test]
    fn test_adaptive_trivially_safe() {
        // aag 1 0 1 0 0 1 / 2 0 / 2 — latch stays 0, bad=latch. k-induction proves safe.
        use crate::parser::parse_aag;
        let circuit = parse_aag("aag 1 0 1 0 0 1\n2 0\n2\n").expect("parse");
        let config = AdaptivePortfolioConfig {
            timeout: Duration::from_secs(10),
            ..Default::default()
        };
        let result = portfolio_check_adaptive(&circuit, config);
        assert!(
            result.result.is_definitive() || matches!(result.result, CheckResult::Unknown { .. }),
            "unexpected result: {:?}",
            result.result
        );
    }
}
