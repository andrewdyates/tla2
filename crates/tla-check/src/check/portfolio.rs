// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Portfolio orchestrator for parallel multi-strategy verification.
//!
//! Runs up to five verification lanes in parallel:
//! 1. **BFS** — explicit-state model checking (always runs)
//! 2. **Random** — random walk witness search for fast bug finding (always runs)
//! 3. **PDR** — z4-based IC3 symbolic safety proving (z4 feature)
//! 4. **BMC** — z4-based bounded model checking for bug finding (z4 feature)
//! 5. **k-Induction** — z4-based inductive safety proving (z4 feature)
//!
//! The first lane to reach a definitive result publishes its verdict via
//! [`SharedVerdict`], and the other lanes exit early on their next poll.
//!
//! Part of #3717.

use std::sync::Arc;

use tla_core::ast::Module;

use crate::check::{CheckResult, ModelChecker, RandomWalkConfig, RandomWalkResult};
use crate::config::Config;
#[cfg(feature = "z4")]
use crate::eval::EvalCtx;
use crate::shared_verdict::{SharedVerdict, Verdict};

/// Default number of random walks per portfolio run.
const DEFAULT_RANDOM_WALKS: usize = 100;
/// Default maximum depth per random walk.
const DEFAULT_WALK_DEPTH: usize = 10_000;

/// Which lane won the portfolio race.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PortfolioWinner {
    /// BFS explicit-state model checking resolved first.
    Bfs,
    /// Random walk witness search resolved first.
    Random,
    /// PDR (IC3) symbolic checking resolved first.
    Pdr,
    /// BMC symbolic bug finding resolved first.
    Bmc,
    /// k-Induction symbolic proving resolved first.
    KInduction,
}

/// Result of a portfolio verification run.
#[derive(Debug)]
pub struct PortfolioResult {
    /// Which lane resolved the verdict first.
    pub winner: PortfolioWinner,
    /// The BFS result (always present — BFS always runs to completion or early exit).
    pub bfs_result: CheckResult,
    /// The random walk result (always present — random walks always run).
    pub random_result: Option<RandomWalkResult>,
    /// The PDR result, if the z4 feature is enabled and PDR ran successfully.
    /// `None` when PDR is not available (z4 feature disabled) or failed with an error.
    #[cfg(feature = "z4")]
    pub pdr_result: Option<Result<crate::z4_pdr::PdrResult, crate::z4_pdr::PdrError>>,
    /// The BMC result, if the z4 feature is enabled and BMC ran.
    #[cfg(feature = "z4")]
    pub bmc_result: Option<Result<crate::z4_bmc::BmcResult, crate::z4_bmc::BmcError>>,
    /// The k-induction result, if the z4 feature is enabled and k-induction ran.
    #[cfg(feature = "z4")]
    pub kinduction_result: Option<
        Result<crate::z4_kinduction::KInductionResult, crate::z4_kinduction::KInductionError>,
    >,
}

/// Run parallel multi-strategy portfolio verification.
///
/// Creates a [`SharedVerdict`] and spawns all lanes using [`std::thread::scope`].
/// The first lane to resolve wins; the other lanes exit early on their next poll.
///
/// # Arguments
///
/// * `module` - The loaded TLA+ module
/// * `checker_modules` - Additional modules loaded via EXTENDS/INSTANCE
/// * `config` - TLC configuration with INIT, NEXT, INVARIANT
/// * `strategy_filter` - If non-empty, only run strategies whose names are in this list.
///   Valid names: `"bfs"`, `"random"`, `"bmc"`, `"pdr"`, `"kinduction"`.
///   If empty, all strategies run.
///
/// # Returns
///
/// A [`PortfolioResult`] containing the winner and all lane results.
///
/// Part of #3717, #3816.
pub fn run_portfolio(
    module: &Module,
    checker_modules: &[&Module],
    config: &Config,
    strategy_filter: &[String],
) -> PortfolioResult {
    let verdict = Arc::new(SharedVerdict::new());

    // Helper: check if a strategy should run based on the filter.
    let should_run = |name: &str| -> bool {
        strategy_filter.is_empty() || strategy_filter.iter().any(|s| s == name)
    };

    std::thread::scope(|scope| {
        let verdict_bfs = verdict.clone();
        let verdict_random = verdict.clone();
        #[cfg(feature = "z4")]
        let verdict_pdr = verdict.clone();
        #[cfg(feature = "z4")]
        let verdict_bmc = verdict.clone();
        #[cfg(feature = "z4")]
        let verdict_kind = verdict.clone();

        // Lane 1: BFS explicit-state model checking.
        let run_bfs = should_run("bfs");
        let bfs_handle = scope.spawn(move || {
            if !run_bfs {
                verdict_bfs.publish(Verdict::Unknown);
                // Return a minimal success result so the portfolio can still determine a winner.
                return CheckResult::Success(crate::check::CheckStats::default());
            }
            let mut checker = ModelChecker::new_with_extends(module, checker_modules, config);
            checker.set_portfolio_verdict(verdict_bfs);
            checker.check()
        });

        // Lane 2: Random walk witness search (fast bug finding, zero memory).
        let run_random = should_run("random");
        let random_handle = scope.spawn(move || {
            let sv = verdict_random;
            if !run_random {
                sv.publish(Verdict::Unknown);
                return RandomWalkResult::NoViolationFound {
                    walks_completed: 0,
                    total_steps: 0,
                };
            }
            let mut checker = ModelChecker::new_with_extends(module, checker_modules, config);
            let walk_config = RandomWalkConfig {
                num_walks: DEFAULT_RANDOM_WALKS,
                max_depth: DEFAULT_WALK_DEPTH,
                seed: None,
            };
            let result = checker.random_walk(&walk_config);
            // Publish random walk verdict to SharedVerdict.
            let v = match &result {
                RandomWalkResult::InvariantViolation { .. } | RandomWalkResult::Deadlock { .. } => {
                    Verdict::Violated
                }
                RandomWalkResult::NoViolationFound { .. } => Verdict::Unknown,
                RandomWalkResult::Error(_) => Verdict::Unknown,
            };
            sv.publish(v);
            result
        });

        // Lane 3: PDR symbolic checking (z4 feature required).
        #[cfg(feature = "z4")]
        let run_pdr = should_run("pdr");
        #[cfg(feature = "z4")]
        let pdr_handle = scope.spawn(move || {
            let sv = verdict_pdr.clone();
            if !run_pdr {
                sv.publish(Verdict::Unknown);
                return Ok(crate::z4_pdr::PdrResult::Unknown {
                    reason: "filtered out by strategy_filter".to_string(),
                });
            }
            let mut pdr_ctx = EvalCtx::new();
            pdr_ctx.load_module(module);
            // Default PDR config with 300s timeout (matches check_pdr() behavior).
            let mut pdr_config: tla_z4::PdrConfig = Default::default();
            pdr_config.solve_timeout = Some(std::time::Duration::from_secs(300));
            let pdr_result = crate::z4_pdr::check_pdr_with_portfolio(
                module,
                config,
                &pdr_ctx,
                pdr_config,
                Some(verdict_pdr),
            );
            // Publish PDR verdict to SharedVerdict.
            if let Ok(ref result) = pdr_result {
                let v = match result {
                    crate::z4_pdr::PdrResult::Safe { .. } => Verdict::Satisfied,
                    crate::z4_pdr::PdrResult::Unsafe { .. } => Verdict::Violated,
                    crate::z4_pdr::PdrResult::Unknown { .. } => Verdict::Unknown,
                };
                sv.publish(v);
            }
            pdr_result
        });

        // Lane 4: BMC symbolic bug finding (z4 feature required).
        #[cfg(feature = "z4")]
        let run_bmc = should_run("bmc");
        #[cfg(feature = "z4")]
        let bmc_handle = scope.spawn(move || {
            let sv = verdict_bmc.clone();
            if !run_bmc {
                sv.publish(Verdict::Unknown);
                return Ok(crate::z4_bmc::BmcResult::Unknown {
                    depth: 0,
                    reason: "filtered out by strategy_filter".to_string(),
                });
            }
            let mut bmc_ctx = EvalCtx::new();
            bmc_ctx.load_module(module);
            let bmc_config = crate::z4_bmc::BmcConfig {
                max_depth: 20,
                ..Default::default()
            };
            let bmc_result = crate::z4_bmc::check_bmc_with_portfolio(
                module,
                config,
                &bmc_ctx,
                bmc_config,
                Some(verdict_bmc),
            );
            // Publish BMC verdict to SharedVerdict.
            if let Ok(ref result) = bmc_result {
                let v = match result {
                    crate::z4_bmc::BmcResult::Violation { .. } => Verdict::Violated,
                    crate::z4_bmc::BmcResult::BoundReached { .. } => Verdict::Unknown,
                    crate::z4_bmc::BmcResult::Unknown { .. } => Verdict::Unknown,
                };
                sv.publish(v);
            }
            bmc_result
        });

        // Lane 5: k-Induction symbolic proving (z4 feature required).
        #[cfg(feature = "z4")]
        let run_kind = should_run("kinduction");
        #[cfg(feature = "z4")]
        let kind_handle = scope.spawn(move || {
            let sv = verdict_kind.clone();
            if !run_kind {
                sv.publish(Verdict::Unknown);
                return Ok(crate::z4_kinduction::KInductionResult::Unknown {
                    max_k: 0,
                    reason: "filtered out by strategy_filter".to_string(),
                });
            }
            let mut kind_ctx = EvalCtx::new();
            kind_ctx.load_module(module);
            let kind_config = crate::z4_kinduction::KInductionConfig::default();
            let kind_result = crate::z4_kinduction::check_kinduction_with_portfolio(
                module,
                config,
                &kind_ctx,
                kind_config,
                Some(verdict_kind),
            );
            // Publish k-induction verdict to SharedVerdict.
            if let Ok(ref result) = kind_result {
                let v = match result {
                    crate::z4_kinduction::KInductionResult::Proved { .. } => Verdict::Satisfied,
                    crate::z4_kinduction::KInductionResult::Counterexample { .. } => {
                        Verdict::Violated
                    }
                    crate::z4_kinduction::KInductionResult::Unknown { .. } => Verdict::Unknown,
                };
                sv.publish(v);
            }
            kind_result
        });

        let bfs_result = bfs_handle.join().expect("BFS thread panicked");
        let random_result = Some(random_handle.join().expect("Random walk thread panicked"));

        #[cfg(feature = "z4")]
        let pdr_result = Some(pdr_handle.join().expect("PDR thread panicked"));
        #[cfg(feature = "z4")]
        let bmc_result = Some(bmc_handle.join().expect("BMC thread panicked"));
        #[cfg(feature = "z4")]
        let kinduction_result = Some(kind_handle.join().expect("k-induction thread panicked"));

        // Determine winner based on which verdict was published first.
        let winner = determine_winner(&verdict, &bfs_result, &random_result);

        PortfolioResult {
            winner,
            bfs_result,
            random_result,
            #[cfg(feature = "z4")]
            pdr_result,
            #[cfg(feature = "z4")]
            bmc_result,
            #[cfg(feature = "z4")]
            kinduction_result,
        }
    })
}

/// Determine which lane won the portfolio race by examining the published
/// verdict and correlating it with each lane's result.
fn determine_winner(
    verdict: &SharedVerdict,
    bfs_result: &CheckResult,
    random_result: &Option<RandomWalkResult>,
) -> PortfolioWinner {
    match verdict.get() {
        Some(Verdict::Satisfied) => {
            // BFS publishes Satisfied when all states explored with no violation.
            // PDR and k-induction publish Satisfied when they prove the invariant.
            // Random walk never publishes Satisfied (it's an under-approximation).
            match bfs_result {
                CheckResult::Success(_) => PortfolioWinner::Bfs,
                // Could be PDR or k-induction; default to Pdr since it's
                // the more common symbolic prover.
                _ => PortfolioWinner::Pdr,
            }
        }
        Some(Verdict::Violated) => {
            // Check if random walk found a violation first.
            if let Some(
                RandomWalkResult::InvariantViolation { .. } | RandomWalkResult::Deadlock { .. },
            ) = random_result
            {
                // Random walk may have found it first. Check if BFS also found a violation.
                match bfs_result {
                    CheckResult::InvariantViolation { .. }
                    | CheckResult::PropertyViolation { .. }
                    | CheckResult::LivenessViolation { .. } => {
                        // Both found violations; random walk is faster for shallow bugs.
                        // Heuristic: credit random walk since it has zero memory overhead.
                        PortfolioWinner::Random
                    }
                    _ => PortfolioWinner::Random,
                }
            } else {
                match bfs_result {
                    CheckResult::InvariantViolation { .. }
                    | CheckResult::PropertyViolation { .. }
                    | CheckResult::LivenessViolation { .. } => PortfolioWinner::Bfs,
                    // Could be PDR or BMC; default to Bmc since it's the
                    // primary symbolic bug finder.
                    _ => PortfolioWinner::Bmc,
                }
            }
        }
        _ => PortfolioWinner::Bfs, // fallback: BFS always produces a result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test that the portfolio orchestrator runs and the SharedVerdict
    /// is resolved by at least one lane.
    #[test]
    fn test_portfolio_shared_verdict_resolves() {
        let sv = Arc::new(SharedVerdict::new());
        let sv1 = sv.clone();
        let sv2 = sv.clone();

        std::thread::scope(|scope| {
            // Lane 1: publishes Satisfied immediately.
            scope.spawn(move || {
                sv1.publish(Verdict::Satisfied);
            });

            // Lane 2: checks and exits early.
            scope.spawn(move || {
                // Busy-wait until resolved (in real code, this would be
                // interleaved with state processing every 4096 states).
                while !sv2.is_resolved() {
                    std::thread::yield_now();
                }
            });
        });

        assert!(sv.is_resolved());
        assert_eq!(sv.get(), Some(Verdict::Satisfied));
    }

    /// Test that PortfolioWinner variants are all distinguishable.
    #[test]
    fn test_portfolio_winner_variants() {
        let variants = [
            PortfolioWinner::Bfs,
            PortfolioWinner::Random,
            PortfolioWinner::Pdr,
            PortfolioWinner::Bmc,
            PortfolioWinner::KInduction,
        ];
        for i in 0..variants.len() {
            for j in (i + 1)..variants.len() {
                assert_ne!(variants[i], variants[j]);
            }
        }
    }

    /// Test a 5-lane race where all lanes publish concurrently.
    #[test]
    fn test_portfolio_five_lane_race() {
        let sv = Arc::new(SharedVerdict::new());
        let handles: Vec<_> = (0..5)
            .map(|i| {
                let sv = sv.clone();
                std::thread::spawn(move || {
                    let v = if i % 2 == 0 {
                        Verdict::Satisfied
                    } else {
                        Verdict::Violated
                    };
                    sv.publish(v)
                })
            })
            .collect();

        let wins: Vec<bool> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        // Exactly one thread should win.
        assert_eq!(wins.iter().filter(|&&w| w).count(), 1);
        assert!(sv.is_resolved());
    }

    /// Test determine_winner with BFS satisfied.
    #[test]
    fn test_determine_winner_bfs_satisfied() {
        let sv = SharedVerdict::new();
        sv.publish(Verdict::Satisfied);
        let bfs_result = CheckResult::Success(crate::check::CheckStats {
            states_found: 10,
            ..Default::default()
        });
        let random_result = Some(RandomWalkResult::NoViolationFound {
            walks_completed: 100,
            total_steps: 1000,
        });
        let winner = determine_winner(&sv, &bfs_result, &random_result);
        assert_eq!(winner, PortfolioWinner::Bfs);
    }

    /// Test determine_winner with random walk finding violation.
    #[test]
    fn test_determine_winner_random_violated() {
        let sv = SharedVerdict::new();
        sv.publish(Verdict::Violated);
        let bfs_result = CheckResult::Success(crate::check::CheckStats {
            states_found: 10,
            ..Default::default()
        });
        let random_result = Some(RandomWalkResult::InvariantViolation {
            invariant: "TypeOK".to_string(),
            trace: crate::check::Trace {
                states: vec![],
                action_labels: vec![],
            },
            walk_id: 0,
            depth: 3,
        });
        let winner = determine_winner(&sv, &bfs_result, &random_result);
        assert_eq!(winner, PortfolioWinner::Random);
    }

    /// Test determine_winner fallback when verdict unresolved.
    #[test]
    fn test_determine_winner_unresolved_fallback() {
        let sv = SharedVerdict::new();
        let bfs_result = CheckResult::Success(crate::check::CheckStats {
            states_found: 10,
            ..Default::default()
        });
        let random_result = None;
        let winner = determine_winner(&sv, &bfs_result, &random_result);
        assert_eq!(winner, PortfolioWinner::Bfs);
    }
}
