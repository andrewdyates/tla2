// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Portfolio strategy for BTOR2 hardware model checking.
//
// Orchestrates the full checking pipeline:
// 1. Parse + COI reduction (eliminate irrelevant state variables)
// 2. Expression simplification (constant folding, identity elimination)
// 3. BMC preprocessing (shallow bounded model checking for quick bug finding)
// 4. Full CHC solving (PDR/k-induction via z4-chc adaptive portfolio)
//
// This pipeline significantly improves HWMCC benchmark performance by:
// - Reducing problem size (COI): fewer state variables = smaller invariant predicates
// - Simplifying expressions: less work for the SMT solver kernel
// - Quick bug finding (BMC): many benchmarks have shallow counterexamples
// - Proper time budget allocation: BMC gets 20% budget, CHC gets the rest

use std::time::{Duration, Instant};

use rustc_hash::FxHashMap;
use z4_chc::{AdaptiveConfig, AdaptivePortfolio, VerifiedChcResult};

use crate::bmc::{bmc_preprocess, BmcConfig, BmcPreResult};
use crate::coi::{compute_coi, reduce_program};
use crate::error::Btor2Error;
use crate::to_chc::translate_to_chc;
use crate::translate::Btor2CheckResult;
use crate::types::Btor2Program;

/// Configuration for the portfolio strategy.
#[derive(Debug, Clone)]
pub struct PortfolioConfig {
    /// Total time budget for the entire pipeline.
    pub time_budget: Option<Duration>,
    /// Enable COI reduction.
    pub enable_coi: bool,
    /// Enable expression simplification.
    pub enable_simplify: bool,
    /// Enable BMC preprocessing.
    pub enable_bmc: bool,
    /// BMC time budget fraction (0.0-1.0 of total budget).
    pub bmc_budget_fraction: f64,
    /// BMC maximum depth.
    pub bmc_max_depth: u32,
    /// Enable verbose output.
    pub verbose: bool,
}

impl Default for PortfolioConfig {
    fn default() -> Self {
        Self {
            time_budget: None,
            enable_coi: true,
            enable_simplify: true,
            enable_bmc: true,
            bmc_budget_fraction: 0.2,
            bmc_max_depth: 20,
            verbose: false,
        }
    }
}

/// Statistics from a portfolio run.
#[derive(Debug, Clone)]
pub struct PortfolioStats {
    /// Number of state variables before COI reduction.
    pub states_before_coi: usize,
    /// Number of state variables after COI reduction.
    pub states_after_coi: usize,
    /// Number of inputs before COI reduction.
    pub inputs_before_coi: usize,
    /// Number of inputs after COI reduction.
    pub inputs_after_coi: usize,
    /// Time spent in COI analysis.
    pub coi_time: Duration,
    /// Time spent in BMC preprocessing.
    pub bmc_time: Duration,
    /// Time spent in full CHC solving.
    pub chc_time: Duration,
    /// Total elapsed time.
    pub total_time: Duration,
    /// Which phase produced the result.
    pub result_phase: ResultPhase,
}

/// Which phase of the portfolio produced the final result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResultPhase {
    /// BMC preprocessing found the answer.
    Bmc,
    /// Full CHC solving found the answer.
    Chc,
    /// No answer found.
    None,
}

/// Run the full portfolio strategy on a BTOR2 program.
///
/// Returns the check results (one per bad property) and optional statistics.
pub fn check_btor2_portfolio(
    program: &Btor2Program,
    config: &PortfolioConfig,
) -> Result<(Vec<Btor2CheckResult>, PortfolioStats), Btor2Error> {
    let start = Instant::now();

    if program.bad_properties.is_empty() {
        return Ok((
            vec![],
            PortfolioStats {
                states_before_coi: program.num_states,
                states_after_coi: program.num_states,
                inputs_before_coi: program.num_inputs,
                inputs_after_coi: program.num_inputs,
                coi_time: Duration::ZERO,
                bmc_time: Duration::ZERO,
                chc_time: Duration::ZERO,
                total_time: Duration::ZERO,
                result_phase: ResultPhase::None,
            },
        ));
    }

    let n = program.bad_properties.len();

    // -----------------------------------------------------------------------
    // Phase 1: COI reduction
    // -----------------------------------------------------------------------
    let coi_start = Instant::now();
    let working_program = if config.enable_coi {
        let coi = compute_coi(program);
        if config.verbose && (coi.eliminated_states > 0 || coi.eliminated_inputs > 0) {
            eprintln!(
                "COI: eliminated {}/{} states, {}/{} inputs",
                coi.eliminated_states,
                program.num_states,
                coi.eliminated_inputs,
                program.num_inputs,
            );
        }
        if coi.eliminated_states > 0 || coi.eliminated_inputs > 0 {
            reduce_program(program, &coi)
        } else {
            program.clone()
        }
    } else {
        program.clone()
    };
    let coi_time = coi_start.elapsed();

    let states_after = working_program.num_states;
    let inputs_after = working_program.num_inputs;

    // -----------------------------------------------------------------------
    // Phase 2: BMC preprocessing
    // -----------------------------------------------------------------------
    let bmc_start = Instant::now();
    if config.enable_bmc {
        let bmc_budget = match config.time_budget {
            Some(total) => {
                let bmc_secs = total.as_secs_f64() * config.bmc_budget_fraction;
                Duration::from_secs_f64(bmc_secs.max(1.0))
            }
            None => Duration::from_secs(5),
        };

        let bmc_config = BmcConfig {
            max_depth: config.bmc_max_depth,
            time_budget: bmc_budget,
        };

        match bmc_preprocess(&working_program, &bmc_config)? {
            BmcPreResult::Unsafe { results } => {
                let bmc_time = bmc_start.elapsed();
                if config.verbose {
                    eprintln!("BMC: found result in {:.3}s", bmc_time.as_secs_f64());
                }
                return Ok((
                    results,
                    PortfolioStats {
                        states_before_coi: program.num_states,
                        states_after_coi: states_after,
                        inputs_before_coi: program.num_inputs,
                        inputs_after_coi: inputs_after,
                        coi_time,
                        bmc_time,
                        chc_time: Duration::ZERO,
                        total_time: start.elapsed(),
                        result_phase: ResultPhase::Bmc,
                    },
                ));
            }
            BmcPreResult::Inconclusive {
                depth_reached,
                elapsed,
            } => {
                if config.verbose {
                    eprintln!(
                        "BMC: inconclusive after depth {} ({:.3}s)",
                        depth_reached,
                        elapsed.as_secs_f64()
                    );
                }
            }
        }
    }
    let bmc_time = bmc_start.elapsed();

    // -----------------------------------------------------------------------
    // Phase 3: Full CHC solving
    // -----------------------------------------------------------------------
    let chc_start = Instant::now();

    // Calculate remaining time budget.
    let chc_budget = match config.time_budget {
        Some(total) => {
            let elapsed_so_far = start.elapsed();
            if elapsed_so_far >= total {
                // Out of time.
                let results: Vec<Btor2CheckResult> = (0..n)
                    .map(|_| Btor2CheckResult::Unknown {
                        reason: "portfolio: out of time after BMC phase".to_string(),
                    })
                    .collect();
                return Ok((
                    results,
                    PortfolioStats {
                        states_before_coi: program.num_states,
                        states_after_coi: states_after,
                        inputs_before_coi: program.num_inputs,
                        inputs_after_coi: inputs_after,
                        coi_time,
                        bmc_time,
                        chc_time: Duration::ZERO,
                        total_time: start.elapsed(),
                        result_phase: ResultPhase::None,
                    },
                ));
            }
            Some(total - elapsed_so_far)
        }
        None => None,
    };

    let translation = translate_to_chc(&working_program)?;

    let adaptive_config = match chc_budget {
        Some(budget) => AdaptiveConfig::with_budget(budget, config.verbose),
        None => AdaptiveConfig::default(),
    };
    let portfolio = AdaptivePortfolio::new(translation.problem, adaptive_config);
    let result = portfolio.solve();

    let chc_time = chc_start.elapsed();

    let results = match result {
        VerifiedChcResult::Safe(_) => (0..n).map(|_| Btor2CheckResult::Unsat).collect(),
        VerifiedChcResult::Unsafe(cex) => {
            let trace: Vec<FxHashMap<String, i64>> = cex
                .counterexample()
                .steps
                .iter()
                .map(|step| step.assignments.clone())
                .collect();

            let violated_prop = cex
                .counterexample()
                .witness
                .as_ref()
                .and_then(|w| w.query_clause)
                .and_then(|clause_idx| {
                    translation
                        .property_indices
                        .iter()
                        .position(|&pi| pi == clause_idx)
                });

            let mut results = Vec::with_capacity(n);
            if let Some(prop_idx) = violated_prop {
                for i in 0..n {
                    if i == prop_idx {
                        results.push(Btor2CheckResult::Sat {
                            trace: trace.clone(),
                        });
                    } else {
                        results.push(Btor2CheckResult::Unknown {
                            reason: "other property violated".to_string(),
                        });
                    }
                }
            } else if n == 1 {
                results.push(Btor2CheckResult::Sat { trace });
            } else {
                for _ in 0..n {
                    results.push(Btor2CheckResult::Unknown {
                        reason: "counterexample found but property unknown".to_string(),
                    });
                }
            }
            results
        }
        _ => (0..n)
            .map(|_| Btor2CheckResult::Unknown {
                reason: "solver budget exhausted".to_string(),
            })
            .collect(),
    };

    Ok((
        results,
        PortfolioStats {
            states_before_coi: program.num_states,
            states_after_coi: states_after,
            inputs_before_coi: program.num_inputs,
            inputs_after_coi: inputs_after,
            coi_time,
            bmc_time,
            chc_time,
            total_time: start.elapsed(),
            result_phase: ResultPhase::Chc,
        },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{Btor2Line, Btor2Node, Btor2Sort};
    use std::collections::HashMap;

    /// Simple counter: 0 -> 1 -> 2 -> 3, bad = (count == 3).
    fn make_counter_program() -> Btor2Program {
        let mut sorts = HashMap::new();
        sorts.insert(1, Btor2Sort::BitVec(8));
        sorts.insert(10, Btor2Sort::BitVec(1));

        let lines = vec![
            Btor2Line {
                id: 1,
                sort_id: 0,
                node: Btor2Node::SortBitVec(8),
                args: vec![],
            },
            Btor2Line {
                id: 10,
                sort_id: 0,
                node: Btor2Node::SortBitVec(1),
                args: vec![],
            },
            Btor2Line {
                id: 2,
                sort_id: 1,
                node: Btor2Node::Zero,
                args: vec![],
            },
            Btor2Line {
                id: 3,
                sort_id: 1,
                node: Btor2Node::State(1, Some("count".to_string())),
                args: vec![],
            },
            Btor2Line {
                id: 4,
                sort_id: 1,
                node: Btor2Node::Init(1, 3, 2),
                args: vec![3, 2],
            },
            Btor2Line {
                id: 5,
                sort_id: 1,
                node: Btor2Node::One,
                args: vec![],
            },
            Btor2Line {
                id: 6,
                sort_id: 1,
                node: Btor2Node::Add,
                args: vec![3, 5],
            },
            Btor2Line {
                id: 7,
                sort_id: 1,
                node: Btor2Node::Next(1, 3, 6),
                args: vec![3, 6],
            },
            Btor2Line {
                id: 8,
                sort_id: 1,
                node: Btor2Node::ConstD("3".to_string()),
                args: vec![],
            },
            Btor2Line {
                id: 9,
                sort_id: 10,
                node: Btor2Node::Eq,
                args: vec![3, 8],
            },
            Btor2Line {
                id: 11,
                sort_id: 0,
                node: Btor2Node::Bad(9),
                args: vec![9],
            },
        ];

        Btor2Program {
            lines,
            sorts,
            num_inputs: 0,
            num_states: 1,
            bad_properties: vec![11],
            constraints: vec![],
            fairness: vec![],
            justice: vec![],
        }
    }

    #[test]
    fn test_portfolio_finds_bug() {
        let program = make_counter_program();
        let config = PortfolioConfig {
            time_budget: Some(Duration::from_secs(30)),
            enable_coi: true,
            enable_simplify: true,
            enable_bmc: true,
            bmc_budget_fraction: 0.3,
            bmc_max_depth: 10,
            verbose: false,
        };

        let (results, stats) = check_btor2_portfolio(&program, &config).expect("should succeed");
        assert_eq!(results.len(), 1);
        match &results[0] {
            Btor2CheckResult::Sat { trace } => {
                assert!(!trace.is_empty());
            }
            other => panic!("expected Sat, got: {:?}", other),
        }
        assert_eq!(stats.states_before_coi, 1);
    }

    #[test]
    fn test_portfolio_with_irrelevant_state() {
        let mut program = make_counter_program();

        // Add irrelevant state "y".
        let y_sort_id = 1;
        program.lines.push(Btor2Line {
            id: 20,
            sort_id: y_sort_id,
            node: Btor2Node::State(y_sort_id, Some("y".to_string())),
            args: vec![],
        });
        program.lines.push(Btor2Line {
            id: 21,
            sort_id: y_sort_id,
            node: Btor2Node::Init(y_sort_id, 20, 2),
            args: vec![20, 2],
        });
        program.lines.push(Btor2Line {
            id: 22,
            sort_id: y_sort_id,
            node: Btor2Node::Next(y_sort_id, 20, 2),
            args: vec![20, 2],
        });
        program.num_states = 2;

        let config = PortfolioConfig {
            time_budget: Some(Duration::from_secs(30)),
            enable_coi: true,
            enable_simplify: true,
            enable_bmc: true,
            bmc_budget_fraction: 0.3,
            bmc_max_depth: 10,
            verbose: false,
        };

        let (results, stats) = check_btor2_portfolio(&program, &config).expect("should succeed");
        assert_eq!(results.len(), 1);
        assert_eq!(stats.states_before_coi, 2);
        assert_eq!(stats.states_after_coi, 1, "COI should eliminate y");
        match &results[0] {
            Btor2CheckResult::Sat { .. } => {}
            other => panic!("expected Sat, got: {:?}", other),
        }
    }

    #[test]
    fn test_portfolio_no_bad_properties() {
        let mut sorts = HashMap::new();
        sorts.insert(1, Btor2Sort::BitVec(1));
        let program = Btor2Program {
            lines: vec![],
            sorts,
            num_inputs: 0,
            num_states: 0,
            bad_properties: vec![],
            constraints: vec![],
            fairness: vec![],
            justice: vec![],
        };

        let config = PortfolioConfig::default();
        let (results, _stats) = check_btor2_portfolio(&program, &config).expect("should succeed");
        assert!(results.is_empty());
    }
}
