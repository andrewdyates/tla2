// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Bounded Model Checking (BMC) preprocessing for BTOR2 programs.
//
// Performs shallow BMC unrolling before attempting full CHC solving. This
// catches bugs reachable within a small number of steps (which is common
// in HWMCC benchmarks) at much lower cost than PDR/k-induction.
//
// Design rationale: Many HWMCC benchmarks are "shallow unsafe" — the bad
// state is reachable within 10-50 steps. Full PDR is overkill for these
// cases. By trying BMC first with a small bound (e.g., 20 steps), we can
// solve these quickly and save the PDR budget for genuinely hard problems.

use std::time::{Duration, Instant};

use rustc_hash::FxHashMap;
use z4_chc::{AdaptiveConfig, AdaptivePortfolio, VerifiedChcResult};

use crate::error::Btor2Error;
use crate::to_chc::translate_to_chc;
use crate::translate::Btor2CheckResult;
use crate::types::Btor2Program;

/// Configuration for BMC preprocessing.
#[derive(Debug, Clone)]
pub(crate) struct BmcConfig {
    /// Maximum BMC unrolling depth.
    pub(crate) max_depth: u32,
    /// Time budget for the BMC phase.
    pub(crate) time_budget: Duration,
}

impl Default for BmcConfig {
    fn default() -> Self {
        Self {
            max_depth: 20,
            time_budget: Duration::from_secs(5),
        }
    }
}

/// Result of BMC preprocessing.
#[derive(Debug)]
pub(crate) enum BmcPreResult {
    /// BMC found a counterexample (property violated).
    Unsafe { results: Vec<Btor2CheckResult> },
    /// BMC could not find a bug within the bound — inconclusive.
    Inconclusive {
        /// Depth reached before timeout/bound.
        depth_reached: u32,
        /// Time spent in BMC.
        elapsed: Duration,
    },
}

/// Run BMC preprocessing on a BTOR2 program.
///
/// Translates to CHC and runs the adaptive portfolio with a short time
/// budget. The adaptive portfolio internally uses BMC as one of its
/// engines, but by giving it a tight budget we force fast termination.
///
/// Returns `BmcPreResult::Unsafe` if a bug is found, otherwise
/// `BmcPreResult::Inconclusive`.
pub(crate) fn bmc_preprocess(
    program: &Btor2Program,
    config: &BmcConfig,
) -> Result<BmcPreResult, Btor2Error> {
    if program.bad_properties.is_empty() {
        return Ok(BmcPreResult::Inconclusive {
            depth_reached: 0,
            elapsed: Duration::ZERO,
        });
    }

    let start = Instant::now();

    // Translate to CHC (same as the main path).
    let translation = translate_to_chc(program)?;
    let n = program.bad_properties.len();

    // Run with a tight time budget — this biases toward BMC lanes.
    let adaptive_config = AdaptiveConfig::with_budget(config.time_budget, false);
    let portfolio = AdaptivePortfolio::new(translation.problem, adaptive_config);
    let result = portfolio.solve();

    let elapsed = start.elapsed();

    match result {
        VerifiedChcResult::Unsafe(cex) => {
            let trace: Vec<FxHashMap<String, i64>> = cex
                .counterexample()
                .steps
                .iter()
                .map(|step| step.assignments.clone())
                .collect();

            // Determine which bad property was violated.
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
                            reason: "BMC: other property violated".to_string(),
                        });
                    }
                }
            } else if n == 1 {
                results.push(Btor2CheckResult::Sat { trace });
            } else {
                for _ in 0..n {
                    results.push(Btor2CheckResult::Unknown {
                        reason: "BMC: counterexample found but property unknown".to_string(),
                    });
                }
            }

            Ok(BmcPreResult::Unsafe { results })
        }
        VerifiedChcResult::Safe(_) => {
            // BMC returned safe — but this is only sound for the bound checked.
            // However, the AdaptivePortfolio uses PDR too, so if it says Safe
            // with proof, we should trust it.
            let results: Vec<Btor2CheckResult> = (0..n).map(|_| Btor2CheckResult::Unsat).collect();
            Ok(BmcPreResult::Unsafe { results })
        }
        _ => Ok(BmcPreResult::Inconclusive {
            depth_reached: config.max_depth,
            elapsed,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{Btor2Line, Btor2Node, Btor2Sort};
    use std::collections::HashMap;

    /// Counter that counts up from 0; bad = (count == 3).
    /// BMC should find this at depth 3.
    fn make_shallow_bug_program() -> Btor2Program {
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
    fn test_bmc_finds_shallow_bug() {
        let program = make_shallow_bug_program();
        let config = BmcConfig {
            max_depth: 10,
            time_budget: Duration::from_secs(10),
        };

        let result = bmc_preprocess(&program, &config).expect("should not error");
        match result {
            BmcPreResult::Unsafe { results } => {
                assert_eq!(results.len(), 1);
                match &results[0] {
                    Btor2CheckResult::Sat { trace } => {
                        assert!(
                            !trace.is_empty(),
                            "counterexample should have at least one step"
                        );
                    }
                    other => panic!("expected Sat, got: {:?}", other),
                }
            }
            BmcPreResult::Inconclusive { .. } => {
                panic!("expected BMC to find the shallow bug");
            }
        }
    }

    #[test]
    fn test_bmc_inconclusive_on_safe_program() {
        // State starts at 0, stays at 0, bad = (state == 1).
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
                node: Btor2Node::State(1, Some("x".to_string())),
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
                node: Btor2Node::Next(1, 3, 2),
                args: vec![3, 2],
            },
            Btor2Line {
                id: 6,
                sort_id: 1,
                node: Btor2Node::One,
                args: vec![],
            },
            Btor2Line {
                id: 7,
                sort_id: 10,
                node: Btor2Node::Eq,
                args: vec![3, 6],
            },
            Btor2Line {
                id: 8,
                sort_id: 0,
                node: Btor2Node::Bad(7),
                args: vec![7],
            },
        ];

        let program = Btor2Program {
            lines,
            sorts,
            num_inputs: 0,
            num_states: 1,
            bad_properties: vec![8],
            constraints: vec![],
            fairness: vec![],
            justice: vec![],
        };

        let config = BmcConfig {
            max_depth: 5,
            time_budget: Duration::from_secs(5),
        };

        let result = bmc_preprocess(&program, &config).expect("should not error");
        // Either the portfolio proves safe or returns inconclusive — both are correct.
        match result {
            BmcPreResult::Unsafe { results } => {
                for r in &results {
                    match r {
                        Btor2CheckResult::Unsat => {}
                        Btor2CheckResult::Sat { .. } => {
                            panic!("BMC should not find a bug in a safe program");
                        }
                        Btor2CheckResult::Unknown { .. } => {}
                    }
                }
            }
            BmcPreResult::Inconclusive { .. } => {
                // Fine — safe program, BMC budget exhausted.
            }
        }
    }
}
