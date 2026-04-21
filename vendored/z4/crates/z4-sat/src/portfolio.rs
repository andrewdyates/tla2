// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parallel portfolio solver
//!
//! Runs multiple solver configurations in parallel and returns the first result.
//! This is the standard approach for robust SAT solving - different heuristics
//! work better on different problem classes.
//!
//! ## Strategies
//!
//! The portfolio includes diverse strategies:
//! - VSIDS with Luby restarts (classic MiniSat-style)
//! - VSIDS with Glucose restarts (LBD-based)
//! - Aggressive inprocessing (all techniques enabled)
//! - Conservative (minimal preprocessing, stable search)
//! - Probe-focused (emphasis on failed literal probing)
//! - BVE-focused (emphasis on variable elimination)
//!
//! ## Instance-Aware Selection
//!
//! When a formula is available, `PortfolioSolver::new_adaptive` extracts
//! static syntactic features (SATzilla-style) and selects strategies based
//! on the instance's structural class. See [`crate::features`].
//!
//! ## Usage
//!
//! ```text
//! use z4_sat::portfolio::{PortfolioSolver, Strategy};
//!
//! let solver = PortfolioSolver::new();
//! let formula: DimacsFormula = ...;
//! let result = solver.solve(&formula);
//! ```

use crate::dimacs::DimacsFormula;
use crate::features::{InstanceClass, SatFeatures};
use crate::solver::{SatResult, Solver};
use parking_lot::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;

/// Configuration for a solver instance.
///
/// Internal -- technique toggles are selected by `Strategy`, not exposed to callers.
#[derive(Debug, Clone)]
pub(crate) struct SolverConfig {
    pub(crate) glucose_restarts: bool,
    pub(crate) chrono_enabled: bool,
    pub(crate) vivify_enabled: bool,
    pub(crate) subsume_enabled: bool,
    pub(crate) probe_enabled: bool,
    pub(crate) bve_enabled: bool,
    pub(crate) bce_enabled: bool,
    pub(crate) factor_enabled: bool,
    pub(crate) htr_enabled: bool,
    pub(crate) gate_enabled: bool,
    pub(crate) sweep_enabled: bool,
    pub(crate) transred_enabled: bool,
    pub(crate) condition_enabled: bool,
    pub(crate) congruence_enabled: bool,
    pub(crate) decompose_enabled: bool,
    pub(crate) hbr_enabled: bool,
    pub(crate) initial_phase: Option<bool>,
    /// Enable UCB1 multi-armed bandit branch-heuristic selection (EVSIDS/VMTF/CHB).
    pub(crate) branch_selector_ucb1: bool,
    pub(crate) seed: u64,
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            glucose_restarts: true,
            chrono_enabled: true,
            vivify_enabled: true,
            subsume_enabled: true,
            probe_enabled: true,
            bve_enabled: true,
            bce_enabled: true,
            factor_enabled: true,
            htr_enabled: true,
            gate_enabled: true,
            sweep_enabled: true,
            transred_enabled: true,
            condition_enabled: true,
            congruence_enabled: true,
            decompose_enabled: true,
            hbr_enabled: true,
            initial_phase: None,
            branch_selector_ucb1: false,
            seed: 0,
        }
    }
}

/// Predefined solver strategies for portfolio solving
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Strategy {
    /// Classic VSIDS with Luby restarts (MiniSat-style)
    VsidsLuby,
    /// VSIDS with Glucose-style EMA restarts
    VsidsGlucose,
    /// Aggressive inprocessing (all techniques enabled)
    AggressiveInprocessing,
    /// Conservative search (minimal preprocessing)
    Conservative,
    /// Focus on failed literal probing
    ProbeFocused,
    /// Focus on variable elimination
    BveFocused,
}

impl Strategy {
    /// Convert strategy to solver configuration
    pub(crate) fn to_config(self) -> SolverConfig {
        match self {
            // Default: all techniques enabled (Luby restarts variant).
            Self::VsidsLuby => SolverConfig {
                glucose_restarts: false,
                seed: 0,
                ..Default::default()
            },
            Self::VsidsGlucose => SolverConfig {
                seed: 1,
                ..Default::default()
            },
            Self::AggressiveInprocessing => SolverConfig {
                // Enable UCB1 MAB branch selection (EVSIDS/VMTF/CHB) for
                // portfolio diversity. The MAB adaptively explores CHB which
                // may benefit structured/BMC instances. This is the only
                // portfolio strategy that runs CHB (#8091).
                branch_selector_ucb1: true,
                seed: 2,
                ..Default::default()
            },
            // Minimal: all inprocessing disabled
            Self::Conservative => SolverConfig {
                glucose_restarts: false,
                chrono_enabled: false,
                vivify_enabled: false,
                subsume_enabled: false,
                probe_enabled: false,
                bve_enabled: false,
                bce_enabled: false,
                factor_enabled: false,
                htr_enabled: false,
                gate_enabled: false,
                sweep_enabled: false,
                transred_enabled: false,
                condition_enabled: false,
                congruence_enabled: false,
                decompose_enabled: false,
                hbr_enabled: false,
                seed: 3,
                ..Default::default()
            },
            // Probing emphasis: subsumption + probing + HBR only
            Self::ProbeFocused => SolverConfig {
                vivify_enabled: false,
                bve_enabled: false,
                bce_enabled: false,
                factor_enabled: false,
                htr_enabled: false,
                gate_enabled: false,
                sweep_enabled: false,
                transred_enabled: false,
                condition_enabled: false,
                congruence_enabled: false,
                decompose_enabled: false,
                hbr_enabled: true,
                initial_phase: Some(false),
                seed: 4,
                ..Default::default()
            },
            // BVE emphasis: elimination + gate + conditioning
            Self::BveFocused => SolverConfig {
                vivify_enabled: false,
                probe_enabled: false,
                htr_enabled: false,
                sweep_enabled: false,
                transred_enabled: false,
                congruence_enabled: false,
                decompose_enabled: false,
                hbr_enabled: false,
                initial_phase: Some(true),
                seed: 5,
                ..Default::default()
            },
        }
    }

    /// Get all predefined strategies
    pub(crate) fn all() -> Vec<Self> {
        vec![
            Self::VsidsLuby,
            Self::VsidsGlucose,
            Self::AggressiveInprocessing,
            Self::Conservative,
            Self::ProbeFocused,
            Self::BveFocused,
        ]
    }

    /// Get the recommended subset of strategies for a given thread count.
    ///
    /// This is the legacy selection path that ignores instance structure.
    /// Prefer `recommended_for_instance` when the formula is available.
    pub(crate) fn recommended(num_threads: usize) -> Vec<Self> {
        match num_threads {
            1 => vec![Self::VsidsGlucose],
            2 => vec![Self::VsidsGlucose, Self::VsidsLuby],
            3 => vec![
                Self::VsidsGlucose,
                Self::VsidsLuby,
                Self::AggressiveInprocessing,
            ],
            4 => vec![
                Self::VsidsGlucose,
                Self::VsidsLuby,
                Self::AggressiveInprocessing,
                Self::Conservative,
            ],
            _ => {
                let mut strategies = Self::all();
                // If we have more threads than strategies, duplicate with different seeds
                while strategies.len() < num_threads {
                    let base = strategies[strategies.len() % 6];
                    strategies.push(base);
                }
                strategies.truncate(num_threads);
                strategies
            }
        }
    }

    /// Select strategies based on instance features and thread count.
    ///
    /// Uses static syntactic features (SATzilla-style) to classify the
    /// instance and prioritize the strategies most likely to perform well.
    ///
    /// This is Phase 1a of the learned algorithm selection design
    /// (designs/2026-03-25-learned-algorithm-selection.md): simple routing
    /// based on cheap static features, no ML inference.
    ///
    /// Strategy prioritization per instance class:
    /// - **Random3Sat**: BVE-focused first (elimination is critical at
    ///   high density), then aggressive inprocessing, then Glucose.
    /// - **Structured**: Aggressive inprocessing (gate extraction,
    ///   congruence, sweeping), then BVE-focused, then probe-focused.
    /// - **Industrial**: VsidsGlucose (robust default), then conservative
    ///   (avoids expensive inprocessing on huge formulas), then BVE.
    /// - **Small**: VsidsGlucose (fast on small instances), then Luby.
    pub(crate) fn recommended_for_instance(
        num_threads: usize,
        features: &SatFeatures,
    ) -> Vec<Self> {
        let class = InstanceClass::classify(features);
        let prioritized = match class {
            InstanceClass::Random3Sat | InstanceClass::RandomKSat => vec![
                Self::BveFocused,
                Self::AggressiveInprocessing,
                Self::VsidsGlucose,
                Self::VsidsLuby,
                Self::ProbeFocused,
                Self::Conservative,
            ],
            InstanceClass::Structured => vec![
                Self::AggressiveInprocessing,
                Self::BveFocused,
                Self::ProbeFocused,
                Self::VsidsGlucose,
                Self::VsidsLuby,
                Self::Conservative,
            ],
            InstanceClass::Industrial => vec![
                Self::VsidsGlucose,
                Self::Conservative,
                Self::BveFocused,
                Self::VsidsLuby,
                Self::AggressiveInprocessing,
                Self::ProbeFocused,
            ],
            InstanceClass::Small => vec![
                Self::VsidsGlucose,
                Self::VsidsLuby,
                Self::AggressiveInprocessing,
                Self::Conservative,
                Self::ProbeFocused,
                Self::BveFocused,
            ],
            // Unknown: use the same balanced strategy as Structured (safest default).
            InstanceClass::Unknown => vec![
                Self::AggressiveInprocessing,
                Self::BveFocused,
                Self::ProbeFocused,
                Self::VsidsGlucose,
                Self::VsidsLuby,
                Self::Conservative,
            ],
        };

        let mut result = prioritized;
        result.truncate(num_threads.max(1));

        // If more threads than strategies, duplicate with the same priority
        // order but different seeds (handled by the caller via seed assignment).
        let base_len = result.len();
        while result.len() < num_threads {
            result.push(result[result.len() % base_len]);
        }

        result
    }
}

/// Result from a portfolio solver thread
#[derive(Debug)]
struct ThreadResult {
    /// The solve result
    result: SatResult,
}

/// Parallel portfolio SAT solver
///
/// Runs multiple solver configurations in parallel and returns the first result.
pub(crate) struct PortfolioSolver {
    /// Number of threads to use
    num_threads: usize,
    /// Solver configurations (one per thread)
    configs: Vec<SolverConfig>,
}

impl PortfolioSolver {
    /// Create a new portfolio solver with the specified number of threads.
    ///
    /// Uses recommended strategies for the thread count (legacy, no instance features).
    pub(crate) fn new(num_threads: usize) -> Self {
        let num_threads = num_threads.max(1);
        let strategies = Strategy::recommended(num_threads);
        let configs = strategies_to_configs(strategies);

        Self {
            num_threads,
            configs,
        }
    }

    /// Create a portfolio solver with instance-aware strategy selection.
    ///
    /// Extracts static features from the formula in O(total_literals) time
    /// and selects strategies best suited for the instance's structural class.
    ///
    /// This is the main entry point for the learned algorithm selection
    /// pipeline (Phase 1a: static features + simple routing).
    pub(crate) fn new_adaptive(num_threads: usize, formula: &DimacsFormula) -> Self {
        let num_threads = num_threads.max(1);
        let features = SatFeatures::extract(formula.num_vars, &formula.clauses);
        let strategies = Strategy::recommended_for_instance(num_threads, &features);
        let configs = strategies_to_configs(strategies);

        Self {
            num_threads,
            configs,
        }
    }

    /// Solve a CNF formula in parallel
    ///
    /// Returns the first result found by any thread.
    pub(crate) fn solve(&self, formula: &DimacsFormula) -> SatResult {
        // Extract features once for adaptive technique gating across all threads.
        let features = SatFeatures::extract(formula.num_vars, &formula.clauses);
        let class = InstanceClass::classify(&features);
        let disable_reorder = crate::adaptive::should_disable_reorder(&features, &class);

        if self.num_threads == 1 || self.configs.len() == 1 {
            // Single-threaded: just run normally
            let config = self.configs.first().cloned().unwrap_or_default();
            let mut solver = create_solver_from_config(formula.num_vars, &config);
            apply_adaptive_adjustments(&mut solver, &features, &class, disable_reorder);
            for clause in &formula.clauses {
                solver.add_clause(clause.clone());
            }
            return solver.solve().into_inner();
        }

        // Multi-threaded portfolio
        let terminate = Arc::new(AtomicBool::new(false));
        let result: Arc<Mutex<Option<ThreadResult>>> = Arc::new(Mutex::new(None));

        let handles: Vec<_> = self
            .configs
            .clone()
            .into_iter()
            .map(|config| {
                let formula_clauses = formula.clauses.clone();
                let num_vars = formula.num_vars;
                let features = features.clone();
                let class = class;
                let terminate = Arc::clone(&terminate);
                let result: Arc<Mutex<Option<ThreadResult>>> = Arc::clone(&result);

                thread::spawn(move || {
                    // Create solver with this configuration
                    let mut solver = create_solver_from_config(num_vars, &config);
                    apply_adaptive_adjustments(&mut solver, &features, &class, disable_reorder);

                    // Add clauses
                    for clause in &formula_clauses {
                        solver.add_clause(clause.clone());
                    }

                    // Solve with termination check
                    let solve_result = solver
                        .solve_interruptible(|| terminate.load(Ordering::Relaxed))
                        .into_inner();

                    // If we got a result and haven't been terminated, store it
                    if !terminate.load(Ordering::Relaxed) {
                        let mut guard = result.lock();
                        if guard.is_none() {
                            *guard = Some(ThreadResult {
                                result: solve_result,
                            });
                            // Signal other threads to stop
                            terminate.store(true, Ordering::Relaxed);
                        }
                    }
                })
            })
            .collect();

        // Wait for all threads to finish
        for handle in handles {
            let _: Result<(), _> = handle.join();
        }

        // Extract result
        let guard = result.lock();
        match guard.as_ref() {
            Some(r) => r.result.clone(),
            None => SatResult::Unknown, // All threads were interrupted
        }
    }

    /// Set explicit configurations for tests.
    #[cfg(test)]
    fn with_configs(mut self, configs: Vec<SolverConfig>) -> Self {
        self.configs = configs;
        self.num_threads = self.configs.len().max(1);
        self
    }
}

/// Convert a list of strategies to solver configs with sequential seeds.
fn strategies_to_configs(strategies: Vec<Strategy>) -> Vec<SolverConfig> {
    strategies
        .into_iter()
        .enumerate()
        .map(|(i, s)| {
            let mut config = s.to_config();
            config.seed = i as u64;
            config
        })
        .collect()
}

/// Apply feature-driven adaptive adjustments to a solver.
///
/// This applies the same threshold rules that the DIMACS single-thread path uses
/// (conditioning ratio gate, random k-SAT symmetry, industrial reorder, etc.),
/// ensuring portfolio threads also benefit from instance-aware technique gating.
fn apply_adaptive_adjustments(
    solver: &mut Solver,
    features: &SatFeatures,
    class: &InstanceClass,
    disable_reorder: bool,
) {
    let mut profile = solver.inprocessing_feature_profile();
    crate::adaptive::adjust_features_for_instance(features, class, &mut profile);
    // Apply the adjusted toggles back to the solver.
    solver.set_condition_enabled(profile.condition);
    solver.set_symmetry_enabled(profile.symmetry);
    solver.set_bce_enabled(profile.bce);
    if disable_reorder {
        solver.set_reorder_enabled(false);
    }
}

/// Create a solver instance from a configuration.
fn create_solver_from_config(num_vars: usize, config: &SolverConfig) -> Solver {
    let mut solver = Solver::new(num_vars);

    // Apply configuration
    solver.set_glucose_restarts(config.glucose_restarts);
    solver.set_chrono_enabled(config.chrono_enabled);
    solver.set_vivify_enabled(config.vivify_enabled);
    solver.set_subsume_enabled(config.subsume_enabled);
    solver.set_probe_enabled(config.probe_enabled);
    solver.set_bve_enabled(config.bve_enabled);
    solver.set_bce_enabled(config.bce_enabled);
    solver.set_factor_enabled(config.factor_enabled);
    solver.set_htr_enabled(config.htr_enabled);
    solver.set_gate_enabled(config.gate_enabled);
    solver.set_sweep_enabled(config.sweep_enabled);
    solver.set_transred_enabled(config.transred_enabled);
    solver.set_condition_enabled(config.condition_enabled);
    solver.set_congruence_enabled(config.congruence_enabled);
    solver.set_decompose_enabled(config.decompose_enabled);
    solver.set_hbr_enabled(config.hbr_enabled);

    // Set initial phase if specified
    if let Some(phase) = config.initial_phase {
        solver.set_initial_phase(phase);
    }

    // Enable MAB branch selection if requested (portfolio diversity).
    solver.set_branch_selector_ucb1(config.branch_selector_ucb1);

    // Set random seed for variable selection tie-breaking
    solver.set_random_seed(config.seed);

    solver
}

#[cfg(test)]
#[path = "portfolio_tests.rs"]
mod tests;
