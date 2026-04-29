// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Portfolio configuration types: engine variants, portfolio config, and results.

use std::time::Duration;

use crate::check_result::CheckResult;
use crate::ic3::Ic3Config;

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
    /// BMC with a linear-offset start depth for mid-deep SAT search (#4299, Wave 29).
    ///
    /// Skips the first `start_depth` depths (already covered by shallow step-1 BMC
    /// configs in the portfolio) and then runs linear step-1 BMC from `start_depth`
    /// to `max_depth`. Unlike geometric backoff, which overshoots by doubling,
    /// linear-offset checks every depth past the skip region — essential for
    /// Sokoban/microban SAT puzzles whose counterexample sits at a specific depth
    /// that geometric doubling skips over.
    ///
    /// Designed for HWMCC top-50 Tier 2 Sokoban SAT benchmarks (microban_64/77/89/
    /// 118/132/136/148/149) where rIC3 finds counterexamples at depth ~100-500.
    BmcLinearOffset {
        /// First depth at which to run the initial SAT check. Prior depths are
        /// unrolled (clauses loaded) but not checked, skipping redundant work
        /// already performed by step-1 BMC configs.
        start_depth: usize,
        /// Step between SAT checks after `start_depth`. Use 1 for exhaustive
        /// per-depth search.
        step: usize,
        /// Maximum depth to explore.
        max_depth: usize,
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
    /// Random forward simulation: SAT-free exploration with random inputs.
    ///
    /// Simulates the circuit forward from the initial state with random inputs,
    /// checking if a bad state is reached. Extremely fast (millions of steps/sec)
    /// but probabilistic — will not find bugs that require specific input sequences.
    ///
    /// Most effective on circuits where the bad state is reachable via many
    /// different input paths. For Sokoban puzzles (single specific solution),
    /// this engine will not help, but it provides zero-cost diversity in the
    /// portfolio since it requires no SAT calls.
    ///
    /// `steps_per_walk`: how many forward steps each random walk takes.
    /// `num_walks`: how many independent random walks to run.
    /// `seed`: random seed for reproducibility with portfolio diversity.
    RandomSim {
        steps_per_walk: usize,
        num_walks: usize,
        seed: u64,
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
                crate::sat_types::SolverBackend::Simple => "bmc-simple",
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
                crate::sat_types::SolverBackend::Simple => "bmc-geometric-simple",
                _ => "bmc-geometric-z4-variant",
            },
            EngineConfig::BmcLinearOffset { .. } => "bmc-linear-offset",
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
            EngineConfig::RandomSim { .. } => "random-sim",
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
        super::factory::default_portfolio()
    }
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
