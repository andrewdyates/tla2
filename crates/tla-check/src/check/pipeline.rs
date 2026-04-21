// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Multi-phase verification pipeline for TLA+ model checking.
//!
//! Runs cheap verification phases first (random walk, BMC) to resolve easy
//! properties, then expensive phases (PDR, BFS) only on remaining hard
//! properties. Ported from `tla-petri/src/examinations/reachability/pipeline.rs`.
//!
//! Part of #3723.

use rustc_hash::FxHashMap;
use std::fmt;
use std::time::{Duration, Instant};

/// Verification phase in the pipeline ordering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VerificationPhase {
    /// Random walk witness search — zero-memory under-approximation.
    /// Uses `check/model_checker/random_walk.rs` (Part of #3720).
    RandomWalk,
    /// Bounded model checking via z4-based symbolic unrolling.
    /// Uses `z4_bmc.rs` (Part of #3702).
    Bmc,
    /// K-induction for proof-side properties via z4.
    /// Uses `z4_kinduction.rs` (Part of #3722, stub if not yet available).
    KInduction,
    /// Property-Directed Reachability (IC3/PDR) via z4 CHC solver.
    /// Uses `z4_pdr.rs` (Part of #642).
    Pdr,
    /// Exhaustive BFS state-space exploration.
    /// Uses `check/model_checker/bfs/` (core model checker).
    Bfs,
    /// Symbolic simulation via z4 SMT solving (Apalache Gap 9).
    /// Uses `z4_symbolic_sim.rs` (Part of #3757).
    SymbolicSim,
}

impl fmt::Display for VerificationPhase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VerificationPhase::RandomWalk => write!(f, "RandomWalk"),
            VerificationPhase::Bmc => write!(f, "BMC"),
            VerificationPhase::KInduction => write!(f, "k-induction"),
            VerificationPhase::Pdr => write!(f, "PDR"),
            VerificationPhase::Bfs => write!(f, "BFS"),
            VerificationPhase::SymbolicSim => write!(f, "SymbolicSim"),
        }
    }
}

/// Per-phase configuration within the pipeline.
#[derive(Debug, Clone)]
pub struct PhaseConfig {
    /// Which verification technique to run.
    pub phase: VerificationPhase,
    /// Maximum wall-clock time budget for this phase.
    pub time_budget: Duration,
    /// Whether this phase is enabled (disabled phases are skipped).
    pub enabled: bool,
}

/// Unique identifier for a property being verified.
///
/// In TLA+ model checking this is typically the invariant name string.
pub type PropertyId = String;

/// Outcome of verifying a single property in a single phase.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropertyVerdict {
    /// Property holds (invariant satisfied across all reachable states).
    Satisfied,
    /// Property violated (counterexample exists).
    Violated,
    /// Phase could not determine the property status (e.g., timeout, bound reached).
    Unknown,
}

/// Record of a single phase execution.
#[derive(Debug, Clone)]
pub struct PhaseRecord {
    /// Which phase ran.
    pub phase: VerificationPhase,
    /// Wall-clock time spent in this phase.
    pub elapsed: Duration,
    /// Number of properties resolved (moved from unknown to satisfied/violated).
    pub properties_resolved: usize,
}

/// Combined results from running the full pipeline.
#[derive(Debug, Clone)]
pub struct PipelineResult {
    /// Final verdict for each property.
    pub verdicts: FxHashMap<PropertyId, PropertyVerdict>,
    /// Execution record for each phase that ran.
    pub phases_run: Vec<PhaseRecord>,
    /// Total wall-clock time across all phases.
    pub total_time: Duration,
}

/// A phase runner receives the set of unresolved property IDs and a time budget,
/// and returns verdicts for any properties it can resolve.
///
/// This trait abstracts over the different verification backends so the pipeline
/// can dispatch generically. Implementations wrap random walk, BMC, PDR, and BFS.
pub trait PhaseRunner: fmt::Debug {
    /// Run this phase on the given unresolved properties within the time budget.
    ///
    /// Returns a map from property ID to verdict for any properties the phase
    /// can determine. Properties not in the returned map remain unresolved.
    fn run(
        &mut self,
        unresolved: &[PropertyId],
        time_budget: Duration,
    ) -> FxHashMap<PropertyId, PropertyVerdict>;

    /// The verification phase this runner implements.
    fn phase(&self) -> VerificationPhase;
}

/// Named verification strategy for CLI `--strategy` flag.
///
/// Each variant maps to a pre-configured `VerificationPipeline` with an
/// appropriate sequence of phases and time budgets.
///
/// Part of #3723.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum VerificationStrategy {
    /// Type-check + BMC(5 steps) — fast feedback for development.
    Quick,
    /// Type-check + exhaustive BFS + liveness — TLC-equivalent completeness.
    Full,
    /// Adaptive: walk -> BMC -> k-induction -> PDR -> BFS with early exit.
    Auto,
}

impl VerificationStrategy {
    /// Build the `VerificationPipeline` for this strategy.
    pub fn into_pipeline(self) -> VerificationPipeline {
        match self {
            VerificationStrategy::Quick => VerificationPipeline::quick_pipeline(),
            VerificationStrategy::Full => VerificationPipeline::full_pipeline(),
            VerificationStrategy::Auto => VerificationPipeline::default_pipeline(),
        }
    }
}

impl fmt::Display for VerificationStrategy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VerificationStrategy::Quick => write!(f, "quick"),
            VerificationStrategy::Full => write!(f, "full"),
            VerificationStrategy::Auto => write!(f, "auto"),
        }
    }
}

/// Multi-phase verification pipeline.
///
/// Executes phases in order, skipping already-resolved properties between
/// phases. Early-exits when all properties are resolved.
#[derive(Debug)]
pub struct VerificationPipeline {
    phases: Vec<PhaseConfig>,
}

impl VerificationPipeline {
    /// Construct a pipeline with the given phase configurations.
    pub fn new(phases: Vec<PhaseConfig>) -> Self {
        Self { phases }
    }

    /// Quick pipeline: RandomWalk(2s) -> BMC(10s).
    ///
    /// Optimized for fast feedback during development. No exhaustive BFS --
    /// if neither walk nor BMC finds a bug, properties remain Unknown.
    pub fn quick_pipeline() -> Self {
        Self {
            phases: vec![
                PhaseConfig {
                    phase: VerificationPhase::RandomWalk,
                    time_budget: Duration::from_secs(2),
                    enabled: true,
                },
                PhaseConfig {
                    phase: VerificationPhase::Bmc,
                    time_budget: Duration::from_secs(10),
                    enabled: true,
                },
            ],
        }
    }

    /// Full pipeline: RandomWalk(5s) -> BFS(600s).
    ///
    /// TLC-equivalent completeness: exhaustive BFS ensures all reachable
    /// states are explored. Liveness properties are checked after BFS
    /// completes (handled by the BFS runner internally).
    pub fn full_pipeline() -> Self {
        Self {
            phases: vec![
                PhaseConfig {
                    phase: VerificationPhase::RandomWalk,
                    time_budget: Duration::from_secs(5),
                    enabled: true,
                },
                PhaseConfig {
                    phase: VerificationPhase::Bfs,
                    time_budget: Duration::from_secs(600),
                    enabled: true,
                },
            ],
        }
    }

    /// Default (auto) pipeline: walk(5s) -> BMC(30s) -> k-induction(30s) -> PDR(60s) -> BFS(300s).
    ///
    /// Used by `--strategy auto`. Runs cheap phases first, escalating to
    /// more expensive phases only for properties that remain unresolved.
    pub fn default_pipeline() -> Self {
        Self {
            phases: vec![
                PhaseConfig {
                    phase: VerificationPhase::RandomWalk,
                    time_budget: Duration::from_secs(5),
                    enabled: true,
                },
                PhaseConfig {
                    phase: VerificationPhase::Bmc,
                    time_budget: Duration::from_secs(30),
                    enabled: true,
                },
                PhaseConfig {
                    phase: VerificationPhase::KInduction,
                    time_budget: Duration::from_secs(30),
                    // Enabled now that #3722 landed a k-induction implementation.
                    enabled: true,
                },
                PhaseConfig {
                    phase: VerificationPhase::Pdr,
                    time_budget: Duration::from_secs(60),
                    enabled: true,
                },
                PhaseConfig {
                    phase: VerificationPhase::Bfs,
                    // BFS gets the remaining budget — 300s as a default cap.
                    time_budget: Duration::from_secs(300),
                    enabled: true,
                },
            ],
        }
    }

    /// Run the pipeline using the provided runners for each phase.
    ///
    /// `runners` is a map from `VerificationPhase` to the runner implementation.
    /// Phases without a registered runner are silently skipped.
    ///
    /// `properties` is the initial set of property IDs to verify.
    pub fn run<'r>(
        &self,
        properties: &[PropertyId],
        runners: &mut FxHashMap<VerificationPhase, Box<dyn PhaseRunner + 'r>>,
    ) -> PipelineResult {
        let pipeline_start = Instant::now();
        let mut verdicts: FxHashMap<PropertyId, PropertyVerdict> = FxHashMap::default();
        let mut phases_run: Vec<PhaseRecord> = Vec::new();

        for phase_config in &self.phases {
            // Skip disabled phases.
            if !phase_config.enabled {
                continue;
            }

            // Collect unresolved properties (not yet determined by earlier phases).
            let unresolved: Vec<PropertyId> = properties
                .iter()
                .filter(|p| !verdicts.contains_key(*p))
                .cloned()
                .collect();

            // Early exit: all properties resolved.
            if unresolved.is_empty() {
                break;
            }

            // Look up the runner for this phase; skip if not registered.
            let runner = match runners.get_mut(&phase_config.phase) {
                Some(r) => r,
                None => {
                    eprintln!(
                        "Pipeline: skipping {} (no runner registered)",
                        phase_config.phase
                    );
                    continue;
                }
            };

            let phase_start = Instant::now();
            let new_verdicts = runner.run(&unresolved, phase_config.time_budget);
            let phase_elapsed = phase_start.elapsed();

            let mut resolved_count = 0;
            for (prop_id, verdict) in new_verdicts {
                if verdict != PropertyVerdict::Unknown {
                    verdicts.insert(prop_id, verdict);
                    resolved_count += 1;
                }
            }

            if resolved_count > 0 {
                eprintln!(
                    "Pipeline: {} resolved {}/{} properties in {:.2}s",
                    phase_config.phase,
                    resolved_count,
                    unresolved.len(),
                    phase_elapsed.as_secs_f64(),
                );
            }

            phases_run.push(PhaseRecord {
                phase: phase_config.phase,
                elapsed: phase_elapsed,
                properties_resolved: resolved_count,
            });
        }

        // Any properties still unresolved after all phases get Unknown.
        for prop in properties {
            verdicts
                .entry(prop.clone())
                .or_insert(PropertyVerdict::Unknown);
        }

        PipelineResult {
            verdicts,
            phases_run,
            total_time: pipeline_start.elapsed(),
        }
    }

    /// Read-only access to the phase configuration.
    pub fn phases(&self) -> &[PhaseConfig] {
        &self.phases
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // Mock phase runner for testing
    // -----------------------------------------------------------------------

    /// A mock runner that resolves a fixed set of properties.
    #[derive(Debug)]
    struct MockRunner {
        phase_type: VerificationPhase,
        /// Properties this runner will resolve and their verdicts.
        resolves: FxHashMap<PropertyId, PropertyVerdict>,
        /// Tracks whether `run` was called.
        was_called: bool,
    }

    impl MockRunner {
        fn new(
            phase_type: VerificationPhase,
            resolves: Vec<(PropertyId, PropertyVerdict)>,
        ) -> Self {
            Self {
                phase_type,
                resolves: resolves.into_iter().collect(),
                was_called: false,
            }
        }
    }

    impl PhaseRunner for MockRunner {
        fn run(
            &mut self,
            unresolved: &[PropertyId],
            _time_budget: Duration,
        ) -> FxHashMap<PropertyId, PropertyVerdict> {
            self.was_called = true;
            unresolved
                .iter()
                .filter_map(|p| self.resolves.get(p).map(|v| (p.clone(), *v)))
                .collect()
        }

        fn phase(&self) -> VerificationPhase {
            self.phase_type
        }
    }

    /// A mock runner that records whether it was called but resolves nothing.
    #[derive(Debug)]
    struct NoOpRunner {
        phase_type: VerificationPhase,
        was_called: bool,
    }

    impl NoOpRunner {
        fn new(phase_type: VerificationPhase) -> Self {
            Self {
                phase_type,
                was_called: false,
            }
        }
    }

    impl PhaseRunner for NoOpRunner {
        fn run(
            &mut self,
            _unresolved: &[PropertyId],
            _time_budget: Duration,
        ) -> FxHashMap<PropertyId, PropertyVerdict> {
            self.was_called = true;
            FxHashMap::default()
        }

        fn phase(&self) -> VerificationPhase {
            self.phase_type
        }
    }

    // -----------------------------------------------------------------------
    // Test: properties resolved at different stages
    // -----------------------------------------------------------------------

    #[test]
    fn test_pipeline_resolves_across_phases() {
        let properties = vec![
            String::from("Inv1"),
            String::from("Inv2"),
            String::from("Inv3"),
        ];

        let pipeline = VerificationPipeline::new(vec![
            PhaseConfig {
                phase: VerificationPhase::RandomWalk,
                time_budget: Duration::from_secs(5),
                enabled: true,
            },
            PhaseConfig {
                phase: VerificationPhase::Bmc,
                time_budget: Duration::from_secs(30),
                enabled: true,
            },
            PhaseConfig {
                phase: VerificationPhase::Pdr,
                time_budget: Duration::from_secs(60),
                enabled: true,
            },
        ]);

        // RandomWalk resolves Inv1 (violated), BMC resolves Inv2 (violated),
        // PDR resolves Inv3 (satisfied).
        let mut runners: FxHashMap<VerificationPhase, Box<dyn PhaseRunner>> = FxHashMap::default();
        runners.insert(
            VerificationPhase::RandomWalk,
            Box::new(MockRunner::new(
                VerificationPhase::RandomWalk,
                vec![(String::from("Inv1"), PropertyVerdict::Violated)],
            )),
        );
        runners.insert(
            VerificationPhase::Bmc,
            Box::new(MockRunner::new(
                VerificationPhase::Bmc,
                vec![(String::from("Inv2"), PropertyVerdict::Violated)],
            )),
        );
        runners.insert(
            VerificationPhase::Pdr,
            Box::new(MockRunner::new(
                VerificationPhase::Pdr,
                vec![(String::from("Inv3"), PropertyVerdict::Satisfied)],
            )),
        );

        let result = pipeline.run(&properties, &mut runners);

        assert_eq!(
            result.verdicts.get("Inv1"),
            Some(&PropertyVerdict::Violated)
        );
        assert_eq!(
            result.verdicts.get("Inv2"),
            Some(&PropertyVerdict::Violated)
        );
        assert_eq!(
            result.verdicts.get("Inv3"),
            Some(&PropertyVerdict::Satisfied)
        );
        assert_eq!(result.phases_run.len(), 3);
        assert_eq!(result.phases_run[0].properties_resolved, 1);
        assert_eq!(result.phases_run[1].properties_resolved, 1);
        assert_eq!(result.phases_run[2].properties_resolved, 1);
    }

    // -----------------------------------------------------------------------
    // Test: early exit when first phase resolves everything
    // -----------------------------------------------------------------------

    #[test]
    fn test_pipeline_early_exit() {
        let properties = vec![String::from("Inv1"), String::from("Inv2")];

        let pipeline = VerificationPipeline::new(vec![
            PhaseConfig {
                phase: VerificationPhase::RandomWalk,
                time_budget: Duration::from_secs(5),
                enabled: true,
            },
            PhaseConfig {
                phase: VerificationPhase::Bfs,
                time_budget: Duration::from_secs(300),
                enabled: true,
            },
        ]);

        // RandomWalk resolves both properties.
        let mut runners: FxHashMap<VerificationPhase, Box<dyn PhaseRunner>> = FxHashMap::default();
        runners.insert(
            VerificationPhase::RandomWalk,
            Box::new(MockRunner::new(
                VerificationPhase::RandomWalk,
                vec![
                    (String::from("Inv1"), PropertyVerdict::Violated),
                    (String::from("Inv2"), PropertyVerdict::Violated),
                ],
            )),
        );
        runners.insert(
            VerificationPhase::Bfs,
            Box::new(NoOpRunner::new(VerificationPhase::Bfs)),
        );

        let result = pipeline.run(&properties, &mut runners);

        // Both resolved by RandomWalk.
        assert_eq!(
            result.verdicts.get("Inv1"),
            Some(&PropertyVerdict::Violated)
        );
        assert_eq!(
            result.verdicts.get("Inv2"),
            Some(&PropertyVerdict::Violated)
        );

        // BFS should NOT have been called (early exit).
        assert_eq!(result.phases_run.len(), 1);
        assert_eq!(result.phases_run[0].phase, VerificationPhase::RandomWalk);
    }

    // -----------------------------------------------------------------------
    // Test: disabled phases are skipped
    // -----------------------------------------------------------------------

    #[test]
    fn test_pipeline_disabled_phase_skipped() {
        let properties = vec![String::from("Inv1")];

        let pipeline = VerificationPipeline::new(vec![
            PhaseConfig {
                phase: VerificationPhase::RandomWalk,
                time_budget: Duration::from_secs(5),
                enabled: false, // Disabled!
            },
            PhaseConfig {
                phase: VerificationPhase::Bmc,
                time_budget: Duration::from_secs(30),
                enabled: true,
            },
        ]);

        let mut runners: FxHashMap<VerificationPhase, Box<dyn PhaseRunner>> = FxHashMap::default();
        runners.insert(
            VerificationPhase::RandomWalk,
            Box::new(MockRunner::new(
                VerificationPhase::RandomWalk,
                vec![(String::from("Inv1"), PropertyVerdict::Violated)],
            )),
        );
        runners.insert(
            VerificationPhase::Bmc,
            Box::new(MockRunner::new(
                VerificationPhase::Bmc,
                vec![(String::from("Inv1"), PropertyVerdict::Violated)],
            )),
        );

        let result = pipeline.run(&properties, &mut runners);

        // Only BMC should have run (RandomWalk disabled).
        assert_eq!(result.phases_run.len(), 1);
        assert_eq!(result.phases_run[0].phase, VerificationPhase::Bmc);
        assert_eq!(
            result.verdicts.get("Inv1"),
            Some(&PropertyVerdict::Violated)
        );
    }

    // -----------------------------------------------------------------------
    // Test: unresolved properties get Unknown verdict
    // -----------------------------------------------------------------------

    #[test]
    fn test_pipeline_unresolved_properties_get_unknown() {
        let properties = vec![String::from("Inv1"), String::from("Inv2")];

        let pipeline = VerificationPipeline::new(vec![PhaseConfig {
            phase: VerificationPhase::RandomWalk,
            time_budget: Duration::from_secs(5),
            enabled: true,
        }]);

        // RandomWalk only resolves Inv1.
        let mut runners: FxHashMap<VerificationPhase, Box<dyn PhaseRunner>> = FxHashMap::default();
        runners.insert(
            VerificationPhase::RandomWalk,
            Box::new(MockRunner::new(
                VerificationPhase::RandomWalk,
                vec![(String::from("Inv1"), PropertyVerdict::Violated)],
            )),
        );

        let result = pipeline.run(&properties, &mut runners);

        assert_eq!(
            result.verdicts.get("Inv1"),
            Some(&PropertyVerdict::Violated)
        );
        // Inv2 was never resolved — should be Unknown.
        assert_eq!(result.verdicts.get("Inv2"), Some(&PropertyVerdict::Unknown));
    }

    // -----------------------------------------------------------------------
    // Test: default pipeline construction
    // -----------------------------------------------------------------------

    #[test]
    fn test_default_pipeline_construction() {
        let pipeline = VerificationPipeline::default_pipeline();
        let phases = pipeline.phases();

        assert_eq!(phases.len(), 5);

        assert_eq!(phases[0].phase, VerificationPhase::RandomWalk);
        assert!(phases[0].enabled);
        assert_eq!(phases[0].time_budget, Duration::from_secs(5));

        assert_eq!(phases[1].phase, VerificationPhase::Bmc);
        assert!(phases[1].enabled);
        assert_eq!(phases[1].time_budget, Duration::from_secs(30));

        assert_eq!(phases[2].phase, VerificationPhase::KInduction);
        assert!(phases[2].enabled); // Enabled by #3722.

        assert_eq!(phases[3].phase, VerificationPhase::Pdr);
        assert!(phases[3].enabled);
        assert_eq!(phases[3].time_budget, Duration::from_secs(60));

        assert_eq!(phases[4].phase, VerificationPhase::Bfs);
        assert!(phases[4].enabled);
        assert_eq!(phases[4].time_budget, Duration::from_secs(300));
    }

    // -----------------------------------------------------------------------
    // Test: missing runner gracefully skipped
    // -----------------------------------------------------------------------

    #[test]
    fn test_pipeline_missing_runner_skipped() {
        let properties = vec![String::from("Inv1")];

        let pipeline = VerificationPipeline::new(vec![
            PhaseConfig {
                phase: VerificationPhase::KInduction,
                time_budget: Duration::from_secs(30),
                enabled: true,
            },
            PhaseConfig {
                phase: VerificationPhase::Bfs,
                time_budget: Duration::from_secs(300),
                enabled: true,
            },
        ]);

        // Only register BFS runner, not KInduction.
        let mut runners: FxHashMap<VerificationPhase, Box<dyn PhaseRunner>> = FxHashMap::default();
        runners.insert(
            VerificationPhase::Bfs,
            Box::new(MockRunner::new(
                VerificationPhase::Bfs,
                vec![(String::from("Inv1"), PropertyVerdict::Satisfied)],
            )),
        );

        let result = pipeline.run(&properties, &mut runners);

        // KInduction skipped (no runner), BFS resolved it.
        assert_eq!(result.phases_run.len(), 1);
        assert_eq!(result.phases_run[0].phase, VerificationPhase::Bfs);
        assert_eq!(
            result.verdicts.get("Inv1"),
            Some(&PropertyVerdict::Satisfied)
        );
    }

    // -----------------------------------------------------------------------
    // Test: Unknown verdicts from a phase do not resolve properties
    // -----------------------------------------------------------------------

    #[test]
    fn test_pipeline_unknown_verdict_does_not_resolve() {
        let properties = vec![String::from("Inv1")];

        let pipeline = VerificationPipeline::new(vec![
            PhaseConfig {
                phase: VerificationPhase::Bmc,
                time_budget: Duration::from_secs(30),
                enabled: true,
            },
            PhaseConfig {
                phase: VerificationPhase::Pdr,
                time_budget: Duration::from_secs(60),
                enabled: true,
            },
        ]);

        // BMC returns Unknown for Inv1, PDR resolves it.
        let mut runners: FxHashMap<VerificationPhase, Box<dyn PhaseRunner>> = FxHashMap::default();
        runners.insert(
            VerificationPhase::Bmc,
            Box::new(MockRunner::new(
                VerificationPhase::Bmc,
                vec![(String::from("Inv1"), PropertyVerdict::Unknown)],
            )),
        );
        runners.insert(
            VerificationPhase::Pdr,
            Box::new(MockRunner::new(
                VerificationPhase::Pdr,
                vec![(String::from("Inv1"), PropertyVerdict::Satisfied)],
            )),
        );

        let result = pipeline.run(&properties, &mut runners);

        // BMC ran but didn't resolve (Unknown doesn't count).
        assert_eq!(result.phases_run.len(), 2);
        assert_eq!(result.phases_run[0].properties_resolved, 0);
        // PDR resolved it.
        assert_eq!(result.phases_run[1].properties_resolved, 1);
        assert_eq!(
            result.verdicts.get("Inv1"),
            Some(&PropertyVerdict::Satisfied)
        );
    }

    // -----------------------------------------------------------------------
    // Test: empty property list
    // -----------------------------------------------------------------------

    #[test]
    fn test_pipeline_empty_properties() {
        let pipeline = VerificationPipeline::default_pipeline();
        let mut runners: FxHashMap<VerificationPhase, Box<dyn PhaseRunner>> = FxHashMap::default();
        runners.insert(
            VerificationPhase::RandomWalk,
            Box::new(NoOpRunner::new(VerificationPhase::RandomWalk)),
        );

        let result = pipeline.run(&[], &mut runners);

        assert!(result.verdicts.is_empty());
        // No phases should run since there are no properties.
        assert!(result.phases_run.is_empty());
    }

    // -----------------------------------------------------------------------
    // Test: phase display formatting
    // -----------------------------------------------------------------------

    #[test]
    fn test_verification_phase_display() {
        assert_eq!(VerificationPhase::RandomWalk.to_string(), "RandomWalk");
        assert_eq!(VerificationPhase::Bmc.to_string(), "BMC");
        assert_eq!(VerificationPhase::KInduction.to_string(), "k-induction");
        assert_eq!(VerificationPhase::Pdr.to_string(), "PDR");
        assert_eq!(VerificationPhase::Bfs.to_string(), "BFS");
        assert_eq!(VerificationPhase::SymbolicSim.to_string(), "SymbolicSim");
    }

    // -----------------------------------------------------------------------
    // Test: VerificationStrategy display
    // -----------------------------------------------------------------------

    #[test]
    fn test_verification_strategy_display() {
        assert_eq!(VerificationStrategy::Quick.to_string(), "quick");
        assert_eq!(VerificationStrategy::Full.to_string(), "full");
        assert_eq!(VerificationStrategy::Auto.to_string(), "auto");
    }

    // -----------------------------------------------------------------------
    // Test: quick pipeline construction
    // -----------------------------------------------------------------------

    #[test]
    fn test_quick_pipeline_construction() {
        let pipeline = VerificationPipeline::quick_pipeline();
        let phases = pipeline.phases();

        assert_eq!(phases.len(), 2);

        assert_eq!(phases[0].phase, VerificationPhase::RandomWalk);
        assert!(phases[0].enabled);
        assert_eq!(phases[0].time_budget, Duration::from_secs(2));

        assert_eq!(phases[1].phase, VerificationPhase::Bmc);
        assert!(phases[1].enabled);
        assert_eq!(phases[1].time_budget, Duration::from_secs(10));
    }

    // -----------------------------------------------------------------------
    // Test: full pipeline construction
    // -----------------------------------------------------------------------

    #[test]
    fn test_full_pipeline_construction() {
        let pipeline = VerificationPipeline::full_pipeline();
        let phases = pipeline.phases();

        assert_eq!(phases.len(), 2);

        assert_eq!(phases[0].phase, VerificationPhase::RandomWalk);
        assert!(phases[0].enabled);
        assert_eq!(phases[0].time_budget, Duration::from_secs(5));

        assert_eq!(phases[1].phase, VerificationPhase::Bfs);
        assert!(phases[1].enabled);
        assert_eq!(phases[1].time_budget, Duration::from_secs(600));
    }

    // -----------------------------------------------------------------------
    // Test: strategy.into_pipeline() produces correct pipeline
    // -----------------------------------------------------------------------

    #[test]
    fn test_strategy_into_pipeline_quick() {
        let pipeline = VerificationStrategy::Quick.into_pipeline();
        let phases = pipeline.phases();
        assert_eq!(phases.len(), 2);
        assert_eq!(phases[0].phase, VerificationPhase::RandomWalk);
        assert_eq!(phases[1].phase, VerificationPhase::Bmc);
    }

    #[test]
    fn test_strategy_into_pipeline_full() {
        let pipeline = VerificationStrategy::Full.into_pipeline();
        let phases = pipeline.phases();
        assert_eq!(phases.len(), 2);
        assert_eq!(phases[0].phase, VerificationPhase::RandomWalk);
        assert_eq!(phases[1].phase, VerificationPhase::Bfs);
    }

    #[test]
    fn test_strategy_into_pipeline_auto() {
        let pipeline = VerificationStrategy::Auto.into_pipeline();
        let phases = pipeline.phases();
        assert_eq!(phases.len(), 5);
        assert_eq!(phases[0].phase, VerificationPhase::RandomWalk);
        assert_eq!(phases[1].phase, VerificationPhase::Bmc);
        assert_eq!(phases[2].phase, VerificationPhase::KInduction);
        assert_eq!(phases[3].phase, VerificationPhase::Pdr);
        assert_eq!(phases[4].phase, VerificationPhase::Bfs);
    }
}
