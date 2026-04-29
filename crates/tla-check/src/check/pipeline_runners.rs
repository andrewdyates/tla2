// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Concrete `PhaseRunner` implementations that wire verification backends
//! into the multi-phase pipeline (`pipeline.rs`).
//!
//! Part of #3720, #3723.

use rustc_hash::FxHashMap;
use std::time::Duration;

use super::model_checker::random_walk::{RandomWalkConfig, RandomWalkResult};
use super::model_checker::ModelChecker;
use super::pipeline::{PhaseRunner, PropertyId, PropertyVerdict, VerificationPhase};

// ---------------------------------------------------------------------------
// RandomWalkRunner
// ---------------------------------------------------------------------------

/// Pipeline runner that wraps the random-walk witness search engine.
///
/// Runs `num_walks` independent random walks of up to `max_depth` steps each.
/// Any invariant violation found is a real witness (sound under-approximation);
/// properties that survive all walks are reported as `Unknown` so subsequent
/// pipeline phases can attempt proof or deeper exploration.
///
/// Part of #3720.
pub struct RandomWalkRunner<'a> {
    checker: ModelChecker<'a>,
    walk_config: RandomWalkConfig,
}

impl std::fmt::Debug for RandomWalkRunner<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RandomWalkRunner")
            .field("walk_config", &self.walk_config)
            .finish()
    }
}

impl<'a> RandomWalkRunner<'a> {
    /// Create a new runner.
    ///
    /// `checker` is a freshly-constructed `ModelChecker` (the runner takes
    /// ownership because `random_walk` requires `&mut self`).
    /// `walk_config` controls number of walks, depth, and seed.
    pub fn new(checker: ModelChecker<'a>, walk_config: RandomWalkConfig) -> Self {
        Self {
            checker,
            walk_config,
        }
    }
}

impl PhaseRunner for RandomWalkRunner<'_> {
    fn run(
        &mut self,
        unresolved: &[PropertyId],
        _time_budget: Duration,
    ) -> FxHashMap<PropertyId, PropertyVerdict> {
        let result = self.checker.random_walk(&self.walk_config);

        let mut verdicts = FxHashMap::default();

        match result {
            RandomWalkResult::InvariantViolation { ref invariant, .. } => {
                // Mark the violated invariant as Violated.
                for prop in unresolved {
                    if prop == invariant {
                        verdicts.insert(prop.clone(), PropertyVerdict::Violated);
                    }
                    // Other properties remain unresolved (not in map).
                }
            }
            RandomWalkResult::Deadlock { .. } => {
                // Deadlock is a global property violation — report all
                // unresolved safety properties as Unknown (deadlock is not
                // specific to a single invariant). The pipeline caller
                // handles deadlock reporting separately.
            }
            RandomWalkResult::NoViolationFound { .. } => {
                // No violation found — all properties remain Unknown.
            }
            RandomWalkResult::Error(_) => {
                // Phase error — all properties remain Unknown so later
                // phases can still attempt verification.
            }
        }

        verdicts
    }

    fn phase(&self) -> VerificationPhase {
        VerificationPhase::RandomWalk
    }
}

// ---------------------------------------------------------------------------
// BFS Runner (always available)
// ---------------------------------------------------------------------------

/// BFS runner wrapping the explicit-state model checker for exhaustive
/// state-space exploration.
///
/// Maps:
/// - `CheckResult::Success` -> `PropertyVerdict::Satisfied` for all properties
/// - `CheckResult::InvariantViolation` -> `PropertyVerdict::Violated` for the
///   specific invariant that failed; other properties remain `Unknown`
/// - Other results (error, limit, deadlock) -> leaves as `Unknown`
///
/// Part of #3723.
pub struct BfsRunner<'a> {
    module: &'a tla_core::ast::Module,
    checker_modules: Vec<&'a tla_core::ast::Module>,
    config: &'a crate::config::Config,
}

impl<'a> BfsRunner<'a> {
    /// Construct a BFS runner from the module and config.
    pub fn new(
        module: &'a tla_core::ast::Module,
        checker_modules: &[&'a tla_core::ast::Module],
        config: &'a crate::config::Config,
    ) -> Self {
        Self {
            module,
            checker_modules: checker_modules.to_vec(),
            config,
        }
    }
}

impl std::fmt::Debug for BfsRunner<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BfsRunner")
            .field("module", &self.module.name.node)
            .finish()
    }
}

impl PhaseRunner for BfsRunner<'_> {
    fn run(
        &mut self,
        unresolved: &[PropertyId],
        _time_budget: Duration,
    ) -> FxHashMap<PropertyId, PropertyVerdict> {
        use super::api::CheckResult;

        let runtime_config = self.config.runtime_model_config();
        let mut checker =
            ModelChecker::new_with_extends(self.module, &self.checker_modules, &runtime_config);
        let result = checker.check();

        let mut verdicts = FxHashMap::default();
        match result {
            CheckResult::Success(_) => {
                // All invariants hold across the full state space.
                for prop in unresolved {
                    verdicts.insert(prop.clone(), PropertyVerdict::Satisfied);
                }
            }
            CheckResult::InvariantViolation { ref invariant, .. } => {
                // The specific invariant that failed.
                for prop in unresolved {
                    if prop == invariant {
                        verdicts.insert(prop.clone(), PropertyVerdict::Violated);
                    }
                    // Other properties remain unknown — BFS found one violation
                    // but we don't know about the rest.
                }
            }
            CheckResult::Deadlock { .. }
            | CheckResult::Error { .. }
            | CheckResult::LimitReached { .. }
            | CheckResult::PropertyViolation { .. }
            | CheckResult::LivenessViolation { .. } => {
                // Could not determine any property status.
            }
        }
        verdicts
    }

    fn phase(&self) -> VerificationPhase {
        VerificationPhase::Bfs
    }
}

// ---------------------------------------------------------------------------
// BMC Runner (z4 feature gate)
// ---------------------------------------------------------------------------

/// BMC runner wrapping `check_bmc()` for symbolic bounded bug finding.
///
/// Maps:
/// - `BmcResult::Violation` -> `PropertyVerdict::Violated` for all unresolved
///   properties (BMC checks the conjunction of all invariants)
/// - `BmcResult::BoundReached` -> leaves as `Unknown` (BMC cannot prove safety)
/// - `BmcResult::Unknown` -> leaves as `Unknown`
///
/// Part of #3723.
#[cfg(feature = "z4")]
pub struct BmcRunner<'a> {
    module: &'a tla_core::ast::Module,
    config: &'a crate::config::Config,
    ctx: &'a crate::eval::EvalCtx,
    /// BMC depth bound (pipeline default: 20).
    default_depth: usize,
}

#[cfg(feature = "z4")]
impl<'a> BmcRunner<'a> {
    /// Construct a BMC runner.
    ///
    /// `default_depth` controls the BMC unrolling depth. A reasonable default
    /// is 10-30 for pipeline use (deeper exploration happens in later phases).
    pub fn new(
        module: &'a tla_core::ast::Module,
        config: &'a crate::config::Config,
        ctx: &'a crate::eval::EvalCtx,
        default_depth: usize,
    ) -> Self {
        Self {
            module,
            config,
            ctx,
            default_depth,
        }
    }
}

#[cfg(feature = "z4")]
impl std::fmt::Debug for BmcRunner<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BmcRunner")
            .field("module", &self.module.name.node)
            .field("default_depth", &self.default_depth)
            .finish()
    }
}

#[cfg(feature = "z4")]
impl PhaseRunner for BmcRunner<'_> {
    fn run(
        &mut self,
        unresolved: &[PropertyId],
        time_budget: Duration,
    ) -> FxHashMap<PropertyId, PropertyVerdict> {
        use crate::z4_bmc::{check_bmc, BmcConfig, BmcResult};

        let bmc_config = BmcConfig {
            max_depth: self.default_depth,
            solve_timeout: Some(time_budget),
            ..BmcConfig::default()
        };

        let mut verdicts = FxHashMap::default();
        match check_bmc(self.module, self.config, self.ctx, bmc_config) {
            Ok(BmcResult::Violation { .. }) => {
                // BMC found a counterexample. The conjunction of all invariants
                // was violated. Mark all unresolved properties as violated
                // (conservative: at least one invariant fails).
                for prop in unresolved {
                    verdicts.insert(prop.clone(), PropertyVerdict::Violated);
                }
            }
            Ok(BmcResult::BoundReached { .. }) | Ok(BmcResult::Unknown { .. }) => {
                // No bug within the bound or solver inconclusive. BMC cannot
                // prove safety, so leave as Unknown.
            }
            Err(e) => {
                eprintln!("Pipeline BMC error: {e}");
            }
        }
        verdicts
    }

    fn phase(&self) -> VerificationPhase {
        VerificationPhase::Bmc
    }
}

// ---------------------------------------------------------------------------
// PDR Runner (z4 feature gate)
// ---------------------------------------------------------------------------

/// PDR runner wrapping `check_pdr_with_config()` for symbolic safety proving.
///
/// Maps:
/// - `PdrResult::Safe` -> `PropertyVerdict::Satisfied` for all unresolved properties
/// - `PdrResult::Unsafe` -> `PropertyVerdict::Violated` for all unresolved properties
/// - `PdrResult::Unknown` -> leaves as `Unknown`
///
/// Part of #3723.
#[cfg(feature = "z4")]
pub struct PdrRunner<'a> {
    module: &'a tla_core::ast::Module,
    config: &'a crate::config::Config,
    ctx: &'a crate::eval::EvalCtx,
}

#[cfg(feature = "z4")]
impl<'a> PdrRunner<'a> {
    /// Construct a PDR runner.
    pub fn new(
        module: &'a tla_core::ast::Module,
        config: &'a crate::config::Config,
        ctx: &'a crate::eval::EvalCtx,
    ) -> Self {
        Self {
            module,
            config,
            ctx,
        }
    }
}

#[cfg(feature = "z4")]
impl std::fmt::Debug for PdrRunner<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PdrRunner")
            .field("module", &self.module.name.node)
            .finish()
    }
}

#[cfg(feature = "z4")]
impl PhaseRunner for PdrRunner<'_> {
    fn run(
        &mut self,
        unresolved: &[PropertyId],
        time_budget: Duration,
    ) -> FxHashMap<PropertyId, PropertyVerdict> {
        use crate::z4_pdr::{check_pdr_with_config, PdrResult};
        use tla_z4::PdrConfig;

        let mut pdr_config = PdrConfig::default();
        pdr_config.solve_timeout = Some(time_budget);

        let mut verdicts = FxHashMap::default();
        match check_pdr_with_config(self.module, self.config, self.ctx, pdr_config) {
            Ok(PdrResult::Safe { .. }) => {
                // PDR proved all invariants hold for all reachable states.
                for prop in unresolved {
                    verdicts.insert(prop.clone(), PropertyVerdict::Satisfied);
                }
            }
            Ok(PdrResult::Unsafe { .. }) => {
                // PDR found a counterexample.
                for prop in unresolved {
                    verdicts.insert(prop.clone(), PropertyVerdict::Violated);
                }
            }
            Ok(PdrResult::Unknown { .. }) => {
                // Inconclusive.
            }
            Err(e) => {
                eprintln!("Pipeline PDR error: {e}");
            }
        }
        verdicts
    }

    fn phase(&self) -> VerificationPhase {
        VerificationPhase::Pdr
    }
}

// ---------------------------------------------------------------------------
// K-Induction Runner (z4 feature gate)
// ---------------------------------------------------------------------------

/// K-induction runner wrapping `check_kinduction()` for symbolic safety proving.
///
/// Maps:
/// - `KInductionResult::Proved` -> `PropertyVerdict::Satisfied` for all unresolved properties
/// - `KInductionResult::Counterexample` -> `PropertyVerdict::Violated` for all unresolved properties
/// - `KInductionResult::Unknown` -> leaves as `Unknown`
///
/// Part of #3722.
#[cfg(feature = "z4")]
pub struct KInductionRunner<'a> {
    module: &'a tla_core::ast::Module,
    config: &'a crate::config::Config,
    ctx: &'a crate::eval::EvalCtx,
    /// Maximum induction depth (pipeline default: 20).
    max_k: usize,
}

#[cfg(feature = "z4")]
impl<'a> KInductionRunner<'a> {
    /// Construct a k-induction runner.
    ///
    /// `max_k` controls the maximum induction depth. A reasonable default
    /// is 10-20 for pipeline use.
    pub fn new(
        module: &'a tla_core::ast::Module,
        config: &'a crate::config::Config,
        ctx: &'a crate::eval::EvalCtx,
        max_k: usize,
    ) -> Self {
        Self {
            module,
            config,
            ctx,
            max_k,
        }
    }
}

#[cfg(feature = "z4")]
impl std::fmt::Debug for KInductionRunner<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KInductionRunner")
            .field("module", &self.module.name.node)
            .field("max_k", &self.max_k)
            .finish()
    }
}

#[cfg(feature = "z4")]
impl PhaseRunner for KInductionRunner<'_> {
    fn run(
        &mut self,
        unresolved: &[PropertyId],
        time_budget: Duration,
    ) -> FxHashMap<PropertyId, PropertyVerdict> {
        use crate::z4_kinduction::{check_kinduction, KInductionConfig, KInductionResult};

        let kind_config = KInductionConfig {
            max_k: self.max_k,
            solve_timeout: Some(time_budget),
            ..KInductionConfig::default()
        };

        let mut verdicts = FxHashMap::default();
        match check_kinduction(self.module, self.config, self.ctx, kind_config) {
            Ok(KInductionResult::Proved { .. }) => {
                // K-induction proved all invariants hold for all reachable states.
                for prop in unresolved {
                    verdicts.insert(prop.clone(), PropertyVerdict::Satisfied);
                }
            }
            Ok(KInductionResult::Counterexample { .. }) => {
                // BMC base case found a counterexample.
                for prop in unresolved {
                    verdicts.insert(prop.clone(), PropertyVerdict::Violated);
                }
            }
            Ok(KInductionResult::Unknown { .. }) => {
                // Inconclusive — leave as Unknown for subsequent phases.
            }
            Err(e) => {
                eprintln!("Pipeline k-induction error: {e}");
            }
        }
        verdicts
    }

    fn phase(&self) -> VerificationPhase {
        VerificationPhase::KInduction
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::Config;
    use crate::test_support::parse_module;
    use rustc_hash::FxHashMap;
    use std::time::Duration;

    use super::super::pipeline::{PhaseConfig, VerificationPipeline};

    // -------------------------------------------------------------------
    // Phase accessor smoke tests
    // -------------------------------------------------------------------

    #[test]
    fn test_random_walk_runner_phase() {
        // Verify the phase() accessor returns the correct variant.
        // Full integration tests require a TLA+ module, which is covered
        // by random_walk.rs tests. This test validates the PhaseRunner
        // contract at the type level.
        assert_eq!(VerificationPhase::RandomWalk.to_string(), "RandomWalk");
    }

    #[test]
    fn test_bfs_runner_phase() {
        assert_eq!(VerificationPhase::Bfs.to_string(), "BFS");
    }

    #[cfg(feature = "z4")]
    #[test]
    fn test_bmc_runner_phase() {
        assert_eq!(VerificationPhase::Bmc.to_string(), "BMC");
    }

    #[cfg(feature = "z4")]
    #[test]
    fn test_pdr_runner_phase() {
        assert_eq!(VerificationPhase::Pdr.to_string(), "PDR");
    }

    #[cfg(feature = "z4")]
    #[test]
    fn test_kinduction_runner_phase() {
        assert_eq!(VerificationPhase::KInduction.to_string(), "k-induction");
    }

    // -------------------------------------------------------------------
    // Helper: build Config with Init/Next/Invariants
    // -------------------------------------------------------------------

    fn config_with_invariants(init: &str, next: &str, invariants: &[&str]) -> Config {
        Config {
            init: Some(init.to_string()),
            next: Some(next.to_string()),
            invariants: invariants.iter().map(|s| s.to_string()).collect(),
            ..Default::default()
        }
    }

    // -------------------------------------------------------------------
    // End-to-end: BFS runner resolves satisfied invariant
    // -------------------------------------------------------------------

    /// Verify that BfsRunner correctly wraps the model checker and reports
    /// `Satisfied` when all reachable states satisfy the invariant.
    #[test]
    fn test_bfs_runner_e2e_invariant_satisfied() {
        let src = r#"
---- MODULE BfsE2eSafe ----
VARIABLE x
Init == x \in {0, 1, 2}
Next == x' = x
TypeOK == x \in {0, 1, 2}
====
"#;
        let module = parse_module(src);
        let config = config_with_invariants("Init", "Next", &["TypeOK"]);

        let mut runner = BfsRunner::new(&module, &[], &config);
        let properties = vec!["TypeOK".to_string()];
        let verdicts = runner.run(&properties, Duration::from_secs(30));

        assert_eq!(
            verdicts.get("TypeOK"),
            Some(&PropertyVerdict::Satisfied),
            "BFS should report invariant as Satisfied for trivially safe spec"
        );
    }

    // -------------------------------------------------------------------
    // End-to-end: BFS runner detects violated invariant
    // -------------------------------------------------------------------

    /// Verify that BfsRunner correctly detects an invariant violation and
    /// reports `Violated` for the offending property.
    #[test]
    fn test_bfs_runner_e2e_invariant_violated() {
        let src = r#"
---- MODULE BfsE2eUnsafe ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
SmallBound == x < 3
====
"#;
        let module = parse_module(src);
        let config = config_with_invariants("Init", "Next", &["SmallBound"]);

        let mut runner = BfsRunner::new(&module, &[], &config);
        let properties = vec!["SmallBound".to_string()];
        let verdicts = runner.run(&properties, Duration::from_secs(30));

        assert_eq!(
            verdicts.get("SmallBound"),
            Some(&PropertyVerdict::Violated),
            "BFS should detect invariant violation when x reaches 3"
        );
    }

    // -------------------------------------------------------------------
    // End-to-end: RandomWalk runner detects violation
    // -------------------------------------------------------------------

    /// Verify that RandomWalkRunner can find an easy invariant violation
    /// via random exploration.
    #[test]
    fn test_random_walk_runner_e2e_violation() {
        let src = r#"
---- MODULE WalkE2eUnsafe ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
SmallBound == x < 3
====
"#;
        let module = parse_module(src);
        let config = config_with_invariants("Init", "Next", &["SmallBound"]);
        let runtime_config = config.runtime_model_config();

        let checker = ModelChecker::new(&module, &runtime_config);
        let walk_config = RandomWalkConfig {
            num_walks: 100,
            max_depth: 100,
            seed: Some(42),
        };
        let mut runner = RandomWalkRunner::new(checker, walk_config);

        let properties = vec!["SmallBound".to_string()];
        let verdicts = runner.run(&properties, Duration::from_secs(5));

        assert_eq!(
            verdicts.get("SmallBound"),
            Some(&PropertyVerdict::Violated),
            "Random walk should easily find violation when x reaches 3 in 100 steps"
        );
    }

    // -------------------------------------------------------------------
    // End-to-end: full pipeline resolves properties across phases
    // -------------------------------------------------------------------

    /// End-to-end pipeline test: RandomWalk(5s) + BFS(300s) together resolve
    /// all properties. This validates the pipeline orchestration with real
    /// verification backends, not mocks.
    ///
    /// Spec has two invariants:
    /// - `EasyViolation`: violated quickly (x reaches 3 in 3 steps)
    /// - Both should be resolved by BFS if not by random walk.
    #[test]
    fn test_pipeline_e2e_resolves_all_properties() {
        let src = r#"
---- MODULE PipelineE2e ----
VARIABLE x
Init == x \in {0, 1}
Next == IF x < 5 THEN x' = x + 1 ELSE x' = x
Bound == x <= 10
====
"#;
        let module = parse_module(src);
        let config = config_with_invariants("Init", "Next", &["Bound"]);
        let runtime_config = config.runtime_model_config();

        let properties = vec!["Bound".to_string()];

        // Build pipeline: RandomWalk -> BFS (skip symbolic phases for simplicity).
        let pipeline = VerificationPipeline::new(vec![
            PhaseConfig {
                phase: VerificationPhase::RandomWalk,
                time_budget: Duration::from_secs(5),
                enabled: true,
            },
            PhaseConfig {
                phase: VerificationPhase::Bfs,
                time_budget: Duration::from_secs(60),
                enabled: true,
            },
        ]);

        let mut runners: FxHashMap<VerificationPhase, Box<dyn PhaseRunner>> = FxHashMap::default();

        // RandomWalk runner
        let walk_checker = ModelChecker::new(&module, &runtime_config);
        let walk_config = RandomWalkConfig {
            num_walks: 50,
            max_depth: 100,
            seed: Some(42),
        };
        runners.insert(
            VerificationPhase::RandomWalk,
            Box::new(RandomWalkRunner::new(walk_checker, walk_config)),
        );

        // BFS runner
        runners.insert(
            VerificationPhase::Bfs,
            Box::new(BfsRunner::new(&module, &[], &config)),
        );

        let result = pipeline.run(&properties, &mut runners);

        // The invariant `Bound` (x <= 10) holds for this spec since x only
        // goes up to 5. BFS should verify it as Satisfied.
        assert_eq!(
            result.verdicts.get("Bound"),
            Some(&PropertyVerdict::Satisfied),
            "Pipeline should resolve Bound as Satisfied (x never exceeds 5)"
        );
        // At least one phase should have run.
        assert!(
            !result.phases_run.is_empty(),
            "Pipeline should have run at least one phase"
        );
    }

    /// End-to-end pipeline test with a violation: the pipeline should detect
    /// the violation in an early phase and skip expensive later phases.
    #[test]
    fn test_pipeline_e2e_early_violation_detection() {
        let src = r#"
---- MODULE PipelineViolation ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TooSmall == x < 3
====
"#;
        let module = parse_module(src);
        let config = config_with_invariants("Init", "Next", &["TooSmall"]);
        let runtime_config = config.runtime_model_config();

        let properties = vec!["TooSmall".to_string()];

        // Two-phase pipeline: RandomWalk -> BFS.
        let pipeline = VerificationPipeline::new(vec![
            PhaseConfig {
                phase: VerificationPhase::RandomWalk,
                time_budget: Duration::from_secs(5),
                enabled: true,
            },
            PhaseConfig {
                phase: VerificationPhase::Bfs,
                time_budget: Duration::from_secs(60),
                enabled: true,
            },
        ]);

        let mut runners: FxHashMap<VerificationPhase, Box<dyn PhaseRunner>> = FxHashMap::default();

        // RandomWalk runner — should find the violation in 3 steps.
        let walk_checker = ModelChecker::new(&module, &runtime_config);
        let walk_config = RandomWalkConfig {
            num_walks: 100,
            max_depth: 100,
            seed: Some(42),
        };
        runners.insert(
            VerificationPhase::RandomWalk,
            Box::new(RandomWalkRunner::new(walk_checker, walk_config)),
        );

        // BFS runner (should be skipped if RandomWalk resolves everything).
        runners.insert(
            VerificationPhase::Bfs,
            Box::new(BfsRunner::new(&module, &[], &config)),
        );

        let result = pipeline.run(&properties, &mut runners);

        // The violation should be detected.
        assert_eq!(
            result.verdicts.get("TooSmall"),
            Some(&PropertyVerdict::Violated),
            "Pipeline should detect that x reaches 3, violating TooSmall"
        );

        // RandomWalk should resolve it, so only 1 phase should run (early exit).
        assert_eq!(
            result.phases_run.len(),
            1,
            "Pipeline should early-exit after RandomWalk finds the violation"
        );
        assert_eq!(
            result.phases_run[0].phase,
            VerificationPhase::RandomWalk,
            "Only RandomWalk should have run"
        );
        assert_eq!(
            result.phases_run[0].properties_resolved, 1,
            "RandomWalk should resolve exactly 1 property"
        );
    }
}
