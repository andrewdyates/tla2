// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Random Walk Witness Search for TLA+ specifications.
//!
//! Zero-memory-overhead random walk engine for fast shallow bug detection.
//! Fires random transitions from initial states without maintaining a visited
//! set (no BFS frontier, no fingerprint storage). Pure under-approximation:
//! any bug found is real, but absence of bugs means nothing.
//!
//! Ported from `tla-petri/src/examinations/reachability_walk.rs` (Petri net
//! random walk) adapted for TLA+ model checking infrastructure.
//!
//! Part of #3720.

use std::time::{SystemTime, UNIX_EPOCH};

use super::{
    bind_constants_from_config, build_ident_hints, precompute_constant_operators,
    promote_env_constants_to_precomputed, ArrayState, CheckError, Fingerprint, ModelChecker, State,
    Trace,
};
use crate::checker_ops::InvariantOutcome;
use crate::var_index::VarRegistry;
use crate::{ConfigCheckError, EvalCheckError};

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Configuration for random walk witness search.
#[derive(Debug, Clone)]
pub struct RandomWalkConfig {
    /// Number of independent walks to run.
    pub num_walks: usize,
    /// Maximum depth (steps) per walk.
    pub max_depth: usize,
    /// Optional seed for reproducibility. `None` = entropy-seeded.
    pub seed: Option<u64>,
}

/// Result of the random walk phase.
#[derive(Debug)]
pub enum RandomWalkResult {
    /// Completed all walks without finding any violation.
    NoViolationFound {
        walks_completed: usize,
        total_steps: usize,
    },
    /// An invariant was violated at the given depth.
    InvariantViolation {
        invariant: String,
        trace: Trace,
        walk_id: usize,
        depth: usize,
    },
    /// A deadlock (no enabled transitions, non-terminal state) was found.
    Deadlock {
        trace: Trace,
        walk_id: usize,
        depth: usize,
    },
    /// A fatal error occurred during the walk.
    Error(CheckError),
}

// ---------------------------------------------------------------------------
// Internal RNG (matches SimpleRng in simulation_rng.rs — no `rand` dep)
// ---------------------------------------------------------------------------

struct WalkRng {
    state: u64,
}

impl WalkRng {
    fn new(seed: u64) -> Self {
        WalkRng {
            state: seed.wrapping_add(1),
        }
    }

    fn entropy_seed() -> u64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(42)
    }

    fn next_u64(&mut self) -> u64 {
        // LCG parameters from Numerical Recipes
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.state
    }

    fn next_usize(&mut self, bound: usize) -> usize {
        if bound == 0 {
            return 0;
        }
        (self.next_u64() % (bound as u64)) as usize
    }
}

// ---------------------------------------------------------------------------
// Preparation (mirrors simulation_setup.rs pattern)
// ---------------------------------------------------------------------------

struct RandomWalkPrep {
    initial_states: Vec<State>,
    next_name: String,
    registry: VarRegistry,
}

impl ModelChecker<'_> {
    fn prepare_random_walk(&mut self) -> Result<RandomWalkPrep, CheckError> {
        // Bind constants from config.
        bind_constants_from_config(&mut self.ctx, self.config)
            .map_err(|e| CheckError::from(EvalCheckError::Eval(e)))?;
        precompute_constant_operators(&mut self.ctx);
        promote_env_constants_to_precomputed(&mut self.ctx);
        build_ident_hints(&mut self.ctx);

        // Validate model has variables.
        if self.module.vars.is_empty() {
            return Err(ConfigCheckError::NoVariables.into());
        }

        // Validate invariants exist.
        for inv_name in &self.config.invariants {
            if !self.ctx.has_op(inv_name) {
                return Err(ConfigCheckError::MissingInvariant(inv_name.clone()).into());
            }
        }

        // Resolve Init/Next names.
        let init_name = self
            .config
            .init
            .as_ref()
            .ok_or(ConfigCheckError::MissingInit)?;
        let init_name = self.ctx.resolve_op_name(init_name).to_string();

        let next_name = self
            .config
            .next
            .as_ref()
            .ok_or(ConfigCheckError::MissingNext)?;
        let next_name = self.ctx.resolve_op_name(next_name).to_string();

        // Detect Trace usage.
        self.compiled.uses_trace =
            super::trace_detect::compute_uses_trace(self.config, &self.module.op_defs)?;

        // Check ASSUME statements.
        if let Some(result) = self.check_assumes() {
            let error = match result {
                super::CheckResult::Error { error, .. } => error,
                other => ConfigCheckError::Setup(format!(
                    "ASSUME check returned unexpected result: {:?}",
                    other.stats()
                ))
                .into(),
            };
            return Err(error);
        }

        // Generate initial states (with simulation fallback for unconstrained vars).
        let initial_states = self.generate_initial_states_simulation_fallback(&init_name)?;
        let registry = self.ctx.var_registry().clone();

        // Filter by state constraints.
        let mut constrained = Vec::with_capacity(initial_states.len());
        for state in initial_states {
            let arr = ArrayState::from_state(&state, &registry);
            if self.check_state_constraints_array(&arr)? {
                constrained.push(state);
            }
        }
        if constrained.is_empty() {
            return Err(ConfigCheckError::InitCannotEnumerate(
                "No valid initial states after constraint filtering".to_string(),
            )
            .into());
        }

        Ok(RandomWalkPrep {
            initial_states: constrained,
            next_name,
            registry,
        })
    }

    /// Run `num_walks` random walks of up to `max_depth` steps each.
    ///
    /// Zero memory overhead: no visited set, no fingerprint storage.
    /// Any violation found is a real witness; absence means nothing.
    pub fn random_walk(&mut self, config: &RandomWalkConfig) -> RandomWalkResult {
        if let Some(err) = self.module.setup_error.take() {
            return RandomWalkResult::Error(err);
        }

        let prep = match self.prepare_random_walk() {
            Ok(p) => p,
            Err(e) => return RandomWalkResult::Error(e),
        };

        let base_seed = config.seed.unwrap_or_else(WalkRng::entropy_seed);
        let mut total_steps: usize = 0;

        for walk_id in 0..config.num_walks {
            let mut rng = WalkRng::new(base_seed.wrapping_add(walk_id as u64));

            // Pick a random initial state.
            let init_idx = rng.next_usize(prep.initial_states.len());
            let init_state = &prep.initial_states[init_idx];
            let mut init_arr = ArrayState::from_state(init_state, &prep.registry);
            let init_fp = init_arr.fingerprint(&prep.registry);

            // Keep path for trace reconstruction.
            let mut path: Vec<ArrayState> = vec![init_arr.clone()];

            // Check invariants on initial state.
            match check_walk_invariants(self, &init_arr, init_fp, 0) {
                WalkInvariantOutcome::Ok => {}
                WalkInvariantOutcome::Violation(inv) => {
                    let trace = build_trace(&path, &prep.registry);
                    return RandomWalkResult::InvariantViolation {
                        invariant: inv,
                        trace,
                        walk_id,
                        depth: 0,
                    };
                }
                WalkInvariantOutcome::Error(e) => return RandomWalkResult::Error(e),
            }

            let mut current_arr = init_arr;

            for step in 0..config.max_depth {
                // Generate successors from current state.
                let current_state = current_arr.to_state(&prep.registry);
                let successors = match self.generate_successors(&prep.next_name, &current_state) {
                    Ok(s) => s,
                    Err(e) => return RandomWalkResult::Error(e),
                };

                if successors.is_empty() {
                    // Check for deadlock.
                    if self.exploration.check_deadlock {
                        match self.is_terminal_state_array(&current_arr) {
                            Ok(true) => {} // Terminal — end walk normally.
                            Ok(false) => {
                                let trace = build_trace(&path, &prep.registry);
                                return RandomWalkResult::Deadlock {
                                    trace,
                                    walk_id,
                                    depth: step,
                                };
                            }
                            Err(e) => return RandomWalkResult::Error(e),
                        }
                    }
                    break; // No successors — end this walk.
                }

                // Pick a random successor.
                let succ_idx = rng.next_usize(successors.len());
                let next_state = &successors[succ_idx];
                let mut next_arr = ArrayState::from_state(next_state, &prep.registry);
                let next_fp = next_arr.fingerprint(&prep.registry);

                // Check invariants on successor.
                path.push(next_arr.clone());
                match check_walk_invariants(self, &next_arr, next_fp, step + 1) {
                    WalkInvariantOutcome::Ok => {}
                    WalkInvariantOutcome::Violation(inv) => {
                        let trace = build_trace(&path, &prep.registry);
                        return RandomWalkResult::InvariantViolation {
                            invariant: inv,
                            trace,
                            walk_id,
                            depth: step + 1,
                        };
                    }
                    WalkInvariantOutcome::Error(e) => return RandomWalkResult::Error(e),
                }

                current_arr = next_arr;
                total_steps += 1;
            }

            total_steps += 1; // Count the initial state.
        }

        RandomWalkResult::NoViolationFound {
            walks_completed: config.num_walks,
            total_steps,
        }
    }
}

// ---------------------------------------------------------------------------
// Invariant checking helper (free function to avoid borrow conflicts)
// ---------------------------------------------------------------------------

enum WalkInvariantOutcome {
    Ok,
    Violation(String),
    Error(CheckError),
}

/// Check invariants on a single state. Uses a free function rather than a
/// method on ModelChecker to avoid simultaneous &mut self borrows (ctx + config).
fn check_walk_invariants(
    checker: &mut ModelChecker<'_>,
    arr: &ArrayState,
    fp: Fingerprint,
    depth: usize,
) -> WalkInvariantOutcome {
    let level = match crate::checker_ops::depth_to_tlc_level(depth) {
        std::result::Result::Ok(l) => l,
        Err(e) => return WalkInvariantOutcome::Error(e),
    };
    let outcome = crate::checker_ops::check_invariants_for_successor(
        &mut checker.ctx,
        &checker.config.invariants,
        &checker.compiled.eval_state_invariants,
        arr,
        fp,
        level,
    );
    match outcome {
        InvariantOutcome::Ok | InvariantOutcome::ViolationContinued => WalkInvariantOutcome::Ok,
        InvariantOutcome::Violation { invariant, .. } => WalkInvariantOutcome::Violation(invariant),
        InvariantOutcome::Error(e) => WalkInvariantOutcome::Error(e),
    }
}

// ---------------------------------------------------------------------------
// Trace construction
// ---------------------------------------------------------------------------

fn build_trace(path: &[ArrayState], registry: &VarRegistry) -> Trace {
    let states: Vec<State> = path.iter().map(|a| a.to_state(registry)).collect();
    Trace::from_states(states)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{reset_global_state, Config};

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn random_walk_finds_invariant_violation() {
        let _serial = crate::test_utils::acquire_interner_lock();
        let _cleanup = ResetGuard;
        reset_global_state();

        let src = r#"
            ---- MODULE Bad ----
            VARIABLE x
            Init == x = 0
            Next == x' = x + 1
            Inv == x < 5
            ====
        "#;
        let tree = tla_core::parse_to_syntax_tree(src);
        let lowered = tla_core::lower(tla_core::FileId(0), &tree);
        let module = lowered.module.expect("module should lower");

        let config =
            Config::parse("INIT Init\nNEXT Next\nINVARIANT Inv\n").expect("config should parse");
        let mut checker = ModelChecker::new(&module, &config);

        let walk_cfg = RandomWalkConfig {
            num_walks: 10,
            max_depth: 100,
            seed: Some(42),
        };
        let result = checker.random_walk(&walk_cfg);
        match result {
            RandomWalkResult::InvariantViolation {
                invariant, depth, ..
            } => {
                assert_eq!(invariant, "Inv");
                assert_eq!(depth, 5, "violation should be at depth 5 where x=5");
            }
            other => panic!("Expected InvariantViolation, got {:?}", other),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn random_walk_no_violation_on_safe_spec() {
        let _serial = crate::test_utils::acquire_interner_lock();
        let _cleanup = ResetGuard;
        reset_global_state();

        let src = r#"
            ---- MODULE Safe ----
            VARIABLE x
            Init == x \in {0, 1}
            Next == x' = 1 - x
            Inv == x \in {0, 1}
            ====
        "#;
        let tree = tla_core::parse_to_syntax_tree(src);
        let lowered = tla_core::lower(tla_core::FileId(0), &tree);
        let module = lowered.module.expect("module should lower");

        let config =
            Config::parse("INIT Init\nNEXT Next\nINVARIANT Inv\n").expect("config should parse");
        let mut checker = ModelChecker::new(&module, &config);

        let walk_cfg = RandomWalkConfig {
            num_walks: 100,
            max_depth: 50,
            seed: Some(99),
        };
        let result = checker.random_walk(&walk_cfg);
        match result {
            RandomWalkResult::NoViolationFound {
                walks_completed, ..
            } => {
                assert_eq!(walks_completed, 100);
            }
            other => panic!("Expected NoViolationFound, got {:?}", other),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn random_walk_finds_deadlock() {
        let _serial = crate::test_utils::acquire_interner_lock();
        let _cleanup = ResetGuard;
        reset_global_state();

        let src = r#"
            ---- MODULE Dead ----
            VARIABLE x
            Init == x = 0
            Next == x < 3 /\ x' = x + 1
            ====
        "#;
        let tree = tla_core::parse_to_syntax_tree(src);
        let lowered = tla_core::lower(tla_core::FileId(0), &tree);
        let module = lowered.module.expect("module should lower");

        // check_deadlock defaults to true in Config
        let config = Config::parse("INIT Init\nNEXT Next\n").expect("config should parse");
        let mut checker = ModelChecker::new(&module, &config);
        // Explicitly enable deadlock checking
        checker.exploration.check_deadlock = true;

        let walk_cfg = RandomWalkConfig {
            num_walks: 10,
            max_depth: 100,
            seed: Some(42),
        };
        let result = checker.random_walk(&walk_cfg);
        match result {
            RandomWalkResult::Deadlock { depth, .. } => {
                assert!(depth <= 3, "deadlock should occur at depth <= 3");
            }
            other => panic!("Expected Deadlock, got {:?}", other),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn random_walk_deterministic_with_seed() {
        let _serial = crate::test_utils::acquire_interner_lock();
        let _cleanup = ResetGuard;
        reset_global_state();

        let src = r#"
            ---- MODULE Det ----
            VARIABLE x
            Init == x \in {0, 1, 2}
            Next == x' \in {0, 1, 2}
            ====
        "#;
        let tree = tla_core::parse_to_syntax_tree(src);
        let lowered = tla_core::lower(tla_core::FileId(0), &tree);
        let module = lowered.module.expect("module should lower");

        let config = Config::parse("INIT Init\nNEXT Next\n").expect("config should parse");

        let walk_cfg = RandomWalkConfig {
            num_walks: 5,
            max_depth: 20,
            seed: Some(12345),
        };

        let mut checker1 = ModelChecker::new(&module, &config);
        let result1 = checker1.random_walk(&walk_cfg);
        drop(checker1);
        reset_global_state();

        let mut checker2 = ModelChecker::new(&module, &config);
        let result2 = checker2.random_walk(&walk_cfg);

        match (&result1, &result2) {
            (
                RandomWalkResult::NoViolationFound {
                    total_steps: s1, ..
                },
                RandomWalkResult::NoViolationFound {
                    total_steps: s2, ..
                },
            ) => {
                assert_eq!(s1, s2, "same seed should produce same step count");
            }
            _ => panic!(
                "Both runs should complete without violation: {:?} vs {:?}",
                result1, result2
            ),
        }
    }

    struct ResetGuard;
    impl Drop for ResetGuard {
        fn drop(&mut self) {
            reset_global_state();
        }
    }
}
