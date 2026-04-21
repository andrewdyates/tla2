// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model Checker - BFS state exploration with invariant checking
//!
//! This module implements the core model checking algorithm:
//! 1. Generate initial states using Init predicate
//! 2. BFS explore states using Next relation
//! 3. Check invariants at each state
//! 4. Generate counterexample traces when violations found
//!
//! # Algorithm
//!
//! ```text
//! seen = {}
//! queue = [all states satisfying Init]
//! for each s in queue:
//!     if s in seen: continue
//!     seen.add(s)
//!     for each invariant I:
//!         if not I(s): return Error(trace to s)
//!     for each successor t of s via Next:
//!         if t not in seen:
//!             queue.append(t)
//! return Success(|seen| states explored)
//! ```

pub(super) use crate::config::Config;
pub(super) use tla_core::ast::Module;

// Test-only imports: used by check/tests.rs via `use super::*`
#[cfg(test)]
use self::debug::fmt_tlc_fp;
#[cfg(test)]
use crate::constants::bind_constants_from_config;
#[cfg(test)]
use crate::eval::EvalCtx;
#[cfg(test)]
use crate::spec_formula::FairnessConstraint;
#[cfg(test)]
use crate::state::State;
#[cfg(test)]
use crate::Value;

// Re-export from liveness/ where it's defined (fixes layering: check → liveness, not reverse).
pub use crate::liveness::SuccessorWitnessMap;

mod api;
pub(crate) mod check_error;
/// Debug and feature flags for model checking behavior.
pub mod debug;
mod implicit_substitutions;
pub(crate) mod model_checker;
pub(crate) mod module_set_validation;

// Re-export temporal_scan utilities for use by checker_ops.rs (#2670).
pub(crate) use model_checker::liveness::temporal_scan::{expr_contains, ScanDecision};
// Multi-phase verification pipeline (Part of #3723)
pub(crate) mod pipeline;
// Concrete PhaseRunner implementations (Part of #3720, #3723)
pub(crate) mod pipeline_runners;
// Portfolio orchestrator for parallel BFS + PDR (Part of #3717)
pub mod portfolio;
// Fused cooperative BFS + PDR + BMC orchestrator (Part of #3769, Epic #3762)
// Module compiles with or without z4: non-z4 fallback runs BFS-only.
pub(crate) mod fused;
// Counterexample cross-validation for fused orchestrator (Part of #3836)
#[cfg(feature = "z4")]
pub(crate) mod cross_validation;
// Symbolic-to-JIT bridge: BMC counterexample states to JIT evaluation (Part of #3855)
#[cfg(feature = "z4")]
pub(crate) mod symbolic_to_jit_bridge;
// Per-action oracle routing for CDEMC engine selection (Part of #3785)
#[cfg(feature = "z4")]
pub(crate) mod oracle;
// Adaptive lane timeout budgets for fused orchestrator (Part of #3841)
// Scaffolded but not yet wired into the cooperative verification loop.
#[allow(dead_code)]
pub(crate) mod lane_budget;
// Symbolic wavefront compression for CDEMC Wave 3 (Part of #3787)
mod resolve;
#[cfg(feature = "z4")]
pub(crate) mod wavefront;
// Distributed BFS framework: fingerprint-partitioned state exploration (Pillar 6 PoC)
#[allow(dead_code)]
pub(crate) mod distributed;

#[cfg(test)]
mod tests;

pub(crate) use self::api::InitProgressCallback;
pub(crate) use self::api::{
    format_span_location, format_span_location_from_source, INLINE_NEXT_NAME,
};
pub use self::api::{
    ActionLabel, CheckResult, CheckStats, LimitType, PorReductionStats, Progress,
    ProgressCallback, PropertyViolationKind, ResolvedSpec, SymmetryReductionStats, Trace,
};
pub use self::check_error::CheckError;
pub use self::check_error::{
    ConfigCheckError, EvalCheckError, InfraCheckError, LivenessCheckError, RuntimeCheckError,
};

pub(crate) use self::api::check_error_to_result;
pub(crate) use self::api::TlcLiveCannotHandleFormulaMsg;
pub(crate) use self::model_checker::invariants::check_terminal_array;

pub(crate) use model_checker::build_ident_hints;
pub(crate) use model_checker::compute_symmetry_perms;
pub(crate) use model_checker::compute_uses_trace;
pub(crate) use model_checker::precompute_constant_operators;
pub(crate) use model_checker::promote_env_constants_to_precomputed;
pub use model_checker::simulation::{SimulationConfig, SimulationResult, SimulationStats};
// Random walk witness search (Part of #3720)
pub use model_checker::random_walk::{RandomWalkConfig, RandomWalkResult};
pub(crate) use model_checker::validate_config::validate_all_config_ops;
pub use model_checker::ModelChecker;
pub use resolve::{resolve_spec_from_config, resolve_spec_from_config_with_extends};

fn validation_result_from_issues(
    issues: impl IntoIterator<Item = crate::config::ConfigValidationIssue>,
    stats: &CheckStats,
) -> Option<CheckResult> {
    for issue in issues {
        if issue.is_error() {
            return Some(CheckResult::from_error(
                ConfigCheckError::Setup(issue.to_string()).into(),
                stats.clone(),
            ));
        }
        eprintln!("{issue}");
    }
    None
}

pub(crate) fn config_validation_result(config: &Config, stats: &CheckStats) -> Option<CheckResult> {
    validation_result_from_issues(config.validate(), stats)
}

pub(crate) fn runtime_config_validation_result(
    config: &Config,
    stats: &CheckStats,
) -> Option<CheckResult> {
    validation_result_from_issues(config.validate_runtime(), stats)
}

/// Simple model checking entry point
pub fn check_module(module: &Module, config: &Config) -> CheckResult {
    if let Some(result) = config_validation_result(config, &CheckStats::default()) {
        return result;
    }
    let mut checker = ModelChecker::new(module, config);
    checker.check()
}
