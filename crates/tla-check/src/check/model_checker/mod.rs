// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Shared imports for items used by 3+ submodules (available via `use super::{...}`).
// Single-consumer items use direct `crate::` imports in their consumer file.
pub(super) use crate::arena::{BulkStateHandle, BulkStateStorage};
#[cfg(feature = "z4")]
pub(super) use crate::config::InitMode;
pub(super) use crate::config::{Config, TerminalSpec};
pub(super) use crate::constants::bind_constants_from_config;
pub(super) use crate::coverage::DetectedAction;
pub(super) use crate::enumerate::{
    enumerate_states_from_constraint_branches, enumerate_successors, extract_conjunction_remainder,
    extract_init_constraints, find_unconstrained_vars, print_enum_profile_stats,
};
#[cfg(debug_assertions)]
pub(super) use crate::eval::Env;
pub(super) use crate::eval::{print_eval_profile_stats, EvalCtx};
pub(super) use crate::liveness::{AstToLive, LiveExpr, LivenessChecker};
pub(super) use crate::spec_formula::FairnessConstraint;
pub(super) use crate::state::{
    compute_diff_fingerprint_with_xor, fp_hashmap, fp_hashmap_with_capacity, states_to_trace_value,
    ArrayState, DiffSuccessor, Fingerprint, FpHashMap, State,
};
pub(super) use crate::storage::{
    CapacityStatus, FingerprintSet, InsertOutcome, LookupOutcome, StorageFault,
    TraceLocationStorage, TraceLocationsStorage,
};
pub(super) use crate::trace_file::TraceFile;
pub(super) use crate::Value;
pub(super) use rustc_hash::FxHashMap;
pub(super) use std::collections::VecDeque;
pub(super) use std::path::PathBuf;
#[cfg(debug_assertions)]
pub(super) use std::sync::atomic::Ordering as AtomicOrdering;
pub(super) use std::sync::Arc;
pub(super) use std::time::{Duration, Instant};
pub(super) use tla_core::ast::{Expr, Module, ModuleTarget, OperatorDef};
pub(super) use tla_core::Spanned;

// Imports from check/mod.rs (parent module)
pub(super) use super::api::{
    check_error_to_result, format_span_location, format_span_location_from_source, LimitType,
    PropertySafetyParts, SafetyTemporalPropertyOutcome, SuccessorResult,
};
// Re-export debug functions as a named module so submodules can
// `use super::debug::*` for debug functions without a full glob.
#[cfg(debug_assertions)]
pub(super) use super::debug::*;
pub(super) mod debug {
    pub(in crate::check) use super::super::debug::*;
}
pub(super) use super::module_set_validation;
pub(super) use super::{
    CheckError, CheckResult, CheckStats, InitProgressCallback, ProgressCallback,
    SuccessorWitnessMap, Trace,
};

pub(super) mod simulation;
mod simulation_actions;
mod simulation_rng;
mod simulation_setup;
#[cfg(test)]
mod simulation_tir_tests;
mod simulation_types;
mod simulation_walk;

// Random walk witness search (Part of #3720)
pub(crate) mod random_walk;

// ModelChecker implementation split across submodules.
// Each module contains `impl ModelChecker` blocks and uses `pub(super)` for
// cross-module method access. This replaces the former `include!()` pattern.

// JIT V2 flat state BFS arena — scaffolding not yet wired into production (#3986)
#[allow(dead_code)]
pub(crate) mod arena;
pub(crate) mod bfs;
mod drop;
mod fingerprint;
mod frontier;
pub(crate) mod invariants;
pub(crate) mod liveness;
mod mc_struct;
pub(crate) mod precompute;
mod run;
mod run_bfs_full;
mod run_bfs_notrace;
mod run_checks;
mod run_debug;
mod run_finalize;
mod run_gen;
mod run_helpers;
mod run_monitoring;
mod run_prepare;
mod run_resume;
pub(crate) mod setup;
pub(crate) mod symmetry_detect;
pub(crate) mod symmetry_perms;
mod tir_parity;
mod trace;
mod trace_actions;
mod trace_detect;
pub(crate) mod trace_invariant;
pub(crate) mod validate_config;

// Re-export all pub(super) items so sibling submodules can access them via `use super::*`.
pub(super) use self::invariants::BulkInitStates;
use self::liveness::{InlineLivenessPropertyPlan, LivenessMode};
pub(super) use self::mc_struct::*;
// Part of #2740: FairnessToLiveExprError moved to checker_ops.rs for shared use.
// Re-exported through trace.rs so existing `use super::FairnessToLiveExprError` works.
use self::trace::FairnessToLiveExprError;

// Public API re-exports
pub use self::mc_struct::ModelChecker;
pub(crate) use self::precompute::build_ident_hints;
pub(crate) use self::precompute::precompute_constant_operators;
pub(crate) use self::precompute::promote_env_constants_to_precomputed;
pub(crate) use self::symmetry_perms::compute_symmetry_perms;
pub(crate) use self::trace_detect::compute_uses_trace;

// Part of #2356 Step 3: re-export CoreStepAdapter infrastructure for parallel worker.
pub(crate) use self::bfs::core_step::{
    run_core_step, CoreStepAction, CoreStepAdapter, CoreStepInput,
};
