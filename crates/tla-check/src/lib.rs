// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! tla-check - TLA+ Model Checker
//!
//! This crate provides:
//! - **Value types**: Re-exported from `tla-value` crate (`value/`)
//! - **Expression evaluator**: Re-exported from `tla-eval` crate (`eval/`)
//! - **State exploration**: BFS state space exploration with parallel workers (`parallel/`)
//! - **Safety checking**: Invariant verification, action constraints, state constraints
//! - **Liveness checking**: Tableau construction, SCC detection, WF/SF fairness (`liveness/`)
//! - **Trace validation**: Verify system traces against specs
//! - **Configuration parsing**: Parse TLC .cfg files (`config/`)
//! - **Checkpoint/resume**: Save and restore model checking state
//! - **Mmap storage**: Memory-mapped state storage for large state spaces (`storage/`)
//! - **POR prototype**: Static dependency and visibility analysis scaffolding (`por/`);
//!   transition reduction is currently disabled pending a sound cycle proviso
//!
//! # Quick Start
//!
//! ```rust
//! use tla_check::{eval, EvalCtx, Value};
//! use tla_core::{lower, parse_to_syntax_tree, FileId};
//!
//! // Parse and evaluate a TLA+ expression
//! let src = "---- MODULE Test ----\nOp == 1 + 2 * 3\n====";
//! let tree = parse_to_syntax_tree(src);
//! let result = lower(FileId(0), &tree);
//! let module = result.module.unwrap();
//!
//! // Find the operator and evaluate it
//! let mut ctx = EvalCtx::new();
//! ctx.load_module(&module);
//!
//! // The result of 1 + 2 * 3 is 7
//! ```
//!
//! # Model Checking
//!
//! ```rust,no_run
//! use tla_check::{check_module, CheckResult, Config};
//! use tla_core::{lower, parse_to_syntax_tree, FileId};
//!
//! // A tiny, finite spec (2 reachable states)
//! let src = "---- MODULE Counter ----\n\
//! VARIABLE x\n\
//! Init == x = 0\n\
//! Next == x' = x + 1 /\\ x < 1\n\
//! ====";
//! let tree = parse_to_syntax_tree(src);
//! let lowered = lower(FileId(0), &tree);
//! let module = lowered.module.unwrap();
//!
//! let config = Config::parse("INIT Init\nNEXT Next\n").unwrap();
//! let result = check_module(&module, &config);
//! match result {
//!     CheckResult::Success(stats) => println!("OK: {} states", stats.states_found),
//!     CheckResult::InvariantViolation { invariant, trace, .. } => {
//!         println!("Violated: {}\n{}", invariant, trace);
//!     }
//!     other => println!("Result: {:?}", other),
//! }
//! ```

#![allow(clippy::result_large_err)]

// debug_flag! macro must be defined before modules that use it
#[macro_use]
pub(crate) mod debug_env;

pub(crate) mod action_instance;
pub(crate) mod adaptive;
pub(crate) mod arena;
mod cfg_overrides;
pub(crate) mod check;
pub(crate) mod checker_ops;
pub(crate) mod checker_setup;
pub(crate) mod checkpoint;
pub mod collision_detection;
pub(crate) mod complexity_visitor;
pub(crate) mod config;
pub(crate) mod constants;
pub(crate) mod coverage;
mod disabled_action_stats;
pub(crate) mod enabled;
pub(crate) mod enumerate;
pub(crate) mod error;
pub(crate) mod error_policy;
/// Compatibility shim — prefer crate-root exports or direct `tla_eval` imports (#3039).
#[doc(hidden)]
pub mod eval;
pub(crate) mod expr_visitor;
pub(crate) mod fingerprint;
mod guard_error_stats;
pub(crate) mod init_strategy;
pub(crate) mod intern;
pub mod itf;
pub(crate) mod json_codec;
pub(crate) mod json_output;
mod json_path;
pub(crate) mod liveness;
pub(crate) mod materialize;
pub(crate) mod memory;
pub(crate) mod parallel;
pub(crate) mod periodic_liveness;
// Distributed model checking — state partitioning prototype (Part of #3796)
#[allow(dead_code)]
pub(crate) mod distributed;
pub mod resource_budget;
#[cfg(test)]
mod resource_budget_tests;
pub(crate) mod spec_formula;
pub mod state;
pub(crate) mod storage;
pub(crate) mod tir_mode;
pub(crate) mod trace_action_label_mapping;
pub(crate) mod trace_action_label_rewrite;
pub mod trace_explain;
pub(crate) mod trace_file;
pub(crate) mod trace_input;
pub(crate) mod trace_validate;
/// Compatibility shim — prefer crate-root exports or direct `tla_value` imports (#3039).
#[doc(hidden)]
pub mod value;
pub(crate) mod var_index;
// State space estimation from BFS level statistics
pub mod state_space_estimator;
// Spec minimizer: delta debugging for TLA+ specs
pub mod minimize;
// Incremental model checking: reuse prior results when spec changes
pub mod incremental_check;
// Deadlock analysis engine
pub mod deadlock_analysis;
// Portfolio racing verdict for parallel BFS + z4 PDR/BMC (Part of #3717)
pub mod shared_verdict;
// Partial Order Reduction (Part of #541)
pub(crate) mod por;
// z4-based Init enumeration (Part of #251)
#[cfg(feature = "z4")]
pub(crate) mod z4_enumerate;
// z4-based nested powerset Init enumeration (Part of #3826)
#[cfg(feature = "z4")]
pub(crate) mod z4_init_powerset;
// Shared sort inference for z4-based symbolic checking
#[cfg(feature = "z4")]
pub(crate) mod z4_shared;
// z4-based PDR symbolic safety checking (Part of #642)
#[cfg(feature = "z4")]
pub(crate) mod z4_pdr;
// z4-based bounded model checking (Part of #3702)
#[cfg(feature = "z4")]
pub(crate) mod z4_bmc;
// Incremental SMT solver for BMC depth ladder (Part of #3724)
#[cfg(feature = "z4")]
pub(crate) mod incremental_solver;
// z4-based k-induction for proving safety properties (Part of #3722)
#[cfg(feature = "z4")]
pub(crate) mod z4_kinduction;
// z4-based inductive invariant convenience checker (Apalache Gap 8, Part of #3756)
#[cfg(feature = "z4")]
pub(crate) mod z4_inductive_check;
// VMT (Verification Modulo Theories) export for external model checkers (Part of #3755)
#[cfg(feature = "z4")]
#[allow(dead_code)]
pub(crate) mod vmt_export;
// Cooperative Dual-Engine Model Checking shared state (Part of #3762)
// Extracted sub-modules for cooperative_state (Part of #3872)
#[cfg(feature = "z4")]
pub(crate) mod action_metrics;
#[cfg(feature = "z4")]
pub(crate) mod convergence;
#[cfg(feature = "z4")]
pub(crate) mod cooperative_state;
#[cfg(feature = "z4")]
pub(crate) mod per_invariant;
#[cfg(feature = "z4")]
pub(crate) mod smt_compat;
// z4-based symbolic simulation (Apalache Gap 9, Part of #3757)
#[cfg(feature = "z4")]
pub(crate) mod z4_symbolic_sim;

// Interactive JSON-RPC server for step-by-step state exploration (Apalache Gap 3, Part of #3751)
pub mod interactive;
// Symbolic exploration engine for interactive SMT-based exploration (Apalache Gap 3, Part of #3751)
#[cfg(feature = "z4")]
pub(crate) mod symbolic_explore;

// On-the-fly LTL checking via Buchi automaton product construction (Part of #3781)
#[allow(dead_code)]
pub(crate) mod on_the_fly_ltl;

// Kani formal verification harnesses (only compiled with cargo kani)
#[cfg(kani)]
mod kani_harnesses;

// Regular tests that mirror Kani proofs (excluded during kani runs to avoid duplicate)
#[cfg(all(test, not(kani)))]
mod kani_harnesses;

// Re-exports
pub use adaptive::{check_module_adaptive, AdaptiveChecker, PilotAnalysis, Strategy};
pub use check::{
    check_module, resolve_spec_from_config, resolve_spec_from_config_with_extends, ActionLabel,
    CheckError, CheckResult, CheckStats, ConfigCheckError, EvalCheckError, InfraCheckError,
    LimitType, LivenessCheckError, ModelChecker, PorReductionStats, Progress, ProgressCallback,
    PropertyViolationKind, RandomWalkConfig, RandomWalkResult, ResolvedSpec, RuntimeCheckError,
    SimulationConfig, SimulationResult, SimulationStats, SuccessorWitnessMap,
    SymmetryReductionStats, Trace,
};
// Multi-phase verification pipeline (Part of #3723)
pub use check::pipeline::{
    PhaseConfig, PhaseRecord, PhaseRunner, PipelineResult, PropertyVerdict, VerificationPhase,
    VerificationPipeline, VerificationStrategy,
};
// Concrete pipeline runners (Part of #3720, #3723)
pub use check::pipeline_runners::{BfsRunner, RandomWalkRunner};
#[cfg(feature = "z4")]
pub use check::pipeline_runners::{BmcRunner, KInductionRunner, PdrRunner};
// Portfolio orchestrator for parallel BFS + PDR (Part of #3717)
pub use check::portfolio::{run_portfolio, PortfolioResult, PortfolioWinner};
pub use config::{
    Config, ConfigError, ConstantValue, InitMode, LivenessExecutionMode, TerminalSpec,
};
pub use constants::{bind_constants_from_config, parse_constant_value};
pub use error::{EvalError, EvalResult};
pub use eval::{aggregate_bytecode_vm_stats, bytecode_vm_stats};
pub use eval::{eval, Env, EvalCtx, OpEnv};
#[cfg(any(test, feature = "testing"))]
pub use liveness::debug::{
    set_liveness_disk_bitmask_flush_threshold_override, set_liveness_inmemory_node_limit_override,
    set_liveness_inmemory_successor_limit_override, set_use_disk_bitmasks_override,
    set_use_disk_graph_override, set_use_disk_successors_override,
    LivenessDiskBitmaskFlushThresholdGuard, LivenessInMemoryNodeLimitGuard,
    LivenessInMemorySuccessorLimitGuard, UseDiskBitmasksGuard, UseDiskGraphGuard,
    UseDiskSuccessorsGuard,
};
pub use parallel::{check_module_parallel, ParallelChecker};
#[cfg(any(test, feature = "testing"))]
pub use parallel::{set_use_handle_state_override, UseHandleStateGuard};
pub use resource_budget::{ResourceBudget, StateSpaceEstimate};
pub use spec_formula::{extract_spec_formula, FairnessConstraint, SpecFormula};
pub use state::{
    value_fingerprint, ArrayState, BuildFingerprintHasher, Fingerprint, FingerprintHasher,
    FpHashMap, FpHashSet, State, fp_hashmap, fp_hashmap_with_capacity, fp_hashset,
    fp_hashset_with_capacity,
};
pub use value::{FuncSetValue, FuncValue, IntervalValue, SubsetValue, Value};
// Explicit root export for memory_stats so CLI callers don't need the shim (#3039).
#[cfg(feature = "memory-stats")]
pub use value::memory_stats;

// Liveness checking — integration tests use AstToLive + ConvertError
pub use liveness::{AstToLive, ConvertError};

// Checker operations (safety/temporal property classification)
pub use checker_ops::any_property_requires_liveness_checker;

// Coverage statistics
pub use coverage::{detect_actions, ActionStats, CoverageStats, DetectedAction, DetectedActionId};

// TLC-style action instances (trace validation / diagnostics)
pub use action_instance::{
    enumerate_successors_by_action_instance, split_action_instances, ActionInstance,
    ActionInstanceSuccessors,
};

// Init enumeration strategy selection (Part of #251)
pub use init_strategy::{analyze_init_predicate, InitAnalysis, InitStrategy, Z4Reason};

// Collision detection for fingerprint-based state storage
pub use collision_detection::{CollisionCheckMode, CollisionDetail, CollisionStats};

// Trace explanation engine
pub use trace_explain::{ExplainedStep, ExplainedTrace, TraceStateDiff, VarChange};

// Scalable storage
pub use storage::factory::{FingerprintSetFactory, StorageConfig, StorageMode};
pub use storage::{
    CapacityStatus, FingerprintSet, FingerprintStorage, InsertOutcome, LookupOutcome, StorageFault,
    StorageStats, TraceLocationStorage, TraceLocationsStorage,
};

// Disk-based trace storage
pub use trace_file::{TraceFile, TraceLocations};

// Trace validation mapping config (action labels)
pub use trace_action_label_mapping::{
    validate_action_label, ActionLabelInstanceError, ActionLabelMapping, ActionLabelMappingConfig,
    ActionLabelValidationError, ActionLabelValidationResult, ActionParamEncoding, OperatorRef,
    TraceActionLabelMappingError,
};
pub use trace_action_label_rewrite::{
    outer_exists_binder_sites, resolve_param_binders_for_rewrite, ActionLabelParamBindError,
    ActionLabelParamBindErrorKind, BoundVarSite,
};

// Trace validation input parsing
pub use trace_input::{
    read_trace_events, read_trace_json, read_trace_jsonl, resolve_trace_input_format,
    TraceActionLabel, TraceEventSink, TraceHeader, TraceInputFormat, TraceInputFormatSelection,
    TraceParseError, TraceSourceHint, TraceStep,
};

// Variable indexing
pub use var_index::{VarIndex, VarRegistry};

// Global state reset and memory/disk policy helpers (Part of #3608)
mod reset;
pub use reset::{
    disk_limit_system_default, log_memory_budget, memory_policy_system_default,
    memory_policy_system_default_info, reset_global_state,
};

// Checkpoint/resume support
pub use checkpoint::{
    Checkpoint, CheckpointMetadata, CheckpointStats, SerializableState, SerializableValue,
};

// JSON output format for AI agents
pub use json_codec::{
    json_to_value, json_to_value_with_path, params_from_json, JsonValueDecodeError,
    JsonValueDecodeErrorAtPath, ParamsDecodeError,
};
pub use json_output::error_codes;
pub use json_output::{
    liveness_trace_to_dot, trace_to_dot, value_to_json, ActionInfo, ActionRef, CounterexampleInfo,
    DiagnosticMessage, DiagnosticsInfo, ErrorSuggestion, InputInfo, JsonOutput, JsonValue,
    JsonlEvent, PrintOutput, ResultInfo, SearchCompleteness, SoundnessMode, SoundnessProvenance,
    SourceLocation, SpecInfo, StateDiff, StateInfo, StatisticsInfo, StorageStatsInfo, ValueChange,
    ViolatedProperty, OUTPUT_VERSION,
};

// ITF (Informal Trace Format) trace serialization (Part of #3781, #3753)
pub use itf::{liveness_trace_to_itf, trace_to_itf};

// Trace validation engine (spec-based validation)
pub use trace_validate::{
    ActionLabelMode, ActionMatchResult, StepDiagnostic, TraceValidationBuilder,
    TraceValidationEngine, TraceValidationError, TraceValidationResult, TraceValidationSuccess,
    TraceValidationWarning,
};

// PDR-based symbolic safety checking (Part of #642)
#[cfg(feature = "z4")]
pub use z4_pdr::{
    check_pdr, check_pdr_cooperative, check_pdr_with_config, check_pdr_with_portfolio,
    expand_operators_for_chc, PdrError, PdrResult,
};
// BMC-based symbolic bug finding (Part of #3702)
#[cfg(feature = "z4")]
pub use tla_z4::{BmcState, BmcValue};
#[cfg(feature = "z4")]
pub use z4_bmc::{
    check_bmc, check_bmc_cooperative, check_bmc_with_portfolio, BmcConfig, BmcError, BmcResult,
};
// k-Induction-based symbolic safety proving (Part of #3722)
#[cfg(feature = "z4")]
pub use z4_kinduction::{
    check_kinduction, check_kinduction_with_portfolio, KInductionConfig, KInductionError,
    KInductionResult,
};
// Inductive invariant convenience checker (Apalache Gap 8, Part of #3756)
#[cfg(feature = "z4")]
pub use z4_inductive_check::{
    check_inductive, InductiveCheckConfig, InductiveCheckError, InductiveCheckResult,
    InductivePhase,
};
// Fused cooperative BFS + symbolic orchestrator (Part of #3769, Epic #3762)
// Available with or without z4: non-z4 path runs BFS-only.
pub use check::fused::{run_fused_check, FusedResult, FusedWinner, SymbolicDegradation};
// Static complexity analysis for exponential state space detection (Part of #3826)
#[cfg(feature = "z4")]
pub use check::oracle::{detect_exponential_complexity, ExponentialComplexity};
// Counterexample cross-validation for fused orchestrator (Part of #3836)
#[cfg(feature = "z4")]
pub use check::cross_validation::{CrossValidationResult, CrossValidationSource};
// VMT export for external model checkers (Apalache Gap 7, Part of #3755)
#[cfg(feature = "z4")]
pub use vmt_export::{export_vmt, VmtError, VmtOutput};
// Symbolic simulation (Apalache Gap 9, Part of #3757)
#[cfg(feature = "z4")]
pub use z4_symbolic_sim::{
    symbolic_simulate, SymbolicSimConfig, SymbolicSimError, SymbolicSimResult, SymbolicSimRunner,
};
// Interactive JSON-RPC server (Apalache Gap 3, Part of #3751)
pub use interactive::{
    InteractiveServer, InteractiveServerError, ServerExploreMode, StateSnapshot,
    DEFAULT_MAX_SYMBOLIC_DEPTH, DEFAULT_PORT,
};

// State space estimation from BFS level statistics
pub use state_space_estimator::{GrowthModel, StateSpaceEstimateResult, StateSpaceEstimator};

// Spec minimizer
pub use minimize::{MinimizeConfig, MinimizeResult, MinimizeStats, Minimizer, ResultClass};

// Incremental model checking (reuse prior results when spec changes)
pub use incremental_check::{
    compute_action_hashes, identify_dirty_states, save_incremental_cache, try_load_incremental,
    ActionProvenance, IncrementalCache, IncrementalCacheMetadata, SpecDiff, SuccessorMap,
};

// Deadlock analysis engine
pub use deadlock_analysis::{analyze_deadlock, ActionDiagnostic, ConjunctResult, DeadlockAnalysis};

/// Shared parse/lower helpers for unit tests within tla-check.
/// Part of #2816: canonical helpers replacing 20+ per-file duplicates.
#[cfg(test)]
pub(crate) mod test_support;

/// Test-only utilities shared across all test modules in tla-check.
/// Part of #3300: Provides the interner serialization lock.
#[cfg(test)]
pub(crate) mod test_utils {
    /// Process-global lock to serialize tests that exercise the parallel checker pipeline.
    /// Required because freeze/unfreeze of the value interner uses process-global state
    /// (PARALLEL_INTERN_ACTIVE, FROZEN_SNAPSHOT) that cannot be isolated between concurrent
    /// test threads. Without this, concurrent `check()` calls cause FROZEN_SNAPSHOT mutex
    /// poisoning when one test's unfreeze races with another's freeze/install cycle.
    pub static PARALLEL_CHECK_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    /// Acquire the interner serialization lock. Returns a MutexGuard that releases on drop.
    /// Uses `unwrap_or_else(into_inner)` to recover from a poisoned mutex.
    pub fn acquire_interner_lock() -> std::sync::MutexGuard<'static, ()> {
        PARALLEL_CHECK_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner())
    }
}
