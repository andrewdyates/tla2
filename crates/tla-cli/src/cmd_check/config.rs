// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;

use crate::cli_schema::{
    LivenessModeArg, OutputFormat, SoundnessGate, StrategyArg, TraceFormat, TypeSpecializeArg,
};

/// Bundled configuration for a model-checking run, replacing 33 positional parameters.
pub(crate) struct CheckConfig {
    pub(crate) file: PathBuf,
    pub(crate) config_path: Option<PathBuf>,
    /// Compile TLA+ to native Rust, build, and run instead of interpreting.
    pub(crate) compiled: bool,
    /// Parse input as Quint JSON IR instead of TLA+ source. Part of #3754.
    pub(crate) quint: bool,
    /// Number of random walks before BFS (0 = disabled). Part of #3720.
    pub(crate) random_walks: usize,
    /// Maximum depth (steps) per random walk. Part of #3720.
    pub(crate) walk_depth: usize,
    pub(crate) workers: usize,
    pub(crate) no_deadlock: bool,
    pub(crate) max_states: usize,
    pub(crate) max_depth: usize,
    pub(crate) memory_limit: usize,
    pub(crate) disk_limit: usize,
    pub(crate) soundness_gate: SoundnessGate,
    pub(crate) require_exhaustive: bool,
    pub(crate) bmc_depth: usize,
    /// Use incremental BMC solving (reuse solver across depths). Part of #3724.
    pub(crate) bmc_incremental: bool,
    pub(crate) pdr_enabled: bool,
    pub(crate) kinduction_enabled: bool,
    pub(crate) kinduction_max_k: usize,
    /// Use incremental solving for k-induction inductive step. Part of #3722.
    pub(crate) kinduction_incremental: bool,
    pub(crate) por_enabled: bool,
    pub(crate) show_coverage: bool,
    /// Enable coverage-guided exploration (priority frontier for rare actions).
    pub(crate) coverage_guided: bool,
    /// Mix ratio for coverage-guided frontier (every N pops, one is priority-guided).
    pub(crate) coverage_mix_ratio: usize,
    /// Show state space size estimate in progress output.
    pub(crate) estimate: bool,
    /// Estimation-only mode: explore N levels then stop.
    pub(crate) estimate_only: Option<usize>,
    pub(crate) no_trace: bool,
    pub(crate) store_states: bool,
    pub(crate) initial_capacity: Option<usize>,
    pub(crate) mmap_fingerprints: Option<usize>,
    /// Enable huge page hints for mmap fingerprint storage. Part of #3856.
    pub(crate) huge_pages: bool,
    pub(crate) disk_fingerprints: Option<usize>,
    pub(crate) mmap_dir: Option<PathBuf>,
    pub(crate) trace_file_path: Option<PathBuf>,
    pub(crate) mmap_trace_locations: Option<usize>,
    /// Collision detection mode for fingerprint-based state storage.
    pub(crate) collision_check: String,
    pub(crate) checkpoint_dir: Option<PathBuf>,
    pub(crate) checkpoint_interval: u64,
    pub(crate) resume_from: Option<PathBuf>,
    pub(crate) output_format: OutputFormat,
    pub(crate) trace_format: TraceFormat,
    pub(crate) difftrace: bool,
    /// Annotate traces with human-readable diff-based explanations.
    pub(crate) explain_trace: bool,
    pub(crate) continue_on_error: bool,
    pub(crate) allow_incomplete: bool,
    pub(crate) force: bool,
    pub(crate) profile_enum: bool,
    pub(crate) profile_enum_detail: bool,
    pub(crate) profile_eval: bool,
    pub(crate) liveness_mode: LivenessModeArg,
    /// Strict liveness: panic on missing states. Part of #3746.
    #[allow(dead_code)]
    pub(crate) strict_liveness: bool,
    /// Enable JIT compilation of invariant and action operators at runtime.
    /// Wired via env var in main.rs before OnceLock init; field stored for documentation.
    /// Part of #4035: JIT opt-in to eliminate interpreter baseline regression.
    #[allow(dead_code)]
    pub(crate) jit: bool,
    /// Cross-check JIT invariant results against the interpreter.
    pub(crate) jit_verify: bool,
    /// Show per-action tier compilation summary at end of run. Part of #3932.
    pub(crate) show_tiers: bool,
    /// Speculative type specialization mode for JIT Tier 2.
    /// Part of #3989: JIT V2 Phase 6 speculative type specialization.
    pub(crate) type_specialize: TypeSpecializeArg,
    /// Disable TIR preprocessing pipeline (NNF, keramelization, constant folding).
    /// Wired via env var in main.rs before OnceLock init; field stored for documentation.
    #[allow(dead_code)]
    pub(crate) no_preprocess: bool,
    /// Enable partial evaluation of CONSTANT bindings into TIR operator bodies.
    /// Wired via env var in main.rs before OnceLock init; also read by cmd_check to
    /// attach a `ConstantEnv` to each `TirProgram`. Part of #4251 Stream 5.
    pub(crate) partial_eval: bool,
    /// Enable multi-phase verification pipeline. Part of #3723.
    pub(crate) pipeline: bool,
    /// Named verification strategy for pipeline mode. Part of #3723.
    pub(crate) strategy: Option<StrategyArg>,
    /// Enable cooperative fused BFS+symbolic verification. Part of #3770.
    pub(crate) fused: bool,
    /// Enable portfolio racing: BFS + symbolic strategies in parallel. Part of #3717.
    pub(crate) portfolio: bool,
    /// Explicit list of strategies for portfolio mode. Part of #3717.
    pub(crate) portfolio_strategies: Vec<String>,
    /// CLI override for Init operator. Part of #3759.
    pub(crate) cli_init: Option<String>,
    /// CLI override for Next operator. Part of #3759.
    pub(crate) cli_next: Option<String>,
    /// CLI override for invariants. Part of #3759.
    pub(crate) cli_invariants: Vec<String>,
    /// CLI override for temporal properties. Part of #3779.
    pub(crate) cli_properties: Vec<String>,
    /// CLI override for constant assignments (NAME=VALUE). Part of #3779.
    pub(crate) cli_constants: Vec<String>,
    /// Skip .cfg file entirely. Part of #3779.
    pub(crate) no_config: bool,
    /// Trace invariant operators (Apalache-style). Part of #3752.
    pub(crate) trace_invariants: Vec<String>,
    /// Inductive invariant operator to check (Apalache-style). Part of #3756.
    pub(crate) inductive_check_invariant: Option<String>,
    /// Enable symbolic simulation mode (Apalache-style). Part of #3757.
    pub(crate) symbolic_sim: bool,
    /// Number of simulation runs for symbolic simulation. Part of #3757.
    pub(crate) symbolic_sim_runs: usize,
    /// Maximum depth (steps) per simulation run. Part of #3757.
    pub(crate) symbolic_sim_length: usize,
    /// Allow IOExec and related operators to execute shell commands.
    /// Part of #3965: Security gate for IOExec command execution.
    pub(crate) allow_io: bool,
    /// Incremental model checking cache directory.
    #[allow(dead_code)] // Scaffolding for incremental checking pipeline
    pub(crate) incremental: Option<PathBuf>,
    /// Enable distributed multi-machine model checking. Part of Pillar 6 Phase 2.
    #[allow(dead_code)] // Scaffolding for distributed checking
    pub(crate) distributed: bool,
    /// Node addresses for distributed checking (host:port list).
    #[allow(dead_code)] // Scaffolding for distributed checking
    pub(crate) distributed_nodes: Vec<String>,
    /// This node's ID in the distributed cluster (0-indexed).
    #[allow(dead_code)] // Scaffolding for distributed checking
    pub(crate) distributed_node_id: u32,
}
