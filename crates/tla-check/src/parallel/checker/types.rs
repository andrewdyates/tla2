// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Internal data types for parallel checker orchestration.

use super::*;

/// Initial-state representation: either streaming bulk storage or a materialized Vec.
pub(super) enum InitialStates {
    Bulk(BulkStateStorage),
    Vec(Vec<State>),
}

/// Result of `prepare_check()`: validated config, built EvalCtx, compiled
/// invariants, actions, and initial states ready for seeding.
pub(super) struct CheckPreparation {
    pub(super) resolved_next_name: String,
    pub(super) parallel_tir_next_selection: Option<crate::tir_mode::ParallelNextTirEvalSelection>,
    pub(super) detected_actions: Vec<String>,
    pub(super) detected_action_ids: Vec<String>,
    pub(super) por_actions: Arc<Vec<crate::coverage::DetectedAction>>,
    pub(super) por_independence: Option<Arc<crate::por::IndependenceMatrix>>,
    pub(super) por_visibility: Arc<crate::por::VisibilitySet>,
    pub(super) ctx: EvalCtx,
    pub(super) cached_view_name: Option<String>,
    /// Part of #2983: Eval-based implied actions for ModuleRef/INSTANCE properties.
    pub(super) eval_implied_actions: Arc<Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>>,
    /// Part of #3113: Eval-based state invariants for ENABLED-containing state-level terms.
    pub(super) eval_state_invariants: Arc<Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>>,
    pub(super) var_registry: Arc<VarRegistry>,
    pub(super) expanded_op_defs: FxHashMap<String, OperatorDef>,
    /// Wrapped in `Option` so `seed_and_spawn_workers` can `.take()` it
    /// without requiring a `Default` impl on `InitialStates`.
    pub(super) initial_states: Option<InitialStates>,
    /// Part of #3053: Init predicates from PROPERTY classification.
    /// Non-Always state/constant-level terms (e.g., `M!Init` in `M!Init /\ [][M!Next]_M!vars`)
    /// that must be checked against every initial state during seeding.
    /// Mirrors sequential checker's `compiled.property_init_predicates`.
    pub(super) property_init_predicates: Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>,
    /// Property names whose state-level terms are checked during BFS.
    ///
    /// This is broader than `promoted_property_invariants`: mixed properties
    /// still need PROPERTY attribution if their state-level safety terms fail
    /// during exploration.
    pub(super) state_property_violation_names: Vec<String>,
    /// Part of #2740: Properties fully promoted to BFS-phase checking.
    /// These are skipped during post-BFS liveness to avoid redundant verification.
    /// Parity with sequential checker's promoted_property_invariants +
    /// promoted_implied_action_properties.
    pub(super) promoted_properties: Vec<String>,
    /// Properties whose full state-level content was extracted into BFS.
    ///
    /// This remains the post-BFS liveness skip list; it is not used for
    /// violation attribution.
    pub(super) promoted_property_invariants: Vec<String>,
    /// Part of #3011: Symmetry permutations for canonical fingerprinting in workers.
    pub(super) mvperms: Arc<Vec<crate::value::MVPerm>>,
    /// Part of #3621: Compiled bytecode for invariant fast path, shared across workers.
    pub(super) bytecode: Option<Arc<tla_eval::bytecode_vm::CompiledBytecode>>,
    /// Part of #3960: Compiled bytecode for next-state action operators (JIT next-state fast path).
    /// Separate from invariant bytecode because actions use StoreVar opcodes for primed variables.
    /// Mirrors sequential checker's `action_bytecode` field in mc_struct.rs.
    pub(super) action_bytecode: Option<Arc<tla_eval::bytecode_vm::CompiledBytecode>>,
    /// Part of #3700: Shared JIT-compiled invariant functions for worker hot paths.
    pub(super) jit_cache: Option<crate::parallel::SharedJitInvariantCache>,
    /// Pre-computed ACTION_CONSTRAINT variable dependency analysis.
    pub(super) action_constraint_analysis:
        Option<Arc<crate::checker_ops::ActionConstraintAnalysis>>,
}

/// Runtime state produced by seeding/spawning, consumed by `finalize_check()`.
pub(super) struct CheckRuntime {
    pub(super) result_rx: Receiver<WorkerResult>,
    pub(super) handles: Vec<thread::JoinHandle<()>>,
    pub(super) num_initial: usize,
    pub(super) start_time: Instant,
    /// Part of #3935: number of JIT-compiled invariants (for summary gating).
    #[allow(dead_code)]
    pub(super) jit_compiled_invariants: usize,
}

/// Render a panic payload into a human-readable message.
pub(super) fn panic_payload_message(payload: &(dyn std::any::Any + Send + 'static)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "non-string panic payload".to_string()
    }
}
