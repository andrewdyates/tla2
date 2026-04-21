// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression evaluator for TLA+.
//!
//! This crate is the evaluation engine used by `tla-check` during model checking.
//! It takes lowered AST expressions (from `tla-core`) and evaluates them against
//! concrete states using the value model (from `tla-value`).
//!
//! Extracted from `tla-check` as part of #1269 to separate evaluation logic from
//! model-checking orchestration.
//!
//! # Module organization
//!
//! - **Builtins** (`builtin_*`) — Modules implementing TLA+ standard library
//!   operators: Sequences, FiniteSets, Bags, Functions, Integers, Reals, TLC
//!   extensions, and community modules (SequencesExt, FunctionsExt, etc.).
//! - **Dispatch** (`eval_dispatch`) — Central `eval()` entry point that routes
//!   expression kinds to the appropriate evaluator.
//! - **Context** (`core`, `eval_ctx_*`) — [`EvalCtx`] and its facets: state/env
//!   management (`eval_ctx_state`), operator environment (`eval_ctx_ops`),
//!   scope/binding management (`eval_ctx_scope`, `eval_ctx_bind`, `eval_ctx_locals`),
//!   and guard tracking (`eval_ctx_guards`).
//! - **Cache** (`cache`) — Evaluation result caching: zero-arg operator cache,
//!   quantifier hoisting, dependency tracking, and lifecycle management for
//!   state/phase/run boundaries.
//! - **Helpers** (`helpers`, `eval_state_var_lookup`, `eval_bool_logic`,
//!   `eval_constructors`, `eval_control_eq`) — Set iteration, substitution,
//!   prime detection, lazy domain materialization, and equality comparisons.
//! - **Specialized evaluators** — Arithmetic (`eval_arith`), set operations
//!   (`eval_sets`), identifiers (`eval_ident`, `eval_ident_zero_arg`),
//!   primed variables (`eval_prime`), LET/IN (`eval_let`), membership
//!   (`eval_membership`), and state variables (`eval_statevar`).
//! - **TIR interpreter** (`tir`) — Dispatch engine for the Typed Intermediate
//!   Representation: `TirProgram` lazy-lowering with persistent caching,
//!   expression dispatch (`dispatch`, `dispatch_bindings`, `dispatch_functions`,
//!   `dispatch_structured`, `dispatch_values`), and parity probe infrastructure
//!   (`probe`). Sole evaluation path since the legacy AST evaluator was removed (#3354).
//!
//! # Key public types
//!
//! - [`EvalCtx`] — The evaluation context holding state, operator environment,
//!   TLC config, and runtime statistics.
//! - [`eval`] — Top-level expression evaluation entry point.
//! - [`BindingChain`] — Tracks variable bindings across nested quantifiers.
//! - Cache lifecycle functions ([`clear_for_state_boundary`], etc.) — Called by
//!   the model checker at appropriate points to manage cached results.

#[macro_use]
pub(crate) mod debug_env;

/// Compatibility re-exports so extracted eval modules can compile without
/// checker-internal dependencies. Internal to this crate; external consumers
/// should import from tla_value or tla_core directly. (Part of #1582)
pub(crate) mod error {
    pub use tla_value::error::{EvalError, EvalResult};
}

/// Persistent collection types used by eval internals.
pub(crate) mod kani_types {
    pub use tla_core::kani_types::*;
}

/// Runtime value model used during expression evaluation.
pub(crate) mod value {
    pub use tla_value::*;

    #[cfg(feature = "memory-stats")]
    pub use tla_value::value::memory_stats;
}

/// Variable indexing utilities for fast state-var lookup.
pub(crate) mod var_index {
    pub use tla_core::{VarIndex, VarRegistry};
}

use crate::error::{EvalError, EvalResult};
use crate::kani_types::HashMap;
use crate::value::{
    FuncValue, IntervalValue, KSubsetValue, LazyDomain, RecordBuilder, SeqSetValue, SetBuilder,
    SetCapValue, SetDiffValue, SetPredValue, SortedSet, UnionValue, Value,
};
use tla_core::ast::{Expr, Module, OperatorDef};
use tla_core::{Span, Spanned};

pub(crate) mod binding_chain;
mod builtin_apalache;
mod builtin_bags;
mod builtin_bagsext;
mod builtin_finite_sets;
mod builtin_fold;
mod builtin_functions;
mod builtin_functions_ext;
mod builtin_graphs;
mod builtin_relation;
pub mod bytecode_vm;
pub mod eval_arena;

mod builtin_io;
mod builtin_misc;
mod builtin_sequences;
mod builtin_sequences_ext;
mod builtin_sequences_ext_ops;
mod builtin_stdlib_ext;
mod builtin_svg;
mod builtin_tlc;
mod builtin_tlc_get;
mod builtin_tlcext;
mod builtin_variants;
mod builtin_vector_clocks;
mod cache;
mod convert;
mod core;
mod eval_arith;
mod eval_bool_logic;
pub(crate) mod eval_cache_lifecycle;
mod eval_constructors;
mod eval_control_eq;
mod eval_ctx_bind;
mod eval_ctx_guards;
mod eval_ctx_locals;
mod eval_ctx_ops;
mod eval_ctx_scope;
mod eval_ctx_state;
mod eval_debug;
mod eval_dispatch;
mod eval_ident;
mod eval_ident_zero_arg;
mod eval_let;
mod eval_membership;
mod eval_module_load;
mod eval_prime;
mod eval_sets;
pub(crate) mod eval_state_var_lookup;
mod eval_statevar;
mod eval_unchanged;
mod helpers;
pub(crate) mod hooks;
mod implicit_instance_substitutions;
mod int_arith;
mod let_def_chain;
mod state_env_ref;
pub mod state_var;
pub mod tir;
mod tlc_types;

// Internal imports: make items from submodules available to sibling submodules
// via `use super::{...}` without widening visibility beyond this module tree.
use self::builtin_apalache::*;
use self::builtin_bags::*;
use self::builtin_bagsext::*;
use self::builtin_finite_sets::*;
use self::builtin_fold::*;
use self::builtin_functions::*;
use self::builtin_functions_ext::*;
use self::builtin_graphs::*;
use self::builtin_io::*;
use self::builtin_misc::*;
use self::builtin_relation::*;
use self::builtin_sequences::*;
use self::builtin_sequences_ext::*;
use self::builtin_sequences_ext_ops::*;
use self::builtin_stdlib_ext::*;
use self::builtin_svg::*;
use self::builtin_tlc::*;
use self::builtin_tlcext::*;
use self::builtin_variants::*;
use self::builtin_vector_clocks::*;
use self::cache::*;
use self::convert::*;
use self::eval_arith::*;
use self::eval_bool_logic::*;
use self::eval_cache_lifecycle::*;
use self::eval_constructors::*;
use self::eval_control_eq::*;
use self::eval_debug::*;
use self::eval_ident::*;
use self::eval_ident_zero_arg::*;
use self::eval_let::*;
use self::eval_membership::*;
use self::eval_prime::*;
use self::eval_sets::*;
use self::eval_state_var_lookup::*;
use self::eval_statevar::*;
use self::eval_unchanged::*;
use self::helpers::*;

// Public API re-exports
pub use self::binding_chain::{BindingChain, BindingValue};
pub use self::cache::try_eval_const_level;
pub use self::cache::{
    clear_diagnostic_counters, clear_for_eval_scope_boundary, clear_for_inline_liveness_boundary,
    clear_for_phase_boundary, clear_for_run_reset, clear_for_state_boundary, clear_for_test_reset,
    clear_subst_cache, enter_enabled_scope, enter_enabled_scope_with_ctx,
    evict_next_state_subst_entries,
    print_subst_cache_stats, EnabledScopeGuard,
};
pub use self::core::{
    Env, EvalCtx, IdentHint, InstanceInfo, OpEnv, SharedCtx, TlcConfig, TlcRuntimeStats,
    MAX_RECURSION_DEPTH,
};
pub use self::core::{SparseStateEnvRef, StateEnvRef};
pub use self::eval_cache_lifecycle::{
    clear_for_bound_state_eval_scope, clear_for_state_eval_replay, eval_entry, eval_entry_inline,
    eval_entry_with, invalidate_next_state_identity_tracking, invalidate_state_identity_tracking,
    invalidate_state_identity_tracking_with_ctx, stack_safe,
};
pub use self::eval_ctx_guards::{
    NextStateEnvGuard, NextStateMutGuard, ScopeGuard, SkipPrimeValidationGuard, StateEnvGuard,
};
pub use self::eval_ctx_locals::{EnumMark, StackMark};
pub use self::eval_debug::set_eval_worker_count;
pub use self::eval_debug::{clear_tlc_registers, print_eval_profile_stats, set_random_seed};
pub use self::eval_dispatch::eval;
pub use self::eval_membership::{check_set_pred_membership, restore_setpred_ctx};
pub use self::eval_module_load::materialize_module_with_substitutions;
pub use self::eval_sets::set_contains_with_ctx;
pub use self::helpers::has_complete_builtin_override;
pub use self::helpers::values_equal;
pub use self::helpers::{
    apply_substitutions, compose_substitutions, eval_iter_set, eval_iter_set_tlc_normalized,
    evict_next_state_eager_bindings, expr_has_any_prime, expr_has_primed_param,
    interval_len_for_bounds_check, materialize_lazy_func_to_func, materialize_setpred_to_vec,
    push_bound_var_mut,
};
pub use self::builtin_io::{is_io_exec_allowed, set_io_exec_allowed};
pub use self::hooks::set_enabled_hook;
pub use self::tir::{
    aggregate_bytecode_vm_stats, bytecode_vm_stats, note_bytecode_vm_execution,
    note_bytecode_vm_fallback,
};

#[cfg(any(kani, test))]
mod kani_harnesses;

#[cfg(test)]
mod tests;
