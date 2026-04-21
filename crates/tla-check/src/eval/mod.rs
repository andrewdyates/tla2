// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compatibility shim: re-exports from `tla-eval` crate.
//!
//! The evaluator was extracted to `tla-eval` as part of #1269.
//! This module re-exports its public API so existing `crate::eval::*` paths
//! in the checker continue to work without mass callsite changes.

// Explicit re-exports from tla-eval (Part of #2957: replace wildcard `pub use tla_eval::*`)
pub use tla_eval::{
    // Helpers
    aggregate_bytecode_vm_stats,
    apply_substitutions,
    bytecode_vm_stats,
    // Membership/set operations
    check_set_pred_membership,
    // Cache lifecycle functions
    clear_for_bound_state_eval_scope,
    clear_for_eval_scope_boundary,
    clear_for_inline_liveness_boundary,
    clear_for_phase_boundary,
    clear_for_run_reset,
    clear_for_state_boundary,
    clear_for_state_eval_replay,
    clear_for_test_reset,
    clear_subst_cache,
    compose_substitutions,
    enter_enabled_scope,
    enter_enabled_scope_with_ctx,
    // Main eval function
    eval,
    // Eval entry points
    eval_entry,
    eval_entry_inline,
    eval_iter_set,
    eval_iter_set_tlc_normalized,
    evict_next_state_eager_bindings,
    evict_next_state_subst_entries,
    expr_has_any_prime,
    has_complete_builtin_override,
    invalidate_next_state_identity_tracking,
    invalidate_state_identity_tracking,
    // Module loading
    materialize_module_with_substitutions,
    // Debug/profiling
    print_eval_profile_stats,
    push_bound_var_mut,
    restore_setpred_ctx,
    set_contains_with_ctx,
    // Hooks
    set_enabled_hook,
    set_eval_worker_count,
    // IO security gate (Part of #3965)
    set_io_exec_allowed,
    set_random_seed,
    stack_safe,
    try_eval_const_level,
    values_equal,
    // Binding types
    BindingChain,
    BindingValue,
    // Core context types
    Env,
    EvalCtx,
    IdentHint,
    OpEnv,
    SharedCtx,
    SparseStateEnvRef,
    // Guard types
    StackMark,
    TlcConfig,
    TlcRuntimeStats,
};

// Flatten commonly used value/error types into this scope for backward
// compatibility with `use crate::eval::*` and `use super::*` in tests.
// Import from tla_value directly (Part of #1582: tla_eval shim modules
// are now pub(crate), external consumers should use tla_value).
pub use tla_value::error::{EvalError, EvalResult};
pub use tla_value::{
    FuncValue, IntervalValue, KSubsetValue, LazyDomain, RecordBuilder, RecordValue, SeqSetValue,
    SetBuilder, SetCapValue, SetDiffValue, SetPredValue, SortedSet, TupleSetValue, UnionValue,
    Value,
};
