// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State enumeration for model checking
//!
//! This module implements constraint extraction and state enumeration for:
//! 1. Init predicates - extracting equality constraints to generate initial states
//! 2. Next relations - handling primed variables to generate successor states
//!
//! # Approach
//!
//! For Init predicates:
//! - Parse conjunctions to extract individual constraints
//! - Handle equality constraints: `x = value`
//! - Handle membership constraints: `x \in S`
//! - Enumerate all satisfying states
//!
//! For Next relations:
//! - Bind current state variables
//! - Find primed variable assignments: `x' = expr`
//! - Handle UNCHANGED: equivalent to `x' = x`
//! - Handle disjunctions (multiple actions)
//! - Enumerate all successor states

use crate::error::EvalError;
use crate::eval::{apply_substitutions, compose_substitutions, EvalCtx, OpEnv};
use crate::state::State;
use crate::Value;
use std::cell::Cell;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::{Span, Spanned};

#[cfg(test)]
use crate::state::ArrayState;

thread_local! {
    static ENABLED_EARLY_EXIT: Cell<bool> = const { Cell::new(false) };
}

pub(super) fn enabled_early_exit() -> bool {
    ENABLED_EARLY_EXIT.with(std::cell::Cell::get)
}

#[cfg(test)]
mod build;
#[cfg(test)]
pub use build::build_successor_array_states_with_ctx;

#[cfg(test)]
mod emitter;

mod build_diff;
#[cfg(test)]
pub use build_diff::{
    build_successor_diffs_from_array, build_successor_diffs_from_array_filtered,
    build_successor_diffs_from_array_into, build_successor_diffs_with_deferred_filtered,
};

mod action_successors;
pub(crate) use action_successors::enumerate_action_successors;

mod constraint;
pub(crate) use constraint::{find_unconstrained_vars, find_values_for_var, Constraint, InitDomain};

mod init_constraints;
#[cfg(test)]
pub(crate) use init_constraints::count_expr_nodes;
pub(crate) use init_constraints::{extract_conjunction_remainder, extract_init_constraints};

mod expr_analysis;
pub(crate) use expr_analysis::collect_state_var_refs;
pub(crate) use expr_analysis::{clear_expr_analysis_caches, expr_contains_any_prime};
#[cfg(test)]
use expr_analysis::{expr_contains_exists, flatten_and};
use expr_analysis::{
    expr_is_action_level, expr_references_primed_vars, expr_references_state_vars,
    get_primed_var_refs, get_primed_var_refs_with_ctx, is_guard_expression,
    is_operator_reference_guard_unsafe,
};

mod expand_ops;
pub(crate) use expand_ops::expand_operators;
pub(crate) use expand_ops::expand_operators_with_primes;

mod symbolic_assignments;
#[cfg(test)]
use symbolic_assignments::toposort::topological_sort_assignments;
#[cfg(test)]
use symbolic_assignments::{evaluate_symbolic_assignments, extract_symbolic_assignments};

mod subst_cache;
pub(crate) use subst_cache::clear_enum_subst_cache;
pub(crate) mod subset_constrained;
pub(crate) mod subset_profile;
mod unified;
mod unified_classify;
mod unified_conjuncts;
mod unified_dispatch;
mod unified_emit;
mod unified_exists;
mod unified_fast_path;
mod unified_module_ref;
mod unified_scope;
mod unified_types;
pub(crate) use unified_types::{ClosureSink, DiffSink};
pub(crate) mod tir_leaf;

mod init_enumerate;
#[cfg(test)]
#[allow(unused_imports)]
use init_enumerate::compute_values_fingerprint;
pub(crate) use init_enumerate::{
    enumerate_constraints_to_bulk, enumerate_constraints_to_bulk_with_stats,
    enumerate_constraints_to_bulk_with_stats_filter_error,
    enumerate_states_from_constraint_branches, eval_filter_expr, BulkConstraintEnumerationError,
    BulkConstraintEnumerationStats,
};

// Part of #3461: local_scope is only used by build_tests, gate to suppress dead_code warning.
#[cfg(test)]
mod local_scope;

mod successor_api;
mod successor_engine;
#[cfg(test)]
pub(crate) use successor_api::enumerate_successors_array;
pub(crate) use successor_api::{
    enumerate_successors, enumerate_successors_array_as_diffs,
    enumerate_successors_array_as_diffs_into,
    enumerate_successors_array_as_diffs_into_with_current_values,
    enumerate_successors_array_as_diffs_into_with_pc_hoist,
    enumerate_successors_array_as_diffs_with_current_values, enumerate_successors_array_with_tir,
};
#[cfg(test)]
pub(crate) use successor_engine::successor_engine_test_helpers;

mod value_to_expr;
#[cfg(feature = "z4")]
pub(crate) use value_to_expr::try_value_to_expr;
pub(crate) use value_to_expr::value_to_expr;

mod action_validation;
mod guard_check;
mod unchanged_extraction;
use guard_check::check_and_guards;

debug_flag!(pub(crate) debug_enum, "TLA2_DEBUG_ENUM");

mod error_classify;
pub(super) use error_classify::is_action_level_error;
pub(crate) use error_classify::{
    classify_iter_error_for_speculative_path, is_disabled_action_error,
    is_speculative_eval_fallback, IterDomainAction,
};

pub(super) fn case_guard_error(err: EvalError, span: Span) -> EvalError {
    if matches!(err, EvalError::ExitRequested { .. }) {
        err
    } else {
        EvalError::CaseGuardError {
            source: Box::new(err),
            span: Some(span),
        }
    }
}

pub(super) fn is_let_lazy_safe_error(err: &EvalError) -> bool {
    !matches!(err, EvalError::ExitRequested { .. })
}

#[cfg(debug_assertions)]
pub(super) fn emit_debug_line(enabled: bool, args: std::fmt::Arguments<'_>) {
    if enabled {
        eprintln!("{args}");
    }
}

#[cfg(not(debug_assertions))]
pub(super) fn emit_debug_line(_: bool, _: std::fmt::Arguments<'_>) {}

feature_flag!(profile_enum_detail, "TLA2_PROFILE_ENUM_DETAIL");

use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};

static PROF_ASSIGN_US: AtomicU64 = AtomicU64::new(0);

pub(crate) fn print_enum_profile_stats() {
    if !profile_enum_detail() {
        return;
    }
    let assign = PROF_ASSIGN_US.swap(0, AtomicOrdering::Relaxed);
    if assign == 0 {
        return;
    }
    eprintln!("=== Enumeration Detail Profile ===");
    eprintln!("  Assignment eval: {:>8.3}s", assign as f64 / 1_000_000.0);
}

debug_flag!(debug_extract, "TLA2_DEBUG_EXTRACT");
debug_flag!(debug_toposort, "TLA2_DEBUG_TOPOSORT");
debug_flag!(pub(super) debug_stage, "TLA2_DEBUG_STAGE");
debug_flag!(pub(super) debug_guards, "TLA2_DEBUG_GUARDS");
debug_flag!(pub(super) debug_enum_trace, "TLA2_DEBUG_ENUM_TRACE");

#[derive(Debug, Clone)]
pub enum PrimedAssignment {
    Assign(Arc<str>, Value),
    #[allow(dead_code)] // Constructed in test-only builders; production retains the match shape.
    Unchanged(Arc<str>),
    InSet(Arc<str>, Vec<Value>),
    #[allow(dead_code)] // Fields read only in test-gated build.rs; production matches with (_, _)
    DeferredExpr(Arc<str>, Spanned<Expr>),
}

type CapturedBindings = Vec<(Arc<str>, Value)>;

#[derive(Debug, Clone)]
pub(super) enum SymbolicAssignment {
    Expr(Arc<str>, Spanned<Expr>, CapturedBindings),
    Value(Arc<str>, Value),
    Unchanged(Arc<str>),
    InSet(Arc<str>, Spanned<Expr>, CapturedBindings),
}

impl SymbolicAssignment {
    fn var_name(&self) -> &Arc<str> {
        match self {
            SymbolicAssignment::Value(n, _)
            | SymbolicAssignment::Expr(n, _, _)
            | SymbolicAssignment::Unchanged(n)
            | SymbolicAssignment::InSet(n, _, _) => n,
        }
    }
}

// Part of #188: Removed all_vars_assigned() - replaced with O(1) bitmap check
// using assigned_mask == full_mask in enumerate_and_conjuncts_as_diffs_opt

// eval_enabled removed — Part of #3004: All ENABLED evaluation now uses
// enabled::eval_enabled_cp (constraint propagation) instead of enumerate_unified.
// The CP approach avoids ArrayState construction, fingerprint computation, and
// undo stack allocation. See crates/tla-check/src/enabled/ for the replacement.
