// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Liveness checking module
//!
//! This module implements liveness checking for TLA+ specifications using
//! the tableau construction method from Manna & Pnueli.
//!
//! # Overview
//!
//! Liveness properties are temporal properties that assert something "eventually"
//! happens. Examples:
//! - `<>P` - Eventually P holds
//! - `[]<>P` - Infinitely often P holds
//! - `P ~> Q` - P leads to Q
//! - `WF_vars(A)` - Weak fairness for action A
//! - `SF_vars(A)` - Strong fairness for action A
//!
//! # Algorithm
//!
//! 1. Parse temporal formula from AST using [`AstToLive`]
//! 2. Convert to positive normal form (negation pushed to atoms)
//! 3. Build tableau graph from the formula
//! 4. Build behavior graph × tableau product during state exploration
//! 5. Find strongly connected components (SCCs) using Tarjan's algorithm
//! 6. Check each SCC for accepting cycles (liveness violations)
//! 7. Extract counterexample trace if violation found
//!
//! # Architecture
//!
//! The liveness checking implementation consists of:
//!
//! - [`LiveExpr`]: Internal representation for temporal formulas (positive normal form)
//! - [`Tableau`]: Automaton graph built from temporal formula negation
//! - [`BehaviorGraph`]: Product graph of (state × tableau) pairs
//! - [`is_state_consistent`]: Check if a state satisfies tableau node predicates
//!
//! # References
//!
//! - Manna & Pnueli, "Temporal Verification of Reactive Systems: Safety", Ch 5
//! - TLC implementation in tlc2.tool.liveness package

mod ast_to_live;
mod behavior_graph;
pub(crate) mod boolean_contract;
mod checker;
mod consistency;
mod cycle_path;
pub(crate) mod debug;
mod enabled_eval;
pub(crate) mod graph_store;
mod inline_eval_scope;
pub(crate) mod inline_leaf_eval;
mod live_expr;
pub(crate) mod live_expr_eval;
pub(crate) mod on_the_fly;
mod scc;
pub(crate) mod storage;
mod tableau;
mod tarjan;
#[cfg(test)]
pub(crate) mod test_helpers;

pub use ast_to_live::{ActionPredHint, AstToLive, ConvertError};
pub(crate) use checker::clear_enabled_cache;
pub(crate) use checker::clear_subscript_value_cache;
pub(crate) use checker::eval_subscript_changed_array_cached;
pub(crate) use checker::log_cache_stats;
pub(crate) use checker::InlineCheckResults;
pub use checker::{GroupedLivenessPlan, LivenessChecker, LivenessResult};
pub(crate) use inline_eval_scope::InlineEvalScope;
pub use live_expr::{ExprLevel, LiveExpr};
pub(crate) use tableau::Tableau;

use crate::state::{ArrayState, Fingerprint};
use rustc_hash::FxHashMap;

/// Type alias for successor witness map used in symmetry-aware liveness checking.
/// Maps each state fingerprint to its concrete successor ArrayStates (fingerprint, array pairs).
/// Required because symmetry reduction canonicalizes fingerprints but liveness checking
/// needs actual state values to evaluate ENABLED and action predicates.
///
/// Part of #2661: Stores ArrayState instead of State to eliminate the O(W) conversion
/// in build_successor_witnesses(). Consumers use values() for O(1) array-backed binding
/// instead of the more expensive State::to_values() which requires allocation + registry lookup.
pub type SuccessorWitnessMap = FxHashMap<Fingerprint, Vec<(Fingerprint, ArrayState)>>;

/// Top-level evaluation entry point for liveness boundary calls.
///
/// All liveness code that starts a fresh top-level evaluation MUST use this
/// instead of raw `eval()`. Delegates to the shared
/// [`crate::enumerate::tir_leaf::eval_leaf_entry`] helper with `tir=None`,
/// preserving the same cache lifecycle semantics as [`crate::eval::eval_entry`]
/// while keeping liveness aligned with the common TIR leaf-eval boundary.
///
/// Internal recursive eval calls within an ongoing evaluation should continue
/// to use `eval()` directly — resetting caches mid-expression is incorrect.
pub(crate) fn eval_live_entry(
    ctx: &crate::eval::EvalCtx,
    expr: &tla_core::Spanned<tla_core::ast::Expr>,
) -> crate::error::EvalResult<crate::Value> {
    crate::enumerate::tir_leaf::eval_leaf_entry(ctx, expr, None)
}
