// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates Apache-2.0.
//
// Context-aware ExprVisitor implementations (require EvalCtx for operator resolution).
// Part of #1192 Wave 2: migrate hand-written walkers from enumerate/expr_analysis.rs.
// Split into domain modules for #2440.

mod guard_analysis;
mod prime_analysis;
mod primed_refs;

pub(crate) use guard_analysis::{is_operator_reference_guard_unsafe_v, might_need_prime_binding_v};

pub(crate) use prime_analysis::{expr_contains_prime_ctx_v, expr_is_action_level_v};

pub(crate) use primed_refs::{expr_references_primed_vars_v, get_primed_var_refs_with_ctx_v};

// Test-only: expr_contains_or_with_primed_ctx_v has no production callers
#[cfg(test)]
pub(crate) use prime_analysis::expr_contains_or_with_primed_ctx_v;
