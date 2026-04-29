// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Dropbox Apache-2.0.
//
// Generic AST expression visitor for tla-check.
// Replaces ~38 hand-written walker functions with a single traversal
// parameterized by visitor behavior.
//
// Design: designs/2026-02-07-generic-ast-visitor.md
// Epic: #1192 (Wave 2)

mod visitors_ctx;
mod visitors_simple;

// Re-export visitor framework items used within tla-check.
pub(crate) use tla_core::{walk_expr, walk_spanned_expr, ExprVisitor};
pub(crate) use visitors_ctx::*;
pub(crate) use visitors_simple::*;

// Re-export utility functions from tla-core root (moved in #1269 Phase 5).
pub(crate) use tla_core::collect_conjuncts_v;
// Test-only re-exports
#[cfg(test)]
pub(crate) use tla_core::apply_substitutions_v;
#[cfg(test)]
pub(crate) use tla_core::single_bound_var_names;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_scope;
#[cfg(test)]
mod tests_short_circuit;
