// Author: Andrew Yates
// Copyright 2026 Andrew Yates. Apache-2.0.
//
// Concrete ExprVisitor implementations that depend only on AST types.
// These are pure expression analysis visitors with no evaluator dependency.
//
// Originally in tla-check/src/expr_visitor/visitors_simple.rs (Part of #1269 Phase 5).
// Moved to tla-core so downstream crates (tla-value, tla-eval) can use them
// without depending on tla-check.

mod binding_visitors;
mod names;
mod simple;
mod utilities;

#[cfg(test)]
mod tests;

pub use binding_visitors::*;
pub use names::*;
pub use simple::*;
pub use utilities::*;
