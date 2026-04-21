// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AST to LiveExpr conversion
//!
//! This module converts TLA+ AST expressions to the internal LiveExpr
//! representation used for liveness checking.
//!
//! Based on TLC's `astToLive` method in Liveness.java.

mod action_resolve;
mod action_resolve_compound;
mod core;
mod errors;
mod level;
mod level_syntactic;
mod name_refs;
mod qualify;
mod reify;
mod substitute;
mod temporal_convert;
mod temporal_fairness;
mod temporal_quantifiers;
#[cfg(test)]
mod tests;

pub use core::{ActionPredHint, AstToLive};
pub use errors::ConvertError;
