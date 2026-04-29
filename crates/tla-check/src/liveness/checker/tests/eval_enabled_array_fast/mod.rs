// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! eval_enabled_array_fast tests — no_state_change, no_successors, stuttering, subscript cache
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use super::*;

pub(super) use crate::liveness::test_helpers::spanned;
pub(super) use crate::Value;
pub(super) use std::sync::Arc;
pub(super) use tla_core::ast::Expr;

/// Helper: build an Env from a State's variable bindings.
pub(super) fn build_env_from_state(state: &State) -> Arc<crate::eval::Env> {
    let mut env = crate::eval::Env::new();
    for (name, value) in state.vars() {
        env.insert(Arc::clone(name), value.clone());
    }
    Arc::new(env)
}

mod basic_paths;
mod subscript_cache;
mod symmetry_witnesses;
