// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hook abstractions for decoupling eval from checker internals.
//!
//! The ENABLED operator requires enumeration logic (from `enumerate` module)
//! to test whether an action has successors. Rather than importing enumerate
//! directly (which would create a cycle when eval moves to `tla-eval`),
//! we use a hook that the checker installs at startup.

use super::core::EvalCtx;
use crate::error::{EvalError, EvalResult};
use std::cell::Cell;
use std::sync::Arc;
use tla_core::{ast::Expr, Spanned};

/// Signature for the ENABLED hook: given an eval context, an action expression,
/// and variable names, returns whether the action is enabled (has successors).
pub type EnabledHook = fn(&mut EvalCtx, &Spanned<Expr>, &[Arc<str>]) -> EvalResult<bool>;

thread_local! {
    static ENABLED_HOOK: Cell<Option<EnabledHook>> = const { Cell::new(None) };
}

/// Install the ENABLED hook. Called by the checker at startup.
pub fn set_enabled_hook(hook: EnabledHook) {
    ENABLED_HOOK.with(|h| h.set(Some(hook)));
}

/// Retrieve the installed ENABLED hook, or return an error if not installed.
pub(super) fn enabled_hook() -> EvalResult<EnabledHook> {
    ENABLED_HOOK.with(|h| {
        h.get().ok_or_else(|| EvalError::Internal {
            message:
                "ENABLED hook not installed: checker must call set_enabled_hook() before evaluation"
                    .into(),
            span: None,
        })
    })
}
