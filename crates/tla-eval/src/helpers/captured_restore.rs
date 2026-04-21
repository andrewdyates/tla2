// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared `CapturedChain` -> `BindingChain` restore boundary.
//!
//! Part of #3383: execution-time restore in `tla-eval` currently requires the
//! concrete captured implementation to be `BindingChain`. Centralize that
//! invariant here so all restore sites fail the same way instead of silently
//! diverging on mismatch.

use crate::binding_chain::BindingChain;
use crate::error::{EvalError, EvalResult};
use tla_core::Span;
use tla_value::CapturedChain;

pub(crate) fn restore_captured_binding_chain(
    captured: Option<&dyn CapturedChain>,
    binding_depth: usize,
    site: &'static str,
    span: Option<Span>,
) -> EvalResult<(BindingChain, usize)> {
    let Some(captured) = captured else {
        return Ok((BindingChain::empty(), 0));
    };

    let Some(chain) = captured.as_any().downcast_ref::<BindingChain>() else {
        return Err(EvalError::Internal {
            message: format!(
                "CapturedChain invariant failed in {site}: expected BindingChain for evaluator restore"
            ),
            span,
        });
    };

    Ok((chain.clone(), binding_depth))
}
