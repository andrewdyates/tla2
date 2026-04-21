// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lazy function values for TLA+ non-enumerable domains.
//!
//! `LazyFuncValue` supports on-demand evaluation for functions with non-enumerable
//! domains (Nat, Int, etc.). `ComponentDomain` and `LazyDomain` describe the
//! domain spaces. `ClosureValue` has been extracted to `closure.rs` as part of #3309.

mod captures;
mod domain;
mod value;

pub use captures::{CapturedChain, LazyFuncCaptures};
pub use domain::{ComponentDomain, LazyDomain};
pub use value::LazyFuncValue;

use std::sync::Arc;
use tla_core::ast::{BoundPattern, BoundVar};
use tla_core::name_intern::{intern_name, NameId};
use tla_core::{Span, FNV_OFFSET, FNV_PRIME};

/// Derive a deterministic ID from a source span.
///
/// FIX #1989: Replaces process-local monotonic counters with span-derived IDs
/// so that fingerprints are deterministic across runs and parallel workers.
/// The span (file + byte offsets) uniquely identifies the source expression
/// and is stable across process invocations.
pub(crate) fn deterministic_id_from_span(span: &Span) -> u64 {
    // FNV-1a-style mixing of the three span components
    let mut h: u64 = FNV_OFFSET;
    h ^= span.file.0 as u64;
    h = h.wrapping_mul(FNV_PRIME);
    h ^= span.start as u64;
    h = h.wrapping_mul(FNV_PRIME);
    h ^= span.end as u64;
    h = h.wrapping_mul(FNV_PRIME);
    h
}

/// Pre-intern bound variable names from a `BoundVar` slice.
///
/// Part of #3395: Computes `(Arc<str>, NameId)` pairs once at `LazyFuncValue`
/// creation time. Application-time binding (`eval_func_apply`) uses these
/// directly via `push_binding_preinterned`, eliminating per-application
/// String→Arc<str> allocation + `intern_name` HashMap lookup.
pub(super) fn pre_intern_bounds(bounds: &[BoundVar]) -> Arc<[(Arc<str>, NameId)]> {
    bounds
        .iter()
        .map(|b| {
            let name_str: Arc<str> = match &b.pattern {
                Some(BoundPattern::Var(var)) => Arc::from(var.node.as_str()),
                _ => Arc::from(b.name.node.as_str()),
            };
            let id = intern_name(&name_str);
            (name_str, id)
        })
        .collect()
}
