// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cross-crate capture boundary types for lazy function values.
//!
//! `CapturedChain` is the trait that bridges `tla-value` and `tla-eval` for
//! opaque binding chain capture. `LazyFuncCaptures` is the DTO that carries
//! the captured evaluation environment during lazy function construction.

use super::super::Value;
use std::sync::Arc;
use tla_core::kani_types::HashMap;

/// Trait for opaque captured bindings that cross the `tla-value` / `tla-eval`
/// crate boundary.
///
/// Part of #2955: `BindingChain` lives in `tla-eval` but `LazyFuncCaptures`
/// lives in `tla-value`, so this trait preserves O(1) clone semantics without
/// moving the concrete type across crates.
///
/// Current boundary note: this trait is generic enough for cloning and
/// `materialize_locals()` consumers, but it is not yet a fully generic
/// execution-time restore interface. Evaluator restore paths in `tla-eval`
/// currently require the concrete implementation to be `BindingChain`; other
/// implementations are only valid for APIs that consume materialized locals or
/// identity data.
pub trait CapturedChain: std::any::Any + Send + Sync {
    fn clone_box(&self) -> Box<dyn CapturedChain>;
    fn as_any(&self) -> &dyn std::any::Any;
    /// Part of #2990: Materialize local bindings into a flat env HashMap.
    fn materialize_locals(&self, env: &mut HashMap<Arc<str>, Value>);
}

impl Clone for Box<dyn CapturedChain> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

/// Captured evaluation environment for lazy function construction.
///
/// Part of #2989: `captured_bindings` removed — the `captured_chain` (BindingChain)
/// is the sole source of truth for local bindings, making the bindings Vec vestigial.
#[must_use]
pub struct LazyFuncCaptures {
    /// Part of #2955: Arc-wrapped to enable O(1) sharing with LazyFuncValue.
    pub(super) env: Arc<HashMap<Arc<str>, Value>>,
    /// Part of #2955: Opaque captured BindingChain from definition time.
    pub(super) captured_chain: Option<Box<dyn CapturedChain>>,
    /// Part of #2955: The binding_depth at capture time.
    pub(super) captured_chain_depth: usize,
    pub(super) local_ops: Option<Arc<tla_core::OpEnv>>,
    pub(super) captured_state: Option<Arc<[Value]>>,
    pub(super) captured_next_state: Option<Arc<[Value]>>,
}

impl LazyFuncCaptures {
    /// Create the external capture bundle for a lazy function.
    pub fn new(
        env: Arc<HashMap<Arc<str>, Value>>,
        local_ops: Option<Arc<tla_core::OpEnv>>,
        captured_state: Option<Arc<[Value]>>,
        captured_next_state: Option<Arc<[Value]>>,
    ) -> Self {
        Self {
            env,
            captured_chain: None,
            captured_chain_depth: 0,
            local_ops,
            captured_state,
            captured_next_state,
        }
    }

    /// Attach an opaque captured binding chain and its definition-site depth.
    pub fn with_captured_chain(mut self, chain: Box<dyn CapturedChain>, depth: usize) -> Self {
        self.captured_chain = Some(chain);
        self.captured_chain_depth = depth;
        self
    }
}
