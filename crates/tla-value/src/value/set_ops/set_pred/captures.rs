// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Capture bundle for `SetPredValue` construction.

use super::super::super::Value;
use crate::CapturedChain;
use std::sync::Arc;
use tla_core::kani_types::HashMap;

/// Captured evaluation environment for lazy set-predicate construction.
#[must_use]
pub struct SetPredCaptures {
    pub(super) env: Arc<HashMap<Arc<str>, Value>>,
    pub(super) captured_chain: Option<Box<dyn CapturedChain>>,
    pub(super) captured_chain_depth: usize,
    pub(super) captured_state: Option<Arc<[Value]>>,
    pub(super) captured_next_state: Option<Arc<[Value]>>,
}

impl SetPredCaptures {
    /// Create the external capture bundle for a set predicate.
    pub fn new(
        env: Arc<HashMap<Arc<str>, Value>>,
        captured_state: Option<Arc<[Value]>>,
        captured_next_state: Option<Arc<[Value]>>,
    ) -> Self {
        Self {
            env,
            captured_chain: None,
            captured_chain_depth: 0,
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
