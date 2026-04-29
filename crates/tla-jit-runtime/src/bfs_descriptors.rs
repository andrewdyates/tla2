// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pure-data descriptors for the compiled BFS step pipeline.
//!
//! These are backend-agnostic shapes that describe actions, invariants, and
//! compiled function bundles participating in a `CompiledBfsStep` /
//! `CompiledBfsLevel` run. The Cranelift backend (`tla-jit`) populates them
//! and `tla-check` reads them — neither usage requires the Cranelift code
//! generator, so the types live here in `tla-jit-runtime` to minimise
//! `tla-check`'s direct `tla_jit::` references.
//!
//! `ActionDescriptor` and `InvariantDescriptor` are defined in
//! `tla_jit_abi::tier_types` (TL-R1, Wave 14) and re-exported here for
//! convenience. `BfsStepSpec`, `CompiledActionFn`, and `CompiledInvariantFn`
//! were moved from `tla_jit::bfs_step` as part of #4267 Wave 12 (epic #4251
//! Stage 2d Gate 1). Back-compat re-exports remain in `tla-jit::bfs_step` so
//! existing Cranelift code keeps compiling unchanged.

use crate::abi::{JitInvariantFn, JitNextStateFn};
use crate::compound_layout::StateLayout;

/// Re-export of [`ActionDescriptor`] from `tla-jit-abi`.
pub use tla_jit_abi::ActionDescriptor;

/// Re-export of [`InvariantDescriptor`] from `tla-jit-abi`.
pub use tla_jit_abi::InvariantDescriptor;

/// Configuration for compiling a BFS step function for a specific spec.
///
/// Bundles all the information needed to generate the Cranelift IR for
/// one `bfs_step` function: the state layout, action descriptors, and
/// invariant descriptors.
#[derive(Debug, Clone)]
pub struct BfsStepSpec {
    /// Number of i64 slots per state (flat representation).
    pub state_len: usize,
    /// Layout of the state variables.
    pub state_layout: StateLayout,
    /// One entry per (action, binding) pair to unroll.
    pub actions: Vec<ActionDescriptor>,
    /// Invariants to check on each new successor.
    pub invariants: Vec<InvariantDescriptor>,
}

/// A pre-compiled action function plus the descriptor metadata it was built for.
#[derive(Debug, Clone)]
pub struct CompiledActionFn {
    /// Metadata for the specialized action instance.
    pub descriptor: ActionDescriptor,
    /// Native function pointer for the compiled next-state action.
    pub func: JitNextStateFn,
}

impl CompiledActionFn {
    /// Create a compiled action wrapper from a descriptor and function pointer.
    #[must_use]
    pub fn new(descriptor: ActionDescriptor, func: JitNextStateFn) -> Self {
        Self { descriptor, func }
    }
}

/// A pre-compiled invariant function plus the descriptor metadata it was built for.
#[derive(Debug, Clone)]
pub struct CompiledInvariantFn {
    /// Metadata for the invariant.
    pub descriptor: InvariantDescriptor,
    /// Native function pointer for the compiled invariant.
    pub func: JitInvariantFn,
}

impl CompiledInvariantFn {
    /// Create a compiled invariant wrapper from a descriptor and function pointer.
    #[must_use]
    pub fn new(descriptor: InvariantDescriptor, func: JitInvariantFn) -> Self {
        Self { descriptor, func }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_action_descriptor_clone() {
        let d = ActionDescriptor {
            name: "Send".to_string(),
            action_idx: 1,
            binding_values: vec![0, 1],
            formal_values: vec![1],
            read_vars: vec![0, 1],
            write_vars: vec![2],
        };
        let d2 = d.clone();
        assert_eq!(d2.name, "Send");
        assert_eq!(d2.action_idx, 1);
        assert_eq!(d2.binding_values, vec![0, 1]);
        assert_eq!(d2.formal_values, vec![1]);
    }

    #[test]
    fn test_invariant_descriptor_clone() {
        let d = InvariantDescriptor {
            name: "Safety".to_string(),
            invariant_idx: 3,
        };
        let d2 = d.clone();
        assert_eq!(d2.name, "Safety");
        assert_eq!(d2.invariant_idx, 3);
    }

    #[test]
    fn test_bfs_step_spec_clone() {
        let spec = BfsStepSpec {
            state_len: 3,
            state_layout: StateLayout::new(vec![]),
            actions: vec![],
            invariants: vec![],
        };
        let spec2 = spec.clone();
        assert_eq!(spec2.state_len, 3);
    }
}
