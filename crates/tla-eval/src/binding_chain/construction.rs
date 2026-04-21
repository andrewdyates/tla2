// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::arena::{arena_alloc, is_arena_active, promote_to_heap};
use super::{BindingChain, BindingNode, BindingSource, BindingValue};
use tla_core::name_intern::NameId;
use tla_value::Value;

impl BindingChain {
    /// Create an empty binding chain (no bindings).
    pub fn empty() -> Self {
        BindingChain {
            arena_head: std::ptr::null(),
            heap_head: None,
        }
    }

    /// O(1) — prepend one binding node to the chain (no deps).
    ///
    /// Part of #3580: Tries arena allocation when the arena is active and
    /// the value is Eager. Falls back to heap allocation otherwise.
    pub fn cons(&self, name: NameId, value: BindingValue) -> Self {
        if matches!(value, BindingValue::Eager(_)) && is_arena_active() {
            let ptr = arena_alloc(name, value, BindingSource::None, self.arena_head);
            return BindingChain {
                arena_head: ptr,
                heap_head: self.heap_head.clone(),
            };
        }
        let heap_head = promote_to_heap(self.arena_head, &self.heap_head);
        BindingChain {
            arena_head: std::ptr::null(),
            heap_head: Some(Arc::new(BindingNode {
                name,
                value,
                source: BindingSource::None,
                next: heap_head,
            })),
        }
    }

    /// O(1) — prepend one INSTANCE substitution binding with dependency tracking.
    ///
    /// Always uses heap path (Instance bindings carry Box<OpEvalDeps>).
    /// Promotes arena nodes to heap first to preserve ordering.
    pub(crate) fn cons_with_deps(
        &self,
        name: NameId,
        value: BindingValue,
        deps: super::super::OpEvalDeps,
    ) -> Self {
        let heap_head = promote_to_heap(self.arena_head, &self.heap_head);
        BindingChain {
            arena_head: std::ptr::null(),
            heap_head: Some(Arc::new(BindingNode {
                name,
                value,
                source: BindingSource::Instance(Box::new(deps)),
                next: heap_head,
            })),
        }
    }

    /// O(1) — prepend one local binding (LET/quantifier) with binding depth.
    ///
    /// Part of #3580: Tries arena allocation for Eager values.
    pub(crate) fn cons_local(
        &self,
        name: NameId,
        value: BindingValue,
        binding_depth: usize,
    ) -> Self {
        if matches!(value, BindingValue::Eager(_)) && is_arena_active() {
            let ptr = arena_alloc(
                name,
                value,
                BindingSource::Local(binding_depth),
                self.arena_head,
            );
            return BindingChain {
                arena_head: ptr,
                heap_head: self.heap_head.clone(),
            };
        }
        let heap_head = promote_to_heap(self.arena_head, &self.heap_head);
        BindingChain {
            arena_head: std::ptr::null(),
            heap_head: Some(Arc::new(BindingNode {
                name,
                value,
                source: BindingSource::Local(binding_depth),
                next: heap_head,
            })),
        }
    }

    /// O(1) — prepend one liveness replay binding with local-style depth tracking.
    ///
    /// Part of #3580: Tries arena allocation for Eager values.
    pub(crate) fn cons_liveness_local(
        &self,
        name: NameId,
        value: BindingValue,
        binding_depth: usize,
    ) -> Self {
        if matches!(value, BindingValue::Eager(_)) && is_arena_active() {
            let ptr = arena_alloc(
                name,
                value,
                BindingSource::Liveness(binding_depth),
                self.arena_head,
            );
            return BindingChain {
                arena_head: ptr,
                heap_head: self.heap_head.clone(),
            };
        }
        let heap_head = promote_to_heap(self.arena_head, &self.heap_head);
        BindingChain {
            arena_head: std::ptr::null(),
            heap_head: Some(Arc::new(BindingNode {
                name,
                value,
                source: BindingSource::Liveness(binding_depth),
                next: heap_head,
            })),
        }
    }

    /// Build a BindingChain from eager name-value pairs (liveness quantifier bindings).
    pub fn from_values(pairs: impl IntoIterator<Item = (Arc<str>, Value, NameId)>) -> Self {
        let mut chain = Self::empty();
        for (_name_str, value, name_id) in pairs {
            chain = chain.cons(name_id, BindingValue::eager(value));
        }
        chain
    }
}
