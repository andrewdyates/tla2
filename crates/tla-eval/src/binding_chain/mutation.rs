// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::arena::{arena_alloc, arena_source_ref, is_arena_active, promote_to_heap};
use super::{BindingChain, BindingNode, BindingSource, BindingSourceRef, BindingValue};
use tla_core::name_intern::NameId;
use tla_value::Value;

impl BindingChain {
    /// O(1) — replace the head node's value, preserving name and source.
    ///
    /// Part of #3580: For arena heads, allocates a fresh arena node (COW) to
    /// preserve snapshot isolation — cloned chains still see the original value.
    /// For heap heads, uses `Arc::get_mut` for zero-alloc when refcount is 1.
    pub(crate) fn update_head_value(&mut self, new_value: BindingValue) {
        if !self.arena_head.is_null() {
            // SAFETY: arena_head is valid within current BFS state.
            let old = unsafe { &*self.arena_head };
            // COW: allocate a fresh arena node instead of mutating in place,
            // so cloned snapshots still see the original value.
            if matches!(new_value, BindingValue::Eager(_)) && is_arena_active() {
                let ptr = arena_alloc(
                    old.name,
                    new_value,
                    arena_source_ref(old).to_owned(),
                    old.next,
                );
                self.arena_head = ptr;
            } else {
                // Non-eager value or arena inactive: promote to heap and rebuild.
                let heap_head = promote_to_heap(old.next, &self.heap_head);
                self.arena_head = std::ptr::null();
                self.heap_head = Some(Arc::new(BindingNode {
                    name: old.name,
                    value: new_value,
                    source: arena_source_ref(old).to_owned(),
                    next: heap_head,
                }));
            }
            return;
        }
        if let Some(ref mut arc) = self.heap_head {
            if let Some(node) = Arc::get_mut(arc) {
                node.value = new_value;
                return;
            }
        }
        if let Some(old_head) = self.heap_head.take() {
            self.heap_head = Some(Arc::new(BindingNode {
                name: old_head.name,
                value: new_value,
                source: old_head.source.clone(),
                next: old_head.next.clone(),
            }));
        }
    }

    /// Rebind the current recursive parameter without growing the chain.
    pub(crate) fn try_rebind_recursive_param(
        &mut self,
        param_name: NameId,
        self_name_id: NameId,
        new_value: Value,
    ) -> bool {
        if !self.arena_head.is_null() {
            // SAFETY: arena_head is valid within current BFS state.
            let head = unsafe { &*self.arena_head };
            if head.name != param_name
                || !matches!(arena_source_ref(head), BindingSourceRef::Local(_))
            {
                return false;
            }
            if !head.next.is_null() {
                let next = unsafe { &*head.next };
                if next.name != self_name_id
                    || !matches!(arena_source_ref(next), BindingSourceRef::Local(_))
                {
                    return false;
                }
            } else {
                let matches = self.heap_head.as_ref().is_some_and(|next| {
                    next.name == self_name_id && matches!(next.source, BindingSource::Local(_))
                });
                if !matches {
                    return false;
                }
            }
            self.update_head_value(BindingValue::eager(new_value));
            return true;
        }
        let matches_recursive_layout = self.heap_head.as_ref().is_some_and(|head| {
            head.name == param_name
                && matches!(head.source, BindingSource::Local(_))
                && head.next.as_ref().is_some_and(|next| {
                    next.name == self_name_id && matches!(next.source, BindingSource::Local(_))
                })
        });
        if !matches_recursive_layout {
            return false;
        }
        self.update_head_value(BindingValue::eager(new_value));
        true
    }

    /// Promote all arena nodes to heap, returning an all-heap chain.
    ///
    /// Part of #3580: Used by `CapturedChain::clone_box()` to ensure captured
    /// chains survive beyond the BFS state boundary.
    pub(crate) fn promote_all_to_heap(&self) -> Self {
        if self.arena_head.is_null() {
            return self.clone();
        }
        BindingChain {
            arena_head: std::ptr::null(),
            heap_head: promote_to_heap(self.arena_head, &self.heap_head),
        }
    }
}
