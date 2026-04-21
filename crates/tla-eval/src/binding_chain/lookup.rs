// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::arena::{arena_source_ref, arena_value_ref, ArenaChainNode};
use super::{BindingChain, BindingNode, BindingSourceRef, BindingValueRef};
use crate::cache::dep_tracking::StateLookupMode;
use tla_core::name_intern::NameId;
use tla_value::Value;

impl BindingChain {
    /// O(depth) — walk chain with NameId integer comparison.
    ///
    /// Part of #3580: Walks arena nodes first, then heap nodes.
    /// Inlined: this is the hottest function in binding resolution (~1.7% self-time).
    /// Inlining eliminates function call overhead and lets the compiler optimize
    /// the empty-chain case (both pointers null) into a single branch at the call site.
    ///
    /// Part of #3805: Added inline head-node match. The most common hit is the
    /// innermost quantifier variable, which is always the head node (depth 0).
    /// Checking the head inline avoids the function call to lookup_slow and the
    /// loop setup overhead for this case (~60% of all chain hits).
    ///
    /// Part of #9062: Extended inline fast path to check both head AND second node
    /// before falling through to the slow path. Nested quantifiers like
    /// `\A i \in S : \A j \in T : P(i, j)` mean lookups of the outer variable `i`
    /// are at depth 1 — the second node. Checking depth 0 + depth 1 inline catches
    /// ~80%+ of all lookups without paying the function call overhead of lookup_slow.
    /// Arena nodes are bump-allocated contiguously, so checking two adjacent nodes
    /// has excellent cache locality.
    #[inline]
    pub fn lookup(&self, target: NameId) -> Option<(BindingValueRef<'_>, BindingSourceRef<'_>)> {
        // Fast path 1: arena head match. The innermost binding is always the
        // arena head when arena is active (quantifier/LET hot path).
        if !self.arena_head.is_null() {
            // SAFETY: arena pointer chain is valid within current BFS state.
            let head = unsafe { &*self.arena_head };
            if head.name == target {
                return Some((arena_value_ref(head), arena_source_ref(head)));
            }
            // Fast path 1b: check second arena node inline (depth 1).
            // In nested quantifiers, the outer variable is at depth 1.
            // Checking it inline avoids the lookup_slow function call overhead.
            let second = head.next;
            if !second.is_null() {
                // SAFETY: arena pointer chain is valid within current BFS state.
                let node = unsafe { &*second };
                if node.name == target {
                    return Some((arena_value_ref(node), arena_source_ref(node)));
                }
            }
            // Neither head nor second matched — fall through to full walk.
            // lookup_slow_arena_skip2 starts from the third node.
            return self.lookup_slow_arena_skip2(target, second);
        }
        // Fast path 2: heap head match (when arena is inactive).
        if let Some(ref head) = self.heap_head {
            if head.name == target {
                return Some((
                    BindingValueRef::from(&head.value),
                    BindingSourceRef::from(&head.source),
                ));
            }
            // Fast path 2b: check second heap node inline (depth 1).
            if let Some(ref second) = head.next {
                if second.name == target {
                    return Some((
                        BindingValueRef::from(&second.value),
                        BindingSourceRef::from(&second.source),
                    ));
                }
                // Head and second didn't match — walk from third node onward.
                return self.lookup_slow_heap_skip2(target, &second.next);
            }
            // Only one node in heap chain and it didn't match.
            return None;
        }
        // Empty chain — no bindings exist.
        None
    }

    /// Non-inlined slow path for arena lookup — called only when the first two
    /// arena nodes didn't match.
    ///
    /// `second_arena` is the pointer to the second arena node (already checked).
    /// This walks from the third arena node onward, then falls through to heap.
    ///
    /// Part of #9062: Replaces lookup_slow which started from the second node.
    /// Now the inline fast path checks both head and second, so the slow path
    /// starts from the third node.
    #[inline(never)]
    fn lookup_slow_arena_skip2(
        &self,
        target: NameId,
        second_arena: *const ArenaChainNode,
    ) -> Option<(BindingValueRef<'_>, BindingSourceRef<'_>)> {
        // Start from third arena node (head and second were already checked inline).
        let mut arena_cur = if !second_arena.is_null() {
            // SAFETY: arena pointer chain is valid within current BFS state.
            unsafe { &*second_arena }.next
        } else {
            std::ptr::null()
        };
        while !arena_cur.is_null() {
            // SAFETY: arena pointer chain is valid within current BFS state.
            let node = unsafe { &*arena_cur };
            if node.name == target {
                return Some((arena_value_ref(node), arena_source_ref(node)));
            }
            arena_cur = node.next;
        }
        let mut cur = &self.heap_head;
        while let Some(node) = cur {
            if node.name == target {
                return Some((
                    BindingValueRef::from(&node.value),
                    BindingSourceRef::from(&node.source),
                ));
            }
            cur = &node.next;
        }
        None
    }

    /// Non-inlined slow path for heap-only lookup, skipping the first two nodes.
    ///
    /// Part of #9062: Called when arena is empty and both heap head and second
    /// didn't match. Starts walking from the given `next` pointer (second.next).
    #[inline(never)]
    fn lookup_slow_heap_skip2<'a>(
        &'a self,
        target: NameId,
        next: &'a Option<Arc<BindingNode>>,
    ) -> Option<(BindingValueRef<'a>, BindingSourceRef<'a>)> {
        let mut cur = next;
        while let Some(node) = cur {
            if node.name == target {
                return Some((
                    BindingValueRef::from(&node.value),
                    BindingSourceRef::from(&node.source),
                ));
            }
            cur = &node.next;
        }
        None
    }

    /// Part of #2991: Return the Local binding depth for `target`, or None.
    pub fn lookup_local_depth(&self, target: NameId) -> Option<usize> {
        match self.lookup(target) {
            Some((_, BindingSourceRef::Local(depth) | BindingSourceRef::Liveness(depth))) => {
                Some(depth)
            }
            _ => None,
        }
    }

    /// Lookup by string name, returning the eager value if found.
    pub fn lookup_by_name(&self, name: &str) -> Option<Value> {
        use tla_core::name_intern::lookup_name_id;
        let name_id = lookup_name_id(name)?;
        self.lookup(name_id)
            .and_then(|(value, source)| value.get_if_ready(StateLookupMode::Current, source))
    }

    /// Walk the chain, yielding `(NameId, &BindingValue, &BindingSource)` per binding.
    ///
    /// Part of #3580: Iterates arena nodes first, then heap nodes.
    pub fn iter(&self) -> BindingChainIter<'_> {
        BindingChainIter {
            arena_cur: self.arena_head,
            heap_cur: &self.heap_head,
        }
    }

    /// Iterate over eager bindings in the chain, yielding (NameId, name_str, Value).
    pub fn iter_eager(&self) -> impl Iterator<Item = (NameId, Arc<str>, Value)> + '_ {
        self.iter().filter_map(|(name_id, bv, _source)| {
            if let BindingValueRef::Eager(v) = bv {
                let name_str = tla_core::name_intern::resolve_name_id(name_id);
                Some((name_id, name_str, Value::from(v)))
            } else {
                None
            }
        })
    }

    /// Check whether the chain is empty (no bindings).
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.arena_head.is_null() && self.heap_head.is_none()
    }

    /// Check whether the chain contains an Instance-sourced binding for `target`.
    pub(crate) fn has_instance_binding(&self, target: NameId) -> bool {
        matches!(
            self.lookup(target),
            Some((_, BindingSourceRef::Instance(_)))
        )
    }

    /// Depth of the chain (number of bindings). O(n).
    #[cfg(test)]
    pub(super) fn depth(&self) -> usize {
        self.iter().count()
    }

    /// Access the heap head for refcount testing. Test-only.
    #[cfg(test)]
    pub(super) fn heap_head_ref(&self) -> &Option<Arc<BindingNode>> {
        &self.heap_head
    }

    /// Collect local bindings from the chain for captured_env/get_local_bindings.
    pub(crate) fn collect_local_bindings(&self) -> Vec<(Arc<str>, Value, NameId)> {
        let mut bindings: Vec<(Arc<str>, Value, NameId)> = self
            .iter()
            .filter(|(_, _, source)| {
                matches!(
                    source,
                    BindingSourceRef::Local(_) | BindingSourceRef::Liveness(_)
                )
            })
            .filter_map(|(name_id, value, source)| {
                value
                    .get_if_ready(StateLookupMode::Current, source)
                    .map(|v| {
                        let name_str = tla_core::name_intern::resolve_name_id(name_id);
                        (name_str, v, name_id)
                    })
            })
            .collect();
        bindings.reverse();
        bindings
    }

    /// Get the n-th local-like binding from the chain head (de Bruijn depth index).
    pub(crate) fn get_local_by_depth(&self, depth: usize) -> Option<Value> {
        let mut count = 0usize;
        for (_name_id, value, source) in self.iter() {
            if matches!(
                source,
                BindingSourceRef::Local(_) | BindingSourceRef::Liveness(_)
            ) {
                if count == depth {
                    return value.get_if_ready(StateLookupMode::Current, source);
                }
                count += 1;
            }
        }
        None
    }

    /// Write all local bindings from the chain into an env HashMap.
    pub(crate) fn write_locals_to_env(&self, env: &mut super::super::core::Env) {
        let bindings = self.collect_local_bindings();
        for (name_str, value, _name_id) in bindings {
            env.insert(name_str, value);
        }
    }
}

/// Iterator over all bindings in a `BindingChain`.
///
/// Part of #3580: Iterates arena nodes first (newest), then heap nodes.
pub struct BindingChainIter<'a> {
    arena_cur: *const ArenaChainNode,
    heap_cur: &'a Option<Arc<BindingNode>>,
}

impl<'a> Iterator for BindingChainIter<'a> {
    type Item = (NameId, BindingValueRef<'a>, BindingSourceRef<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        if !self.arena_cur.is_null() {
            // SAFETY: arena pointer chain is valid within current BFS state.
            let node = unsafe { &*self.arena_cur };
            let result = (node.name, arena_value_ref(node), arena_source_ref(node));
            self.arena_cur = node.next;
            return Some(result);
        }
        let node = self.heap_cur.as_ref()?;
        let result = (
            node.name,
            BindingValueRef::from(&node.value),
            BindingSourceRef::from(&node.source),
        );
        self.heap_cur = &node.next;
        Some(result)
    }
}
