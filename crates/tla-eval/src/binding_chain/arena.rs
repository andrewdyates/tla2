// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Arena-allocated chain nodes for the binding chain dual-path (#3580 Slice 2).
//!
//! `ArenaChainNode` has the same logical fields as `BindingNode` but links
//! via raw pointer instead of `Arc`. Saves 16B Arc header + atomic refcount
//! operations per node.
//!
//! # Invariants
//!
//! - `value` is always `BindingValue::Eager(CompactValue)` — Lazy values go to heap.
//! - `source` is never `BindingSource::Instance(...)` — Instance bindings go to heap.
//! - Heap-backed eager values register an explicit deferred destructor with the
//!   arena because arena chunks are reused without per-node `Drop`.

use std::sync::Arc;

use tla_core::name_intern::NameId;

use super::{BindingNode, BindingSource, BindingSourceRef, BindingValue, BindingValueRef};
use crate::eval_arena::{with_eval_arena, ArenaBindingNode, ArenaSourceTag};

pub(crate) type ArenaChainNode = ArenaBindingNode;

/// Check whether the thread-local arena is initialized and active.
///
/// Cheap check (no allocation). Used by cons methods to decide whether
/// to take the arena path before moving the BindingValue.
pub(crate) fn is_arena_active() -> bool {
    with_eval_arena(|arena| arena.is_active()).unwrap_or(false)
}

/// Allocate an ArenaChainNode in the thread-local arena.
///
/// # Panics
///
/// Panics (in debug) if the arena is not active. Caller must check
/// `is_arena_active()` first.
///
/// Only called for Eager values with non-Instance sources.
pub(crate) fn arena_alloc(
    name: NameId,
    value: BindingValue,
    source: BindingSource,
    arena_next: *const ArenaChainNode,
) -> *const ArenaChainNode {
    with_eval_arena(|arena| {
        debug_assert!(arena.is_active(), "arena_alloc called with inactive arena");
        let BindingValue::Eager(value) = value else {
            panic!("arena_alloc called with non-eager binding");
        };
        let (source_tag, binding_depth) = match source {
            BindingSource::None => (ArenaSourceTag::None, 0),
            BindingSource::Local(depth) => (
                ArenaSourceTag::Local,
                u32::try_from(depth).expect("binding depth fits in u32"),
            ),
            BindingSource::Liveness(depth) => (
                ArenaSourceTag::Liveness,
                u32::try_from(depth).expect("binding depth fits in u32"),
            ),
            BindingSource::Instance(_) => panic!("arena_alloc called with instance binding"),
        };
        // SAFETY: arena is active, returned pointer stays valid until reset.
        unsafe { arena.alloc_binding_node(name, value, source_tag, binding_depth, arena_next) }
    })
    .expect("arena_alloc called without initialized arena")
}

pub(crate) fn arena_value_ref<'a>(node: &'a ArenaChainNode) -> BindingValueRef<'a> {
    BindingValueRef::Eager(&node.value)
}

pub(crate) fn arena_source_ref(node: &ArenaChainNode) -> BindingSourceRef<'_> {
    match node.source_tag {
        ArenaSourceTag::None => BindingSourceRef::None,
        ArenaSourceTag::Local => BindingSourceRef::Local(node.binding_depth as usize),
        ArenaSourceTag::Liveness => BindingSourceRef::Liveness(node.binding_depth as usize),
    }
}

/// Promote all arena nodes to heap, producing a fully heap-based chain head.
///
/// Used when:
/// 1. A closure/LazyFunc captures the chain (`CapturedChain::clone_box`)
/// 2. An Instance binding is added (`cons_with_deps` needs heap-only chain)
/// 3. A Lazy binding is added (Lazy values can't be in arena nodes)
///
/// Walks the arena chain head→tail, collects nodes, then rebuilds as
/// `Arc<BindingNode>` bottom-up (preserving original newest→oldest order).
pub(crate) fn promote_to_heap(
    arena_head: *const ArenaChainNode,
    heap_head: &Option<Arc<BindingNode>>,
) -> Option<Arc<BindingNode>> {
    if arena_head.is_null() {
        return heap_head.clone();
    }

    // Collect arena nodes in newest → oldest order.
    let mut arena_nodes = Vec::new();
    let mut cur = arena_head;
    while !cur.is_null() {
        // SAFETY: pointer chain is valid within current BFS state.
        let node = unsafe { &*cur };
        arena_nodes.push(node);
        cur = node.next;
    }

    // Build heap chain: start from heap base, prepend arena nodes oldest-first.
    let mut new_head = heap_head.clone();
    for node in arena_nodes.into_iter().rev() {
        let value = BindingValue::Eager(node.value.clone());
        let source = arena_source_ref(node).to_owned();
        new_head = Some(Arc::new(BindingNode {
            name: node.name,
            value,
            source,
            next: new_head,
        }));
    }

    new_head
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval_arena::init_thread_arena;
    use tla_value::Value;

    #[test]
    fn test_arena_alloc_when_active() {
        init_thread_arena();
        let _guard = crate::eval_arena::ArenaStateGuard::new();

        assert!(is_arena_active());

        let name = NameId(42);
        let value = BindingValue::eager(Value::int(7));
        let source = BindingSource::Local(0);

        let ptr = arena_alloc(name, value, source, std::ptr::null());
        assert!(!ptr.is_null());

        // SAFETY: pointer is valid within active arena state.
        let node = unsafe { &*ptr };
        assert_eq!(node.name, NameId(42));
        assert!(matches!(arena_source_ref(node), BindingSourceRef::Local(0)));
        assert!(node.next.is_null());
    }

    #[test]
    fn test_is_arena_active_when_inactive() {
        // Without an active guard, arena should not be active
        // (depends on thread-local state, may vary in test runner).
        // The function should return a boolean without panicking.
        let active = is_arena_active();
        // Calling twice should return the same value (deterministic).
        let active2 = is_arena_active();
        assert_eq!(
            active, active2,
            "is_arena_active() should be deterministic across consecutive calls"
        );
    }

    #[test]
    fn test_promote_empty_arena() {
        let heap = Some(Arc::new(BindingNode {
            name: NameId(1),
            value: BindingValue::eager(Value::int(10)),
            source: BindingSource::None,
            next: None,
        }));

        let result = promote_to_heap(std::ptr::null(), &heap);
        assert!(result.is_some());
        assert_eq!(result.unwrap().name, NameId(1));
    }

    #[test]
    fn test_promote_arena_chain() {
        init_thread_arena();
        let _guard = crate::eval_arena::ArenaStateGuard::new();

        // Build arena chain: node2 -> node1
        let ptr1 = arena_alloc(
            NameId(1),
            BindingValue::eager(Value::int(10)),
            BindingSource::Local(0),
            std::ptr::null(),
        );
        let ptr2 = arena_alloc(
            NameId(2),
            BindingValue::eager(Value::int(20)),
            BindingSource::Local(1),
            ptr1,
        );

        // Promote with a heap base
        let heap_base = Some(Arc::new(BindingNode {
            name: NameId(0),
            value: BindingValue::eager(Value::int(0)),
            source: BindingSource::None,
            next: None,
        }));

        let promoted = promote_to_heap(ptr2, &heap_base);
        assert!(promoted.is_some());

        // Walk promoted chain: should be node2 -> node1 -> heap_base
        let n2 = promoted.unwrap();
        assert_eq!(n2.name, NameId(2));
        let n1 = n2.next.as_ref().unwrap();
        assert_eq!(n1.name, NameId(1));
        let n0 = n1.next.as_ref().unwrap();
        assert_eq!(n0.name, NameId(0));
        assert!(n0.next.is_none());
    }

    #[test]
    fn test_arena_alloc_inline_eager_skips_deferred_drop() {
        init_thread_arena();
        let _guard = crate::eval_arena::ArenaStateGuard::new();

        let _ptr = arena_alloc(
            NameId(7),
            BindingValue::eager(Value::int(1)),
            BindingSource::Local(0),
            std::ptr::null(),
        );

        let deferred = crate::eval_arena::with_eval_arena(|arena| arena.deferred_drop_count());
        assert_eq!(deferred, Some(0));
    }

    #[test]
    fn test_arena_alloc_heap_eager_registers_deferred_drop() {
        init_thread_arena();
        let _guard = crate::eval_arena::ArenaStateGuard::new();

        let _ptr = arena_alloc(
            NameId(8),
            BindingValue::eager(Value::tuple([Value::int(1), Value::int(2)])),
            BindingSource::Local(0),
            std::ptr::null(),
        );

        let deferred = crate::eval_arena::with_eval_arena(|arena| arena.deferred_drop_count());
        assert_eq!(deferred, Some(1));
    }
}
