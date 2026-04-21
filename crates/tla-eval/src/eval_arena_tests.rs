// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::atomic::{AtomicUsize, Ordering};

#[test]
fn test_arena_basic_lifecycle() {
    let mut arena = EvalArena::new();
    assert_eq!(arena.chunk_count(), 1);
    assert!(!arena.is_active());

    arena.begin_state();
    assert!(arena.is_active());

    // Allocate a u64
    // SAFETY: arena is active, reference used within this state.
    let val: &mut u64 = unsafe { arena.alloc(42u64) };
    assert_eq!(*val, 42);
    assert_eq!(arena.alloc_count(), 1);

    arena.end_state();
    assert!(!arena.is_active());
    assert_eq!(arena.reset_count(), 1);
}

#[test]
fn test_arena_multiple_allocs() {
    let mut arena = EvalArena::new();
    arena.begin_state();

    // Allocate several values
    for i in 0u64..100 {
        // SAFETY: arena is active, references not held across iterations.
        let val: &mut u64 = unsafe { arena.alloc(i) };
        assert_eq!(*val, i);
    }
    assert_eq!(arena.alloc_count(), 100);
    assert!(arena.total_allocated() >= 800); // 100 * 8B

    arena.end_state();

    // Reset and allocate again — should reuse the same chunk(s)
    let chunks_before = arena.chunk_count();
    arena.begin_state();
    for i in 0u64..100 {
        // SAFETY: arena is active, fresh state.
        let val: &mut u64 = unsafe { arena.alloc(i) };
        assert_eq!(*val, i);
    }
    assert_eq!(arena.chunk_count(), chunks_before);
    arena.end_state();
}

#[test]
fn test_arena_chunk_overflow() {
    let mut arena = EvalArena::new();
    arena.begin_state();

    // Fill beyond one chunk (64KB / 8B per u64 = 8192 u64s per chunk)
    let allocs_per_chunk = CHUNK_SIZE / std::mem::size_of::<u64>();
    for i in 0u64..(allocs_per_chunk as u64 + 100) {
        // SAFETY: arena is active.
        let val: &mut u64 = unsafe { arena.alloc(i) };
        assert_eq!(*val, i);
    }
    assert!(arena.chunk_count() >= 2);

    arena.end_state();
}

#[test]
fn test_arena_alignment() {
    let mut arena = EvalArena::new();
    arena.begin_state();

    // Allocate a u8 followed by a u64 — the u64 should be aligned
    // SAFETY: arena is active.
    let _byte: &mut u8 = unsafe { arena.alloc(0xFFu8) };
    let val: &mut u64 = unsafe { arena.alloc(0x1234567890ABCDEFu64) };
    assert_eq!(*val, 0x1234567890ABCDEFu64);
    // Verify alignment
    let ptr = val as *const u64;
    assert_eq!(ptr as usize % std::mem::align_of::<u64>(), 0);

    arena.end_state();
}

#[test]
fn test_arena_thread_local() {
    init_thread_arena();

    let result = with_eval_arena(|arena| {
        arena.begin_state();
        // SAFETY: arena is active.
        let val: &mut u64 = unsafe { arena.alloc(99u64) };
        let r = *val;
        arena.end_state();
        r
    });

    assert_eq!(result, Some(99));
}

#[test]
fn test_arena_state_guard_recovers_after_panic() {
    init_thread_arena();
    with_eval_arena(|arena| {
        if arena.is_active() {
            arena.end_state();
        }
    });

    let unwind_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _arena_state = ArenaStateGuard::new();
        let result = with_eval_arena(|arena| {
            assert!(arena.is_active());
            // SAFETY: the guard has activated the arena for this scope.
            let value: &mut u64 = unsafe { arena.alloc(7u64) };
            *value
        });
        assert_eq!(result, Some(7));
        panic!("synthetic arena state panic");
    }));
    assert!(unwind_result.is_err());
    assert_eq!(with_eval_arena(|arena| arena.is_active()), Some(false));

    let recovered = {
        let _arena_state = ArenaStateGuard::new();
        with_eval_arena(|arena| {
            assert!(arena.is_active());
            // SAFETY: the guard has activated the arena for this scope.
            let value: &mut u64 = unsafe { arena.alloc(11u64) };
            *value
        })
    };
    assert_eq!(recovered, Some(11));
    assert_eq!(with_eval_arena(|arena| arena.is_active()), Some(false));
}

#[test]
#[should_panic(expected = "begin_state called while arena is already active")]
fn test_arena_double_begin_panics() {
    let mut arena = EvalArena::new();
    arena.begin_state();
    arena.begin_state(); // should panic
}

#[test]
#[should_panic(expected = "end_state called while arena is not active")]
fn test_arena_end_without_begin_panics() {
    let mut arena = EvalArena::new();
    arena.end_state(); // should panic
}

/// Simulate the per-BFS-step lifecycle with a struct resembling ArenaBindingNode.
#[test]
fn test_arena_binding_node_simulation() {
    #[repr(C)]
    struct SimNode {
        name: u32,
        value: u64,
        next: *const SimNode,
    }

    let mut arena = EvalArena::new();
    arena.begin_state();

    // Build a chain of 10 nodes
    let mut head: *const SimNode = std::ptr::null();
    for i in 0u32..10 {
        // SAFETY: arena is active, SimNode fits in a chunk.
        let node: &mut SimNode = unsafe {
            arena.alloc(SimNode {
                name: i,
                value: i as u64 * 100,
                next: head,
            })
        };
        head = node as *const SimNode;
    }

    // Walk the chain
    let mut cur = head;
    let mut count = 0u32;
    while !cur.is_null() {
        // SAFETY: all nodes were allocated in the active arena above.
        let node = unsafe { &*cur };
        assert_eq!(node.name, 9 - count);
        assert_eq!(node.value, (9 - count) as u64 * 100);
        cur = node.next;
        count += 1;
    }
    assert_eq!(count, 10);

    arena.end_state();
}

/// Test ArenaBindingNode allocation and chain walking.
#[test]
fn test_arena_binding_node_chain() {
    use tla_value::Value;

    let mut arena = EvalArena::new();
    arena.begin_state();

    // Build a chain of 5 ArenaBindingNodes
    let mut head: *const ArenaBindingNode = std::ptr::null();
    for i in 0u32..5 {
        let value = CompactValue::from(Value::int(i as i64));
        // SAFETY: arena is active, all pointers are within this state.
        head = unsafe {
            arena.alloc_binding_node(NameId(i), value, ArenaSourceTag::Local, i as u32, head)
        };
    }

    // Walk and verify
    let mut cur = head;
    let mut count = 0u32;
    while !cur.is_null() {
        // SAFETY: all nodes allocated in the active arena above.
        let node = unsafe { &*cur };
        let expected_name = 4 - count;
        assert_eq!(node.name, NameId(expected_name));
        assert_eq!(node.source_tag, ArenaSourceTag::Local);
        assert_eq!(node.binding_depth, expected_name);
        cur = node.next;
        count += 1;
    }
    assert_eq!(count, 5);
    assert_eq!(arena.alloc_count(), 5);

    arena.end_state();
}

/// Verify ArenaBindingNode is exactly 32 bytes.
#[test]
fn test_arena_binding_node_size() {
    assert_eq!(std::mem::size_of::<ArenaBindingNode>(), 32);
    assert!(std::mem::align_of::<ArenaBindingNode>() <= 8);
}

#[test]
fn test_alloc_binding_node_tracks_heap_backed_values_only() {
    use tla_value::Value;

    let mut arena = EvalArena::new();
    arena.begin_state();

    let inline = CompactValue::from(Value::int(1));
    let heap = CompactValue::from(Value::tuple([Value::int(1), Value::int(2)]));

    unsafe {
        let _inline = arena.alloc_binding_node(
            NameId(1),
            inline,
            ArenaSourceTag::Local,
            0,
            std::ptr::null(),
        );
    }
    assert_eq!(arena.deferred_drop_count(), 0);

    unsafe {
        let _heap =
            arena.alloc_binding_node(NameId(2), heap, ArenaSourceTag::Local, 1, std::ptr::null());
    }
    assert_eq!(arena.deferred_drop_count(), 1);

    arena.end_state();
}

#[test]
fn test_deferred_drop_in_place_runs_on_end_state() {
    struct DropSpy<'a> {
        drops: &'a AtomicUsize,
    }

    impl Drop for DropSpy<'_> {
        fn drop(&mut self) {
            self.drops.fetch_add(1, Ordering::SeqCst);
        }
    }

    let drops = AtomicUsize::new(0);
    let mut arena = EvalArena::new();
    arena.begin_state();

    let spy_ptr = unsafe { arena.alloc_ptr(DropSpy { drops: &drops }) };
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    unsafe {
        arena.defer_drop_in_place(spy_ptr);
    }
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    assert_eq!(arena.deferred_drop_count(), 1);

    arena.end_state();
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    assert_eq!(arena.deferred_drop_count(), 0);
}
