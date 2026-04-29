// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Snapshot and scope tests: persistent chain push/pop, nested scope management,
//! concurrent snapshots, EvalCtx chain_snapshots simulation.
//! Part of #2364 and #2748.

use super::super::*;
use std::sync::Arc;
use tla_core::name_intern::intern_name;
use tla_value::Value;

// --- Chain snapshot push/pop tests (Part of #2364) ---
//
// These test the persistent data structure property that underpins scope management.
// "Snapshot" = clone the chain head. "Push" = cons new bindings. "Restore" = reassign
// from the snapshot. This mirrors how EvalCtx::scope_guard saves/restores the env.

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_snapshot_push_restore_basic() {
    // Save a snapshot, push bindings, then restore. The snapshot should be unchanged.
    let base = BindingChain::empty();
    let x_id = intern_name("test_bc_snap_basic_x");
    let y_id = intern_name("test_bc_snap_basic_y");

    let base = base.cons(x_id, BindingValue::eager(Value::int(1)));

    // Snapshot
    let snapshot = base.clone();
    assert_eq!(snapshot.depth(), 1);

    // Push into a new scope (would normally be done by quantifier/LET binding)
    let scoped = base.cons(y_id, BindingValue::eager(Value::int(2)));
    assert_eq!(scoped.depth(), 2);
    assert!(scoped.lookup(y_id).is_some());

    // Snapshot still has depth 1 and doesn't see y
    assert_eq!(snapshot.depth(), 1);
    assert!(snapshot.lookup(y_id).is_none());
    match snapshot.lookup(x_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(1)),
        _ => panic!("expected Eager"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_snapshot_restore_drops_intermediate_nodes() {
    // Verify that restoring a snapshot allows intermediate nodes to be freed.
    // We check this via Arc::strong_count on a dedicated tracking Arc.
    let x_id = intern_name("test_bc_snap_drop_x");
    let y_id = intern_name("test_bc_snap_drop_y");
    let z_id = intern_name("test_bc_snap_drop_z");

    let base = BindingChain::empty().cons(x_id, BindingValue::eager(Value::int(1)));

    // Get an Arc clone to track the base node's refcount
    let tracker = base.heap_head_ref().as_ref().unwrap().clone();
    let count_before = Arc::strong_count(&tracker);

    // Snapshot preserves the chain
    let snapshot = base.clone();
    let count_after_snapshot = Arc::strong_count(&tracker);
    assert!(
        count_after_snapshot > count_before,
        "snapshot should bump refcount"
    );

    // Push two bindings into a scoped chain
    let scoped = base
        .cons(y_id, BindingValue::eager(Value::int(2)))
        .cons(z_id, BindingValue::eager(Value::int(3)));
    assert_eq!(scoped.depth(), 3);
    let count_with_scope = Arc::strong_count(&tracker);
    assert!(
        count_with_scope > count_after_snapshot,
        "scoped chain should add references to base node"
    );

    // "Restore" by dropping the scoped chain -- simulate scope exit
    drop(scoped);

    // Scoped chain's transitive reference to base node should be freed
    let count_after_drop = Arc::strong_count(&tracker);
    assert!(
        count_after_drop < count_with_scope,
        "dropping scoped chain should release references: {} < {}",
        count_after_drop,
        count_with_scope
    );

    // The snapshot is intact
    assert_eq!(snapshot.depth(), 1);
    match snapshot.lookup(x_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(1)),
        _ => panic!("expected Eager"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_snapshots() {
    // Simulate nested scope entry/exit using the persistent chain.
    // Each scope level has a snapshot (clone) that remains valid after deeper scopes drop.
    //
    // Key distinction: the snapshots test ISOLATION (snapshot never sees later bindings),
    // NOT removal of bindings from existing references. The persistent structure means
    // scope exit is just "stop using the deeper chain" -- the snapshot was always separate.
    let x_id = intern_name("test_bc_nested_x");
    let y_id = intern_name("test_bc_nested_y");
    let z_id = intern_name("test_bc_nested_z");

    // Scope 0
    let scope0 = BindingChain::empty().cons(x_id, BindingValue::eager(Value::int(1)));
    let snapshot0 = scope0.clone();

    // Enter scope 1
    let scope1 = scope0.cons(y_id, BindingValue::eager(Value::int(2)));
    let snapshot1 = scope1.clone();
    assert_eq!(scope1.depth(), 2);

    // Enter scope 2
    let scope2 = scope1.cons(z_id, BindingValue::eager(Value::int(3)));
    assert_eq!(scope2.depth(), 3);

    // scope2 sees all three bindings
    assert!(scope2.lookup(x_id).is_some());
    assert!(scope2.lookup(y_id).is_some());
    assert!(scope2.lookup(z_id).is_some());

    // Exit scope 2: deeper chain dropped, snapshot1 is the "restored" view
    drop(scope2);
    assert_eq!(snapshot1.depth(), 2);
    assert!(snapshot1.lookup(x_id).is_some());
    assert!(snapshot1.lookup(y_id).is_some());
    // snapshot1 was cloned before z was added -- isolation, not removal
    assert!(snapshot1.lookup(z_id).is_none());

    // Exit scope 1: snapshot0 is the "restored" view
    drop(snapshot1);
    assert_eq!(snapshot0.depth(), 1);
    assert!(snapshot0.lookup(x_id).is_some());
    // snapshot0 was cloned before y was added -- isolation, not removal
    assert!(snapshot0.lookup(y_id).is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_snapshot_with_update_head_value() {
    // Snapshot, then update_head_value on the original. The snapshot should be unaffected.
    let x_id = intern_name("test_bc_snap_upd_x");

    let mut chain = BindingChain::empty().cons(x_id, BindingValue::eager(Value::int(1)));
    let snapshot = chain.clone();

    // Update head on the live chain (simulates ForAllConst in-place mutation)
    chain.update_head_value(BindingValue::eager(Value::int(99)));

    // Live chain sees the updated value
    match chain.lookup(x_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(99)),
        _ => panic!("expected Eager"),
    }

    // Snapshot still sees the original value -- update_head_value creates a new Rc node
    match snapshot.lookup(x_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(1)),
        _ => panic!("expected Eager"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_concurrent_snapshots_independent() {
    // Multiple snapshots from the same point should be fully independent.
    let x_id = intern_name("test_bc_concurrent_x");
    let a_id = intern_name("test_bc_concurrent_a");
    let b_id = intern_name("test_bc_concurrent_b");

    let base = BindingChain::empty().cons(x_id, BindingValue::eager(Value::int(0)));

    // Two snapshots from the same base
    let snap_a = base.clone();
    let snap_b = base.clone();

    // Each snapshot gets different bindings pushed
    let branch_a = snap_a.cons(a_id, BindingValue::eager(Value::int(1)));
    let branch_b = snap_b.cons(b_id, BindingValue::eager(Value::int(2)));

    // branch_a sees x and a, but not b
    assert!(branch_a.lookup(x_id).is_some());
    assert!(branch_a.lookup(a_id).is_some());
    assert!(branch_a.lookup(b_id).is_none());

    // branch_b sees x and b, but not a
    assert!(branch_b.lookup(x_id).is_some());
    assert!(branch_b.lookup(b_id).is_some());
    assert!(branch_b.lookup(a_id).is_none());

    // Dropping one branch doesn't affect the other
    drop(branch_a);
    assert!(branch_b.lookup(x_id).is_some());
    assert!(branch_b.lookup(b_id).is_some());
}

// --- Arena snapshot isolation tests (Part of #3580 audit) ---
//
// When an arena-backed chain is cloned (snapshotted) and the live chain's head
// is updated via update_head_value(), the snapshot must still see the original
// value. This exercises the COW fix that allocates a fresh arena node instead
// of mutating the shared one in place.

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_snapshot_with_arena_update_head_value() {
    use crate::eval_arena::{init_thread_arena, ArenaStateGuard};

    init_thread_arena();
    let _guard = ArenaStateGuard::new();

    let x_id = intern_name("test_bc_arena_snap_upd_x");

    // Build a chain with arena allocation active.
    let mut chain = BindingChain::empty().cons(x_id, BindingValue::eager(Value::int(1)));

    // Snapshot the chain (cheap pointer copy for arena nodes).
    let snapshot = chain.clone();

    // Update head value on the live chain. Before the COW fix, this mutated the
    // shared arena node and the snapshot would see the new value.
    chain.update_head_value(BindingValue::eager(Value::int(99)));

    // Live chain sees the updated value.
    match chain.lookup(x_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(99)),
        _ => panic!("expected Eager"),
    }

    // Snapshot must still see the original value (isolation).
    match snapshot.lookup(x_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(1)),
        _ => panic!("expected Eager"),
    }
}

// --- EvalCtx chain_snapshots push/pop simulation tests (Part of #2748) ---
//
// These simulate the exact push_binding / pop_binding / pop_to_mark pattern from
// EvalCtx (core.rs:1340-1470). The chain_snapshots Vec<(usize, BindingChain)> saves
// a (stack_idx, chain.clone()) before each cons_local, and restores from it on pop.

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_push_pop_binding_symmetry() {
    // Simulates EvalCtx: push_binding saves snapshot + cons_local,
    // pop_binding restores from snapshot. After pop, chain must match pre-push state.
    let x_id = intern_name("test_bc_pushpop_x");
    let y_id = intern_name("test_bc_pushpop_y");

    let mut chain = BindingChain::empty().cons(x_id, BindingValue::eager(Value::int(1)));
    let mut chain_snapshots: Vec<(usize, BindingChain)> = vec![];

    // Pre-push state
    assert_eq!(chain.depth(), 1);
    assert!(chain.lookup(y_id).is_none());

    // push_binding: save snapshot, then cons_local
    chain_snapshots.push((0, chain.clone()));
    chain = chain.cons_local(y_id, BindingValue::eager(Value::int(2)), 1);

    // During scope: both bindings visible
    assert_eq!(chain.depth(), 2);
    assert!(chain.lookup(x_id).is_some());
    assert!(chain.lookup(y_id).is_some());

    // pop_binding: restore from snapshot
    let (_, restored) = chain_snapshots.pop().unwrap();
    chain = restored;

    // After pop: matches pre-push state exactly
    assert_eq!(chain.depth(), 1);
    assert!(chain.lookup(x_id).is_some());
    assert!(chain.lookup(y_id).is_none());
    match chain.lookup(x_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(1)),
        _ => panic!("expected Eager"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pop_to_mark_restores_chain() {
    // Simulates EvalCtx::pop_to_mark (core.rs:1411-1435): push N bindings after
    // a mark, then pop back to that mark using the real depth-matching algorithm.
    //
    // Real pop_to_mark uses mark = local_stack.len() (not chain_snapshots.len()),
    // and matches snapshots by depth: entries with depth >= mark are popped,
    // and the entry with depth == mark provides the restored chain state.
    let x_id = intern_name("test_bc_mark_x");
    let y_id = intern_name("test_bc_mark_y");
    let z_id = intern_name("test_bc_mark_z");
    let w_id = intern_name("test_bc_mark_w");

    let mut chain = BindingChain::empty().cons(x_id, BindingValue::eager(Value::int(1)));
    let mut chain_snapshots: Vec<(usize, BindingChain)> = vec![];

    // Mark = simulated local_stack.len() = 1 (x is already on the stack).
    // This matches real production usage where mark captures the stack depth
    // BEFORE new bindings are pushed.
    let mark: usize = 1;

    // Push three bindings (simulating nested quantifiers).
    // Each push saves (stack_idx, chain.clone()) where stack_idx = local_stack.len()
    // before the push. First push has stack_idx == mark.
    chain_snapshots.push((1, chain.clone())); // depth 1 == mark
    chain = chain.cons_local(y_id, BindingValue::eager(Value::int(2)), 1);

    chain_snapshots.push((2, chain.clone())); // depth 2
    chain = chain.cons_local(z_id, BindingValue::eager(Value::int(3)), 2);

    chain_snapshots.push((3, chain.clone())); // depth 3
    chain = chain.cons_local(w_id, BindingValue::eager(Value::int(4)), 3);

    // All four bindings visible
    assert_eq!(chain.depth(), 4);
    assert!(chain.lookup(w_id).is_some());

    // pop_to_mark: real algorithm from core.rs:1419-1433.
    // Walk backwards, pop entries with depth >= mark, restore from depth == mark.
    while let Some(&(depth, _)) = chain_snapshots.last() {
        if depth >= mark {
            let (d, saved_chain) = chain_snapshots.pop().unwrap();
            if d == mark {
                chain = saved_chain;
                break;
            }
        } else {
            break;
        }
    }

    // After pop_to_mark: only x visible, all pushed bindings gone
    assert_eq!(chain.depth(), 1);
    assert!(chain.lookup(x_id).is_some());
    assert!(chain.lookup(y_id).is_none());
    assert!(chain.lookup(z_id).is_none());
    assert!(chain.lookup(w_id).is_none());
    match chain.lookup(x_id).unwrap().0 {
        BindingValueRef::Eager(v) => assert_eq!(Value::from(v), Value::int(1)),
        _ => panic!("expected Eager"),
    }
}
