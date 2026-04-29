// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for [`DiskGraphStore`].

use super::*;
use crate::liveness::checker::CheckMask;
use crate::state::Fingerprint;

fn make_node(fp: u64, tidx: usize) -> BehaviorGraphNode {
    BehaviorGraphNode::new(Fingerprint(fp), tidx)
}

fn make_info(
    successors: Vec<BehaviorGraphNode>,
    parent: Option<BehaviorGraphNode>,
    depth: usize,
) -> NodeInfo {
    NodeInfo {
        successors,
        parent,
        depth,
        state_check_mask: CheckMask::new(),
        action_check_masks: Vec::new(),
    }
}

#[test]
fn test_append_and_read_single_node() {
    let dir = tempfile::tempdir().unwrap();
    let mut store = DiskGraphStore::with_capacity(dir.path(), 64).unwrap();

    let node = make_node(42, 0);
    let info = make_info(vec![], None, 0);

    store.append_node(node, &info).unwrap();
    assert_eq!(store.node_count(), 1);
    assert!(store.contains(node));

    let read_info = store.read_node(node).unwrap().unwrap();
    assert_eq!(read_info.depth, 0);
    assert!(read_info.successors.is_empty());
    assert!(read_info.parent.is_none());
}

#[test]
fn test_append_and_read_with_successors() {
    let dir = tempfile::tempdir().unwrap();
    let mut store = DiskGraphStore::with_capacity(dir.path(), 64).unwrap();

    let parent = make_node(10, 0);
    let child = make_node(20, 1);
    let succ_a = make_node(30, 0);
    let succ_b = make_node(40, 2);

    let parent_info = make_info(vec![child], None, 0);
    let child_info = make_info(vec![succ_a, succ_b], Some(parent), 1);

    store.append_node(parent, &parent_info).unwrap();
    store.append_node(child, &child_info).unwrap();

    let read_child = store.read_node(child).unwrap().unwrap();
    assert_eq!(read_child.parent, Some(parent));
    assert_eq!(read_child.depth, 1);
    assert_eq!(read_child.successors.len(), 2);
    assert_eq!(read_child.successors[0], succ_a);
    assert_eq!(read_child.successors[1], succ_b);
}

#[test]
fn test_missing_node_returns_none() {
    let dir = tempfile::tempdir().unwrap();
    let mut store = DiskGraphStore::with_capacity(dir.path(), 64).unwrap();

    let node = make_node(99, 0);
    assert!(!store.contains(node));
    assert!(store.read_node(node).unwrap().is_none());
}

#[test]
fn test_multiple_nodes_random_access() {
    let dir = tempfile::tempdir().unwrap();
    let mut store = DiskGraphStore::with_capacity(dir.path(), 256).unwrap();

    // Append 50 nodes.
    let nodes: Vec<BehaviorGraphNode> = (1..=50)
        .map(|i| make_node(i * 100, (i % 3) as usize))
        .collect();

    for (i, &node) in nodes.iter().enumerate() {
        let info = make_info(vec![], None, i);
        store.append_node(node, &info).unwrap();
    }
    assert_eq!(store.node_count(), 50);

    // Read in reverse order (forces disk reads for cache misses).
    for (i, &node) in nodes.iter().enumerate().rev() {
        let read_info = store.read_node(node).unwrap().unwrap();
        assert_eq!(read_info.depth, i);
    }
}

#[test]
fn test_cache_hit_avoids_disk_read() {
    let dir = tempfile::tempdir().unwrap();
    let mut store = DiskGraphStore::with_capacity(dir.path(), 64).unwrap();

    let node = make_node(42, 0);
    let info = make_info(vec![make_node(99, 1)], None, 7);
    store.append_node(node, &info).unwrap();

    // First read populates cache via append.
    // Second read should hit cache.
    let read1 = store.read_node(node).unwrap().unwrap();
    let read2 = store.read_node(node).unwrap().unwrap();
    assert_eq!(read1.depth, read2.depth);
    assert_eq!(read1.successors, read2.successors);
}

#[test]
fn test_init_nodes_tracking() {
    let dir = tempfile::tempdir().unwrap();
    let mut store = DiskGraphStore::with_capacity(dir.path(), 64).unwrap();

    let node_a = make_node(1, 0);
    let node_b = make_node(2, 0);

    store.mark_init_node(node_a);
    store.mark_init_node(node_b);

    assert_eq!(store.init_nodes().len(), 2);
    assert_eq!(store.init_nodes()[0], node_a);
    assert_eq!(store.init_nodes()[1], node_b);
}

#[test]
fn test_with_check_masks() {
    let dir = tempfile::tempdir().unwrap();
    let mut store = DiskGraphStore::with_capacity(dir.path(), 64).unwrap();

    let node = make_node(42, 0);
    let succ = make_node(99, 1);

    let mut state_mask = CheckMask::new();
    state_mask.set(3);
    state_mask.set(64); // multi-word

    let mut action_mask = CheckMask::new();
    action_mask.set(7);

    let info = NodeInfo {
        successors: vec![succ],
        parent: None,
        depth: 0,
        state_check_mask: state_mask,
        action_check_masks: vec![action_mask],
    };

    store.append_node(node, &info).unwrap();

    // Invalidate cache to force disk read.
    store.cache[DiskGraphStore::cache_index(node)] = None;

    let read_info = store.read_node(node).unwrap().unwrap();
    assert!(read_info.state_check_mask.get(3));
    assert!(read_info.state_check_mask.get(64));
    assert!(!read_info.state_check_mask.get(4));
    assert!(read_info.action_check_masks[0].get(7));
}

#[test]
fn test_update_node_rewrites_pointer_and_preserves_count() {
    let dir = tempfile::tempdir().unwrap();
    let mut store = DiskGraphStore::with_capacity(dir.path(), 64).unwrap();

    let node = make_node(42, 0);
    store
        .append_node(node, &make_info(vec![], None, 0))
        .unwrap();
    let mut updated = make_info(vec![make_node(7, 1)], None, 9);
    updated.state_check_mask.set(3);

    store.update_node(node, &updated).unwrap();

    assert_eq!(store.node_count(), 1);
    assert_eq!(store.all_nodes(), &[node]);

    let read_info = store.read_node(node).unwrap().unwrap();
    assert_eq!(read_info.depth, 9);
    assert_eq!(read_info.successors, vec![make_node(7, 1)]);
    assert!(read_info.state_check_mask.get(3));
}

#[test]
fn test_update_node_succeeds_at_pointer_table_load_limit() {
    let dir = tempfile::tempdir().unwrap();
    let mut store = DiskGraphStore::with_capacity(dir.path(), 4).unwrap();

    let node_a = make_node(11, 0);
    let node_b = make_node(22, 0);
    let node_c = make_node(33, 0);
    store
        .append_node(node_a, &make_info(vec![], None, 0))
        .unwrap();
    store
        .append_node(node_b, &make_info(vec![], None, 1))
        .unwrap();
    store
        .append_node(node_c, &make_info(vec![], None, 2))
        .unwrap();

    let updated = make_info(vec![make_node(44, 1)], Some(node_a), 7);
    store.update_node(node_b, &updated).unwrap();

    let read_info = store.read_node(node_b).unwrap().unwrap();
    assert_eq!(read_info.parent, Some(node_a));
    assert_eq!(read_info.depth, 7);
    assert_eq!(read_info.successors, vec![make_node(44, 1)]);
    assert_eq!(store.node_count(), 3);
}

#[test]
fn test_flush() {
    let dir = tempfile::tempdir().unwrap();
    let mut store = DiskGraphStore::with_capacity(dir.path(), 64).unwrap();

    let node = make_node(42, 0);
    let info = make_info(vec![], None, 0);
    store.append_node(node, &info).unwrap();

    // Flush should not error.
    store.flush().unwrap();
}

#[test]
fn test_same_fp_different_tidx() {
    let dir = tempfile::tempdir().unwrap();
    let mut store = DiskGraphStore::with_capacity(dir.path(), 64).unwrap();

    // Same state fingerprint, different tableau indices.
    let node_a = make_node(42, 0);
    let node_b = make_node(42, 1);
    let node_c = make_node(42, 2);

    store
        .append_node(node_a, &make_info(vec![], None, 0))
        .unwrap();
    store
        .append_node(node_b, &make_info(vec![], None, 1))
        .unwrap();
    store
        .append_node(node_c, &make_info(vec![], None, 2))
        .unwrap();

    assert_eq!(store.node_count(), 3);

    // Each has a distinct record.
    assert_eq!(store.read_node(node_a).unwrap().unwrap().depth, 0);
    assert_eq!(store.read_node(node_b).unwrap().unwrap().depth, 1);
    assert_eq!(store.read_node(node_c).unwrap().unwrap().depth, 2);
}
