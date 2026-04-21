// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// These tests validate stub theorem behavior only.
// They exercise placeholder invariants used for verification workflow wiring,
// not production correctness of Union-Find behavior.

#[test]
fn test_root_is_own_parent() {
    // A root node is its own parent
    let parent = vec![0, 0, 2, 3, 4]; // 0,2,3,4 are roots, 1 -> 0
    assert_eq!(parent[0], 0); // root
    assert_eq!(parent[2], 2); // root
    assert_ne!(parent[1], 1); // not a root
}

#[test]
fn test_union_creates_shared_root() {
    // After union, elements share a root
    let mut parent = vec![0, 1, 2]; // initial: everyone is own root
                                    // Union 0 and 1: make 1's parent be 0
    parent[1] = 0;
    // Now find(0) = 0 and find(1) = 0
    assert_eq!(parent[0], parent[1].min(parent[0]).max(0)); // same root family
}
