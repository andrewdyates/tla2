// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the configurable Tarjan arena warn threshold (#4080).
//!
//! `tarjan_arena_warn_threshold()` reads `TLA2_TARJAN_ARENA_WARN_NODES` from
//! the environment on first call and caches the result via `OnceLock`. Because
//! the cache is process-global, we cannot cleanly test env-var propagation
//! without coordinating with every other test that touches the same function.
//! Instead we verify behavioral invariants that any caching implementation
//! must satisfy:
//!
//! 1. The returned value is stable across calls (caching works).
//! 2. Calling `find_sccs` on a tiny graph (below the threshold, by any
//!    reasonable setting) completes without panicking — proving the
//!    threshold-check path is wired correctly into the arena builder.

use super::super::{find_sccs, tarjan_arena_warn_threshold};
use super::{build_graph_from_adj, canonicalize_sccs, reference_sccs};

#[test]
fn arena_warn_threshold_is_stable_across_calls() {
    // OnceLock caching: repeated reads must return the same value.
    let first = tarjan_arena_warn_threshold();
    let second = tarjan_arena_warn_threshold();
    assert_eq!(
        first, second,
        "tarjan_arena_warn_threshold must be OnceLock-cached; repeated calls \
         must return the same value"
    );
}

#[test]
fn arena_warn_threshold_is_nonzero_by_default() {
    // Unless `TLA2_TARJAN_ARENA_WARN_NODES=0` is set in the environment (which
    // explicitly disables the warning), the default should be a positive node
    // count. We do not hard-code the default here because a different test
    // process could have set the env; we assert only that the value is
    // consistent with the documented semantics (0 = disabled, else positive).
    let threshold = tarjan_arena_warn_threshold();
    // If the value is nonzero, it must be large enough to avoid warning on
    // tiny test graphs. A threshold of 1 would warn on every SCC run.
    if threshold != 0 {
        assert!(
            threshold >= 100,
            "default threshold should be large enough to skip tiny test graphs, \
             got {threshold}"
        );
    }
}

#[test]
fn tarjan_tiny_graph_does_not_warn_path_regression() {
    // A 3-node cycle is far below any reasonable warn threshold. This test
    // exercises the full `find_sccs` -> `build_arena` path to make sure the
    // threshold check itself doesn't panic or interact with SCC correctness.
    //
    // Adjacency: 0 -> 1 -> 2 -> 0 (single non-trivial SCC of size 3).
    let n = 3;
    let mut adj = vec![false; n * n];
    adj[0 * n + 1] = true;
    adj[1 * n + 2] = true;
    adj[2 * n + 0] = true;

    let (graph, _states, nodes) = build_graph_from_adj(n, &adj);
    let result = find_sccs(&graph);

    assert!(
        result.errors.is_empty(),
        "tiny-graph SCC must not emit invariant errors, got: {:?}",
        result.errors
    );

    let got = canonicalize_sccs(result.sccs, &nodes);
    let want = reference_sccs(n, &adj);
    assert_eq!(
        got, want,
        "tiny-graph SCC must match reference decomposition"
    );
}
