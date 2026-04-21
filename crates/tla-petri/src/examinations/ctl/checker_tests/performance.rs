// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::support::{atom_at_least, test_net};
use crate::examinations::ctl::checker::CtlChecker;
use crate::examinations::ctl::resolve::ResolvedCtl;
use crate::explorer::{FullReachabilityGraph, ReachabilityGraph};

/// Performance regression test: EG on a linear chain is O(V+E), not O(V²).
///
/// A chain of N states where all satisfy φ except the terminal dead-end:
///   s0 → s1 → s2 → ... → s_{n-2} → s_{n-1}  (s_{n-1} is dead-end, φ=false)
///
/// The naive O(V²) implementation removes one state per full scan of all V
/// states, requiring ~V iterations × V states = V² operations.
/// The worklist implementation removes all states in a single backward pass:
/// O(V+E) = O(V) for a chain.
///
/// With N=50_000, O(V²) = 2.5 billion operations (~10s+). O(V) = 50K (~<10ms).
#[test]
fn test_gfp_eg_linear_chain_performance() {
    let n = 50_000usize;
    // Chain: s0 → s1 → ... → s_{n-2} → s_{n-1} (dead-end).
    // All states have marking [1] (φ = "place0 >= 1") except s_{n-1} which
    // has marking [0] (φ = false). Dead-end with φ=false is immediately
    // removed; removal cascades backward through the entire chain.
    let adj: Vec<Vec<u32>> = (0..n)
        .map(|i| {
            if i < n - 1 {
                vec![(i + 1) as u32]
            } else {
                vec![] // dead-end
            }
        })
        .collect();
    let markings: Vec<Vec<u64>> = (0..n)
        .map(|i| {
            if i < n - 1 {
                vec![1u64]
            } else {
                vec![0u64] // φ = false at terminal
            }
        })
        .collect();

    let full = FullReachabilityGraph {
        graph: ReachabilityGraph {
            num_states: n as u32,
            adj: adj
                .into_iter()
                .map(|succs| succs.into_iter().map(|s| (s, 0u32)).collect())
                .collect(),
            completed: true,
        },
        markings,
    };
    let net = test_net(1);
    let checker = CtlChecker::new(&full, &net);

    let start = std::time::Instant::now();
    let result = checker.eval(&ResolvedCtl::EG(Box::new(atom_at_least(0, 1))));
    let elapsed = start.elapsed();

    // Every state should be false: the chain leads to a dead-end where φ is
    // false, so no state has an infinite path satisfying φ.
    assert!(result.iter().all(|&v| !v), "all states should be false");

    // The worklist O(V+E) implementation should finish in well under 1 second.
    // The naive O(V²) implementation on 50K states takes ~10+ seconds.
    assert!(
        elapsed.as_millis() < 1_000,
        "gfp_eg on {n}-state chain took {}ms (>1000ms = likely O(V²) regression)",
        elapsed.as_millis()
    );
}

/// Performance regression test: EG on a cycle preserves all states in O(V+E).
///
/// A ring of N states where all satisfy φ. Every state has a successor in
/// the set, so EG(φ) should be true for all states. The worklist should
/// never enqueue any state (all successor counts remain > 0).
#[test]
fn test_gfp_eg_cycle_all_true_performance() {
    let n = 50_000usize;
    let adj: Vec<Vec<u32>> = (0..n).map(|i| vec![((i + 1) % n) as u32]).collect();
    let markings: Vec<Vec<u64>> = vec![vec![1u64]; n];

    let full = FullReachabilityGraph {
        graph: ReachabilityGraph {
            num_states: n as u32,
            adj: adj
                .into_iter()
                .map(|succs| succs.into_iter().map(|s| (s, 0u32)).collect())
                .collect(),
            completed: true,
        },
        markings,
    };
    let net = test_net(1);
    let checker = CtlChecker::new(&full, &net);

    let start = std::time::Instant::now();
    let result = checker.eval(&ResolvedCtl::EG(Box::new(atom_at_least(0, 1))));
    let elapsed = start.elapsed();

    // All states should be true: the ring provides an infinite path.
    assert!(
        result.iter().all(|&v| v),
        "all states on cycle should be true"
    );

    assert!(
        elapsed.as_millis() < 1_000,
        "gfp_eg on {n}-state cycle took {}ms (>1000ms = likely O(V²) regression)",
        elapsed.as_millis()
    );
}
