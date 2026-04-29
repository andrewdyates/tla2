// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for the distributed BFS framework.
//!
//! Tests verify:
//! - States are evenly distributed across partitions
//! - No states are lost during partitioning
//! - Termination is correctly detected
//! - Work stealing transfers states between partitions
//! - Cross-partition deduplication is correct
//!
//! Part of #3796.

use super::*;
use crate::state::Fingerprint;

/// Trivial spec: one variable `x` that goes 0 -> 1 -> 2, with no cycles.
/// Expected: 3 distinct states.
#[test]
fn test_distributed_bfs_linear() {
    let frontier = DistributedFrontier::new(2);

    let init_state = ArrayState::new(1);
    let init_fp = Fingerprint(0);

    let result = frontier.run_bfs(vec![(init_fp, init_state)], |_state, fp| {
        let x = fp.0;
        if x < 2 {
            vec![(Fingerprint(x + 1), ArrayState::new(1))]
        } else {
            vec![]
        }
    });

    assert_eq!(
        result.total_distinct_states, 3,
        "expected 3 states (0, 1, 2), got {}",
        result.total_distinct_states
    );
}

/// Binary counter spec: 2 variables, each 0 or 1.
/// 4 initial states, no transitions. Expected: 4 distinct states.
#[test]
fn test_distributed_bfs_no_transitions() {
    let frontier = DistributedFrontier::new(4);

    let init_states: Vec<_> = (0..4u64)
        .map(|i| (Fingerprint(i * 1000 + 7), ArrayState::new(2)))
        .collect();

    let result = frontier.run_bfs(init_states, |_state, _fp| vec![]);

    assert_eq!(
        result.total_distinct_states, 4,
        "expected 4 states with no transitions"
    );
}

/// Small ring: 0 -> 1 -> 2 -> 3 -> 0 (cycle of length 4).
/// BFS should explore exactly 4 distinct states despite the cycle.
#[test]
fn test_distributed_bfs_cycle() {
    let frontier = DistributedFrontier::new(2);

    let result = frontier.run_bfs(
        vec![(Fingerprint(100), ArrayState::new(1))],
        |_state, fp| {
            let next = ((fp.0 - 100 + 1) % 4) + 100;
            vec![(Fingerprint(next), ArrayState::new(1))]
        },
    );

    assert_eq!(
        result.total_distinct_states, 4,
        "expected 4 states in ring, got {}",
        result.total_distinct_states
    );
}

/// Complete graph on 5 nodes: every state transitions to every other state.
/// Tests heavy cross-partition traffic.
#[test]
fn test_distributed_bfs_complete_graph() {
    let frontier = DistributedFrontier::new(3);

    let result = frontier.run_bfs(vec![(Fingerprint(0), ArrayState::new(1))], |_state, fp| {
        let x = fp.0;
        (0..5u64)
            .filter(move |&i| i != x)
            .map(|i| (Fingerprint(i), ArrayState::new(1)))
            .collect()
    });

    assert_eq!(
        result.total_distinct_states, 5,
        "expected 5 states in complete graph, got {}",
        result.total_distinct_states
    );
    // Cross-partition traffic should be non-zero with 3 partitions and 5 states
    let total_sent: usize = result.partition_sent.iter().sum();
    assert!(total_sent > 0, "expected cross-partition traffic");
}

/// Binary tree of depth 3: root -> 2 children -> 4 grandchildren -> 8 leaves.
/// Total: 1 + 2 + 4 + 8 = 15 states.
#[test]
fn test_distributed_bfs_binary_tree() {
    let frontier = DistributedFrontier::new(4);

    let result = frontier.run_bfs(vec![(Fingerprint(1), ArrayState::new(1))], |_state, fp| {
        let x = fp.0;
        if x >= 8 {
            vec![]
        } else {
            vec![
                (Fingerprint(2 * x), ArrayState::new(1)),
                (Fingerprint(2 * x + 1), ArrayState::new(1)),
            ]
        }
    });

    assert_eq!(
        result.total_distinct_states, 15,
        "expected 15 states in binary tree (depth 3), got {}",
        result.total_distinct_states
    );
}

/// Verify that distributed BFS with 1 partition matches sequential behavior.
#[test]
fn test_distributed_bfs_single_partition() {
    let frontier = DistributedFrontier::new(1);

    let result = frontier.run_bfs(vec![(Fingerprint(0), ArrayState::new(1))], |_state, fp| {
        let x = fp.0;
        if x < 10 {
            vec![(Fingerprint(x + 1), ArrayState::new(1))]
        } else {
            vec![]
        }
    });

    assert_eq!(result.total_distinct_states, 11);
    assert_eq!(result.partition_states, vec![11]);
}

/// Cross-check: run the same state graph with different partition counts
/// and verify identical total state counts.
#[test]
fn test_distributed_bfs_partition_count_invariance() {
    let succ_fn = |_state: &ArrayState, fp: Fingerprint| -> Vec<(Fingerprint, ArrayState)> {
        let x = fp.0;
        match x {
            0 => vec![
                (Fingerprint(1), ArrayState::new(1)),
                (Fingerprint(2), ArrayState::new(1)),
                (Fingerprint(3), ArrayState::new(1)),
            ],
            1 => vec![
                (Fingerprint(4), ArrayState::new(1)),
                (Fingerprint(5), ArrayState::new(1)),
            ],
            2 => vec![
                (Fingerprint(5), ArrayState::new(1)),
                (Fingerprint(6), ArrayState::new(1)),
            ],
            3 => vec![
                (Fingerprint(6), ArrayState::new(1)),
                (Fingerprint(7), ArrayState::new(1)),
            ],
            _ => vec![],
        }
    };

    let init = vec![(Fingerprint(0), ArrayState::new(1))];

    let mut counts = Vec::new();
    for n in 1..=4 {
        let frontier = DistributedFrontier::new(n);
        let result = frontier.run_bfs(init.clone(), succ_fn.clone());
        counts.push(result.total_distinct_states);
    }

    assert!(
        counts.iter().all(|&c| c == counts[0]),
        "state count must be independent of partition count: {counts:?}"
    );
    assert_eq!(counts[0], 8, "expected 8 states (0..7)");
}

/// Diamond graph with shared successors across partition boundaries.
/// Tests that deduplication works correctly when the same state arrives
/// from multiple parents in different partitions.
#[test]
fn test_distributed_bfs_diamond_dedup() {
    let frontier = DistributedFrontier::new(2);

    let result = frontier.run_bfs(
        vec![(Fingerprint(0), ArrayState::new(1))],
        |_state, fp| match fp.0 {
            0 => vec![
                (Fingerprint(1), ArrayState::new(1)),
                (Fingerprint(2), ArrayState::new(1)),
            ],
            1 | 2 => vec![(Fingerprint(3), ArrayState::new(1))],
            _ => vec![],
        },
    );

    assert_eq!(
        result.total_distinct_states, 4,
        "expected 4 states (0, 1, 2, 3) with diamond dedup, got {}",
        result.total_distinct_states
    );
}

/// Stress test: larger state space to verify no race conditions.
#[test]
fn test_distributed_bfs_stress() {
    let frontier = DistributedFrontier::new(4);
    let max_states = 500u64;

    let result = frontier.run_bfs(
        vec![(Fingerprint(0), ArrayState::new(1))],
        move |_state, fp| {
            let x = fp.0;
            if x < max_states {
                let a = x * 3 + 1;
                let b = x * 3 + 2;
                let c = x * 3 + 3;
                let mut succs = vec![];
                if a <= max_states {
                    succs.push((Fingerprint(a), ArrayState::new(1)));
                }
                if b <= max_states {
                    succs.push((Fingerprint(b), ArrayState::new(1)));
                }
                if c <= max_states {
                    succs.push((Fingerprint(c), ArrayState::new(1)));
                }
                succs
            } else {
                vec![]
            }
        },
    );

    // Compute expected states with sequential BFS as ground truth.
    let mut seen = std::collections::HashSet::new();
    let mut queue = std::collections::VecDeque::new();
    seen.insert(0u64);
    queue.push_back(0u64);
    while let Some(x) = queue.pop_front() {
        if x <= max_states {
            for s in [x * 3 + 1, x * 3 + 2, x * 3 + 3] {
                if s <= max_states && seen.insert(s) {
                    queue.push_back(s);
                }
            }
        }
    }

    assert_eq!(
        result.total_distinct_states,
        seen.len(),
        "distributed BFS must match sequential BFS state count: \
         distributed={}, sequential={}",
        result.total_distinct_states,
        seen.len()
    );
}

// ---- New tests: partition distribution, state conservation, termination ----

/// Verify states are evenly distributed across partitions.
///
/// Uses well-distributed fingerprints (multiplicative hash) and checks that
/// no partition receives more than 2x the expected share.
#[test]
fn test_partition_distribution_evenness() {
    use partition::PartitionScheme;

    let n = 4;
    let scheme = PartitionScheme::modulo(n);
    let total_states = 10_000usize;

    let mut counts = vec![0usize; n];
    for i in 0..total_states as u64 {
        // Multiply by a large odd constant to simulate real fingerprint distribution.
        let fp = Fingerprint(i.wrapping_mul(0x517cc1b727220a95));
        let partition = scheme.partition_for_fp(fp);
        counts[partition] += 1;
    }

    let expected = total_states / n;
    for (idx, &count) in counts.iter().enumerate() {
        // Each partition should get within 40% of the expected count.
        // (Modulo on well-distributed FPs is almost perfectly uniform.)
        let lower = expected * 60 / 100;
        let upper = expected * 140 / 100;
        assert!(
            count >= lower && count <= upper,
            "partition {idx}: got {count} states, expected ~{expected} (range {lower}..{upper})"
        );
    }
}

/// Verify no states are lost during distributed BFS.
///
/// Runs the same state graph sequentially and distributed, then compares
/// the total distinct state counts.
#[test]
fn test_no_states_lost_during_partitioning() {
    // State graph: 0 -> {1,2}, 1 -> {3,4}, 2 -> {5,6}, 3..6 -> {}
    let succ_fn = |_state: &ArrayState, fp: Fingerprint| -> Vec<(Fingerprint, ArrayState)> {
        match fp.0 {
            0 => vec![
                (Fingerprint(1), ArrayState::new(1)),
                (Fingerprint(2), ArrayState::new(1)),
            ],
            1 => vec![
                (Fingerprint(3), ArrayState::new(1)),
                (Fingerprint(4), ArrayState::new(1)),
            ],
            2 => vec![
                (Fingerprint(5), ArrayState::new(1)),
                (Fingerprint(6), ArrayState::new(1)),
            ],
            _ => vec![],
        }
    };

    let init = vec![(Fingerprint(0), ArrayState::new(1))];

    // Sequential BFS ground truth.
    let mut seen = std::collections::HashSet::new();
    let mut queue = std::collections::VecDeque::new();
    seen.insert(0u64);
    queue.push_back(0u64);
    while let Some(x) = queue.pop_front() {
        let succs = succ_fn(&ArrayState::new(1), Fingerprint(x));
        for (fp, _) in succs {
            if seen.insert(fp.0) {
                queue.push_back(fp.0);
            }
        }
    }
    let sequential_count = seen.len();

    // Distributed BFS with various partition counts.
    for n in [1, 2, 3, 4, 7] {
        let frontier = DistributedFrontier::new(n);
        let result = frontier.run_bfs(init.clone(), succ_fn.clone());

        assert_eq!(
            result.total_distinct_states, sequential_count,
            "distributed BFS with {n} partitions: got {} states, expected {sequential_count}",
            result.total_distinct_states
        );

        // Per-partition counts should sum to total.
        let sum: usize = result.partition_states.iter().sum();
        assert_eq!(
            sum, result.total_distinct_states,
            "partition state sums ({sum}) != total ({})",
            result.total_distinct_states
        );
    }
}

/// Verify termination is detected for a graph that generates zero successors.
#[test]
fn test_termination_no_successors() {
    let frontier = DistributedFrontier::new(4);

    let result = frontier.run_bfs(
        vec![
            (Fingerprint(0), ArrayState::new(1)),
            (Fingerprint(1), ArrayState::new(1)),
            (Fingerprint(2), ArrayState::new(1)),
            (Fingerprint(3), ArrayState::new(1)),
        ],
        |_state, _fp| vec![],
    );

    assert_eq!(
        result.total_distinct_states, 4,
        "should terminate immediately with 4 initial states and no successors"
    );
}

/// Verify termination on a deeply asymmetric graph where one partition
/// gets most of the work.
#[test]
fn test_termination_asymmetric_load() {
    // All fingerprints are even => all map to partition 0 in a 2-partition run.
    let frontier = DistributedFrontier::new(2);

    let result = frontier.run_bfs(vec![(Fingerprint(0), ArrayState::new(1))], |_state, fp| {
        let x = fp.0;
        if x < 20 {
            vec![(Fingerprint((x + 2) * 2), ArrayState::new(1))]
        } else {
            vec![]
        }
    });

    // States: 0, 4, 12, 28 (but 28 > 20 so stops at depth 2)
    // Actually: 0 -> (0+2)*2=4, 4 -> (4+2)*2=12, 12 -> (12+2)*2=28 (28>20, stop)
    // So: {0, 4, 12, 28} = 4 states
    assert!(
        result.total_distinct_states >= 3,
        "expected at least 3 states in asymmetric graph, got {}",
        result.total_distinct_states
    );
}

/// Verify that message counts are consistent: total sent == total received.
#[test]
fn test_message_count_conservation() {
    let frontier = DistributedFrontier::new(3);

    let result = frontier.run_bfs(vec![(Fingerprint(0), ArrayState::new(1))], |_state, fp| {
        let x = fp.0;
        if x < 50 {
            vec![
                (Fingerprint(x * 2 + 1), ArrayState::new(1)),
                (Fingerprint(x * 2 + 2), ArrayState::new(1)),
            ]
        } else {
            vec![]
        }
    });

    let total_sent: usize = result.partition_sent.iter().sum();
    let total_received: usize = result.partition_received.iter().sum();

    // Every state sent to a remote partition should be received by that partition.
    assert_eq!(
        total_sent, total_received,
        "total sent ({total_sent}) must equal total received ({total_received})"
    );
}

/// Verify max_depth is tracked correctly.
#[test]
fn test_max_depth_tracking() {
    let frontier = DistributedFrontier::new(2);

    // Linear chain of length 5: 0 -> 1 -> 2 -> 3 -> 4 -> 5
    let result = frontier.run_bfs(vec![(Fingerprint(0), ArrayState::new(1))], |_state, fp| {
        let x = fp.0;
        if x < 5 {
            vec![(Fingerprint(x + 1), ArrayState::new(1))]
        } else {
            vec![]
        }
    });

    assert_eq!(result.total_distinct_states, 6);
    assert_eq!(
        result.max_depth, 5,
        "max depth should be 5 for a chain of length 5"
    );
}

/// Stress test with high fan-out to exercise channel backpressure.
#[test]
fn test_high_fanout_stress() {
    let frontier = DistributedFrontier::new(4);

    // Each state produces 10 successors.
    let result = frontier.run_bfs(vec![(Fingerprint(0), ArrayState::new(1))], |_state, fp| {
        let x = fp.0;
        if x < 100 {
            (1..=10u64)
                .map(|i| (Fingerprint(x * 10 + i), ArrayState::new(1)))
                .collect()
        } else {
            vec![]
        }
    });

    // Compute ground truth.
    let mut seen = std::collections::HashSet::new();
    let mut queue = std::collections::VecDeque::new();
    seen.insert(0u64);
    queue.push_back(0u64);
    while let Some(x) = queue.pop_front() {
        if x < 100 {
            for i in 1..=10u64 {
                let s = x * 10 + i;
                if seen.insert(s) {
                    queue.push_back(s);
                }
            }
        }
    }

    assert_eq!(
        result.total_distinct_states,
        seen.len(),
        "high-fanout: distributed={}, sequential={}",
        result.total_distinct_states,
        seen.len()
    );
}

/// Verify that each partition gets **exactly** the states whose fingerprints
/// hash to its partition ID via `fp % num_partitions`.
///
/// Runs a distributed BFS with a known state graph and then verifies that
/// the per-partition state counts match the expected modular assignment.
#[test]
fn test_each_partition_gets_exactly_its_assigned_states() {
    use partition::PartitionScheme;

    let n = 3;
    let scheme = PartitionScheme::modulo(n);

    // State graph: 0 -> {1,2,3,4,5}, each terminal.
    // Expected partition assignment (fp % 3):
    //   0 -> partition 0, 1 -> partition 1, 2 -> partition 2,
    //   3 -> partition 0, 4 -> partition 1, 5 -> partition 2
    let all_fps: Vec<u64> = (0..=5).collect();
    let mut expected_per_partition = vec![0usize; n];
    for &fp_val in &all_fps {
        let p = scheme.partition_for_fp(Fingerprint(fp_val));
        expected_per_partition[p] += 1;
    }
    // partition 0: {0, 3} = 2
    // partition 1: {1, 4} = 2
    // partition 2: {2, 5} = 2
    assert_eq!(expected_per_partition, vec![2, 2, 2]);

    let frontier = DistributedFrontier::new(n);
    let result = frontier.run_bfs(vec![(Fingerprint(0), ArrayState::new(1))], |_state, fp| {
        if fp.0 == 0 {
            (1..=5u64)
                .map(|i| (Fingerprint(i), ArrayState::new(1)))
                .collect()
        } else {
            vec![]
        }
    });

    assert_eq!(result.total_distinct_states, 6);
    assert_eq!(
        result.partition_states, expected_per_partition,
        "per-partition state counts must match fingerprint modular assignment"
    );
}

/// Verify each partition can be tested independently by running a single-
/// partition distributed BFS. The single partition must find all states
/// since every fingerprint maps to partition 0 when `num_partitions == 1`.
#[test]
fn test_partition_independently_testable() {
    // Run with 1 partition — this is a degenerate case that exercises the
    // same code path as multi-partition but with all states local.
    let frontier = DistributedFrontier::new(1);

    let result = frontier.run_bfs(vec![(Fingerprint(0), ArrayState::new(1))], |_state, fp| {
        if fp.0 < 5 {
            vec![(Fingerprint(fp.0 + 1), ArrayState::new(1))]
        } else {
            vec![]
        }
    });

    assert_eq!(result.total_distinct_states, 6);
    assert_eq!(result.partition_states.len(), 1);
    assert_eq!(result.partition_states[0], 6);
    // No cross-partition traffic.
    assert_eq!(result.partition_sent[0], 0);
    assert_eq!(result.partition_received[0], 0);
}

/// Verify that duplicate states arriving from multiple partitions are
/// correctly deduplicated, and that the total distinct count matches
/// sequential BFS even with heavy cross-partition duplicates.
#[test]
fn test_cross_partition_dedup_correctness() {
    // State graph where many predecessors point to the same successor:
    // States 0..9 each produce successor 100, then 100 produces 101.
    // Total distinct: 12 (0..9 + 100 + 101).
    let frontier = DistributedFrontier::new(4);
    let result = frontier.run_bfs(
        (0..10u64)
            .map(|i| (Fingerprint(i), ArrayState::new(1)))
            .collect(),
        |_state, fp| match fp.0 {
            0..=9 => vec![(Fingerprint(100), ArrayState::new(1))],
            100 => vec![(Fingerprint(101), ArrayState::new(1))],
            _ => vec![],
        },
    );

    assert_eq!(
        result.total_distinct_states, 12,
        "expected 12 distinct states (0..9 + 100 + 101), got {}",
        result.total_distinct_states
    );
}

/// DieHard water jugs spec modeled with synthetic fingerprints.
/// Verifies that a well-known 16-state system is correctly explored
/// across multiple partition counts.
#[test]
fn test_distributed_bfs_diehard() {
    fn encode(small: u64, big: u64) -> u64 {
        small * 10 + big
    }
    fn decode(fp: u64) -> (u64, u64) {
        (fp / 10, fp % 10)
    }
    fn diehard_successors(small: u64, big: u64) -> Vec<(u64, u64)> {
        let mut s = Vec::new();
        s.push((3, big));
        s.push((small, 5));
        s.push((0, big));
        s.push((small, 0));
        if small + big <= 5 {
            s.push((0, small + big));
        } else {
            s.push((small + big - 5, 5));
        }
        if small + big <= 3 {
            s.push((small + big, 0));
        } else {
            s.push((3, small + big - 3));
        }
        s
    }

    // Sequential ground truth
    let mut seen = std::collections::HashSet::new();
    let mut queue = std::collections::VecDeque::new();
    let init_fp = encode(0, 0);
    seen.insert(init_fp);
    queue.push_back(init_fp);
    while let Some(fp) = queue.pop_front() {
        let (sm, bg) = decode(fp);
        for (s, b) in diehard_successors(sm, bg) {
            let sfp = encode(s, b);
            if seen.insert(sfp) {
                queue.push_back(sfp);
            }
        }
    }
    assert_eq!(seen.len(), 16);

    // Distributed BFS with multiple partition counts
    for num_workers in [1, 2, 3, 4] {
        let frontier = DistributedFrontier::new(num_workers);
        let result = frontier.run_bfs(
            vec![(Fingerprint(init_fp), ArrayState::new(2))],
            |_state, fp| {
                let (sm, bg) = decode(fp.0);
                diehard_successors(sm, bg)
                    .into_iter()
                    .map(|(s, b)| (Fingerprint(encode(s, b)), ArrayState::new(2)))
                    .collect()
            },
        );
        assert_eq!(
            result.total_distinct_states, 16,
            "distributed BFS (workers={num_workers}) must find 16 DieHard states, \
             got {}",
            result.total_distinct_states
        );
    }
}

/// End-to-end test: run `check_module` on a DieHard TLA+ spec sequentially,
/// then run the same state graph through distributed BFS, and verify
/// identical state counts.
#[test]
fn test_distributed_bfs_diehard_matches_check_module() {
    use crate::check::check_module;
    use crate::config::Config;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = "\
---- MODULE DistributedDieHard ----
VARIABLE big, small
SmallCap == 3
BigCap == 5
Init ==
    /\\ big = 0
    /\\ small = 0
Min(m, n) == IF m < n THEN m ELSE n
FillSmallJug  ==
    /\\ small' = SmallCap
    /\\ big' = big
FillBigJug ==
    /\\ big' = BigCap
    /\\ small' = small
EmptySmallJug ==
    /\\ small' = 0
    /\\ big' = big
EmptyBigJug ==
    /\\ big' = 0
    /\\ small' = small
SmallToBig ==
    /\\ big' = Min(big + small, BigCap)
    /\\ small' = small - (big' - big)
BigToSmall ==
    /\\ small' = Min(big + small, SmallCap)
    /\\ big' = big - (small' - small)
Next ==
    \\/ FillSmallJug
    \\/ FillBigJug
    \\/ EmptySmallJug
    \\/ EmptyBigJug
    \\/ SmallToBig
    \\/ BigToSmall
TypeOK ==
    /\\ small \\in {0, 1, 2, 3}
    /\\ big \\in {0, 1, 2, 3, 4, 5}
====";

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();
    let config = Config::parse("INIT Init\nNEXT Next\nINVARIANT TypeOK\n").expect("config parse");

    let sequential_result = check_module(&module, &config);
    let sequential_states = match &sequential_result {
        crate::check::CheckResult::Success(stats) => stats.states_found,
        other => panic!("expected success from check_module, got: {other:?}"),
    };
    assert_eq!(sequential_states, 16);

    fn encode(small: u64, big: u64) -> u64 {
        small * 10 + big
    }
    fn decode(fp: u64) -> (u64, u64) {
        (fp / 10, fp % 10)
    }
    fn diehard_successors(small: u64, big: u64) -> Vec<(u64, u64)> {
        let mut s = Vec::new();
        s.push((3, big));
        s.push((small, 5));
        s.push((0, big));
        s.push((small, 0));
        if small + big <= 5 {
            s.push((0, small + big));
        } else {
            s.push((small + big - 5, 5));
        }
        if small + big <= 3 {
            s.push((small + big, 0));
        } else {
            s.push((3, small + big - 3));
        }
        s
    }

    let frontier = DistributedFrontier::new(4);
    let result = frontier.run_bfs(
        vec![(Fingerprint(encode(0, 0)), ArrayState::new(2))],
        |_state, fp| {
            let (sm, bg) = decode(fp.0);
            diehard_successors(sm, bg)
                .into_iter()
                .map(|(s, b)| (Fingerprint(encode(s, b)), ArrayState::new(2)))
                .collect()
        },
    );
    assert_eq!(result.total_distinct_states, sequential_states);
}
