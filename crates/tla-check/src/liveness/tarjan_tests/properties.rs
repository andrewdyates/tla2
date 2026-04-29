// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use proptest::prelude::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn prop_tarjan_matches_reference_on_small_graphs() {
    let n = 4usize;
    let config = proptest::test_runner::Config {
        failure_persistence: None,
        ..proptest::test_runner::Config::default()
    };
    let mut runner = proptest::test_runner::TestRunner::new(config);
    let strategy = proptest::collection::vec(any::<bool>(), n * n);

    runner
        .run(&strategy, |adj| {
            let (graph, _states, nodes) = build_graph_from_adj(n, &adj);

            let result = find_sccs(&graph);
            prop_assert!(
                result.errors.is_empty(),
                "Tarjan invariant violation on random 4-node graph: {:?}",
                result.errors
            );
            let tarjan = canonicalize_sccs(result.sccs, &nodes);
            let reference = reference_sccs(n, &adj);

            prop_assert_eq!(tarjan, reference);
            Ok(())
        })
        .expect("small-graph Tarjan proptest should complete");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[allow(clippy::erasing_op, clippy::identity_op)]
fn test_1516_cross_scc_edges_separate_sccs() {
    let n = 6;
    let mut adj = vec![false; n * n];
    adj[0 * n + 1] = true;
    adj[1 * n + 2] = true;
    adj[2 * n + 0] = true;
    adj[3 * n + 4] = true;
    adj[4 * n + 3] = true;
    adj[2 * n + 3] = true;

    let (graph, _states, nodes) = build_graph_from_adj(n, &adj);
    let result = find_sccs(&graph);
    assert!(
        result.errors.is_empty(),
        "Tarjan invariant violation: {:?}",
        result.errors
    );
    let tarjan = canonicalize_sccs(result.sccs, &nodes);
    let reference = reference_sccs(n, &adj);

    assert_eq!(tarjan, reference, "Forward cross edge must not merge SCCs");
    assert!(
        tarjan.iter().any(|scc| scc == &[0, 1, 2]),
        "SCC A should be {{0,1,2}}"
    );
    assert!(
        tarjan.iter().any(|scc| scc == &[3, 4]),
        "SCC B should be {{3,4}}"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn prop_tarjan_matches_reference_on_medium_graphs() {
    let n = 6usize;

    let config = proptest::test_runner::Config {
        failure_persistence: None,
        ..proptest::test_runner::Config::default()
    };
    let mut runner = proptest::test_runner::TestRunner::new(config);
    let strategy = proptest::collection::vec(any::<bool>(), n * n);

    runner
        .run(&strategy, |adj| {
            let (graph, _states, nodes) = build_graph_from_adj(n, &adj);

            let result = find_sccs(&graph);
            prop_assert!(
                result.errors.is_empty(),
                "Tarjan invariant violation on random 6-node graph: {:?}",
                result.errors
            );
            let tarjan = canonicalize_sccs(result.sccs, &nodes);
            let reference = reference_sccs(n, &adj);

            prop_assert_eq!(tarjan, reference);
            Ok(())
        })
        .expect("medium-graph Tarjan proptest should complete");
}
