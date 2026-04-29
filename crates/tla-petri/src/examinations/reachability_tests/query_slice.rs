// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tempfile::TempDir;

use super::fixtures::*;
use super::*;

#[test]
fn test_check_reachability_parallel_matches_sequential() {
    let net = simple_net();
    let props = vec![
        make_ef_prop(
            "ef-00",
            StatePredicate::IntLe(
                IntExpr::Constant(3),
                IntExpr::TokensCount(vec!["p1".to_string()]),
            ),
        ),
        make_ag_prop(
            "ag-00",
            StatePredicate::IntLe(
                IntExpr::TokensCount(vec!["p0".to_string(), "p1".to_string()]),
                IntExpr::Constant(3),
            ),
        ),
    ];

    let sequential = check_reachability_properties(&net, &props, &default_config());
    let parallel = check_reachability_properties(&net, &props, &parallel_config());

    assert_eq!(parallel, sequential);
}

#[test]
fn test_query_slice_shrinks_reachability_budget_net() {
    let net = query_slice_budget_net();
    let props = vec![make_ef_prop(
        "budget-ef",
        StatePredicate::IntLe(
            IntExpr::Constant(2),
            IntExpr::TokensCount(vec!["r1".to_string()]),
        ),
    )];

    let (_prepared, trackers) = prepare_trackers(&net, &props);
    let reduced = reduce_reachability_queries(&net, &trackers)
        .expect("query-protected reduction should succeed");

    // Rule I prunes disconnected components during reduction, so the
    // reduced net is already smaller than the original. The subsequent
    // query slice may find nothing extra to prune.
    assert!(
        reduced.net.num_places() < net.num_places(),
        "Rule I should prune irrelevant places during reduction"
    );
    assert!(
        reduced.net.num_transitions() < net.num_transitions(),
        "Rule I should prune irrelevant transitions during reduction"
    );
}

#[test]
fn test_query_slice_matches_unsliced_reachability_results() {
    let tempdir = TempDir::new().expect("tempdir should create");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4",
        "cat >/dev/null\nprintf 'unknown\\n'",
    );
    let net = query_slice_budget_net();
    let props = vec![make_ef_prop(
        "budget-ef",
        StatePredicate::IntLe(
            IntExpr::Constant(2),
            IntExpr::TokensCount(vec!["r1".to_string()]),
        ),
    )];

    let sliced = with_z4_path(&solver, || {
        check_reachability_properties(&net, &props, &default_config())
    });
    let unsliced = with_z4_path(&solver, || {
        check_reachability_properties_unsliced(&net, &props, &default_config())
    });

    assert_eq!(sliced, unsliced);
}

#[test]
fn test_query_slice_reachability_avoids_cannot_compute_under_budget() {
    let tempdir = TempDir::new().expect("tempdir should create");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4",
        "cat >/dev/null\nprintf 'unknown\\n'",
    );
    let net = query_slice_budget_net();
    let props = vec![make_ef_prop(
        "budget-ef",
        StatePredicate::IntLe(
            IntExpr::Constant(2),
            IntExpr::TokensCount(vec!["r1".to_string()]),
        ),
    )];
    let config = parallel_budget_config(4);

    let sliced = with_z4_path(&solver, || {
        check_reachability_properties(&net, &props, &config)
    });
    let unsliced = with_z4_path(&solver, || {
        check_reachability_properties_unsliced(&net, &props, &config)
    });

    // Both paths benefit from Rule I irrelevance pruning during
    // reduction, so neither exceeds the state budget on this net.
    assert_eq!(sliced, vec![(String::from("budget-ef"), Verdict::True)]);
    assert_eq!(unsliced, vec![(String::from("budget-ef"), Verdict::True)]);
}
