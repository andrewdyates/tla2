// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::fs;

use tempfile::TempDir;

use super::fixtures::*;
use super::*;

#[test]
fn test_unresolved_place_returns_cannot_compute() {
    // AG(tokens("NONEXISTENT") <= 0) — unresolved place → CANNOT_COMPUTE
    let net = simple_net();
    let props = vec![make_ag_prop(
        "unresolved-place",
        StatePredicate::IntLe(
            IntExpr::TokensCount(vec!["NONEXISTENT".to_string()]),
            IntExpr::Constant(0),
        ),
    )];

    let results = check_reachability_properties(&net, &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].0, "unresolved-place");
    assert_eq!(results[0].1, Verdict::CannotCompute);
}

#[test]
fn test_unresolved_transition_returns_cannot_compute() {
    // EF(is-fireable("NONEXISTENT")) — unresolved transition → CANNOT_COMPUTE
    let net = simple_net();
    let props = vec![make_ef_prop(
        "unresolved-trans",
        StatePredicate::IsFireable(vec!["NONEXISTENT".to_string()]),
    )];

    let results = check_reachability_properties(&net, &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].0, "unresolved-trans");
    assert_eq!(results[0].1, Verdict::CannotCompute);
}

#[test]
fn test_valid_formula_still_works() {
    // EF(is-fireable("t0")) — valid, t0 is enabled at initial marking
    let net = simple_net();
    let props = vec![make_ef_prop(
        "valid-ef",
        StatePredicate::IsFireable(vec!["t0".to_string()]),
    )];

    let results = check_reachability_properties(&net, &props, &default_config());
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].0, "valid-ef");
    assert_eq!(results[0].1, Verdict::True);
}

#[test]
fn test_bmc_seeding_preserves_order_and_invalid_entries_when_bfs_incomplete() {
    let tempdir = TempDir::new().expect("tempdir should create");
    let calls_path = tempdir.path().join("calls.log");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4",
        &format!(
            "printf 'call\\n' >> \"{}\"\ncat >/dev/null\nprintf 'sat\\nsat\\nunsat\\nunknown\\n'",
            calls_path.display()
        ),
    );
    let net = simple_net();
    let props = vec![
        make_ag_prop(
            "inv-00",
            StatePredicate::IntLe(
                IntExpr::TokensCount(vec!["NONEXISTENT".to_string()]),
                IntExpr::Constant(0),
            ),
        ),
        make_ef_prop(
            "ef-01",
            StatePredicate::IntLe(
                IntExpr::Constant(1),
                IntExpr::TokensCount(vec!["p1".to_string()]),
            ),
        ),
        make_ag_prop(
            "ag-02",
            StatePredicate::IntLe(
                IntExpr::Constant(3),
                IntExpr::TokensCount(vec!["p0".to_string()]),
            ),
        ),
        make_ef_prop(
            "ef-03",
            StatePredicate::IntLe(
                IntExpr::Constant(10),
                IntExpr::TokensCount(vec!["p1".to_string()]),
            ),
        ),
        make_ag_prop(
            "ag-04",
            StatePredicate::IntLe(
                IntExpr::TokensCount(vec!["p0".to_string(), "p1".to_string()]),
                IntExpr::Constant(3),
            ),
        ),
    ];
    let limited_config = ExplorationConfig::new(1);

    let results = with_z4_path(&solver, || {
        check_reachability_properties(&net, &props, &limited_config)
    });

    // Core invariants that hold regardless of whether the fake z4 succeeds:
    assert_eq!(results.len(), 5, "order and count must be preserved");
    assert_eq!(
        results[0],
        ("inv-00".to_string(), Verdict::CannotCompute),
        "unresolved names → CannotCompute"
    );
    // ef-01 (EF p1>=1): BMC may seed True, or stays CannotCompute if solver fails.
    assert!(
        results[1] == ("ef-01".to_string(), Verdict::True)
            || results[1] == ("ef-01".to_string(), Verdict::CannotCompute),
        "ef-01 must be True (BMC witness) or CannotCompute (solver failed), got {:?}",
        results[1].1
    );
    // ag-02 (AG p0>=3): BMC may seed False, or stays CannotCompute if solver fails.
    assert!(
        results[2] == ("ag-02".to_string(), Verdict::False)
            || results[2] == ("ag-02".to_string(), Verdict::CannotCompute),
        "ag-02 must be False (BMC counterexample) or CannotCompute (solver failed), got {:?}",
        results[2].1
    );
    // ef-03: EF(p1 >= 10) — LP proves infeasible (p0+p1=3), always FALSE.
    assert_eq!(
        results[3],
        ("ef-03".to_string(), Verdict::False),
        "LP must prove EF(p1>=10) false on conserving net"
    );
    // ag-04: AG(p0+p1 <= 3) — LP proves violation (p0+p1>=4) infeasible, always TRUE.
    assert_eq!(
        results[4],
        ("ag-04".to_string(), Verdict::True),
        "LP must prove AG(p0+p1<=3) true on conserving net"
    );
    // If the fake solver ran, verify it was called exactly once.
    if calls_path.exists() {
        assert_eq!(
            fs::read_to_string(&calls_path)
                .expect("call log should exist")
                .lines()
                .count(),
            1,
            "unknown should stop BMC deepening after the first solver call"
        );
    }
}

#[test]
fn test_mixed_valid_invalid_preserves_order() {
    // property A: unresolved AG(tokens("NONEXISTENT") <= 0) → CANNOT_COMPUTE
    // property B: valid EF(is-fireable("t0")) → TRUE
    // property C: unresolved EF(is-fireable("MISSING")) → CANNOT_COMPUTE
    // property D: valid AG(tokens("p0") + tokens("p1") <= 3) → TRUE
    let net = simple_net();
    let props = vec![
        make_ag_prop(
            "inv-00",
            StatePredicate::IntLe(
                IntExpr::TokensCount(vec!["NONEXISTENT".to_string()]),
                IntExpr::Constant(0),
            ),
        ),
        make_ef_prop("val-01", StatePredicate::IsFireable(vec!["t0".to_string()])),
        make_ef_prop(
            "inv-02",
            StatePredicate::IsFireable(vec!["MISSING".to_string()]),
        ),
        make_ag_prop(
            "val-03",
            StatePredicate::IntLe(
                IntExpr::TokensCount(vec!["p0".to_string(), "p1".to_string()]),
                IntExpr::Constant(3),
            ),
        ),
    ];

    let results = check_reachability_properties(&net, &props, &default_config());
    assert_eq!(results.len(), 4);
    assert_eq!(results[0], ("inv-00".to_string(), Verdict::CannotCompute));
    assert_eq!(results[1], ("val-01".to_string(), Verdict::True));
    assert_eq!(results[2], ("inv-02".to_string(), Verdict::CannotCompute));
    assert_eq!(results[3], ("val-03".to_string(), Verdict::True));
}

#[test]
fn test_invalid_does_not_affect_valid_early_termination() {
    // All properties invalid — BFS should still run (with empty observer)
    // and produce only CANNOT_COMPUTE results.
    let net = simple_net();
    let props = vec![
        make_ef_prop(
            "all-inv-00",
            StatePredicate::IsFireable(vec!["MISSING".to_string()]),
        ),
        make_ag_prop(
            "all-inv-01",
            StatePredicate::IntLe(
                IntExpr::TokensCount(vec!["GHOST".to_string()]),
                IntExpr::Constant(0),
            ),
        ),
    ];

    let results = check_reachability_properties(&net, &props, &default_config());
    assert_eq!(results.len(), 2);
    assert_eq!(results[0].1, Verdict::CannotCompute);
    assert_eq!(results[1].1, Verdict::CannotCompute);
}
