// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tempfile::TempDir;

use super::fixtures::*;
use super::*;

/// Budget-boundary test for the BFS exploration seam.
///
/// Uses `AG(is-fireable(T0))` on `linear_deadlock_net`:
/// - With full budget (2 states), BFS finds the deadlock → `False`
/// - With tight budget (1 state) and fake z4 returning `unknown`,
///   SMT proof engines are neutralized, but the random walk phase
///   fires T0 and discovers the deadlock state without BFS → `False`
///
/// The random walk (Phase 2d) runs on the unreduced net without z4
/// and legitimately proves AG(is-fireable(T0))=FALSE by finding a
/// counterexample marking where T0 is disabled.
#[test]
fn test_reachability_budget_boundary_with_fake_solver() {
    let net = linear_deadlock_net();
    let props = vec![make_ag_prop(
        "budget-ag",
        StatePredicate::IsFireable(vec!["T0".to_string()]),
    )];

    // Exact budget: BFS explores both states, discovers deadlock → False
    let exact = check_reachability_properties(&net, &props, &ExplorationConfig::new(2));
    assert_eq!(exact, vec![(String::from("budget-ag"), Verdict::False)]);

    // Tight budget with fake solver: SMT engines neutralized but the random
    // walk fires T0, reaches (0,1) where T0 is disabled → False
    let tempdir = TempDir::new().expect("tempdir should create");
    let solver = write_fake_solver_script(
        tempdir.path(),
        "fake-z4",
        "cat >/dev/null\nprintf 'unknown\\n'",
    );
    let tight = with_z4_path(&solver, || {
        check_reachability_properties(&net, &props, &ExplorationConfig::new(1))
    });
    assert_eq!(tight, vec![(String::from("budget-ag"), Verdict::False)]);
}
