// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the DT theory solver.

use super::*;

#[test]
fn test_new_solver() {
    let terms = TermStore::new();
    let solver = DtSolver::new(&terms);
    assert!(solver.term_constructors.is_empty());
}

#[test]
fn test_register_datatype() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);
    assert!(solver.datatype_defs.contains_key("Option"));
    assert!(solver.tester_map.contains_key("is-None"));
    assert!(solver.tester_map.contains_key("is-Some"));
    assert!(solver.ctor_to_dt.contains_key("None"));
    assert!(solver.ctor_to_dt.contains_key("Some"));
}

#[test]
fn test_register_constructor() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    // Register a None constructor application
    let none_term = TermId::new(100);
    solver.register_constructor(none_term, "Option", "None", &[]);

    assert!(solver.term_constructors.contains_key(&none_term));
    assert_eq!(solver.term_constructors[&none_term].ctor_name, "None");
}

#[test]
fn test_no_clash_same_constructor() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Point", &["mk_point".to_string()]);

    // Two mk_point terms with different args
    let p1 = TermId::new(100);
    let p2 = TermId::new(101);
    let x1 = TermId::new(1);
    let y1 = TermId::new(2);
    let x2 = TermId::new(3);
    let y2 = TermId::new(4);

    solver.register_constructor(p1, "Point", "mk_point", &[x1, y1]);
    solver.register_constructor(p2, "Point", "mk_point", &[x2, y2]);

    // Make p1 = p2 (same equivalence class)
    solver.assert_equality(p1, p2);

    // Should NOT be a clash - same constructor
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
}

#[test]
fn test_clash_different_constructors() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    // None and Some(x) terms
    let none_term = TermId::new(100);
    let some_term = TermId::new(101);
    let x = TermId::new(1);

    solver.register_constructor(none_term, "Option", "None", &[]);
    solver.register_constructor(some_term, "Option", "Some", &[x]);

    // Make none_term = some_term (clash!)
    solver.assert_equality(none_term, some_term);

    // Should be a conflict
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Unsat(_)));
}

#[test]
fn test_clash_conflict_uses_equality_literals() {
    use z4_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(z4_core::DatatypeSort::new("Option", vec![]));

    let x = terms.mk_var("x", dt_sort.clone());
    let y = terms.mk_var("y", Sort::Int);
    let none_term = terms.mk_var("None", dt_sort.clone());
    let some_y_term = terms.mk_app(Symbol::Named("Some".to_string()), vec![y], dt_sort);

    let eq_x_none = terms.mk_eq(x, none_term);
    let eq_x_some_y = terms.mk_eq(x, some_y_term);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    solver.assert_literal(eq_x_none, true);
    solver.assert_literal(eq_x_some_y, true);

    let TheoryResult::Unsat(conflict) = solver.check() else {
        panic!("expected UNSAT from constructor clash");
    };

    assert!(
        conflict.contains(&TheoryLit::new(eq_x_none, true)),
        "conflict should include asserted equality literal (= x None)"
    );
    assert!(
        conflict.contains(&TheoryLit::new(eq_x_some_y, true)),
        "conflict should include asserted equality literal (= x (Some y))"
    );
}

#[test]
fn test_occurs_check_unsat_direct_cycle() {
    use z4_core::Sort;

    let mut terms = TermStore::new();
    let list_sort = Sort::Datatype(z4_core::DatatypeSort::new("List", vec![]));

    let x = terms.mk_var("x", list_sort.clone());
    let hd = terms.mk_var("hd", Sort::Int);
    let cons_hd_x = terms.mk_app(Symbol::Named("cons".to_string()), vec![hd, x], list_sort);
    let eq = terms.mk_eq(x, cons_hd_x);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("List", &["nil".to_string(), "cons".to_string()]);
    solver.assert_literal(eq, true);

    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));
}

#[test]
fn test_push_pop() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    // Register in base scope
    let none_term = TermId::new(100);
    solver.register_constructor(none_term, "Option", "None", &[]);

    solver.push();

    // Register in new scope
    let some_term = TermId::new(101);
    let x = TermId::new(1);
    solver.register_constructor(some_term, "Option", "Some", &[x]);
    assert!(solver.term_constructors.contains_key(&some_term));

    solver.pop();

    // some_term should be gone, none_term should remain
    assert!(!solver.term_constructors.contains_key(&some_term));
    assert!(solver.term_constructors.contains_key(&none_term));
}

/// Regression test for #3725: pop() must clear pending propagations.
#[test]
fn test_pop_clears_pending_propagations() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);

    solver.push();
    solver.pending.push(TheoryPropagation {
        literal: TheoryLit::new(TermId::new(10), true),
        reason: vec![TheoryLit::new(TermId::new(11), true)],
    });
    assert_eq!(solver.pending.len(), 1, "test setup must queue propagation");

    solver.pop();

    assert!(
        solver.pending.is_empty(),
        "pop() must clear pending propagations from popped scope (#3725)"
    );
    assert!(
        solver.propagate().is_empty(),
        "propagate() after pop() must not return stale propagations (#3725)"
    );
}

/// Regression test for #3656: push/pop must undo union-find merges.
///
/// Before the fix, `union()` mutations persisted after `pop()`, so
/// terms merged in a scoped context remained equivalent after the
/// scope was popped. This caused spurious constructor clashes in
/// subsequent incremental solves.
#[test]
fn test_push_pop_undoes_union_find() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    let t1 = TermId::new(100);
    let t2 = TermId::new(101);
    let x = TermId::new(1);

    // Register constructors in base scope.
    solver.register_constructor(t1, "Option", "None", &[]);
    solver.register_constructor(t2, "Option", "Some", &[x]);

    // Confirm different representatives before any equality.
    assert_ne!(
        solver.find(t1),
        solver.find(t2),
        "terms should be in separate equivalence classes initially"
    );

    // Push, merge, verify merge, pop.
    solver.push();
    solver.assert_equality(t1, t2);
    assert_eq!(
        solver.find(t1),
        solver.find(t2),
        "terms should be merged after assert_equality"
    );
    solver.pop();

    // After pop, the union must be undone.
    assert_ne!(
        solver.find(t1),
        solver.find(t2),
        "pop() must undo union-find merge (#3656)"
    );

    // No constructor clash should be detected after pop.
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "solver must not report a clash after pop undoes the scoped merge"
    );
}

/// Regression test for #3656: push/pop must undo tester_results.
#[test]
fn test_push_pop_undoes_tester_results() {
    use z4_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(z4_core::DatatypeSort::new("Option", vec![]));
    let x = terms.mk_var("x", dt_sort);
    let is_none_x = terms.mk_app(Symbol::Named("is-None".to_string()), vec![x], Sort::Bool);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    assert!(solver.tester_results.is_empty());

    solver.push();
    solver.assert_literal(is_none_x, true);
    assert!(
        solver.tester_results.contains_key(&x),
        "tester result should be recorded after assert_literal"
    );
    solver.pop();

    assert!(
        !solver.tester_results.contains_key(&x),
        "pop() must undo tester_results insert (#3656)"
    );
}

#[test]
fn test_reset() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    let none_term = TermId::new(100);
    solver.register_constructor(none_term, "Option", "None", &[]);

    solver.reset();

    // Constructor registrations cleared, but datatype defs preserved
    assert!(solver.term_constructors.is_empty());
    assert!(solver.datatype_defs.contains_key("Option"));
}
