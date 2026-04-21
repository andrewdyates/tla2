// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Gap 9: DpllT push/pop incremental solving tests.

use super::*;

/// Test basic push/pop scope depth tracking
#[test]
fn test_dpllt_push_pop_scope_depth() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(3, theory);

    assert_eq!(dpll.scope_depth(), 0, "Initial scope depth should be 0");

    dpll.push();
    assert_eq!(dpll.scope_depth(), 1, "After push, scope depth should be 1");

    dpll.push();
    assert_eq!(
        dpll.scope_depth(),
        2,
        "After second push, scope depth should be 2"
    );

    let ok = dpll.pop();
    assert!(ok, "Pop should succeed");
    assert_eq!(dpll.scope_depth(), 1, "After pop, scope depth should be 1");

    let ok = dpll.pop();
    assert!(ok, "Pop should succeed");
    assert_eq!(
        dpll.scope_depth(),
        0,
        "After second pop, scope depth should be 0"
    );

    let ok = dpll.pop();
    assert!(!ok, "Pop on empty should return false");
    assert_eq!(dpll.scope_depth(), 0, "Scope depth should remain 0");
}

/// Test that clauses added after push are disabled after pop
#[test]
fn test_dpllt_push_pop_clause_scoping() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    // Add a base clause that makes formula SAT: (x ∨ y)
    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    // Solve - should be SAT
    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));

    // Push and add a conflicting clause
    dpll.push();

    // Add ¬x and ¬y unit clauses - combined with (x ∨ y), this is UNSAT
    dpll.add_clause(vec![Literal::negative(Variable::new(0))]);
    dpll.add_clause(vec![Literal::negative(Variable::new(1))]);

    // Should now be UNSAT
    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Unsat));

    // Pop - the ¬x and ¬y clauses should be disabled
    let ok = dpll.pop();
    assert!(ok);

    // Should be SAT again (only base clause (x ∨ y) is active)
    let result = dpll.solve().unwrap();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "After pop, formula should be SAT again"
    );
}

/// Test incremental solving with multiple push/pop cycles
#[test]
fn test_dpllt_incremental_multiple_cycles() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(3, theory);

    // Base clause: (x ∨ y ∨ z)
    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    // First cycle: force x=false, y=false - only z can be true
    dpll.push();
    dpll.add_clause(vec![Literal::negative(Variable::new(0))]); // ¬x
    dpll.add_clause(vec![Literal::negative(Variable::new(1))]); // ¬y

    let result = dpll.solve().unwrap();
    match result {
        SatResult::Sat(model) => {
            // z must be true
            assert!(model.get(2).copied().unwrap_or(false), "z should be true");
        }
        _ => panic!("Should be SAT with z=true"),
    }

    dpll.pop();

    // Second cycle: force x=false, z=false - only y can be true
    dpll.push();
    dpll.add_clause(vec![Literal::negative(Variable::new(0))]); // ¬x
    dpll.add_clause(vec![Literal::negative(Variable::new(2))]); // ¬z

    let result = dpll.solve().unwrap();
    match result {
        SatResult::Sat(model) => {
            // y must be true
            assert!(model.get(1).copied().unwrap_or(false), "y should be true");
        }
        _ => panic!("Should be SAT with y=true"),
    }

    dpll.pop();

    // After all pops, should be SAT with any of x, y, z
    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));
}

/// Test nested push/pop scopes
#[test]
fn test_dpllt_nested_push_pop() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(3, theory);

    // Base: (x ∨ y ∨ z)
    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    // Level 1: add ¬x
    dpll.push();
    dpll.add_clause(vec![Literal::negative(Variable::new(0))]);
    assert_eq!(dpll.scope_depth(), 1);

    // Level 2: add ¬y
    dpll.push();
    dpll.add_clause(vec![Literal::negative(Variable::new(1))]);
    assert_eq!(dpll.scope_depth(), 2);

    // At level 2: only z can be true
    let result = dpll.solve().unwrap();
    match result {
        SatResult::Sat(model) => {
            assert!(!model.first().copied().unwrap_or(true), "x should be false");
            assert!(!model.get(1).copied().unwrap_or(true), "y should be false");
            assert!(model.get(2).copied().unwrap_or(false), "z should be true");
        }
        _ => panic!("Should be SAT"),
    }

    // Pop level 2 - ¬y is removed
    dpll.pop();
    assert_eq!(dpll.scope_depth(), 1);

    // At level 1: x is false, y or z can be true
    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));

    // Pop level 1 - ¬x is removed
    dpll.pop();
    assert_eq!(dpll.scope_depth(), 0);

    // At base level: any of x, y, z can be true
    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));
}

/// Test that pop on empty scope returns false and is safe
#[test]
fn test_dpllt_pop_empty_safe() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    // Pop without any push should be safe and return false
    assert!(!dpll.pop());
    assert!(!dpll.pop());
    assert_eq!(dpll.scope_depth(), 0);

    // Solver should still work
    dpll.add_clause(vec![Literal::positive(Variable::new(0))]);
    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));
}
