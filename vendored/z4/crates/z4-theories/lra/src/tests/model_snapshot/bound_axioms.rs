// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ─── sort_atom_index tests ──────────────────────────────────────────────

/// sort_atom_index sorts atom entries by bound_value within each variable.
#[test]
fn test_sort_atom_index_orders_by_bound_value() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));

    // Register atoms in non-sorted order: x<=10, x<=3, x<=7
    let a10 = terms.mk_le(x, ten);
    let a3 = terms.mk_le(x, three);
    let a7 = terms.mk_le(x, seven);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(a10);
    solver.register_atom(a3);
    solver.register_atom(a7);

    solver.sort_atom_index();

    let x_var = *solver.term_to_var.get(&x).expect("x registered");
    let atoms = solver.atom_index.get(&x_var).expect("atom_index for x");
    assert!(atoms.len() >= 3, "should have at least 3 atoms for x");

    // Verify sorted ascending by bound_value
    for i in 1..atoms.len() {
        assert!(
            atoms[i - 1].bound_value <= atoms[i].bound_value,
            "atom_index not sorted: {} > {} at positions {}, {}",
            atoms[i - 1].bound_value,
            atoms[i].bound_value,
            i - 1,
            i
        );
    }
}

/// sort_atom_index with a single atom is a no-op.
#[test]
fn test_sort_atom_index_single_atom() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let atom = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(atom);

    solver.sort_atom_index();

    let x_var = *solver.term_to_var.get(&x).expect("x registered");
    let atoms = solver.atom_index.get(&x_var).expect("atom_index for x");
    assert_eq!(atoms.len(), 1, "single atom");
    assert_eq!(atoms[0].bound_value, BigRational::from(BigInt::from(5)));
}

/// sort_atom_index handles multiple variables independently.
#[test]
fn test_sort_atom_index_multiple_variables() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);

    // x atoms: x <= 9, x <= 1
    let r9 = terms.mk_rational(BigRational::from(BigInt::from(9)));
    let x9 = terms.mk_le(x, r9);
    let r1 = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let x1 = terms.mk_le(x, r1);
    // y atoms: y <= 8, y <= 2
    let r8 = terms.mk_rational(BigRational::from(BigInt::from(8)));
    let y8 = terms.mk_le(y, r8);
    let r2 = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let y2 = terms.mk_le(y, r2);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x9);
    solver.register_atom(x1);
    solver.register_atom(y8);
    solver.register_atom(y2);

    solver.sort_atom_index();

    let x_var = *solver.term_to_var.get(&x).expect("x registered");
    let y_var = *solver.term_to_var.get(&y).expect("y registered");

    let x_atoms = solver.atom_index.get(&x_var).expect("atom_index for x");
    assert!(
        x_atoms[0].bound_value <= x_atoms[1].bound_value,
        "x atoms sorted"
    );

    let y_atoms = solver.atom_index.get(&y_var).expect("atom_index for y");
    assert!(
        y_atoms[0].bound_value <= y_atoms[1].bound_value,
        "y atoms sorted"
    );
}

// ─── generate_bound_axiom_terms tests ───────────────────────────────────

/// With two lower bounds on the same variable (x >= 3, x >= 7),
/// generate_bound_axiom_terms produces an implication axiom.
#[test]
fn test_generate_bound_axiom_terms_two_lower_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));

    let ge3 = terms.mk_ge(x, three); // x >= 3
    let ge7 = terms.mk_ge(x, seven); // x >= 7

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(ge3);
    solver.register_atom(ge7);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms();
    assert!(
        !axioms.is_empty(),
        "should generate at least one axiom for two lower bounds on same variable"
    );
    // With two lower bounds, the axiom should encode:
    // (x >= 7) => (x >= 3), i.e., ~ge7 | ge3
    // The tuple format is (term1, pol1, term2, pol2)
    let has_expected = axioms.iter().any(|&(t1, p1, t2, p2)| {
        // ~ge7 | ge3  OR  ge3 | ~ge7  (depending on order in mk_bound_axiom_terms)
        (t1 == ge7 && !p1 && t2 == ge3 && p2) || (t1 == ge3 && p1 && t2 == ge7 && !p2)
    });
    assert!(
        has_expected,
        "expected axiom encoding (x>=7) => (x>=3), got: {axioms:?}",
    );
}

/// With two upper bounds on the same variable (x <= 3, x <= 7),
/// generate_bound_axiom_terms produces an implication axiom.
#[test]
fn test_generate_bound_axiom_terms_two_upper_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));

    let le3 = terms.mk_le(x, three); // x <= 3
    let le7 = terms.mk_le(x, seven); // x <= 7

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(le3);
    solver.register_atom(le7);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms();
    assert!(
        !axioms.is_empty(),
        "should generate at least one axiom for two upper bounds on same variable"
    );
    // (x <= 3) => (x <= 7), i.e., ~le3 | le7
    // mk_bound_axiom_terms: both upper, k1=7 >= k2=3 → l1 | ~l2 where b1.is_upper
    // But which is b1? Depends on iteration order. Check both orientations.
    let has_expected = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (t1 == le3 && !p1 && t2 == le7 && p2) || (t1 == le7 && p1 && t2 == le3 && !p2)
    });
    assert!(
        has_expected,
        "expected axiom encoding (x<=3) => (x<=7), got: {axioms:?}",
    );
}

/// Lower and upper bounds on the same variable with compatible ranges produce
/// a tautology-aiding axiom (l1 | l2).
#[test]
fn test_generate_bound_axiom_terms_lower_upper_compatible() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));

    let ge3 = terms.mk_ge(x, three); // x >= 3 (lower)
    let le7 = terms.mk_le(x, seven); // x <= 7 (upper)

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(ge3);
    solver.register_atom(le7);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms();
    assert!(
        !axioms.is_empty(),
        "should generate at least one axiom for lower + upper bounds"
    );
    // Lower k1=3 <= upper k2=7 → tautology: l1 | l2
    let has_tautology = axioms.iter().any(|&(t1, p1, t2, p2)| {
        // Either (ge3, true, le7, true) or (le7, true, ge3, true)
        (p1 && p2) && ((t1 == ge3 && t2 == le7) || (t1 == le7 && t2 == ge3))
    });
    assert!(
        has_tautology,
        "expected tautology axiom (ge3 | le7), got: {axioms:?}",
    );
}

/// With conflicting lower > upper bounds (x >= 7, x <= 3), generate
/// a conflict-exclusion axiom (~l1 | ~l2).
#[test]
fn test_generate_bound_axiom_terms_lower_upper_conflicting() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));

    let ge7 = terms.mk_ge(x, seven); // x >= 7 (lower, k=7)
    let le3 = terms.mk_le(x, three); // x <= 3 (upper, k=3)

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(ge7);
    solver.register_atom(le3);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms();
    assert!(
        !axioms.is_empty(),
        "should generate at least one axiom for conflicting bounds"
    );
    // Lower k=7 > upper k=3 → conflict exclusion: ~l1 | ~l2
    let has_conflict = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (!p1 && !p2) && ((t1 == ge7 && t2 == le3) || (t1 == le3 && t2 == ge7))
    });
    assert!(
        has_conflict,
        "expected conflict axiom (~ge7 | ~le3), got: {axioms:?}",
    );
}

/// An equality atom with a single variable (x = 5) generates one-directional
/// axioms to related bound atoms.
#[test]
fn test_generate_bound_axiom_terms_equality_to_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));

    let eq5 = terms.mk_eq(x, five); // x = 5
    let ge3 = terms.mk_ge(x, three); // x >= 3 (lower, k=3)
    let le7 = terms.mk_le(x, seven); // x <= 7 (upper, k=7)

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(eq5);
    solver.register_atom(ge3);
    solver.register_atom(le7);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms();

    // (x = 5) → (x >= 3): ~eq5 | ge3
    let has_eq_to_lower = axioms
        .iter()
        .any(|&(t1, p1, t2, p2)| t1 == eq5 && !p1 && t2 == ge3 && p2);
    assert!(
        has_eq_to_lower,
        "expected axiom (x=5) => (x>=3), i.e., ~eq5 | ge3. Got: {axioms:?}",
    );

    // (x = 5) → (x <= 7): ~eq5 | le7
    let has_eq_to_upper = axioms
        .iter()
        .any(|&(t1, p1, t2, p2)| t1 == eq5 && !p1 && t2 == le7 && p2);
    assert!(
        has_eq_to_upper,
        "expected axiom (x=5) => (x<=7), i.e., ~eq5 | le7. Got: {axioms:?}",
    );
}

/// No atoms registered → generate_bound_axiom_terms returns empty.
#[test]
fn test_generate_bound_axiom_terms_empty() {
    let terms = TermStore::new();
    let solver = LraSolver::new(&terms);
    let axioms = solver.generate_bound_axiom_terms();
    assert!(axioms.is_empty(), "no atoms → no axioms");
}

/// Single atom → no pairs → no axioms (need at least 2 atoms per variable).
#[test]
fn test_generate_bound_axiom_terms_single_atom_no_axioms() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let le5 = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(le5);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms();
    assert!(
        axioms.is_empty(),
        "single atom per variable → no bound pair axioms"
    );
}

// ─── generate_incremental_bound_axioms tests (#4919) ──────────────────────

/// Incremental bound axiom generation returns nearest-neighbor axioms for a
/// newly-registered atom against existing atoms on the same variable.
#[test]
fn test_generate_incremental_bound_axioms_nearest_neighbors() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    let ge1 = terms.mk_ge(x, one); // x >= 1
    let ge3 = terms.mk_ge(x, three); // x >= 3
    let ge5 = terms.mk_ge(x, five); // x >= 5

    let mut solver = LraSolver::new(&terms);
    // Register the outer bounds first
    solver.register_atom(ge1);
    solver.register_atom(ge5);
    solver.sort_atom_index();

    // Now generate incremental axioms for ge3 (the middle bound)
    // ge3 must also be registered so atom_cache has its info
    solver.register_atom(ge3);
    solver.sort_atom_index();

    let axioms = solver.generate_incremental_bound_axioms(ge3);
    assert!(
        !axioms.is_empty(),
        "should generate axioms for ge3 vs nearest neighbors ge1 and ge5"
    );

    // ge5 => ge3 (stronger lower bound implies weaker): ~ge5 | ge3
    let has_ge5_implies_ge3 = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (t1 == ge5 && !p1 && t2 == ge3 && p2) || (t1 == ge3 && p1 && t2 == ge5 && !p2)
    });
    assert!(
        has_ge5_implies_ge3,
        "expected axiom (x>=5) => (x>=3), got: {axioms:?}",
    );

    // ge3 => ge1 (stronger lower bound implies weaker): ~ge3 | ge1
    let has_ge3_implies_ge1 = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (t1 == ge3 && !p1 && t2 == ge1 && p2) || (t1 == ge1 && p1 && t2 == ge3 && !p2)
    });
    assert!(
        has_ge3_implies_ge1,
        "expected axiom (x>=3) => (x>=1), got: {axioms:?}",
    );

    // At most 4 axioms (nearest-neighbor strategy)
    assert!(
        axioms.len() <= 4,
        "nearest-neighbor should produce at most 4 axioms, got {}",
        axioms.len()
    );
}

/// Incremental bound axioms for an atom with no existing neighbors returns empty.
#[test]
fn test_generate_incremental_bound_axioms_no_neighbors() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ge5 = terms.mk_ge(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(ge5);
    solver.sort_atom_index();

    let axioms = solver.generate_incremental_bound_axioms(ge5);
    assert!(
        axioms.is_empty(),
        "single atom per variable → no neighbors → no axioms"
    );
}

/// Incremental bound axioms skip equality/distinct atoms.
#[test]
fn test_generate_incremental_bound_axioms_skips_eq() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let eq5 = terms.mk_eq(x, five); // x = 5

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(eq5);
    solver.sort_atom_index();

    let axioms = solver.generate_incremental_bound_axioms(eq5);
    assert!(
        axioms.is_empty(),
        "equality atoms should be skipped (handled by eq-to-bound path)"
    );
}
