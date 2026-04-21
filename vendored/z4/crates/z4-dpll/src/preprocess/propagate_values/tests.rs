// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;
use z4_core::Sort;

#[test]
fn test_propagate_simple_ground_equality() {
    let mut terms = TermStore::new();

    // Create: (= (f 0) 42)
    let zero = terms.mk_int(BigInt::from(0));
    let fortytwo = terms.mk_int(BigInt::from(42));
    let f_0 = terms.mk_app(Symbol::Named("f".to_string()), vec![zero], Sort::Int);
    let eq = terms.mk_eq(f_0, fortytwo);

    // Create: (= x (+ (f 0) 1))
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let f0_plus_1 = terms.mk_add(vec![f_0, one]);
    let eq2 = terms.mk_eq(x, f0_plus_1);

    let mut assertions = vec![eq, eq2];
    let mut pass = PropagateValues::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified, "pass should modify assertions");

    // The first assertion (= (f 0) 42) is a defining equality — preserved.
    // The second assertion should become (= x (+ 42 1)) = (= x 43)
    // after constant folding by mk_add.
    assert_eq!(
        assertions.len(),
        2,
        "defining equality preserved + rewritten"
    );

    // The defining equality is preserved unchanged
    assert_eq!(assertions[0], eq, "defining equality preserved");

    // Check that the second assertion references the constant 43
    let fortythree = terms.mk_int(BigInt::from(43));
    let expected_eq = terms.mk_eq(x, fortythree);
    assert!(
        assertions.contains(&expected_eq),
        "should contain (= x 43) after value propagation and constant folding"
    );
}

#[test]
fn test_propagate_no_ground_equalities() {
    let mut terms = TermStore::new();

    // Create: (= x y) — no constants, nothing to propagate
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq = terms.mk_eq(x, y);

    let mut assertions = vec![eq];
    let mut pass = PropagateValues::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(
        !modified,
        "pass should not modify when no ground equalities"
    );
    assert_eq!(assertions.len(), 1);
}

#[test]
fn test_propagate_cascading_through_fixed_point() {
    let mut terms = TermStore::new();

    // Create lookup table: (= (Succ 0) 1), (= (Succ 1) 2)
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let succ_0 = terms.mk_app(Symbol::Named("Succ".to_string()), vec![zero], Sort::Int);
    let succ_1 = terms.mk_app(Symbol::Named("Succ".to_string()), vec![one], Sort::Int);
    let eq1 = terms.mk_eq(succ_0, one);
    let eq2 = terms.mk_eq(succ_1, two);

    // Create: (= x (Succ (Succ 0)))
    // Because the value_map contains both (Succ 0) -> 1 and (Succ 1) -> 2,
    // the bottom-up rewrite resolves the full chain in a single pass:
    //   rewrite(Succ(Succ(0))) -> rewrite inner: Succ(0) -> 1
    //   -> rebuild Succ(1) -> hash-consed to succ_1 -> value_map -> 2
    let x = terms.mk_var("x", Sort::Int);
    let succ_succ_0 = terms.mk_app(Symbol::Named("Succ".to_string()), vec![succ_0], Sort::Int);
    let eq3 = terms.mk_eq(x, succ_succ_0);

    let mut assertions = vec![eq1, eq2, eq3];
    let mut pass = PropagateValues::new();

    // Single iteration resolves the full cascade via bottom-up rewriting
    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified);

    // eq1 and eq2 are defining equalities — preserved unchanged.
    // eq3 becomes (= x 2) via cascading substitution.
    assert_eq!(assertions.len(), 3, "defining equalities preserved");
    assert_eq!(assertions[0], eq1, "first defining equality preserved");
    assert_eq!(assertions[1], eq2, "second defining equality preserved");
    let expected_eq = terms.mk_eq(x, two);
    assert_eq!(
        assertions[2],
        expected_eq,
        "should contain (= x 2) after value propagation; got {:?}",
        terms.get(assertions[2])
    );
}

#[test]
fn test_propagate_preserves_defining_equalities() {
    let mut terms = TermStore::new();

    // Create: (= (f 0) 5) and just that assertion
    let zero = terms.mk_int(BigInt::from(0));
    let five = terms.mk_int(BigInt::from(5));
    let f_0 = terms.mk_app(Symbol::Named("f".to_string()), vec![zero], Sort::Int);
    let eq = terms.mk_eq(f_0, five);

    let mut assertions = vec![eq];
    let mut pass = PropagateValues::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified, "should detect ground equality");

    // The defining equality is preserved (EUF needs it for congruence closure)
    assert_eq!(assertions.len(), 1, "defining equality preserved");
    assert_eq!(assertions[0], eq, "original equality unchanged");
}
