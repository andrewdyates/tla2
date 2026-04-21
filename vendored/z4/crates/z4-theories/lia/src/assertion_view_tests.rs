// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_traits::One;
use z4_core::Sort;

#[test]
fn test_assertion_view_classifies_equalities_and_inequalities() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let one = terms.mk_int(BigInt::one());
    let eq = terms.mk_eq(x, one);
    let ge = terms.mk_ge(y, one);

    // (= x 1) true, (>= y 1) true
    let asserted = vec![(eq, true), (ge, true)];
    let view = AssertionView::build(&terms, &asserted);

    assert_eq!(view.positive_equalities.len(), 1);
    assert_eq!(view.negative_equalities.len(), 0);
    assert_eq!(view.inequalities.len(), 1);
    assert_eq!(view.equality_key.len(), 1);
    // y should have a lower bound of 1
    let y_bounds = view.bounds_by_term.get(&y).expect("y should have bounds");
    assert_eq!(y_bounds.lower, Some(BigInt::one()));
}

#[test]
fn test_assertion_view_negative_equality_is_disequality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::ZERO);
    let eq = terms.mk_eq(x, zero);

    let asserted = vec![(eq, false)];
    let view = AssertionView::build(&terms, &asserted);

    assert_eq!(view.positive_equalities.len(), 0);
    assert_eq!(view.negative_equalities.len(), 1);
    assert_eq!(view.equality_key.len(), 0);
}
