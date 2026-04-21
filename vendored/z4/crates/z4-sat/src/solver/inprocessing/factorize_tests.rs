// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_build_factor_occ_filters_nonproductive_large_clauses() {
    let mut solver = Solver::new(8);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));
    let f = Literal::positive(Variable(5));
    let g = Literal::positive(Variable(6));
    let h = Literal::positive(Variable(7));

    solver.add_clause(vec![a, b]);
    solver.add_clause(vec![a, c, d]);
    solver.add_clause(vec![b, c, d]);
    solver.add_clause(vec![a, c, e]);
    solver.add_clause(vec![b, c, e]);
    solver.add_clause(vec![f, g, h]);

    let occ = solver.build_factor_occ();

    assert_eq!(
        occ.count(a),
        3,
        "productive clauses should stay in occ lists"
    );
    assert_eq!(
        occ.count(b),
        3,
        "productive clauses should stay in occ lists"
    );
    assert_eq!(
        occ.count(c),
        4,
        "shared quotient literal should stay in occ lists"
    );
    assert_eq!(
        occ.count(d),
        2,
        "shared quotient literal should stay in occ lists"
    );
    assert_eq!(
        occ.count(e),
        2,
        "shared quotient literal should stay in occ lists"
    );
    assert_eq!(
        occ.count(f),
        0,
        "unique large clause should be filtered out"
    );
    assert_eq!(
        occ.count(g),
        0,
        "unique large clause should be filtered out"
    );
    assert_eq!(
        occ.count(h),
        0,
        "unique large clause should be filtered out"
    );
}
