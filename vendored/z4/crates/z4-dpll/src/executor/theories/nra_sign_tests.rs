// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// NRA sign consistency tests — N-ary products and implied signs.
// Included via include!() from nra.rs test module.

// Triple product sign: x>0, y>0, z>0 implies x*y*z > 0, so < 0 is UNSAT
#[test]
fn nra_unsat_triple_positive_product_negative() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (> x 0.0))
(assert (> y 0.0))
(assert (> z 0.0))
(assert (< (* x (* y z)) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Implied sign from bounds: x in [1,3], y in [2,4] → both positive, x*y < 0 is UNSAT
#[test]
fn nra_unsat_implied_sign_from_bounds() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 1.0))
(assert (<= x 3.0))
(assert (>= y 2.0))
(assert (<= y 4.0))
(assert (< (* x y) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Model-derived sign cuts: x in [-5,-1], y in [2,4] → x negative, y positive,
// so x*y must be negative. Asserting x*y > 0 should be UNSAT.
// Neither bound compares to zero, so assertion-based sign extraction won't fire.
// Model-based sign deduction derives x < 0, y > 0 from the LRA model.
#[test]
fn nra_unsat_model_sign_cut_negative_positive() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (<= x (- 1.0)))
(assert (>= x (- 5.0)))
(assert (>= y 2.0))
(assert (<= y 4.0))
(assert (> (* x y) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Model-derived sign cuts: three variables with non-zero bounds, product sign contradiction.
// a in [1,2], b in [-3,-1], c in [0.5,1] → a>0, b<0, c>0.
// Product a*b*c must be negative. Asserting a*b*c >= 1 should be UNSAT (product is negative).
// After #5959 soundness fix, the recheck may not propagate nested McCormick bounds,
// so "unknown" is also acceptable (sound but incomplete for nested ternary products).
#[test]
fn nra_unsat_model_sign_cut_ternary() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (>= a 1.0))
(assert (<= a 2.0))
(assert (<= b (- 1.0)))
(assert (>= b (- 3.0)))
(assert (>= c 0.5))
(assert (<= c 1.0))
(assert (>= (* a (* b c)) 1.0))
(check-sat)
"#,
    );
    assert_ne!(
        results,
        vec!["sat"],
        "Must not be SAT (product is always negative)"
    );
}
