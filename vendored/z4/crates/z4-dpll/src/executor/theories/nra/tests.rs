// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::Executor;
use z4_frontend::parse;

fn run_script(input: &str) -> Vec<String> {
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("SMT-LIB script should execute")
}

// Basic QF_NRA: x*y > 0 with x > 0 and y > 0
#[test]
fn nra_sat_positive_product() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (> x 1.0))
(assert (> y 1.0))
(assert (> (* x y) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// QF_NRA: x*x >= 0 is always true (square is non-negative)
#[test]
fn nra_sat_square_nonneg() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (>= (* x x) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// QF_NRA UNSAT: x > 0, y > 0, x*y < 0 is impossible
#[test]
fn nra_unsat_sign_conflict() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (> x 0.0))
(assert (> y 0.0))
(assert (< (* x y) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// QF_NRA: constant * variable (linear) - should be straightforward
#[test]
fn nra_sat_constant_mul() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (= (* 2.0 x) 6.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// QF_NRA: product with fixed values (tangent plane converges trivially)
#[test]
fn nra_sat_fixed_product() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x 2.0))
(assert (= y 3.0))
(assert (<= (* x y) 7.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// QF_NRA: negative × negative = positive via sign reasoning
#[test]
fn nra_unsat_neg_neg_product_positive() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (< x 0.0))
(assert (< y 0.0))
(assert (< (* x y) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// --- Tests exercising order lemmas ---

// Order lemma: bounded product with ordering constraint
// x in [1,3], y in [2,4], x*y <= 5 is SAT (e.g., x=1, y=2, x*y=2)
#[test]
fn nra_sat_bounded_product_order() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 1.0))
(assert (<= x 3.0))
(assert (>= y 2.0))
(assert (<= y 4.0))
(assert (<= (* x y) 5.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Order lemma: tight product bound that requires ordering reasoning
// x in [2,3], y in [2,3], x*y >= 10 is UNSAT (max product is 3*3=9)
#[test]
fn nra_unsat_product_exceeds_bound() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 2.0))
(assert (<= x 3.0))
(assert (>= y 2.0))
(assert (<= y 3.0))
(assert (>= (* x y) 10.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Order lemma: product ordering with mixed signs
// x in [-3,-1], y in [2,4], x*y >= 0 is UNSAT (negative * positive < 0)
#[test]
fn nra_unsat_mixed_sign_product_positive() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x (- 3.0)))
(assert (<= x (- 1.0)))
(assert (>= y 2.0))
(assert (<= y 4.0))
(assert (>= (* x y) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// --- Tests exercising monotonicity lemmas ---

// Monotonicity: product with tighter bounds
// x in [1,2], y in [1,2], x*y in [1,4] is SAT
#[test]
fn nra_sat_monotone_bounded_product() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 1.0))
(assert (<= x 2.0))
(assert (>= y 1.0))
(assert (<= y 2.0))
(assert (>= (* x y) 1.0))
(assert (<= (* x y) 4.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Monotonicity: product with impossible lower bound
// x in [0,1], y in [0,1], x*y >= 2 is UNSAT
#[test]
fn nra_unsat_monotone_product_too_large() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0.0))
(assert (<= x 1.0))
(assert (>= y 0.0))
(assert (<= y 1.0))
(assert (>= (* x y) 2.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// --- Quadratic constraint tests (gamma-crown patterns) ---

// Quadratic: x^2 + y^2 <= 1 with x,y > 0.5 is UNSAT
// (0.5^2 + 0.5^2 = 0.5, but x > 0.5 means x^2 > 0.25 for each)
#[test]
fn nra_sat_quadratic_unit_circle() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (<= (+ (* x x) (* y y)) 1.0))
(assert (> x 0.0))
(assert (> y 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Polynomial approximation pattern (gamma-crown style):
// a*x^2 + b*x + c = y with bounds
#[test]
fn nra_sat_polynomial_approx() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0.0))
(assert (<= x 1.0))
(assert (= y (+ (* x x) x 1.0)))
(assert (>= y 1.0))
(assert (<= y 3.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// --- Acceptance criteria tests (Phase 2 design) ---

// Model patching: fixed product value (patching makes the model consistent
// without needing lemma refinement)
#[test]
fn nra_sat_model_patching_fixed() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x 3.0))
(assert (= y 4.0))
(assert (= (* x y) 12.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Model patching: product with bounded region (tangent + order + monotone
// should converge via model patching shortcut)
#[test]
fn nra_sat_model_patching_bounded() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x 2.0))
(assert (>= y 1.0))
(assert (<= y 5.0))
(assert (>= (* x y) 2.0))
(assert (<= (* x y) 10.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Order + tangent convergence: product tightly bounded
// x = 5, x*y = 15, so y must be 3
#[test]
fn nra_sat_order_tangent_convergence() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x 5.0))
(assert (= (* x y) 15.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Tangent plane refinement: narrow interval around a product value
// x in [1,2], y in [1,2], x*y in [3,5]
// Feasible: x=2, y=2, x*y=4
//
// In debug mode, the NRA iteration limit is reduced (#6785) so this
// may return "unknown" instead of "sat". Release mode with the full
// 50-iteration budget always finds the solution.
#[test]
fn nra_sat_tangent_narrow_interval() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 1.0))
(assert (<= x 2.0))
(assert (>= y 1.0))
(assert (<= y 2.0))
(assert (>= (* x y) 3.0))
(assert (<= (* x y) 5.0))
(check-sat)
"#,
    );
    let result = &results[0];
    assert!(
        result == "sat" || result == "unknown",
        "expected sat or unknown, got {result}"
    );
}

// --- Unbounded square tests (tangent fallback for McCormick) ---

// Square non-negativity: x^2 < 0 is impossible (no bounds on x needed)
#[test]
fn nra_unsat_square_negative() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (< (* x x) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Square non-negativity with stricter bound: x^2 < -1 is impossible
#[test]
fn nra_unsat_square_less_than_neg1() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (< (* x x) (- 1.0)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Unbounded product: x=2, y=3, xy=6 (model patching, no explicit bounds)
#[test]
fn nra_sat_unbounded_fixed_product() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (= x 2.0))
(assert (= y 3.0))
(assert (= (* x y) 6.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// x^2 >= 0 is trivially satisfiable (any x works)
#[test]
fn nra_sat_square_nonneg_trivial() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (>= (* x x) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// --- gamma-crown neural network verification patterns ---

// Quadratic bound: x^2+y^2 > 2 on unit box is UNSAT (max is 1+1=2)
#[test]
fn nra_unsat_quadratic_box_bound() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 0.0))
(assert (<= x 1.0))
(assert (>= y 0.0))
(assert (<= y 1.0))
(assert (> (+ (* x x) (* y y)) 2.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// NN layer with product weights: max(w1*x1+w2*x2) = 1.5+1.5 = 3, so y>4 is UNSAT
#[test]
fn nra_unsat_nn_layer_product_bound() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x1 Real)
(declare-const x2 Real)
(declare-const w1 Real)
(declare-const w2 Real)
(declare-const y Real)
(assert (>= x1 (- 1.0)))
(assert (<= x1 1.0))
(assert (>= x2 (- 1.0)))
(assert (<= x2 1.0))
(assert (>= w1 0.5))
(assert (<= w1 1.5))
(assert (>= w2 0.5))
(assert (<= w2 1.5))
(assert (= y (+ (* w1 x1) (* w2 x2))))
(assert (> y 4.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// #5959: x^2 = 2 has solutions at x = ±√2 but the NRA solver's
// incremental linearization used to incorrectly return UNSAT when the
// linear relaxation became infeasible around the irrational solution.
// The fix ensures post-refinement LRA UNSAT is demoted to Unknown when
// the UNSAT depends on approximation lemmas (tangent planes, sign cuts).
#[test]
fn nra_irrational_solution_not_false_unsat_5959() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (= (* x x) 2.0))
(check-sat)
"#,
    );
    // Must NOT return "unsat" — x = ±√2 are valid solutions.
    // "unknown" or "sat" are acceptable.
    assert_ne!(results, vec!["unsat"], "BUG #5959: false UNSAT on x^2 = 2");
}

// x^2 = -1 has no real solutions (x^2 >= 0 for all real x).
// Even-power non-negativity lemma (exact algebraic) should detect this.
#[test]
fn nra_even_power_negative_is_genuine_unsat_5959() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (= (* x x) (- 1.0)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// --- Phase 2 acceptance criteria (#5712) ---

// Order lemma (bounded variant): a ∈ [0,1], b ∈ [2,3], c ∈ [1,2]
// max(a*c) = 1*2 = 2, min(b*c) = 2*1 = 2. For a*c >= b*c we need
// a*c >= 2, which forces a=1, c=2 (corner). But then b*c = 2*b >= 4
// (since b >= 2), so b*c >= 4 > 2 = a*c. Contradiction.
// McCormick envelope detects this via upper bound on a*c and lower
// bound on b*c.
#[test]
fn nra_unsat_order_bounded_acceptance_5712() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (>= a 0.0))
(assert (<= a 1.0))
(assert (>= b 2.0))
(assert (<= b 3.0))
(assert (>= c 1.0))
(assert (<= c 2.0))
(assert (>= (* a c) (* b c)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Order lemma (unbounded): a < b, c > 0 => a*c < b*c
// Without bounds on a,b,c, McCormick cannot produce envelopes.
// Currently returns "unknown" — order lemmas need DPLL(T) theory
// lemma channel to handle unbounded cases (#5712).
#[test]
fn nra_order_unbounded_known_limitation_5712() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(assert (< a b))
(assert (> c 0.0))
(assert (>= (* a c) (* b c)))
(check-sat)
"#,
    );
    // "unsat" is correct, "unknown" is acceptable (incomplete).
    // "sat" would be a soundness bug.
    assert_ne!(results, vec!["sat"], "BUG: sat on unsatisfiable formula");
}

// Monotonicity acceptance criterion: x ∈ [1,2], y ∈ [3,4], x*y > 10 is UNSAT
// (max product is 2*4 = 8 < 10)
// McCormick upper bound 2 at (xL=1, yU=4): m ≤ xL*y + yU*x - xL*yU = y + 4x - 4
// At x=2,y=4: m ≤ 4+8-4 = 8 < 10, so UNSAT.
#[test]
fn nra_unsat_monotone_acceptance_5712() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x 1.0))
(assert (<= x 2.0))
(assert (>= y 3.0))
(assert (<= y 4.0))
(assert (> (* x y) 10.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Higher-degree acceptance criterion: x > 0, y > 0, z > 0, x*y*z < 0 is UNSAT
// (positive * positive * positive is always positive)
// Detected by sign propagation across nested monomials.
#[test]
fn nra_unsat_higher_degree_acceptance_5712() {
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

// --- UF+NRA combined solver tests (#6294) ---

#[test]
fn test_uf_nra_sat_basic() {
    // f(x*x) = x+1 with x > 0 is SAT
    let results = run_script(
        r#"
(set-logic QF_UFNRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (= (f (* x x)) (+ x 1.0)))
(assert (> x 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

#[test]
fn test_uf_nra_unsat_zero_square() {
    // x = 0, x*x > 0 is UNSAT (0*0 = 0, not > 0)
    let results = run_script(
        r#"
(set-logic QF_UFNRA)
(declare-fun x () Real)
(assert (= x 0.0))
(assert (> (* x x) 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

#[test]
fn test_uf_nra_congruence() {
    // f is uninterpreted; if x = y then f(x) = f(y)
    // f(x) != f(y), x = y is UNSAT by EUF congruence
    let results = run_script(
        r#"
(set-logic QF_UFNRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

#[test]
fn test_uf_nra_interface_propagation() {
    // Tests Nelson-Oppen interface propagation between NRA and EUF.
    // x > 0, y > 0, x*y < 0 is UNSAT (positive product is positive).
    // Combined with UF: f(x) = f(y) is satisfiable on its own.
    // The UNSAT comes purely from NRA; EUF adds no conflict.
    // This exercises the combined solver without requiring nonlinear
    // terms inside UF function arguments (#6890).
    let results = run_script(
        r#"
(set-logic QF_UFNRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (> x 0.0))
(assert (> y 0.0))
(assert (< (* x y) 0.0))
(assert (= (f x) (f y)))
(check-sat)
"#,
    );
    // x>0, y>0, x*y<0 is UNSAT by NRA sign reasoning
    assert_eq!(results, vec!["unsat"]);
}

#[test]
fn test_uf_nra_nonlinear_sat() {
    // NRA with UF: f(x*x) > 0, x > 1 is SAT (any f works)
    let results = run_script(
        r#"
(set-logic QF_UFNRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(assert (> (f (* x x)) 0.0))
(assert (> x 1.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// QF_NRA symbolic division UNSAT: x > 1 AND (/ 1 x) >= 1 (#6811)
#[test]
fn nra_unsat_symbolic_division() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (> x 1))
(assert (>= (/ 1 x) 1))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// QF_NRA symbolic division SAT: x > 2 AND (/ 1 x) > 0
#[test]
fn nra_sat_symbolic_division() {
    let results = run_script(
        r#"
(set-logic QF_NRA)
(declare-const x Real)
(assert (> x 2))
(assert (> (/ 1 x) 0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

include!("../nra_sign_tests.rs");
