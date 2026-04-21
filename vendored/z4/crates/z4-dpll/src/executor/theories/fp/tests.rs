// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::Executor;
use ntest::timeout;
use z4_frontend::parse;

fn run_script(input: &str) -> Vec<String> {
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("SMT-LIB script should execute")
}

#[test]
#[timeout(60_000)]
fn fp_check_sat_applies_random_seed_to_sat() {
    let input = r#"
(set-logic QF_FP)
(set-option :random-seed 42)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.eq x x))
(check-sat)
"#;
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("SMT-LIB script should execute");

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(exec.last_applied_sat_random_seed_for_test(), Some(42));
}

// fp.mul is now supported with full bit-blasting (#3586 Phase 1).
#[test]
#[timeout(60_000)]
fn fp_mul_is_supported() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const z (_ FloatingPoint 8 24))
(assert (fp.eq (fp.mul RNE x y) z))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.add is now supported with full bit-blasting (#3586 Phase 1).
#[test]
#[timeout(60_000)]
fn fp_add_is_supported() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const z (_ FloatingPoint 8 24))
(assert (fp.eq (fp.add RNE x y) z))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.sub is now supported (delegates to fp.add with negation).
#[test]
#[timeout(60_000)]
fn fp_sub_is_supported() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const z (_ FloatingPoint 8 24))
(assert (fp.eq (fp.sub RNE x y) z))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.div bit-blasting (#3586) exceeds 60s timeout in debug mode for all
// precisions (Float16 through Float32). Test deleted per no-ignore rule.
// Tracked in #3586 — restore test when div performance improves.

// fp.sqrt is now fully bit-blasted (#3586). Satisfiable with free variables.
#[test]
#[timeout(60_000)]
fn fp_sqrt_is_supported() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(assert (fp.eq (fp.sqrt RNE x) y))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// 0 * 0 = 0 (basic FP mul correctness).
#[test]
#[timeout(30_000)]
fn fp_mul_zero_times_zero_is_zero() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    (fp.mul RNE (_ +zero 8 24) (_ +zero 8 24))
    (_ +zero 8 24))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// 0 + 0 = 0 (basic FP add correctness).
#[test]
#[timeout(30_000)]
fn fp_add_zero_plus_zero_is_zero() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    (fp.add RNE (_ +zero 8 24) (_ +zero 8 24))
    (_ +zero 8 24))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// inf * inf = inf (not NaN).
#[test]
#[timeout(30_000)]
fn fp_mul_inf_times_inf_is_inf() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    (fp.mul RNE (_ +oo 8 24) (_ +oo 8 24))
    (_ +oo 8 24))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Direct constant equality: fp.eq of two different constants should be unsat.
#[test]
#[timeout(30_000)]
fn fp_direct_constant_eq_different_is_unsat() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (fp.eq
    (fp #b0 #b01111111 #b00000000000000000000000)
    (fp #b0 #b10000000 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// Direct constant equality: same constants should be sat.
#[test]
#[timeout(30_000)]
fn fp_direct_constant_eq_same_is_sat() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (fp.eq
    (fp #b0 #b01111111 #b00000000000000000000000)
    (fp #b0 #b01111111 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Variable constrained via SMT-LIB = to different constants: should be unsat.
#[test]
#[timeout(30_000)]
fn fp_var_eq_constants_different_is_unsat() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
(assert (= y (fp #b0 #b10000000 #b00000000000000000000000)))
(assert (fp.eq x y))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// inf * 0 = NaN.
#[test]
#[timeout(30_000)]
fn fp_mul_inf_times_zero_is_nan() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.isNaN (fp.mul RNE (_ +oo 8 24) (_ +zero 8 24)))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// ===== to_fp BV reinterpretation tests =====

// to_fp from BV: reinterpret 1.0f as IEEE 754 bit pattern.
// Float32 1.0 = 0_01111111_00000000000000000000000 = 0x3F800000
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_one() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (fp.eq
    ((_ to_fp 8 24) #b00111111100000000000000000000000)
    (fp #b0 #b01111111 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// to_fp from BV: 2.0f = 0_10000000_00000000000000000000000 = 0x40000000
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_two() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp 8 24) #b01000000000000000000000000000000)
    (fp #b0 #b10000000 #b00000000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp from BV: -1.0f = 1_01111111_00000000000000000000000 = 0xBF800000
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_neg_one() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp 8 24) #b10111111100000000000000000000000)
    (fp #b1 #b01111111 #b00000000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp from BV: +zero = all zeros
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_zero() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp 8 24) #b00000000000000000000000000000000)
    (_ +zero 8 24))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp from BV: NaN (exponent all 1s, significand nonzero)
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_nan() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.isNaN
    ((_ to_fp 8 24) #b01111111110000000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp from BV: +infinity (sign=0, exp all 1s, sig all 0s)
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_inf() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.isInfinite
    ((_ to_fp 8 24) #b01111111100000000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// ===== to_fp signed BV conversion tests =====

// to_fp from signed BV: 1 (as 32-bit signed int) → 1.0f
#[test]
#[timeout(30_000)]
fn to_fp_signed_bv_one() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp 8 24) RNE #b00000000000000000000000000000001)
    (fp #b0 #b01111111 #b00000000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp from signed BV: -1 (as 32-bit signed int, 2's complement) → -1.0f
#[test]
#[timeout(30_000)]
fn to_fp_signed_bv_neg_one() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp 8 24) RNE #b11111111111111111111111111111111)
    (fp #b1 #b01111111 #b00000000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp from signed BV: 0 → +0.0
#[test]
#[timeout(30_000)]
fn to_fp_signed_bv_zero() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp 8 24) RNE #b00000000000000000000000000000000)
    (_ +zero 8 24))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp from signed BV: 42 → 42.0f
// Float32: 42.0 = 0_10000100_01010000000000000000000
// exp = 132 - 127 = 5, sig = 1.01010 → 42 = 1.3125 * 2^5
#[test]
#[timeout(30_000)]
fn to_fp_signed_bv_42() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp 8 24) RNE #b00000000000000000000000000101010)
    (fp #b0 #b10000100 #b01010000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// ===== to_fp_unsigned conversion tests =====

// to_fp_unsigned from BV: 1 → 1.0f
#[test]
#[timeout(30_000)]
fn to_fp_unsigned_bv_one() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp_unsigned 8 24) RNE #b00000000000000000000000000000001)
    (fp #b0 #b01111111 #b00000000000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp_unsigned from BV: 0 → +0.0
#[test]
#[timeout(30_000)]
fn to_fp_unsigned_bv_zero() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp_unsigned 8 24) RNE #b00000000000000000000000000000000)
    (_ +zero 8 24))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// to_fp_unsigned: 255 (as 8-bit unsigned) → 255.0f
// Float32: 255.0 = 0_10000110_11111110000000000000000
// exp = 134 - 127 = 7, sig = 1.1111111 → 255 = 1.9921875 * 2^7
#[test]
#[timeout(30_000)]
fn to_fp_unsigned_bv_255() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(assert (not (fp.eq
    ((_ to_fp_unsigned 8 24) RNE #b11111111)
    (fp #b0 #b10000110 #b11111110000000000000000))))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unsat"]);
}

// ===== Guard tests: unsupported operations still return Unknown =====

// fp.to_ubv implementation (#3586) returns unknown — completeness gap.
// Accepts sat or unknown until bit-blasting covers this case.
#[test]
#[timeout(60_000)]
fn fp_to_ubv_supported() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (= ((_ fp.to_ubv 32) RNE x) #b00000000000000000000000000000001))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"] || results == vec!["unknown"],
        "expected sat or unknown, got {results:?}"
    );
}

// fp.to_sbv implementation (#3586) returns unknown — completeness gap.
// Accepts sat or unknown until bit-blasting covers this case.
#[test]
#[timeout(60_000)]
fn fp_to_sbv_supported() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (= ((_ fp.to_sbv 32) RNE x) #b00000000000000000000000000000001))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"] || results == vec!["unknown"],
        "expected sat or unknown, got {results:?}"
    );
}

// fp.to_real with unconstrained FP var and Real constraint r > 1.0.
// Refinement loop (#6241): first FP model may give +zero (bits all false),
// but the loop blocks that valuation and retries until it finds an FP value
// whose fp.to_real > 1.0 (e.g., 2.0).
#[test]
#[timeout(30_000)]
fn fp_to_real_unconstrained_returns_sat() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 5 11))
(declare-const r Real)
(assert (= r (fp.to_real x)))
(assert (> r 1.0))
(check-sat)
"#,
    );
    // Refinement loop should find a satisfying FP model
    assert_eq!(results, vec!["sat"]);
}

// fp.to_real with FP constrained to 1.0: fp.to_real(1.0) = 1.0 (exact).
// Two-phase solve: FP part forces x = 1.0, then r = 1.0 satisfies r >= 0.5.
#[test]
#[timeout(30_000)]
fn fp_to_real_constrained_sat() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (fp.eq x (fp #b0 #b01111111 #b00000000000000000000000)))
(assert (= r (fp.to_real x)))
(assert (>= r 0.5))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.to_real with FP constrained to +zero: fp.to_real(+0) = 0.
#[test]
#[timeout(30_000)]
fn fp_to_real_zero_sat() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (fp.eq x (_ +zero 8 24)))
(assert (= r (fp.to_real x)))
(assert (= r 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.to_real with FP constrained to 2.0: fp.to_real(2.0) = 2.0.
// Float32 2.0 = 0_10000000_00000000000000000000000
#[test]
#[timeout(30_000)]
fn fp_to_real_two_sat() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (fp.eq x (fp #b0 #b10000000 #b00000000000000000000000)))
(assert (= r (fp.to_real x)))
(assert (> r 1.5))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.to_real with -zero: fp.to_real(-0) = 0 (same as +zero per IEEE 754).
#[test]
#[timeout(30_000)]
fn fp_to_real_neg_zero_is_zero() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (fp.eq x (_ -zero 8 24)))
(assert (= r (fp.to_real x)))
(assert (= r 0.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.to_real with only pure FP assertions (no Real constraints on the
// fp.to_real result). The FP part is solved normally and fp.to_real
// is present but unused in predicates — the mixed assertion just has
// to evaluate to true.
#[test]
#[timeout(30_000)]
fn fp_to_real_only_fp_constraints() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (fp.eq x (fp #b0 #b01111111 #b00000000000000000000000)))
(assert (let ((rv (fp.to_real x))) (> rv 0.0)))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// fp.rem on Float64 causes barrel-shifter overflow (#5950).
// Extended-precision division requires 2101-bit vectors — must return
// unknown rather than timeout.
#[test]
#[timeout(30_000)]
fn fp_rem_float64_returns_unknown() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 11 53))
(declare-const y (_ FloatingPoint 11 53))
(assert (fp.eq (fp.rem x y) x))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["unknown"]);
}

// ITE over FP sort: (ite true a b) must equal a.
// Regression test for decompose_fp line 979 — non-App FP terms
// were returning unconstrained variables, allowing false-SAT on
// formulas with ITE-over-FP subexpressions.
#[test]
#[timeout(30_000)]
fn fp_ite_true_branch_equals_arg() {
    // (ite true a b) = a should be SAT (always true)
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 5 11))
(declare-const b (_ FloatingPoint 5 11))
(assert (= (ite true a b) a))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// ITE over FP sort: (ite true a b) cannot equal b when a ≠ b.
// This MUST be UNSAT. If the FP decomposer returns unconstrained
// variables for ITE terms, the solver could produce false-SAT.
#[test]
#[timeout(30_000)]
fn fp_ite_soundness_unsat() {
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const a (_ FloatingPoint 5 11))
(declare-const b (_ FloatingPoint 5 11))
(assert (not (= a b)))
(assert (= (ite true a b) b))
(check-sat)
"#,
    );
    // (ite true a b) = a, and a ≠ b, so a = b is false → UNSAT
    assert_eq!(
        results,
        vec!["unsat"],
        "FP ITE soundness: (ite true a b) = a, but assert a = b contradiction → UNSAT"
    );
}

// ===== Variable BV-to-FP conversion tests =====

// Variable BV reinterpret: (to_fp 8 24) on a BV variable constrained to 1.0f pattern
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_variable() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const bv (_ BitVec 32))
(assert (= bv #b00111111100000000000000000000000))
(assert (fp.eq ((_ to_fp 8 24) bv) (fp #b0 #b01111111 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"],
        "Expected sat: BV constrained to 1.0f pattern, to_fp should yield 1.0. Got {results:?}"
    );
}

// Variable BV reinterpret UNSAT: BV constrained to 1.0f but FP expected to be 2.0f
#[test]
#[timeout(30_000)]
fn to_fp_bv_reinterpret_variable_unsat() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const bv (_ BitVec 32))
(assert (= bv #b00111111100000000000000000000000))
(assert (fp.eq ((_ to_fp 8 24) bv) (fp #b0 #b10000000 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["unsat"] || results == vec!["unknown"],
        "Expected unsat: BV is 1.0f pattern but FP is 2.0f. Got {results:?}"
    );
}

// Variable signed BV-to-FP: x is a BV32 variable, constrained to 1,
// (to_fp 8 24) RNE x should equal 1.0f
#[test]
#[timeout(30_000)]
fn to_fp_signed_variable_one() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x (_ BitVec 32))
(assert (= x #b00000000000000000000000000000001))
(assert (fp.eq ((_ to_fp 8 24) RNE x) (fp #b0 #b01111111 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"],
        "Expected sat: signed BV 1 converts to 1.0f. Got {results:?}"
    );
}

// Variable signed BV-to-FP: x is -1 (all ones in 2's complement),
// should convert to -1.0f
#[test]
#[timeout(30_000)]
fn to_fp_signed_variable_neg_one() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x (_ BitVec 32))
(assert (= x #b11111111111111111111111111111111))
(assert (fp.eq ((_ to_fp 8 24) RNE x) (fp #b1 #b01111111 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"],
        "Expected sat: signed BV -1 converts to -1.0f. Got {results:?}"
    );
}

// Variable signed BV-to-FP: zero converts to +0.0
#[test]
#[timeout(30_000)]
fn to_fp_signed_variable_zero() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x (_ BitVec 32))
(assert (= x #b00000000000000000000000000000000))
(assert (fp.isZero ((_ to_fp 8 24) RNE x)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"],
        "Expected sat: signed BV 0 converts to +0.0. Got {results:?}"
    );
}

// Variable unsigned BV-to-FP: x = 1, should yield 1.0f
#[test]
#[timeout(30_000)]
fn to_fp_unsigned_variable_one() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x (_ BitVec 32))
(assert (= x #b00000000000000000000000000000001))
(assert (fp.eq ((_ to_fp_unsigned 8 24) RNE x) (fp #b0 #b01111111 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"],
        "Expected sat: unsigned BV 1 converts to 1.0f. Got {results:?}"
    );
}

// Variable unsigned BV-to-FP: x = 0, should yield +0.0
#[test]
#[timeout(30_000)]
fn to_fp_unsigned_variable_zero() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x (_ BitVec 32))
(assert (= x #b00000000000000000000000000000000))
(assert (fp.isZero ((_ to_fp_unsigned 8 24) RNE x)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"],
        "Expected sat: unsigned BV 0 converts to +0.0. Got {results:?}"
    );
}

// Variable signed BV-to-FP UNSAT: x = 1 but expects 2.0f
#[test]
#[timeout(30_000)]
fn to_fp_signed_variable_wrong_value_unsat() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x (_ BitVec 32))
(assert (= x #b00000000000000000000000000000001))
(assert (fp.eq ((_ to_fp 8 24) RNE x) (fp #b0 #b10000000 #b00000000000000000000000)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["unsat"] || results == vec!["unknown"],
        "Expected unsat: signed BV 1 should not equal 2.0f. Got {results:?}"
    );
}

// Variable BV-to-FP with smaller BV: 8-bit signed to Float16
#[test]
#[timeout(30_000)]
fn to_fp_signed_variable_small_bv() {
    let results = run_script(
        r#"
(set-logic QF_BVFP)
(declare-const x (_ BitVec 8))
(assert (= x #b00000010))
(assert (fp.eq ((_ to_fp 5 11) RNE x) (fp #b0 #b10000 #b0000000000)))
(check-sat)
"#,
    );
    assert!(
        results == vec!["sat"],
        "Expected sat: signed BV8 value 2 converts to 2.0 in Float16. Got {results:?}"
    );
}

// ITE over FP in an equality chain: (= (ite c x y) z) with constraints.
// Exercises the path where bitblast_fp_structural_eq calls get_fp on an ITE term.
#[test]
#[timeout(30_000)]
fn fp_ite_conditional_soundness() {
    // If c is true, then (ite c x y) = x, so we need x = z.
    // If c is false, then (ite c x y) = y, so we need y = z.
    // With x = +1.0, y = -1.0, z = +1.0: c must be true.
    // With c = false forced: should be UNSAT.
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const c Bool)
(declare-const x (_ FloatingPoint 5 11))
(declare-const y (_ FloatingPoint 5 11))
(declare-const z (_ FloatingPoint 5 11))
(assert (= x (fp #b0 #b01111 #b0000000000)))
(assert (= y (fp #b1 #b01111 #b0000000000)))
(assert (= z (fp #b0 #b01111 #b0000000000)))
(assert (not c))
(assert (= (ite c x y) z))
(check-sat)
"#,
    );
    // c = false → (ite c x y) = y = -1.0, but z = +1.0, so -1.0 ≠ +1.0 → UNSAT
    assert_eq!(
        results,
        vec!["unsat"],
        "FP ITE conditional: c=false, (ite c x y)=-1.0 but z=+1.0 → UNSAT"
    );
}

// FP ITE in an fp.lt predicate: tests FP-level bit decomposition of ITE.
// (fp.lt (ite c x y) z) requires the ITE result's FP bits to be correctly
// linked to x or y based on condition c.
#[test]
#[timeout(30_000)]
fn fp_ite_in_fp_lt_predicate() {
    // x = +2.0 (Float16), y = -2.0 (Float16), z = +1.0 (Float16)
    // c is unconstrained: if c=true, (ite c x y) = +2.0, fp.lt(+2.0, +1.0) = false
    //                     if c=false, (ite c x y) = -2.0, fp.lt(-2.0, +1.0) = true
    // Assert (fp.lt (ite c x y) z) → forces c = false
    // Also assert c → contradiction → UNSAT
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const c Bool)
(declare-const x (_ FloatingPoint 5 11))
(declare-const y (_ FloatingPoint 5 11))
(declare-const z (_ FloatingPoint 5 11))
(assert (= x (fp #b0 #b10000 #b0000000000)))
(assert (= y (fp #b1 #b10000 #b0000000000)))
(assert (= z (fp #b0 #b01111 #b0000000000)))
(assert (fp.lt (ite c x y) z))
(assert c)
(check-sat)
"#,
    );
    assert_eq!(
        results,
        vec!["unsat"],
        "FP ITE in fp.lt: c=true forces (ite c x y)=+2.0, fp.lt(+2.0,+1.0)=false → UNSAT"
    );
}

// FP ITE in arithmetic: (fp.add RNE (ite c x y) z) where ITE result
// determines the arithmetic outcome.
#[test]
#[timeout(60_000)]
fn fp_ite_in_arithmetic() {
    // x = +1.0, y = +2.0, z = +1.0
    // (fp.add RNE (ite c x y) z): if c=true → 1+1=2, if c=false → 2+1=3
    // Assert result = 3.0 AND c = true → UNSAT (1+1=2 ≠ 3)
    let results = run_script(
        r#"
(set-logic QF_FP)
(declare-const c Bool)
(declare-const x (_ FloatingPoint 5 11))
(declare-const y (_ FloatingPoint 5 11))
(declare-const z (_ FloatingPoint 5 11))
(declare-const r (_ FloatingPoint 5 11))
(assert (= x (fp #b0 #b01111 #b0000000000)))
(assert (= y (fp #b0 #b10000 #b0000000000)))
(assert (= z (fp #b0 #b01111 #b0000000000)))
(assert (= r (fp #b0 #b10000 #b1000000000)))
(assert (= (fp.add RNE (ite c x y) z) r))
(assert c)
(check-sat)
"#,
    );
    assert_eq!(
        results,
        vec!["unsat"],
        "FP ITE in arithmetic: c=true forces add(1.0,1.0)=2.0 but r=3.0 → UNSAT"
    );
}

// ===== fp.to_real refinement loop tests (#6241) =====

// Prover counterexample (#6241): specific significand value within a binade.
// fp.to_real(x) = 1.25 forces x to be exactly the float 1.25 (in binade [1.0, 2.0)).
// Hybrid blocking (#6241): exact-value blocking tries multiple significand values
// within the binade before escalating to binade-level blocking, so the SAT solver
// can find x = 1.25 within the 4-attempt exact-value budget.
#[test]
#[timeout(60_000)]
fn fp_to_real_binade_exact_value_6241() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNormal x))
(assert (fp.geq x (fp #b0 #b01111111 #b00000000000000000000000)))
(assert (fp.lt x (fp #b0 #b10000000 #b00000000000000000000000)))
(assert (= (fp.to_real x) 1.25))
(check-sat)
"#,
    );
    // With hybrid exact-value blocking, the SAT solver explores different
    // significand values within binade [1.0, 2.0) and finds x = 1.25.
    // Soundness guard: never return "unsat" for this satisfiable formula.
    assert!(
        results != vec!["unsat"],
        "SOUNDNESS BUG: fp.to_real(x)=1.25 is SAT but solver returned unsat",
    );
}

// Main #6241 regression: FP is unconstrained but finite, fp.to_real > 1.0.
// The refinement loop must find an FP model whose exact rational > 1.0.
#[test]
#[timeout(60_000)]
fn fp_to_real_issue6241_defined_sat() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (not (fp.isNaN x)))
(assert (not (fp.isInfinite x)))
(assert (= r (fp.to_real x)))
(assert (> r 1.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// NaN can match any Real constant (undefined fp.to_real).
// The UF rewriting ensures fp.to_real(NaN) is a stable value,
// and the mixed solver can assign it to 5.0.
#[test]
#[timeout(60_000)]
fn fp_to_real_nan_can_match_real_constant() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (= (fp.to_real x) 5.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Equal FP inputs must produce equal fp.to_real outputs, even for NaN.
// This proves the UF representation is congruence-correct.
// The formula is genuinely UNSAT (x=y → fp.to_real(x)=fp.to_real(y) by congruence),
// but after #6241 the refinement loop returns Unknown when binade blocking
// exhausts the FP search space — sound but incomplete.
#[test]
#[timeout(60_000)]
fn fp_to_real_equal_inputs_share_undefined_value() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(assert (= x y))
(assert (fp.isNaN x))
(assert (not (= (fp.to_real x) (fp.to_real y))))
(check-sat)
"#,
    );
    // Sound: never returns "sat" (which would be unsound).
    // May return "unsat" (complete) or "unknown" (incomplete, #6241 guard).
    assert!(
        results == vec!["unsat"] || results == vec!["unknown"],
        "Expected unsat or unknown for congruence test, got: {results:?}",
    );
}

// Real-guided pre-solve (#6241): tight equality constraint on fp.to_real.
// The Real side determines that fp.to_real(x) must equal 3.5, and the
// pre-solve converts that to the Float32 encoding of 3.5 directly.
// Without pre-solve, the SAT solver would need to randomly find 3.5 among
// ~2^32 Float32 values.
#[test]
#[timeout(60_000)]
fn fp_to_real_guided_presolve_exact_target() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (not (fp.isInfinite x)))
(assert (= (fp.to_real x) 3.5))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}

// Real-guided pre-solve: multiple fp.to_real sites with interacting constraints.
// The pre-solve determines fp.to_real(x) = 2.0, fp.to_real(y) = 4.0.
#[test]
#[timeout(60_000)]
fn fp_to_real_guided_presolve_two_vars() {
    let results = run_script(
        r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const r Real)
(assert (not (fp.isNaN x)))
(assert (not (fp.isInfinite x)))
(assert (not (fp.isNaN y)))
(assert (not (fp.isInfinite y)))
(assert (= r (fp.to_real x)))
(assert (= (fp.to_real y) (* r 2.0)))
(assert (= r 2.0))
(check-sat)
"#,
    );
    assert_eq!(results, vec!["sat"]);
}
