// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! evaluate_term tests: bitvector theory predicates, BV shift/div/concat/extend,
//! and model validation tests (validate_model, validate_sat_assumptions).

use super::*;

// ==========================================================================
// evaluate_term: theory predicates
// ==========================================================================

#[test]
fn test_evaluate_term_bv_predicates_evaluate_concretely() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let bvult = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![x, y], Sort::Bool);
    let bvslt = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvslt"), vec![x, y], Sort::Bool);

    let mut bv_values = HashMap::new();
    bv_values.insert(x, BigInt::from(0xFFu8)); // -1 signed, 255 unsigned
    bv_values.insert(y, BigInt::from(1u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });

    // Unsigned: 255 < 1 is false
    assert_eq!(
        executor.evaluate_term(&model, bvult),
        EvalValue::Bool(false)
    );
    // Signed: -1 < 1 is true
    assert_eq!(executor.evaluate_term(&model, bvslt), EvalValue::Bool(true));
}

#[test]
fn test_validate_model_rejects_false_bv_predicate_assertion() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let bvult = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![x, y], Sort::Bool);
    executor.ctx.assertions.push(bvult);

    let mut bv_values = HashMap::new();
    bv_values.insert(x, BigInt::from(0u8));
    bv_values.insert(y, BigInt::from(0u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("Expected false bvult assertion to be rejected");
    assert!(
        err.contains("Assertion 0 violated"),
        "Unexpected error: {err}"
    );
}

#[test]
fn test_validate_model_rejects_unknown_bv_with_uf_subterms() {
    // (#3903) Fail closed: if bvult(f(u), g(u)) is Unknown, model
    // validation must reject and the SAT path must degrade to Unknown.
    let mut executor = Executor::new();
    let u = executor
        .ctx
        .terms
        .mk_var("u", Sort::Uninterpreted("U".to_string()));
    let f_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![u], Sort::bitvec(8));
    let g_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![u], Sort::bitvec(8));
    let bvult = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![f_u, g_u], Sort::Bool);
    executor.ctx.assertions.push(bvult);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("UF-containing BV assertion Unknown should be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_evaluate_bv_shift_operations() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let shl = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvshl"), vec![x, y], Sort::bitvec(8));
    let lshr = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvlshr"), vec![x, y], Sort::bitvec(8));
    let ashr = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvashr"), vec![x, y], Sort::bitvec(8));

    let mut bv_values = HashMap::new();
    bv_values.insert(x, BigInt::from(0b1100_0011u8)); // 195 unsigned, -61 signed
    bv_values.insert(y, BigInt::from(2u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });

    // shl: 0b1100_0011 << 2 = 0b0000_1100 (mod 256)
    assert_eq!(
        executor.evaluate_term(&model, shl),
        EvalValue::BitVec {
            value: BigInt::from(0b0000_1100u8),
            width: 8,
        }
    );
    // lshr (logical): 0b1100_0011 >> 2 = 0b0011_0000
    assert_eq!(
        executor.evaluate_term(&model, lshr),
        EvalValue::BitVec {
            value: BigInt::from(0b0011_0000u8),
            width: 8,
        }
    );
    // ashr (arithmetic): -61 >> 2 = -16 = 0b1111_0000 (240 unsigned)
    assert_eq!(
        executor.evaluate_term(&model, ashr),
        EvalValue::BitVec {
            value: BigInt::from(0b1111_0000u8),
            width: 8,
        }
    );
}

#[test]
fn test_evaluate_bv_div_rem() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let udiv = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvudiv"), vec![x, y], Sort::bitvec(8));
    let urem = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvurem"), vec![x, y], Sort::bitvec(8));

    let mut bv_values = HashMap::new();
    bv_values.insert(x, BigInt::from(200u8));
    bv_values.insert(y, BigInt::from(7u8));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });

    // 200 / 7 = 28
    assert_eq!(
        executor.evaluate_term(&model, udiv),
        EvalValue::BitVec {
            value: BigInt::from(28u8),
            width: 8,
        }
    );
    // 200 % 7 = 4
    assert_eq!(
        executor.evaluate_term(&model, urem),
        EvalValue::BitVec {
            value: BigInt::from(4u8),
            width: 8,
        }
    );
}

#[test]
fn test_evaluate_bv_concat_extend() {
    let mut executor = Executor::new();
    let hi = executor.ctx.terms.mk_var("hi", Sort::bitvec(4));
    let lo = executor.ctx.terms.mk_var("lo", Sort::bitvec(4));
    let concat = executor
        .ctx
        .terms
        .mk_app(Symbol::named("concat"), vec![hi, lo], Sort::bitvec(8));

    let narrow = executor.ctx.terms.mk_var("narrow", Sort::bitvec(4));
    let zext =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("zero_extend"), vec![narrow], Sort::bitvec(8));
    let sext =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("sign_extend"), vec![narrow], Sort::bitvec(8));

    let mut bv_values = HashMap::new();
    bv_values.insert(hi, BigInt::from(0b1010u8));
    bv_values.insert(lo, BigInt::from(0b0101u8));
    bv_values.insert(narrow, BigInt::from(0b1100u8)); // -4 in 4-bit signed
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });

    // concat(0b1010, 0b0101) = 0b10100101 = 165
    assert_eq!(
        executor.evaluate_term(&model, concat),
        EvalValue::BitVec {
            value: BigInt::from(0b10100101u8),
            width: 8,
        }
    );
    // zero_extend(0b1100) = 0b00001100 = 12
    assert_eq!(
        executor.evaluate_term(&model, zext),
        EvalValue::BitVec {
            value: BigInt::from(0b00001100u8),
            width: 8,
        }
    );
    // sign_extend(0b1100) = 0b11111100 = 252 (sign bit propagated)
    assert_eq!(
        executor.evaluate_term(&model, sext),
        EvalValue::BitVec {
            value: BigInt::from(0b11111100u8),
            width: 8,
        }
    );
}

/// Regression test for #5627: when a sign_extend child variable is missing from
/// the BV model (e.g., eliminated by BVE and not recovered), the evaluator should
/// fall back to the BV model cache for the application term instead of returning
/// Unknown.
#[test]
fn test_bv_model_cache_fallback_sign_extend_5627() {
    let mut executor = Executor::new();
    // Create a variable "x" (4-bit) and sign_extend to 8-bit.
    // Do NOT put "x" in the BV model — simulates BVE eliminating it.
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(4));
    let sext = executor
        .ctx
        .terms
        .mk_app(Symbol::named("sign_extend"), vec![x], Sort::bitvec(8));

    // Only the application term is in the BV model (from bit-blasting),
    // NOT the child variable. This simulates BVE eliminating "x".
    let mut bv_values = HashMap::new();
    // sign_extend(0b1100) = 0b11111100 = 252
    bv_values.insert(sext, BigInt::from(252u16));

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });

    // Without the fallback, this would return Unknown (child "x" evaluates to
    // default 0, then sign_extend(0) = 0, which is wrong).
    // Actually, child "x" is in the BV model as default 0 (line 555), so
    // sign_extend(0) = 0. But 0 != 252 from the cache. The fallback only
    // fires when the child returns non-BitVec (Unknown).
    //
    // Revised scenario: child "x" is NOT a BV var but returns Unknown.
    // Use an Int-sorted var to make the child return a non-BitVec value.
    // Actually, x IS BV-sorted, so it defaults to 0. The sign_extend
    // of 0 is 0, which is semantically correct for a missing variable.
    //
    // The real fallback triggers when evaluate_term returns non-BitVec for
    // the child — which happens for more complex terms, not simple vars.
    // Let's test with a non-trivial child (e.g., a UF application).
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::bitvec(4));
    let sext2 = executor
        .ctx
        .terms
        .mk_app(Symbol::named("sign_extend"), vec![f_x], Sort::bitvec(8));

    let mut bv_values2 = HashMap::new();
    // sign_extend(f(x)) = 252 in the BV model cache
    bv_values2.insert(sext2, BigInt::from(252u16));

    let mut model2 = empty_model();
    model2.bv_model = Some(BvModel {
        values: bv_values2,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });

    // f(x) is an uninterpreted function — with no EUF model, it returns Unknown.
    // sign_extend should fall back to BV model cache and return 252.
    assert_eq!(
        executor.evaluate_term(&model2, sext2),
        EvalValue::BitVec {
            value: BigInt::from(252u16),
            width: 8,
        }
    );
}

/// Regression test for #5627: zero_extend BV model cache fallback.
#[test]
fn test_bv_model_cache_fallback_zero_extend_5627() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(4));
    // f(x) returns Unknown (no EUF model)
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::bitvec(4));
    let zext = executor
        .ctx
        .terms
        .mk_app(Symbol::named("zero_extend"), vec![f_x], Sort::bitvec(8));

    let mut bv_values = HashMap::new();
    bv_values.insert(zext, BigInt::from(12u8)); // 0b00001100

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });

    assert_eq!(
        executor.evaluate_term(&model, zext),
        EvalValue::BitVec {
            value: BigInt::from(12u8),
            width: 8,
        }
    );
}

/// Regression test for #5627: concat BV model cache fallback.
#[test]
fn test_bv_model_cache_fallback_concat_5627() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(4));
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::bitvec(4));
    let concat = executor
        .ctx
        .terms
        .mk_app(Symbol::named("concat"), vec![x, f_x], Sort::bitvec(8));

    let mut bv_values = HashMap::new();
    bv_values.insert(x, BigInt::from(0b1010u8));
    // f(x) is Unknown, but concat application has a cached value
    bv_values.insert(concat, BigInt::from(0b10100101u8));

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });

    // One child (f(x)) returns Unknown, so concat falls back to cache
    assert_eq!(
        executor.evaluate_term(&model, concat),
        EvalValue::BitVec {
            value: BigInt::from(0b10100101u8),
            width: 8,
        }
    );
}

/// Regression test for #5627 audit: bvcomp BV model cache fallback.
/// bvcomp was missed in the original fix — it returns (_ BitVec 1) and
/// should also fall back to the cache when children return Unknown.
#[test]
fn test_bv_model_cache_fallback_bvcomp_5627() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(8));
    // f(x) returns Unknown (no EUF model)
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::bitvec(8));
    // bvcomp(x, f(x)) -> (_ BitVec 1), result 1 means equal, 0 means not equal
    let bvcomp = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvcomp"), vec![x, f_x], Sort::bitvec(1));

    let mut bv_values = HashMap::new();
    bv_values.insert(x, BigInt::from(42u8));
    // f(x) is Unknown, but bvcomp application has a cached value of 1 (equal)
    bv_values.insert(bvcomp, BigInt::one());

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });

    // One child (f(x)) returns Unknown, so bvcomp falls back to cache
    assert_eq!(
        executor.evaluate_term(&model, bvcomp),
        EvalValue::BitVec {
            value: BigInt::one(),
            width: 1,
        }
    );
}

/// Regression test for #5461: when a BV UF application is missing from the BV
/// model cache, evaluation should reuse a congruent application with the same
/// function symbol and argument values.
#[test]
fn test_bv_uf_congruence_fallback_5461() {
    let mut executor = Executor::new();
    let sort_u = Sort::Uninterpreted("U".to_string());
    let x = executor.ctx.terms.mk_var("x", sort_u.clone());
    let y = executor.ctx.terms.mk_var("y", sort_u);
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::bitvec(8));
    let f_y = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![y], Sort::bitvec(8));

    let mut bv_values = HashMap::new();
    bv_values.insert(f_x, BigInt::from(0x2Au8));

    let mut term_values = HashMap::new();
    term_values.insert(x, "@U!0".to_string());
    term_values.insert(y, "@U!0".to_string());

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });
    model.euf_model = Some(EufModel {
        term_values,
        ..Default::default()
    });

    assert_eq!(
        executor.evaluate_term(&model, f_y),
        EvalValue::BitVec {
            value: BigInt::from(0x2Au8),
            width: 8,
        }
    );
}

/// Regression test for #5627: sign_extend with a BV variable child that is
/// MISSING from the BV model (eliminated by preprocessing, not recovered).
/// Without the is_bv_child_missing_from_model check, evaluate_term returns
/// BitVec(0) for the missing child, then sign_extend(0) = 0, which may
/// differ from the correct cached value. With the fix, the sign_extend
/// handler detects the missing child and falls back to the BV model cache.
#[test]
fn test_sign_extend_missing_child_var_uses_cache_5627() {
    let mut executor = Executor::new();
    // Child "x" is a 32-bit BV variable, NOT in the BV model (simulates
    // preprocessing elimination with failed recovery).
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(32));
    // sign_extend from 32-bit to 64-bit
    let sext = executor
        .ctx
        .terms
        .mk_app(Symbol::named("sign_extend"), vec![x], Sort::bitvec(64));

    // Only the sign_extend APPLICATION term is in the BV model cache
    // (from bit-blasting). The child "x" is NOT — it was eliminated.
    // The correct value is 0xFFFFFFFF_FFFF0000 (sign_extend of 0xFFFF0000).
    let expected_val = BigInt::from(0xFFFF_FFFF_FFFF_0000u64);
    let mut bv_values = HashMap::new();
    bv_values.insert(sext, expected_val.clone());
    // x is deliberately NOT in bv_values

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });

    // Without the fix: evaluate_term(x) -> BitVec(0, 32) (default)
    //   sign_extend(0) -> BitVec(0, 64) (WRONG)
    // With the fix: detect x is missing -> fall back to cache -> BitVec(0xFFFFFFFFFFFF0000, 64) (CORRECT)
    assert_eq!(
        executor.evaluate_term(&model, sext),
        EvalValue::BitVec {
            value: expected_val,
            width: 64,
        }
    );
}

/// Same as above but for zero_extend with a missing child variable.
#[test]
fn test_zero_extend_missing_child_var_uses_cache_5627() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::bitvec(32));
    let zext = executor
        .ctx
        .terms
        .mk_app(Symbol::named("zero_extend"), vec![x], Sort::bitvec(64));

    let expected_val = BigInt::from(0x0000_0000_FFFF_0000u64);
    let mut bv_values = HashMap::new();
    bv_values.insert(zext, expected_val.clone());
    // x is deliberately NOT in bv_values

    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });

    assert_eq!(
        executor.evaluate_term(&model, zext),
        EvalValue::BitVec {
            value: expected_val,
            width: 64,
        }
    );
}

#[test]
fn test_validate_model_rejects_unknown_non_bv_comparison() {
    // (#3903) Non-BV-comparison assertions that evaluate to Unknown are rejected.
    // Unknown means the evaluator cannot verify the model satisfies the assertion.
    // Use an uninterpreted function (UF) application: the evaluator cannot resolve
    // UF applications without a UF model, so it returns Unknown and is rejected.
    let mut executor = Executor::new();
    let hello = executor.ctx.terms.mk_string("hello".to_string());
    let uf_app =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("my_uf_predicate"), vec![hello], Sort::Bool);
    executor.ctx.assertions.push(uf_app);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown UF application should be rejected by validate_model");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_rejects_unknown_string_var_assertion() {
    // (#3903) Fail closed for String assertions that evaluate to Unknown.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);
    let pattern = executor.ctx.terms.mk_string("hello".to_string());
    let contains =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("str.contains"), vec![x, pattern], Sort::Bool);
    executor.ctx.assertions.push(contains);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown String assertion should be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_accepts_quantified_assertion_skipped_before_evaluation() {
    // Quantified assertions are skipped before evaluation —
    // validate_model returns Ok because the solver already verified
    // them via E-matching/CEGQI during solving.
    let mut executor = Executor::new();
    let body = executor.ctx.terms.mk_var("x", Sort::Bool);
    let forall = executor
        .ctx
        .terms
        .mk_forall(vec![("x".to_string(), Sort::Bool)], body);
    executor.ctx.assertions.push(forall);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    executor
        .validate_model()
        .expect("Quantified assertion should be accepted (skipped before evaluation)");
}

#[test]
fn test_validate_model_rejects_unknown_bv_comparison_with_uf_arguments() {
    // (#3903) Fail closed even when the Unknown originates from UF args.
    let mut executor = Executor::new();
    let x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bv_x"), vec![], Sort::bitvec(8));
    let y = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bv_y"), vec![], Sort::bitvec(8));
    let comparison = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![x, y], Sort::Bool);
    executor.ctx.assertions.push(comparison);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown BV comparison should be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_accepts_unknown_quantified_assertion() {
    // Quantified assertions cannot be model-checked; Unknown is acceptable.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let body = executor
        .ctx
        .terms
        .mk_app(Symbol::named(">="), vec![x, zero], Sort::Bool);
    let forall = executor
        .ctx
        .terms
        .mk_forall(vec![("x".to_string(), Sort::Int)], body);
    executor.ctx.assertions.push(forall);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    executor
        .validate_model()
        .expect("Quantified assertion Unknown should be accepted");
}

#[test]
fn test_validate_model_rejects_unknown_uf_assertion() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let p_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    executor.ctx.assertions.push(p_x);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown UF predicate assertion must be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_rejects_unknown_array_assertion() {
    // Unknown array assertions return Incomplete so
    // finalize_sat_model_validation can return Unknown instead of
    // silently accepting a potentially wrong SAT answer (#5116).
    let mut executor = Executor::new();
    let a = executor
        .ctx
        .terms
        .mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let i = executor.ctx.terms.mk_var("i", Sort::Int);
    let v = executor.ctx.terms.mk_var("v", Sort::Int);
    let sel = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![a, i], Sort::Int);
    let eq = executor.ctx.terms.mk_eq(sel, v);
    executor.ctx.assertions.push(eq);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown array assertion should now be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_finalize_sat_model_validation_degrades_array_false_with_sat_assignment() {
    let mut executor = Executor::new();
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let const_array = executor.ctx.terms.mk_app(
        Symbol::named("const-array"),
        vec![zero],
        Sort::array(Sort::Int, Sort::Int),
    );
    let stored = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![const_array, zero, one],
        Sort::array(Sort::Int, Sort::Int),
    );
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![stored, zero], Sort::Int);
    let assertion = executor
        .ctx
        .terms
        .mk_app(Symbol::named("<"), vec![selected, zero], Sort::Bool);
    assert!(
        executor.contains_array_term(assertion),
        "assertion must retain array structure"
    );
    executor.ctx.assertions.push(assertion);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model_with_sat_assignments(&[(assertion, true)]));

    let result = executor
        .finalize_sat_model_validation()
        .expect("array false assertion should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

#[test]
fn test_validate_model_equality_sat_fallback() {
    // (#5499) When both operands of an equality evaluate to Unknown
    // (e.g., string variables with no string model), the equality
    // returns Unknown (no SAT-model fallback — that would be circular).
    // If the SAT variable is true, validate_model tracks this as
    // sat_fallback_count. With only one assertion and no independent
    // evidence, the zero-check guard rejects the model.
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::String);
    let b = executor.ctx.terms.mk_var("b", Sort::String);
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    executor.ctx.assertions.push(eq_ab);

    // Build a model where the equality term has SAT variable = true
    let model = model_with_sat_assignments(&[(eq_ab, true)]);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("SAT-fallback-only model should be rejected (#5499)");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_validate_model_equality_sat_fallback_false_rejects() {
    // (#5499) SAT-fallback false → reject. UF sort, not String (#4057 handler).
    let mut executor = Executor::new();
    let uf = Sort::Uninterpreted("UFSort".into());
    let a = executor.ctx.terms.mk_var("a", uf.clone());
    let b = executor.ctx.terms.mk_var("b", uf);
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    executor.ctx.assertions.push(eq_ab);

    let model = model_with_sat_assignments(&[(eq_ab, false)]);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("SAT fallback false should reject");
    assert!(
        err.contains("evaluates to Unknown"),
        "Expected 'evaluates to Unknown' error, got: {err}"
    );
}

#[test]
fn test_validate_model_string_equality_uses_string_model() {
    // Validate leaf string equality without SAT-literal fallback by
    // providing a concrete string model assignment.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);
    let abc = executor.ctx.terms.mk_string("abc".to_string());
    let eq_x_abc = executor.ctx.terms.mk_eq(x, abc);
    executor.ctx.assertions.push(eq_x_abc);

    let mut string_values = HashMap::new();
    string_values.insert(x, "abc".to_string());
    let mut model = empty_model();
    model.string_model = Some(StringModel {
        values: string_values,
    });
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    executor
        .validate_model()
        .expect("String equality should validate from string model");
}

#[test]
fn test_validate_model_rejects_unknown_extf_string_equality() {
    // (#3903) Unsupported extf terms evaluating to Unknown are rejected.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);
    let lower_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("str.to_lower"), vec![x], Sort::String);
    let abc = executor.ctx.terms.mk_string("abc".to_string());
    let eq_term = executor.ctx.terms.mk_eq(lower_x, abc);
    executor.ctx.assertions.push(eq_term);

    let model = model_with_sat_assignments(&[(eq_term, true)]);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("Unknown extf equality should be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
}

#[test]
fn test_finalize_sat_model_validation_returns_unknown_for_unevaluable_string_term() {
    // (#3903) Unknown validation must degrade SAT to Unknown.
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::String);
    let pattern = executor.ctx.terms.mk_string("hello".to_string());
    let contains =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("str.contains"), vec![x, pattern], Sort::Bool);
    executor.ctx.assertions.push(contains);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let result = executor.finalize_sat_model_validation();
    assert!(
        matches!(result, Ok(SolveResult::Unknown)),
        "Expected Unknown for unevaluable string term, got: {result:?}"
    );
}

#[test]
fn test_finalize_sat_assumption_validation_accepts_true_assumption() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Bool);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model_with_sat_assignments(&[(a, true)]));

    let result = executor
        .finalize_sat_assumption_validation(&[a])
        .expect("true assumption should pass assumption validation");

    assert_eq!(result, SolveResult::Sat);
}

#[test]
fn test_finalize_sat_assumption_validation_degrades_unknown_assumption() {
    // Use an uninterpreted function — the evaluator cannot resolve it without
    // a UF model, so the assumption evaluates to Unknown and degrades to Unknown.
    let mut executor = Executor::new();
    let hello = executor.ctx.terms.mk_string("hello".to_string());
    let uf_app =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("my_uf_predicate"), vec![hello], Sort::Bool);

    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let result = executor
        .finalize_sat_assumption_validation(&[uf_app])
        .expect("unknown assumption evaluability should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

#[test]
fn test_finalize_sat_assumption_validation_degrades_unknown_bv_with_uf_subterms() {
    // Keep fail-closed behavior consistent with assertion validation:
    // bv comparison assumptions with UF arguments must not be skipped.
    let mut executor = Executor::new();
    let u = executor
        .ctx
        .terms
        .mk_var("u", Sort::Uninterpreted("U".to_string()));
    let f_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![u], Sort::bitvec(8));
    let g_u = executor
        .ctx
        .terms
        .mk_app(Symbol::named("g"), vec![u], Sort::bitvec(8));
    let bvult = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![f_u, g_u], Sort::Bool);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let result = executor
        .finalize_sat_assumption_validation(&[bvult])
        .expect("UF-containing BV assumption should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

#[test]
fn test_finalize_sat_assumption_validation_degrades_array_false_assumption() {
    let mut executor = Executor::new();
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let const_array = executor.ctx.terms.mk_app(
        Symbol::named("const-array"),
        vec![zero],
        Sort::array(Sort::Int, Sort::Int),
    );
    let stored = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![const_array, zero, one],
        Sort::array(Sort::Int, Sort::Int),
    );
    let selected =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("select"), vec![stored, zero], Sort::Int);
    let assumption =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("<"), vec![selected, zero], Sort::Bool);
    assert!(
        executor.contains_array_term(assumption),
        "assumption must retain array structure"
    );

    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model_with_sat_assignments(&[(assumption, true)]));

    let result = executor
        .finalize_sat_assumption_validation(&[assumption])
        .expect("array false assumption should degrade to Unknown");

    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::Incomplete)
    );
}

// ==========================================================================
// Cross-type equality: Rational vs BitVec (#5356)
// ==========================================================================

#[test]
fn test_evaluate_equality_rational_vs_bitvec_matching_values() {
    // (#5356) When the evaluator produces Rational for one side and BitVec
    // for the other (e.g., DT+BV combined theories, int2bv boundaries),
    // the equality should compare numerically instead of returning Unknown.
    let mut executor = Executor::new();
    // Use mk_app to create a raw equality that bypasses sort checks.
    // In practice, this arises when internal terms have mismatched
    // evaluator types (e.g., LIA model provides Int value for a term
    // that appears in a BV equality context).
    let int_const = executor.ctx.terms.mk_int(BigInt::from(42));
    let bv_const = executor.ctx.terms.mk_bitvec(BigInt::from(42), 32);
    let eq = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![int_const, bv_const], Sort::Bool);

    let model = empty_model();
    // Int constant evaluates to Rational(42), BV constant evaluates to BitVec(42, 32).
    // The cross-type handler should compare numerically: 42 == 42 → true.
    assert_eq!(
        executor.evaluate_term(&model, eq),
        EvalValue::Bool(true),
        "Rational(42) == BitVec(42, 32) should be true"
    );
}

#[test]
fn test_evaluate_equality_rational_vs_bitvec_different_values() {
    let mut executor = Executor::new();
    let int_const = executor.ctx.terms.mk_int(BigInt::from(7));
    let bv_const = executor.ctx.terms.mk_bitvec(BigInt::from(8), 8);
    let eq = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![int_const, bv_const], Sort::Bool);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, eq),
        EvalValue::Bool(false),
        "Rational(7) == BitVec(8, 8) should be false"
    );
}

#[test]
fn test_evaluate_equality_bitvec_vs_rational_symmetric() {
    // Same as above but reversed order — (BitVec, Rational) should also work.
    let mut executor = Executor::new();
    let bv_const = executor.ctx.terms.mk_bitvec(BigInt::from(100), 16);
    let int_const = executor.ctx.terms.mk_int(BigInt::from(100));
    let eq = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![bv_const, int_const], Sort::Bool);

    let model = empty_model();
    assert_eq!(
        executor.evaluate_term(&model, eq),
        EvalValue::Bool(true),
        "BitVec(100, 16) == Rational(100) should be true"
    );
}
