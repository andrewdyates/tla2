// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

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
fn test_validate_model_rejects_unknown_uf_assertion_empty_model() {
    // UF assertions are fail-closed (#4686): with an empty model, the UF
    // predicate P(x) evaluates to Unknown, which is rejected.
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
        .expect_err("Unknown UF predicate assertion must be rejected (fail-closed #4686)");
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
    // (#5499) When the equality evaluates to Unknown and the SAT model
    // says false, validation rejects with "evaluates to Unknown".
    // Use Uninterpreted sort (not String) so the assertion hits the general
    // evaluator's SAT-fallback path — String-sorted vars are intercepted by
    // the dedicated string handler (#4057) and route to skipped_internal.
    let mut executor = Executor::new();
    let a = executor
        .ctx
        .terms
        .mk_var("a", Sort::Uninterpreted("UFSort".into()));
    let b = executor
        .ctx
        .terms
        .mk_var("b", Sort::Uninterpreted("UFSort".into()));
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
fn test_validate_model_sat_fallback_mixed_with_independent_passes() {
    // (#5499) When some assertions are independently validated (checked > 0)
    // and others use SAT fallback, the model passes. The zero-check guard
    // only fires when ALL assertions are SAT-fallback (no independent evidence).
    let mut executor = Executor::new();
    // Independent assertion: Bool(true) evaluates directly.
    let true_const = executor.ctx.terms.mk_bool(true);
    executor.ctx.assertions.push(true_const);
    // SAT-fallback assertion: string equality with no string model.
    let a = executor.ctx.terms.mk_var("a", Sort::String);
    let b = executor.ctx.terms.mk_var("b", Sort::String);
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    executor.ctx.assertions.push(eq_ab);

    let model = model_with_sat_assignments(&[(eq_ab, true)]);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    executor
        .validate_model()
        .expect("Mixed independent+SAT-fallback model should pass (#5499)");
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

#[test]
fn test_validate_model_rejects_false_seq_assertion_6044() {
    // (#6044) When a Seq assertion evaluates to Bool(false), validate_model
    // must reject it — not silently skip it as skipped_internal.
    // Construct: (= (seq.len s) 5) where s is a 3-element sequence.
    let mut executor = Executor::new();
    let seq_sort = Sort::Seq(Box::new(Sort::Int));
    let s = executor.ctx.terms.mk_var("s", seq_sort);
    let seq_len = executor
        .ctx
        .terms
        .mk_app(Symbol::named("seq.len"), vec![s], Sort::Int);
    let five = executor.ctx.terms.mk_int(BigInt::from(5));
    let assertion = executor.ctx.terms.mk_eq(seq_len, five);
    executor.ctx.assertions.push(assertion);

    // Build a SeqModel where s = [10, 20, 30] (length 3, not 5).
    let mut seq_values = HashMap::new();
    seq_values.insert(
        s,
        vec!["10".to_string(), "20".to_string(), "30".to_string()],
    );
    let mut model = empty_model();
    model.seq_model = Some(SeqModel { values: seq_values });
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    let err = executor
        .validate_model()
        .expect_err("Seq assertion evaluating to false must be rejected (#6044)");
    assert!(
        err.contains("evaluates to false"),
        "Expected 'evaluates to false' error, got: {err}"
    );
}

#[test]
fn test_validate_model_rejects_unknown_seq_assertion_without_independent_evidence() {
    // (#6273, #4057) Unknown Seq assertions contribute only skipped_internal
    // evidence. When no assertion was independently checked, validation must
    // fail closed so finalize_sat_model_validation can degrade SAT to Unknown.
    let mut executor = Executor::new();
    let seq_sort = Sort::Seq(Box::new(Sort::Int));
    let s = executor.ctx.terms.mk_var("s", seq_sort);
    let seq_len = executor
        .ctx
        .terms
        .mk_app(Symbol::named("seq.len"), vec![s], Sort::Int);
    let five = executor.ctx.terms.mk_int(BigInt::from(5));
    let assertion = executor.ctx.terms.mk_eq(seq_len, five);
    executor.ctx.assertions.push(assertion);

    // No SeqModel -> seq.len(s) evaluates to Unknown, so the assertion only
    // contributes skipped_internal evidence.
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(empty_model());

    let err = executor
        .validate_model()
        .expect_err("Unknown Seq assertion with zero checked evidence must be rejected");
    assert!(err.is_incomplete(), "Expected Incomplete error, got: {err}");
    // Rejected at per-assertion Unknown path (line 4728), not summary accounting.
    assert!(err.contains("evaluates to Unknown"), "got: {err}");
}

#[test]
fn test_validate_model_proportional_sat_fallback_rejects() {
    // (#6223) When >90% of assertions use SAT-fallback, the model is
    // rejected even if some assertions independently validated. A single
    // independent check should not validate 10+ circularly-checked assertions.
    // Use Uninterpreted sort (not String) so assertions hit the general
    // evaluator's SAT-fallback path — String-sorted vars are intercepted by
    // the dedicated string handler (#4057) and route to skipped_internal.
    let mut executor = Executor::new();

    // 1 independent assertion: Bool(true) evaluates directly.
    let true_const = executor.ctx.terms.mk_bool(true);
    executor.ctx.assertions.push(true_const);

    // 10 SAT-fallback assertions: UF equalities with no UF model.
    // These will evaluate to Unknown → SAT-fallback.
    let mut sat_assignments = Vec::new();
    for i in 0..10 {
        let a = executor
            .ctx
            .terms
            .mk_var(format!("a{i}"), Sort::Uninterpreted("UFSort".into()));
        let b = executor
            .ctx
            .terms
            .mk_var(format!("b{i}"), Sort::Uninterpreted("UFSort".into()));
        let eq = executor.ctx.terms.mk_eq(a, b);
        executor.ctx.assertions.push(eq);
        sat_assignments.push((eq, true));
    }

    let model = model_with_sat_assignments(&sat_assignments);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    // total=11, checked=1, sat_fallback=10 → ~91% SAT-fallback (>90%) → rejected
    let result = executor.validate_model();
    assert!(
        result.is_err(),
        "Model with >90% SAT-fallback should be rejected (#6223)"
    );
    let msg = result.unwrap_err();
    assert!(
        msg.contains("SAT-fallback"),
        "Error should mention SAT-fallback: {msg}"
    );
}

#[test]
fn test_validate_model_proportional_sat_fallback_below_threshold_passes() {
    // (#6223) When SAT-fallback is <=90% of assertions, the model passes.
    // 3 independent + 2 SAT-fallback = 40% → below threshold.
    let mut executor = Executor::new();

    // 3 independent assertions
    for _ in 0..3 {
        let true_const = executor.ctx.terms.mk_bool(true);
        executor.ctx.assertions.push(true_const);
    }

    // 2 SAT-fallback assertions
    let mut sat_assignments = Vec::new();
    for i in 0..2 {
        let a = executor.ctx.terms.mk_var(format!("x{i}"), Sort::String);
        let b = executor.ctx.terms.mk_var(format!("y{i}"), Sort::String);
        let eq = executor.ctx.terms.mk_eq(a, b);
        executor.ctx.assertions.push(eq);
        sat_assignments.push((eq, true));
    }

    let model = model_with_sat_assignments(&sat_assignments);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    // total=5, checked=3, sat_fallback=2 → 40% → passes
    executor
        .validate_model()
        .expect("Model with 40% SAT-fallback should pass (#6223)");
}

#[test]
fn test_validate_model_proportional_guard_skips_small_formulas() {
    // (#6223) The proportional guard requires total >= 5. Small formulas
    // with high SAT-fallback ratios are not rejected.
    let mut executor = Executor::new();

    // 1 independent + 3 SAT-fallback = 75% but only 4 assertions total
    let true_const = executor.ctx.terms.mk_bool(true);
    executor.ctx.assertions.push(true_const);

    let mut sat_assignments = Vec::new();
    for i in 0..3 {
        let a = executor.ctx.terms.mk_var(format!("s{i}"), Sort::String);
        let b = executor.ctx.terms.mk_var(format!("t{i}"), Sort::String);
        let eq = executor.ctx.terms.mk_eq(a, b);
        executor.ctx.assertions.push(eq);
        sat_assignments.push((eq, true));
    }

    let model = model_with_sat_assignments(&sat_assignments);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);

    // total=4, checked=1, sat_fallback=3 → 75% but total < 5 → passes
    executor
        .validate_model()
        .expect("Small formula should skip proportional guard (#6223)");
}

/// (#6280) Build an executor with a pure-BV assertion (bvult(f(x), y)) that
/// evaluates to Unknown despite a BV model being present. The UF application
/// f(x) makes evaluate_term return Unknown.
fn setup_pure_bv_unknown_with_model_6280() -> Executor {
    let mut executor = Executor::new();
    let x = executor
        .ctx
        .terms
        .mk_var("x", Sort::Uninterpreted("U".to_string()));
    let f_x = executor
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::bitvec(8));
    let y = executor.ctx.terms.mk_var("y", Sort::bitvec(8));
    let bvult = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), vec![f_x, y], Sort::Bool);
    executor.ctx.assertions.push(bvult);
    let mut bv_values = HashMap::new();
    bv_values.insert(y, BigInt::from(42));
    let mut model = empty_model();
    model.bv_model = Some(BvModel {
        values: bv_values,
        term_to_bits: HashMap::new(),
        bool_overrides: HashMap::new(),
    });
    model.sat_model = vec![true];
    model.term_to_var.insert(bvult, 0);
    executor.last_result = Some(SolveResult::Sat);
    executor.last_model = Some(model);
    executor
}

#[test]
fn test_validate_model_rejects_pure_bv_unknown_with_bv_model_6280() {
    // (#6280) Pure-BV assertion with BV model that evaluates to Unknown must
    // be rejected — BV bit-blasting is complete, so Unknown indicates a bug.
    let executor = setup_pure_bv_unknown_with_model_6280();
    let err = executor
        .validate_model()
        .expect_err("Pure BV Unknown with BV model should be rejected (#6280)");
    assert!(err.is_incomplete(), "Expected Incomplete error: {err}");
    assert!(err.contains("pure BV assertion"), "Error: {err}");
}

#[test]
fn test_finalize_pure_bv_unknown_degrades_to_unknown_6280() {
    // (#6280) End-to-end: finalize must convert pure-BV Unknown rejection
    // into SolveResult::Unknown (not crash, not Sat).
    let mut executor = setup_pure_bv_unknown_with_model_6280();
    let result = executor
        .finalize_sat_model_validation()
        .expect("finalize should not crash");
    assert_eq!(
        result,
        SolveResult::Unknown,
        "Should degrade to Unknown (#6280)"
    );
}
