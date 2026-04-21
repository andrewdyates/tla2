// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_division_by_zero() {
    // Division by zero should return DivisionByZero error
    let result = eval_str("10 / 0");
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::DivisionByZero { .. }),
        "Expected DivisionByZero, got: {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_modulo_by_zero() {
    // TLC requires positive divisor for %, so 0 returns ModulusNotPositive (#554)
    let result = eval_str("10 % 0");
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::ModulusNotPositive { .. }),
        "Expected ModulusNotPositive, got: {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_choose_failed() {
    // CHOOSE with no satisfying element should return ChooseFailed
    let result = eval_str(r#"CHOOSE x \in {} : TRUE"#);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::ChooseFailed { .. }),
        "Expected ChooseFailed, got: {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_choose_failed_predicate() {
    // CHOOSE with no element satisfying predicate
    let result = eval_str(r#"CHOOSE x \in {1, 2, 3} : x > 100"#);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::ChooseFailed { .. }),
        "Expected ChooseFailed, got: {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_type_error_arithmetic() {
    // Adding non-integers should return ArgumentError (TLC: EC.TLC_MODULE_ARGUMENT_ERROR)
    let result = eval_str(r#"TRUE + 1"#);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::ArgumentError { .. }),
        "Expected ArgumentError, got: {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_type_error_set_membership() {
    // Set membership with non-set should return TypeError
    let result = eval_str(r#"1 \in 2"#);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::TypeError { .. }),
        "Expected TypeError, got: {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_or_propagates_left_branch_type_error() {
    // Part of #1999: OR must not suppress TypeError from the left branch.
    let result = eval_str(r#"(1 \in 2) \/ TRUE"#);
    assert!(
        matches!(result, Err(EvalError::TypeError { .. })),
        "Expected TypeError to propagate from OR lhs, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_or_propagates_right_branch_index_error() {
    // Part of #1999: when lhs is FALSE, rhs errors must still propagate.
    let result = eval_str(r#"FALSE \/ (([x \in {1, 2} |-> x])[3] = 0)"#);
    assert!(
        matches!(result, Err(EvalError::IndexOutOfBounds { .. })),
        "Expected IndexOutOfBounds to propagate from OR rhs, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_or_short_circuits_past_rhs_error() {
    // Part of #1999: when lhs is TRUE, short-circuit must prevent rhs evaluation.
    // Ensures the error propagation change doesn't break short-circuit semantics.
    let result = eval_str(r#"TRUE \/ (1 \in 2)"#);
    assert!(
        matches!(result, Ok(Value::Bool(true))),
        "TRUE \\/ <error> should short-circuit to TRUE, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_type_error_domain() {
    // DOMAIN of non-function should return TypeError
    let result = eval_str(r#"DOMAIN 42"#);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::TypeError { .. }),
        "Expected TypeError, got: {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_no_such_field() {
    // Record field access with non-existent field — TLC: RecordValue.java:488
    // TLC format: "Attempted to access nonexistent field '<field>' of record\n<record>"
    let result = eval_str(r#"[a |-> 1].b"#);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(
            err,
            EvalError::NoSuchField {
                record_display: Some(_),
                ..
            }
        ),
        "Expected NoSuchField with record_display, got: {:?}",
        err
    );
    let msg = err.to_string();
    assert!(
        msg.contains("Attempted to access nonexistent field 'b' of record"),
        "Expected TLC-format NoSuchField message, got: {}",
        msg
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_not_in_domain_function() {
    // Function application with argument not in domain.
    // Note: [x \in {1, 2} |-> x * 2] has domain 1..2 and is stored as Seq.
    // TLC would report NotInDomain (FcnRcdValue), but our Seq representation
    // matches TupleValue behavior (IndexOutOfBounds). Both are fatal errors
    // with identical propagation semantics.
    let result = eval_str(r#"([x \in {1, 2} |-> x * 2])[3]"#);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::IndexOutOfBounds { .. }),
        "Expected IndexOutOfBounds for seq-stored function application, got: {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_division_by_zero_div() {
    let result = eval_str(r#"5 \div 0"#);
    assert!(
        matches!(result, Err(EvalError::DivisionByZero { .. })),
        "Expected DivisionByZero error, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_modulus_not_positive() {
    // TLC requires positive divisor for %, so 0 returns ModulusNotPositive (#554)
    let result = eval_str("5 % 0");
    assert!(
        matches!(result, Err(EvalError::ModulusNotPositive { .. })),
        "Expected ModulusNotPositive error, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_type_mismatch_arithmetic_plus() {
    // Adding boolean to integer should fail with ArgumentError (TLC: EC.TLC_MODULE_ARGUMENT_ERROR)
    let result = eval_str("1 + TRUE");
    assert!(
        matches!(
            result,
            Err(EvalError::ArgumentError {
                expected_type: "integer",
                ..
            })
        ),
        "Expected ArgumentError for integer, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_type_mismatch_arithmetic_minus() {
    // Subtracting with non-integer should fail with ArgumentError (TLC: EC.TLC_MODULE_ARGUMENT_ERROR)
    let result = eval_str(r#""hello" - 1"#);
    assert!(
        matches!(
            result,
            Err(EvalError::ArgumentError {
                expected_type: "integer",
                ..
            })
        ),
        "Expected ArgumentError for integer, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_type_mismatch_arithmetic_mult() {
    // Multiplying with non-integer should fail with ArgumentError (TLC: EC.TLC_MODULE_ARGUMENT_ERROR)
    let result = eval_str("{1,2} * 3");
    assert!(
        matches!(
            result,
            Err(EvalError::ArgumentError {
                expected_type: "integer",
                ..
            })
        ),
        "Expected ArgumentError for integer, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_type_mismatch_set_union_left() {
    // Set union with non-set should fail
    let result = eval_str(r#"1 \cup {2}"#);
    assert!(
        matches!(
            result,
            Err(EvalError::TypeError {
                expected: "Set",
                ..
            })
        ),
        "Expected TypeError for Set, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_type_mismatch_set_union_right() {
    let result = eval_str(r#"{1} \cup 2"#);
    assert!(
        matches!(
            result,
            Err(EvalError::TypeError {
                expected: "Set",
                ..
            })
        ),
        "Expected TypeError for Set, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_type_mismatch_set_intersect() {
    let result = eval_str(r#"{1} \cap TRUE"#);
    assert!(
        matches!(
            result,
            Err(EvalError::TypeError {
                expected: "Set",
                ..
            })
        ),
        "Expected TypeError for Set, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_type_mismatch_set_difference() {
    let result = eval_str(r#"{1} \ "string""#);
    assert!(
        matches!(
            result,
            Err(EvalError::TypeError {
                expected: "Set",
                ..
            })
        ),
        "Expected TypeError for Set, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_sequence_index_out_of_bounds_high() {
    // Accessing index beyond sequence length — TLC: TupleValue.java:144
    // TLC format: "Attempted to access index <N> of tuple\n<tuple>\nwhich is out of bounds."
    let result = eval_str("<<1,2,3>>[5]");
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(
            err,
            EvalError::IndexOutOfBounds {
                index: 5,
                len: 3,
                value_display: Some(_),
                ..
            }
        ),
        "Expected IndexOutOfBounds with value_display, got: {:?}",
        err
    );
    let msg = err.to_string();
    assert!(
        msg.contains("Attempted to access index 5 of tuple"),
        "Expected TLC-format IndexOutOfBounds message, got: {}",
        msg
    );
    assert!(
        msg.contains("which is out of bounds."),
        "Expected 'which is out of bounds.' suffix, got: {}",
        msg
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_sequence_index_out_of_bounds_zero() {
    // TLA+ sequences are 1-indexed, so index 0 is invalid
    let result = eval_str("<<1,2,3>>[0]");
    assert!(
        matches!(result, Err(EvalError::IndexOutOfBounds { index: 0, .. })),
        "Expected IndexOutOfBounds error for index 0, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_sequence_index_out_of_bounds_negative() {
    let result = eval_str("<<1,2,3>>[-1]");
    assert!(
        matches!(result, Err(EvalError::IndexOutOfBounds { index: -1, .. })),
        "Expected IndexOutOfBounds error for negative index, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_choose_failed_empty_set() {
    // CHOOSE from empty set should fail
    let result = eval_str(r#"CHOOSE x \in {} : TRUE"#);
    assert!(
        matches!(result, Err(EvalError::ChooseFailed { .. })),
        "Expected ChooseFailed error, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_choose_failed_no_satisfying_element() {
    // CHOOSE where no element satisfies predicate
    let result = eval_str(r#"CHOOSE x \in {1,2,3} : x > 10"#);
    assert!(
        matches!(result, Err(EvalError::ChooseFailed { .. })),
        "Expected ChooseFailed error, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_exponentiation_negative_exponent() {
    // Negative exponents are not supported in TLA+ integer arithmetic
    let result = eval_str("2^(-1)");
    assert!(
        matches!(result, Err(EvalError::Internal { .. })),
        "Expected Internal error for negative exponent, got: {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_undefined_op() {
    // Calling an undefined operator should return UndefinedOp error
    // We need a full module setup since the eval_str helper doesn't support
    // operator applications that reference undefined names
    let src = r#"
---- MODULE Test ----
Op == UndefinedOperator(1, 2)
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let ctx = EvalCtx::new();
    // Find and evaluate Op
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                let result = eval(&ctx, &def.body);
                assert!(
                    matches!(result, Err(EvalError::UndefinedOp { .. })),
                    "Expected UndefinedOp error, got: {:?}",
                    result
                );
                return;
            }
        }
    }
    panic!("Op not found in module");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_arity_mismatch() {
    // Calling an operator with wrong number of arguments should return ArityMismatch
    let src = r#"
---- MODULE Test ----
F(x) == x + 1
Op == F(1, 2)
====
"#;
    let tree = tla_core::parse_to_syntax_tree(src);
    let lower_result = tla_core::lower(tla_core::FileId(0), &tree);
    let module = lower_result.module.expect("Module should lower");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    // Find and evaluate Op
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                let result = eval(&ctx, &def.body);
                assert!(
                    matches!(result, Err(EvalError::ArityMismatch { .. })),
                    "Expected ArityMismatch error, got: {:?}",
                    result
                );
                return;
            }
        }
    }
    panic!("Op not found in module");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_type_error_concat_on_non_seqs() {
    // Sequence concatenation requires sequences — TLC: EC.TLC_MODULE_EVALUATING
    let result = eval_str(r#"<<1,2>> \o {3,4}"#);
    assert!(result.is_err(), "Concat with non-seq should error");
    let err = result.unwrap_err();
    assert!(
        matches!(
            err,
            EvalError::EvaluatingError {
                form: "t \\o s",
                expected_type: "sequence",
                ..
            }
        ),
        "Expected EvaluatingError for concat, got {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_head_of_empty_sequence() {
    // Head of empty sequence should error — TLC: EC.TLC_MODULE_APPLY_EMPTY_SEQ
    let result = eval_str("Head(<<>>)");
    assert!(result.is_err(), "Head of empty sequence should error");
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::ApplyEmptySeq { op: "Head", .. }),
        "Expected ApplyEmptySeq for Head(<<>>), got {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_tail_of_empty_sequence() {
    // Tail of empty sequence should error — TLC: EC.TLC_MODULE_APPLY_EMPTY_SEQ
    let result = eval_str("Tail(<<>>)");
    assert!(result.is_err(), "Tail of empty sequence should error");
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::ApplyEmptySeq { op: "Tail", .. }),
        "Expected ApplyEmptySeq for Tail(<<>>), got {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_type_error_cardinality_non_set() {
    // Cardinality requires a set
    let result = eval_str("Cardinality(42)");
    assert!(result.is_err(), "Cardinality of non-set should error");
    let err = result.unwrap_err();
    assert!(
        matches!(
            err,
            EvalError::TypeError {
                expected: "Set",
                ..
            }
        ),
        "Expected TypeError for Set, got {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_subseteq_with_non_sets() {
    // Subset requires sets - implementation returns Internal error when
    // left operand cannot be enumerated as a set
    let result = eval_str(r#"42 \subseteq {1, 2}"#);
    assert!(result.is_err(), "Subseteq with non-set should error");
    let err = result.unwrap_err();
    // The evaluator returns Internal error when subseteq left operand
    // isn't enumerable (not TypeError because it checks enumerability first)
    assert!(
        matches!(
            err,
            EvalError::Internal { .. } | EvalError::TypeError { .. }
        ),
        "Expected Internal or TypeError error, got {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_nested_error_propagates() {
    // Errors in nested expressions should propagate
    let result = eval_str(r#"1 + (10 \div 0)"#);
    assert!(result.is_err(), "Nested error should propagate");
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::DivisionByZero { .. }),
        "Expected DivisionByZero to propagate, got {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_in_function_constructor_domain() {
    // Error in domain expression should propagate
    let result = eval_str(r#"[x \in (1 \div 0)..10 |-> x]"#);
    assert!(result.is_err(), "Error in domain should propagate");
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::DivisionByZero { .. }),
        "Expected DivisionByZero in domain, got {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_error_in_set_filter_domain() {
    // Error in filter domain should propagate
    let result = eval_str(r#"{x \in (10 \div 0)..5 : x > 0}"#);
    assert!(result.is_err(), "Error in filter domain should propagate");
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::DivisionByZero { .. }),
        "Expected DivisionByZero in filter domain, got {:?}",
        err
    );
}
