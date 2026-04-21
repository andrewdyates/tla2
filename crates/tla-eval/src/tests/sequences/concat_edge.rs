// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_seq_concat() {
    // Sequence \o sequence → concatenation (TLC: Sequences.java:117-146)
    assert_eq!(
        eval_str(r#"<<1, 2>> \o <<3, 4>>"#).unwrap(),
        Value::seq([Value::int(1), Value::int(2), Value::int(3), Value::int(4)])
    );
    // Empty left
    assert_eq!(
        eval_str(r#"<<>> \o <<1, 2>>"#).unwrap(),
        Value::seq([Value::int(1), Value::int(2)])
    );
    // Empty right
    assert_eq!(
        eval_str(r#"<<1, 2>> \o <<>>"#).unwrap(),
        Value::seq([Value::int(1), Value::int(2)])
    );
    // Both empty
    assert_eq!(eval_str(r#"<<>> \o <<>>"#).unwrap(), Value::seq([]));
    // \circ alias
    assert_eq!(
        eval_str(r#"<<1>> \circ <<2>>"#).unwrap(),
        Value::seq([Value::int(1), Value::int(2)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_string_concat_success() {
    // String \o string → string concatenation (TLC: Sequences.java:147-158)
    assert_eq!(
        eval_str(r#""abc" \o "def""#).unwrap(),
        Value::string("abcdef")
    );
    // Empty strings
    assert_eq!(eval_str(r#""" \o "abc""#).unwrap(), Value::string("abc"));
    assert_eq!(eval_str(r#""abc" \o """#).unwrap(), Value::string("abc"));
    assert_eq!(eval_str(r#""" \o """#).unwrap(), Value::string(""));
    // \circ alias with strings
    assert_eq!(eval_str(r#""x" \circ "y""#).unwrap(), Value::string("xy"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_string_concat_type_mismatch() {
    // String \o non-string → EvaluatingError with expected_type "string"
    let err = eval_str(r#""abc" \o <<1,2>>"#).unwrap_err();
    assert!(
        matches!(
            err,
            EvalError::EvaluatingError {
                form: "t \\o s",
                expected_type: "string",
                ..
            }
        ),
        "Expected EvaluatingError for string \\o seq, got {:?}",
        err
    );
    // Non-string \o string falls through to seq path → "sequence" expected
    let err = eval_str(r#"<<1,2>> \o "abc""#).unwrap_err();
    assert!(
        matches!(
            err,
            EvalError::EvaluatingError {
                form: "t \\o s",
                expected_type: "sequence",
                ..
            }
        ),
        "Expected EvaluatingError for seq \\o string, got {:?}",
        err
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_sequence_ops_accept_empty_bag_function_variant() {
    // EmptyBag is represented as Func([]) but is sequence-like in TLA+ (domain 1..0 = {}).
    // Ported from tla-check eval tests during #2034 consolidation.
    assert_eq!(eval_str("ToSet(EmptyBag)").unwrap(), Value::empty_set());
    assert_eq!(eval_str("Reverse(EmptyBag)").unwrap(), Value::seq([]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_sequence_ops_survive_set_intern_variant_substitution() {
    // Force both set forms through SET_INTERN_TABLE in opposite order. If interning
    // substitutes <<>> with EmptyBag's Func([]) representation, ToSet must still work.
    // Ported from tla-check eval tests during #2034 consolidation.
    crate::value::clear_set_intern_table();
    let v = eval_str(
        r#"LET prime == CHOOSE x \in {EmptyBag} : TRUE
               seqv == CHOOSE x \in {<<>>} : TRUE
           IN IF prime = prime THEN ToSet(seqv) ELSE {}"#,
    )
    .unwrap();
    assert_eq!(v, Value::empty_set());
    crate::value::clear_set_intern_table();
}

/// Regression test: Permutations({}) must return Func values even when the
/// global SET_INTERN_TABLE has been seeded with {<<>>} (Tuple variant).
/// Without clearing intern tables in clear_run_reset_impl(), the intern
/// lookup at normalized_elements_from_raw() returns the cached Tuple([])
/// instead of Func(empty), causing as_func() to return None.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_permutations_empty_survives_intern_table_tuple_pollution() {
    // Step 1: Seed the intern table with a set containing an empty tuple.
    // This creates an entry mapping fingerprint(Tuple([])) -> Arc<[Tuple([])]>.
    let _seed = eval_str("CHOOSE x \\in {<<>>} : TRUE").unwrap();

    // Step 2: Evaluate Permutations({}) which produces {Func(empty)}.
    // Because Func(empty) == Tuple([]) under cross-type equality and they
    // share hash discriminant 6u8, intern_set_array() finds the cached entry
    // and returns Arc<[Tuple([])]> instead of Arc<[Func(empty)]>.
    let perms = eval_str("Permutations({})").unwrap();
    let perm_set = perms.as_set().unwrap();
    assert_eq!(
        perm_set.len(),
        1,
        "Permutations({{}}) should have exactly 1 element"
    );
    for v in perm_set.iter() {
        // This assertion fails without the lifecycle.rs fix because v is
        // Value::Tuple([]) from the intern cache, not Value::Func(empty).
        assert!(
            v.as_func().is_some(),
            "Permutations({{}}): expected Func, got {:?}",
            v
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_foldseq_string_concat() {
    // FoldSeq with string concatenation via user-defined Concat operator.
    // Validates end-to-end \o string handling through fold machinery.
    assert_eq!(
        eval_with_ops(
            r#"Concat(a, b) == a \o b"#,
            r#"FoldSeq(Concat, "", <<"a", "b", "c">>)"#
        )
        .unwrap(),
        Value::string("abc")
    );
    // Empty sequence returns string base
    assert_eq!(
        eval_with_ops(r#"Concat(a, b) == a \o b"#, r#"FoldSeq(Concat, "x", <<>>)"#).unwrap(),
        Value::string("x")
    );
}
