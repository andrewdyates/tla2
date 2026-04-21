// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for Apalache module builtin operators and Variants module operators.

use super::{eval_str, eval_with_ops};
use crate::Value;

// === Gen ===

#[test]
fn test_gen_returns_empty_set() {
    // Gen(n) returns empty set in BFS mode (placeholder semantics).
    let v = eval_str("Gen(3)").unwrap();
    assert_eq!(v, Value::set(vec![]));
}

#[test]
fn test_gen_zero() {
    let v = eval_str("Gen(0)").unwrap();
    assert_eq!(v, Value::set(vec![]));
}

// === Guess ===

#[test]
fn test_guess_singleton() {
    // Guess({42}) picks the only element.
    let v = eval_str("Guess({42})").unwrap();
    assert_eq!(v, Value::SmallInt(42));
}

#[test]
fn test_guess_multi_element() {
    // Guess picks the first element in TLC-normalized order.
    let v = eval_str("Guess({3, 1, 2})").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_guess_empty_set_errors() {
    let err = eval_str("Guess({})").unwrap_err();
    let msg = format!("{}", err);
    assert!(
        msg.contains("non-empty"),
        "Expected 'non-empty' in error, got: {}",
        msg
    );
}

// === Skolem / Expand / ConstCardinality (identity operators) ===

#[test]
fn test_skolem_identity() {
    let v = eval_str("Skolem(TRUE)").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_expand_identity() {
    let v = eval_str("Expand({1, 2, 3})").unwrap();
    assert_eq!(
        v,
        Value::set(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3)
        ])
    );
}

#[test]
fn test_const_cardinality_identity() {
    let v = eval_str("ConstCardinality(42)").unwrap();
    assert_eq!(v, Value::SmallInt(42));
}

// === ApaFoldSet ===

#[test]
fn test_apa_fold_set_sum() {
    let v = eval_with_ops("Add(a, b) == a + b", "ApaFoldSet(Add, 0, {1, 2, 3})").unwrap();
    assert_eq!(v, Value::SmallInt(6));
}

#[test]
fn test_apa_fold_set_empty() {
    let v = eval_with_ops("Add(a, b) == a + b", "ApaFoldSet(Add, 100, {})").unwrap();
    assert_eq!(v, Value::SmallInt(100));
}

// === ApaFoldSeqLeft ===

#[test]
fn test_apa_fold_seq_left_concat() {
    let v = eval_with_ops(
        "Cat(acc, x) == acc + x",
        "ApaFoldSeqLeft(Cat, 0, <<10, 20, 30>>)",
    )
    .unwrap();
    assert_eq!(v, Value::SmallInt(60));
}

#[test]
fn test_apa_fold_seq_left_empty() {
    let v = eval_with_ops("Cat(acc, x) == acc + x", "ApaFoldSeqLeft(Cat, 42, <<>>)").unwrap();
    assert_eq!(v, Value::SmallInt(42));
}

// === MkSeq ===

#[test]
fn test_mkseq_basic() {
    let v = eval_with_ops("Double(i) == i * 2", "MkSeq(3, Double)").unwrap();
    // MkSeq(3, Double) == <<2, 4, 6>>
    let seq = v.as_seq().expect("should be a sequence");
    assert_eq!(seq.len(), 3);
    assert_eq!(seq[0], Value::SmallInt(2));
    assert_eq!(seq[1], Value::SmallInt(4));
    assert_eq!(seq[2], Value::SmallInt(6));
}

#[test]
fn test_mkseq_zero_length() {
    let v = eval_with_ops("Id(i) == i", "MkSeq(0, Id)").unwrap();
    let seq = v.as_seq().expect("should be a sequence");
    assert_eq!(seq.len(), 0);
}

// === Repeat ===

#[test]
fn test_repeat_basic() {
    // Repeat(F, 3, 0) where F(x, i) == x + i
    // result_1 = F(0, 1) = 1
    // result_2 = F(1, 2) = 3
    // result_3 = F(3, 3) = 6
    let v = eval_with_ops("F(x, i) == x + i", "Repeat(F, 3, 0)").unwrap();
    assert_eq!(v, Value::SmallInt(6));
}

#[test]
fn test_repeat_zero_iterations() {
    let v = eval_with_ops("F(x, i) == x + i", "Repeat(F, 0, 42)").unwrap();
    assert_eq!(v, Value::SmallInt(42));
}

#[test]
fn test_repeat_negative_iterations() {
    let v = eval_with_ops("F(x, i) == x + i", "Repeat(F, -1, 42)").unwrap();
    assert_eq!(v, Value::SmallInt(42));
}

// === SetAsFun ===

#[test]
fn test_set_as_fun_basic() {
    let v = eval_str("SetAsFun({<<1, \"a\">>, <<2, \"b\">>})").unwrap();
    // Should produce a function [1 |-> "a", 2 |-> "b"]
    if let Value::Func(f) = &v {
        assert_eq!(
            f.apply(&Value::SmallInt(1)).unwrap().as_string().unwrap(),
            "a"
        );
        assert_eq!(
            f.apply(&Value::SmallInt(2)).unwrap().as_string().unwrap(),
            "b"
        );
    } else {
        panic!("Expected Func, got {:?}", v);
    }
}

#[test]
fn test_set_as_fun_empty() {
    let v = eval_str("SetAsFun({})").unwrap();
    if let Value::Func(f) = &v {
        assert_eq!(f.domain_iter().count(), 0);
    } else {
        panic!("Expected Func, got {:?}", v);
    }
}

// === Variant ===

#[test]
fn test_variant_create() {
    let v = eval_str("Variant(\"Some\", 42)").unwrap();
    let rec = v.as_record().expect("should be a record");
    assert_eq!(rec.get("tag").unwrap().as_string().unwrap(), "Some");
    assert_eq!(*rec.get("value").unwrap(), Value::SmallInt(42));
}

// === VariantTag ===

#[test]
fn test_variant_tag() {
    let v = eval_str("VariantTag([tag |-> \"None\", value |-> 0])").unwrap();
    assert_eq!(v.as_string().unwrap(), "None");
}

#[test]
fn test_variant_tag_from_variant() {
    let v = eval_str("VariantTag(Variant(\"Ok\", 1))").unwrap();
    assert_eq!(v.as_string().unwrap(), "Ok");
}

// === VariantGetUnsafe ===

#[test]
fn test_variant_get_unsafe_match() {
    let v = eval_str("VariantGetUnsafe(\"Some\", Variant(\"Some\", 42))").unwrap();
    assert_eq!(v, Value::SmallInt(42));
}

#[test]
fn test_variant_get_unsafe_mismatch() {
    let err = eval_str("VariantGetUnsafe(\"None\", Variant(\"Some\", 42))").unwrap_err();
    let msg = format!("{}", err);
    assert!(
        msg.contains("expected tag") && msg.contains("None") && msg.contains("Some"),
        "Expected tag mismatch error, got: {}",
        msg
    );
}

// === VariantGetOrElse ===

#[test]
fn test_variant_get_or_else_match() {
    let v = eval_str("VariantGetOrElse(\"Some\", Variant(\"Some\", 42), 0)").unwrap();
    assert_eq!(v, Value::SmallInt(42));
}

#[test]
fn test_variant_get_or_else_mismatch() {
    let v = eval_str("VariantGetOrElse(\"None\", Variant(\"Some\", 42), -1)").unwrap();
    assert_eq!(v, Value::SmallInt(-1));
}

// === VariantFilter ===

#[test]
fn test_variant_filter() {
    let v = eval_str(
        "VariantFilter(\"Ok\", {Variant(\"Ok\", 1), Variant(\"Err\", 2), Variant(\"Ok\", 3)})",
    )
    .unwrap();
    // Should contain only variants with tag "Ok"
    let set_len = v.set_len().expect("should be a set");
    assert_eq!(set_len, 2u64.into(), "expected 2 Ok variants");
}

// === Lambda support for higher-order Apalache operators ===

#[test]
fn test_apa_fold_set_lambda() {
    // ApaFoldSet with LAMBDA instead of named operator
    let v = eval_with_ops("", "ApaFoldSet(LAMBDA a, b: a + b, 0, {1, 2, 3})").unwrap();
    assert_eq!(v, Value::SmallInt(6));
}

#[test]
fn test_apa_fold_set_lambda_empty() {
    let v = eval_with_ops("", "ApaFoldSet(LAMBDA a, b: a + b, 100, {})").unwrap();
    assert_eq!(v, Value::SmallInt(100));
}

#[test]
fn test_apa_fold_seq_left_lambda() {
    // ApaFoldSeqLeft with LAMBDA instead of named operator
    let v = eval_with_ops(
        "",
        "ApaFoldSeqLeft(LAMBDA acc, x: acc + x, 0, <<10, 20, 30>>)",
    )
    .unwrap();
    assert_eq!(v, Value::SmallInt(60));
}

#[test]
fn test_apa_fold_seq_left_lambda_empty() {
    let v = eval_with_ops("", "ApaFoldSeqLeft(LAMBDA acc, x: acc + x, 42, <<>>)").unwrap();
    assert_eq!(v, Value::SmallInt(42));
}

#[test]
fn test_mkseq_lambda() {
    // MkSeq with LAMBDA instead of named operator
    let v = eval_with_ops("", "MkSeq(3, LAMBDA i: i * 2)").unwrap();
    let seq = v.as_seq().expect("should be a sequence");
    assert_eq!(seq.len(), 3);
    assert_eq!(seq[0], Value::SmallInt(2));
    assert_eq!(seq[1], Value::SmallInt(4));
    assert_eq!(seq[2], Value::SmallInt(6));
}

#[test]
fn test_mkseq_lambda_zero() {
    let v = eval_with_ops("", "MkSeq(0, LAMBDA i: i)").unwrap();
    let seq = v.as_seq().expect("should be a sequence");
    assert_eq!(seq.len(), 0);
}

#[test]
fn test_repeat_lambda() {
    // Repeat with LAMBDA instead of named operator
    // LAMBDA x, i: x + i applied 3 times starting from 0:
    // i=1: 0+1=1, i=2: 1+2=3, i=3: 3+3=6
    let v = eval_with_ops("", "Repeat(LAMBDA x, i: x + i, 3, 0)").unwrap();
    assert_eq!(v, Value::SmallInt(6));
}

#[test]
fn test_repeat_lambda_zero() {
    let v = eval_with_ops("", "Repeat(LAMBDA x, i: x + i, 0, 42)").unwrap();
    assert_eq!(v, Value::SmallInt(42));
}

// === := assignment operator (Apalache) ===

#[test]
fn test_colon_eq_true() {
    // 1 := 1 should be TRUE (equality in BFS mode)
    let v = eval_str("1 := 1").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_colon_eq_false() {
    let v = eval_str("1 := 2").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_colon_eq_string() {
    let v = eval_str("\"hello\" := \"hello\"").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_colon_eq_set() {
    let v = eval_str("{1, 2, 3} := {3, 2, 1}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_colon_eq_mismatch() {
    let v = eval_str("{1, 2} := {1, 2, 3}").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// === Module-scoped override tests ===

#[test]
fn test_apalache_override_requires_module() {
    use crate::has_complete_builtin_override;
    use crate::EvalCtx;
    use std::sync::Arc;

    let ctx_none = EvalCtx::new();
    assert!(!has_complete_builtin_override("Gen", 1, &ctx_none));
    assert!(!has_complete_builtin_override("Guess", 1, &ctx_none));
    assert!(!has_complete_builtin_override("ApaFoldSet", 3, &ctx_none));

    let mut ctx_apa = EvalCtx::new();
    {
        let shared = Arc::make_mut(ctx_apa.shared_arc_mut());
        shared.extended_module_names.insert("Apalache".to_string());
    }
    assert!(has_complete_builtin_override("Gen", 1, &ctx_apa));
    assert!(has_complete_builtin_override("Guess", 1, &ctx_apa));
    assert!(has_complete_builtin_override("ApaFoldSet", 3, &ctx_apa));
    assert!(has_complete_builtin_override("ApaFoldSeqLeft", 3, &ctx_apa));
    assert!(has_complete_builtin_override("MkSeq", 2, &ctx_apa));
    assert!(has_complete_builtin_override("Repeat", 3, &ctx_apa));
    assert!(has_complete_builtin_override("SetAsFun", 1, &ctx_apa));
    assert!(has_complete_builtin_override("Skolem", 1, &ctx_apa));
    assert!(has_complete_builtin_override("Expand", 1, &ctx_apa));
    assert!(has_complete_builtin_override(
        "ConstCardinality",
        1,
        &ctx_apa
    ));
}

#[test]
fn test_variants_override_requires_module() {
    use crate::has_complete_builtin_override;
    use crate::EvalCtx;
    use std::sync::Arc;

    let ctx_none = EvalCtx::new();
    assert!(!has_complete_builtin_override("Variant", 2, &ctx_none));
    assert!(!has_complete_builtin_override("VariantTag", 1, &ctx_none));

    let mut ctx_var = EvalCtx::new();
    {
        let shared = Arc::make_mut(ctx_var.shared_arc_mut());
        shared.extended_module_names.insert("Variants".to_string());
    }
    assert!(has_complete_builtin_override("Variant", 2, &ctx_var));
    assert!(has_complete_builtin_override("VariantTag", 1, &ctx_var));
    assert!(has_complete_builtin_override(
        "VariantGetUnsafe",
        2,
        &ctx_var
    ));
    assert!(has_complete_builtin_override(
        "VariantGetOrElse",
        3,
        &ctx_var
    ));
    assert!(has_complete_builtin_override("VariantFilter", 2, &ctx_var));
}
