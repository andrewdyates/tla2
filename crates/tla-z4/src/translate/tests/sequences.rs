// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for sequence operations in the Z4 translator.
//!
//! Tests the wiring from TLA+ AST expressions through `resolve_seq_term_with_sort`
//! to the `SequenceEncoder` for Head, Tail, Len, Append, SubSeq, and concatenation.
//!
//! Part of #3793.

use super::*;
use z4_dpll::api::SolveResult;

use crate::translate::sequence_encoder::SequenceEncoder;

// =========================================================================
// Helpers
// =========================================================================

fn make_ident(name: &str) -> Spanned<Expr> {
    spanned(Expr::Ident(
        name.to_string(),
        tla_core::name_intern::NameId::INVALID,
    ))
}

fn make_int(val: i64) -> Spanned<Expr> {
    spanned(Expr::Int(BigInt::from(val)))
}

/// Build `Expr::Apply(Ident(op_name), args)` — the AST form for Tail(s), Append(s,e), etc.
fn make_apply(op_name: &str, args: Vec<Spanned<Expr>>) -> Spanned<Expr> {
    spanned(Expr::Apply(
        Box::new(spanned(Expr::Ident(
            op_name.to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        args,
    ))
}

/// Create a translator with an Int sequence variable declared.
fn setup_int_seq(name: &str, max_len: usize) -> Z4Translator {
    let mut trans = Z4Translator::new_with_arrays();
    trans
        .declare_seq_var(name, TlaSort::Int, max_len)
        .expect("declare_seq_var should succeed");
    trans
}

/// Create a translator with two Int sequence variables declared.
fn setup_two_int_seqs(
    name1: &str,
    max1: usize,
    name2: &str,
    max2: usize,
) -> Z4Translator {
    let mut trans = Z4Translator::new_with_arrays();
    trans
        .declare_seq_var(name1, TlaSort::Int, max1)
        .expect("declare first seq");
    trans
        .declare_seq_var(name2, TlaSort::Int, max2)
        .expect("declare second seq");
    trans
}

/// Constrain a sequence variable's elements to concrete values.
/// e.g., constrain_seq(&mut trans, "s", &[10, 20, 30]) sets s = <<10, 20, 30>>.
fn constrain_seq(trans: &mut Z4Translator, name: &str, values: &[i64]) {
    let info = trans.get_seq_var(name).unwrap().clone();

    // Set length
    let len_val = trans.solver_mut().int_const(values.len() as i64);
    let len_eq = trans.solver_mut().try_eq(info.len_term, len_val).unwrap();
    trans.assert(len_eq);

    // Set each element
    for (i, &val) in values.iter().enumerate() {
        let idx = i + 1; // 1-indexed
        if let Some(&elem_term) = info.element_terms.get(&idx) {
            let val_term = trans.solver_mut().int_const(val);
            let eq = trans.solver_mut().try_eq(elem_term, val_term).unwrap();
            trans.assert(eq);
        }
    }
}

// =========================================================================
// Tail tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tail_via_ast_len() {
    // Len(Tail(s)) where s = <<10, 20, 30>> should be 2
    let mut trans = setup_int_seq("s", 3);
    constrain_seq(&mut trans, "s", &[10, 20, 30]);

    // Translate Len(Tail(s)) through the AST dispatch
    let func = spanned(Expr::Ident(
        "Len".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let tail_arg = make_apply("Tail", vec![make_ident("s")]);
    let result = trans.try_translate_seq_op_int(&func, &[tail_arg]);
    assert!(result.is_some(), "Len(Tail(s)) should be recognized");
    let len_term = result.unwrap().expect("Len(Tail(s)) should translate");

    // Assert Len(Tail(s)) = 2
    let two = trans.solver_mut().int_const(2);
    let eq = trans.solver_mut().try_eq(len_term, two).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tail_via_ast_head() {
    // Head(Tail(s)) where s = <<10, 20, 30>> should be 20
    let mut trans = setup_int_seq("s", 3);
    constrain_seq(&mut trans, "s", &[10, 20, 30]);

    let func = spanned(Expr::Ident(
        "Head".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let tail_arg = make_apply("Tail", vec![make_ident("s")]);
    let result = trans.try_translate_seq_op_int(&func, &[tail_arg]);
    assert!(result.is_some(), "Head(Tail(s)) should be recognized");
    let head_term = result.unwrap().expect("Head(Tail(s)) should translate");

    // Assert Head(Tail(s)) = 20
    let twenty = trans.solver_mut().int_const(20);
    let eq = trans.solver_mut().try_eq(head_term, twenty).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tail_via_ast_head_wrong_value_unsat() {
    // Head(Tail(s)) where s = <<10, 20, 30>> should NOT be 10
    let mut trans = setup_int_seq("s", 3);
    constrain_seq(&mut trans, "s", &[10, 20, 30]);

    let func = spanned(Expr::Ident(
        "Head".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let tail_arg = make_apply("Tail", vec![make_ident("s")]);
    let head_term = trans
        .try_translate_seq_op_int(&func, &[tail_arg])
        .unwrap()
        .unwrap();

    // Assert Head(Tail(s)) = 10 (wrong — should be 20)
    let ten = trans.solver_mut().int_const(10);
    let eq = trans.solver_mut().try_eq(head_term, ten).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Unsat(_));
}

// =========================================================================
// Append tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_append_via_ast_len() {
    // Len(Append(s, 40)) where s = <<10, 20, 30>> should be 4
    let mut trans = setup_int_seq("s", 3);
    constrain_seq(&mut trans, "s", &[10, 20, 30]);

    let func = spanned(Expr::Ident(
        "Len".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let append_arg = make_apply("Append", vec![make_ident("s"), make_int(40)]);
    let len_term = trans
        .try_translate_seq_op_int(&func, &[append_arg])
        .unwrap()
        .unwrap();

    // Assert Len(Append(s, 40)) = 4
    let four = trans.solver_mut().int_const(4);
    let eq = trans.solver_mut().try_eq(len_term, four).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_append_via_ast_head_preserved() {
    // Head(Append(s, 40)) where s = <<10, 20, 30>> should still be 10
    let mut trans = setup_int_seq("s", 3);
    constrain_seq(&mut trans, "s", &[10, 20, 30]);

    let func = spanned(Expr::Ident(
        "Head".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let append_arg = make_apply("Append", vec![make_ident("s"), make_int(40)]);
    let head_term = trans
        .try_translate_seq_op_int(&func, &[append_arg])
        .unwrap()
        .unwrap();

    // Head(Append(s, 40)) = 10
    let ten = trans.solver_mut().int_const(10);
    let eq = trans.solver_mut().try_eq(head_term, ten).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_append_last_element() {
    // Use encoder directly to verify the appended element is at the right position
    let mut trans = setup_int_seq("s", 3);
    constrain_seq(&mut trans, "s", &[10, 20, 30]);

    // Resolve Append(s, 40) as a SeqTerm
    let append_expr = make_apply("Append", vec![make_ident("s"), make_int(40)]);
    let (seq_term, elem_sort) = trans.resolve_seq_term_with_sort(&append_expr).unwrap();

    // Verify the appended element at index 4 is 40
    let enc = SequenceEncoder::new(elem_sort);
    let idx4 = trans.solver_mut().int_const(4);
    let val = enc.encode_index(&mut trans, &seq_term, idx4).unwrap();
    let forty = trans.solver_mut().int_const(40);
    let eq = trans.solver_mut().try_eq(val, forty).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

// =========================================================================
// SubSeq tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseq_via_ast_len() {
    // Len(SubSeq(s, 2, 3)) where s = <<10, 20, 30, 40>> should be 2
    let mut trans = setup_int_seq("s", 4);
    constrain_seq(&mut trans, "s", &[10, 20, 30, 40]);

    let func = spanned(Expr::Ident(
        "Len".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let subseq_arg = make_apply("SubSeq", vec![make_ident("s"), make_int(2), make_int(3)]);
    let len_term = trans
        .try_translate_seq_op_int(&func, &[subseq_arg])
        .unwrap()
        .unwrap();

    // Assert Len(SubSeq(s, 2, 3)) = 2
    let two = trans.solver_mut().int_const(2);
    let eq = trans.solver_mut().try_eq(len_term, two).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseq_via_ast_head() {
    // Head(SubSeq(s, 2, 4)) where s = <<10, 20, 30, 40>> should be 20
    let mut trans = setup_int_seq("s", 4);
    constrain_seq(&mut trans, "s", &[10, 20, 30, 40]);

    let func = spanned(Expr::Ident(
        "Head".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let subseq_arg = make_apply("SubSeq", vec![make_ident("s"), make_int(2), make_int(4)]);
    let head_term = trans
        .try_translate_seq_op_int(&func, &[subseq_arg])
        .unwrap()
        .unwrap();

    // Head(SubSeq(s, 2, 4)) = 20
    let twenty = trans.solver_mut().int_const(20);
    let eq = trans.solver_mut().try_eq(head_term, twenty).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseq_elements() {
    // SubSeq(s, 2, 3) where s = <<10, 20, 30, 40>> should be <<20, 30>>
    let mut trans = setup_int_seq("s", 4);
    constrain_seq(&mut trans, "s", &[10, 20, 30, 40]);

    let subseq_expr = make_apply("SubSeq", vec![make_ident("s"), make_int(2), make_int(3)]);
    let (seq_term, elem_sort) = trans.resolve_seq_term_with_sort(&subseq_expr).unwrap();

    let enc = SequenceEncoder::new(elem_sort);

    // sub[1] = 20
    let idx1 = trans.solver_mut().int_const(1);
    let val1 = enc.encode_index(&mut trans, &seq_term, idx1).unwrap();
    let twenty = trans.solver_mut().int_const(20);
    let eq1 = trans.solver_mut().try_eq(val1, twenty).unwrap();
    trans.assert(eq1);

    // sub[2] = 30
    let idx2 = trans.solver_mut().int_const(2);
    let val2 = enc.encode_index(&mut trans, &seq_term, idx2).unwrap();
    let thirty = trans.solver_mut().int_const(30);
    let eq2 = trans.solver_mut().try_eq(val2, thirty).unwrap();
    trans.assert(eq2);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseq_empty_when_m_gt_n() {
    // SubSeq(s, 3, 1) where s = <<10, 20, 30>> should be <<>> (len=0)
    let mut trans = setup_int_seq("s", 3);
    constrain_seq(&mut trans, "s", &[10, 20, 30]);

    let func = spanned(Expr::Ident(
        "Len".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let subseq_arg = make_apply("SubSeq", vec![make_ident("s"), make_int(3), make_int(1)]);
    let len_term = trans
        .try_translate_seq_op_int(&func, &[subseq_arg])
        .unwrap()
        .unwrap();

    // Len(SubSeq(s, 3, 1)) = 0
    let zero = trans.solver_mut().int_const(0);
    let eq = trans.solver_mut().try_eq(len_term, zero).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

// =========================================================================
// Concatenation tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_concat_via_ast_len() {
    // Len(s \o t) where s = <<1, 2>> and t = <<3, 4, 5>> should be 5
    let mut trans = setup_two_int_seqs("s", 2, "t", 3);
    constrain_seq(&mut trans, "s", &[1, 2]);
    constrain_seq(&mut trans, "t", &[3, 4, 5]);

    let func = spanned(Expr::Ident(
        "Len".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let concat_arg = make_apply("\\o", vec![make_ident("s"), make_ident("t")]);
    let len_term = trans
        .try_translate_seq_op_int(&func, &[concat_arg])
        .unwrap()
        .unwrap();

    // Len(s \o t) = 5
    let five = trans.solver_mut().int_const(5);
    let eq = trans.solver_mut().try_eq(len_term, five).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_concat_via_ast_head() {
    // Head(s \o t) where s = <<1, 2>> and t = <<3, 4, 5>> should be 1
    let mut trans = setup_two_int_seqs("s", 2, "t", 3);
    constrain_seq(&mut trans, "s", &[1, 2]);
    constrain_seq(&mut trans, "t", &[3, 4, 5]);

    let func = spanned(Expr::Ident(
        "Head".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let concat_arg = make_apply("\\o", vec![make_ident("s"), make_ident("t")]);
    let head_term = trans
        .try_translate_seq_op_int(&func, &[concat_arg])
        .unwrap()
        .unwrap();

    // Head(s \o t) = 1
    let one = trans.solver_mut().int_const(1);
    let eq = trans.solver_mut().try_eq(head_term, one).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_concat_elements() {
    // (s \o t) where s = <<1, 2>> and t = <<3, 4, 5>>
    // result should be <<1, 2, 3, 4, 5>>
    let mut trans = setup_two_int_seqs("s", 2, "t", 3);
    constrain_seq(&mut trans, "s", &[1, 2]);
    constrain_seq(&mut trans, "t", &[3, 4, 5]);

    let concat_expr = make_apply("\\o", vec![make_ident("s"), make_ident("t")]);
    let (seq_term, elem_sort) = trans.resolve_seq_term_with_sort(&concat_expr).unwrap();
    let enc = SequenceEncoder::new(elem_sort);

    // Verify first two elements come from s
    let idx1 = trans.solver_mut().int_const(1);
    let val1 = enc.encode_index(&mut trans, &seq_term, idx1).unwrap();
    let one = trans.solver_mut().int_const(1);
    let eq1 = trans.solver_mut().try_eq(val1, one).unwrap();
    trans.assert(eq1);

    let idx2 = trans.solver_mut().int_const(2);
    let val2 = enc.encode_index(&mut trans, &seq_term, idx2).unwrap();
    let two = trans.solver_mut().int_const(2);
    let eq2 = trans.solver_mut().try_eq(val2, two).unwrap();
    trans.assert(eq2);

    // Verify last three elements come from t
    let idx3 = trans.solver_mut().int_const(3);
    let val3 = enc.encode_index(&mut trans, &seq_term, idx3).unwrap();
    let three = trans.solver_mut().int_const(3);
    let eq3 = trans.solver_mut().try_eq(val3, three).unwrap();
    trans.assert(eq3);

    let idx5 = trans.solver_mut().int_const(5);
    let val5 = enc.encode_index(&mut trans, &seq_term, idx5).unwrap();
    let five = trans.solver_mut().int_const(5);
    let eq5 = trans.solver_mut().try_eq(val5, five).unwrap();
    trans.assert(eq5);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_concat_circ_alias() {
    // \circ is an alias for \o — verify it works too
    let mut trans = setup_two_int_seqs("s", 2, "t", 3);
    constrain_seq(&mut trans, "s", &[1, 2]);
    constrain_seq(&mut trans, "t", &[3, 4, 5]);

    let func = spanned(Expr::Ident(
        "Len".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let concat_arg = make_apply("\\circ", vec![make_ident("s"), make_ident("t")]);
    let len_term = trans
        .try_translate_seq_op_int(&func, &[concat_arg])
        .unwrap()
        .unwrap();

    let five = trans.solver_mut().int_const(5);
    let eq = trans.solver_mut().try_eq(len_term, five).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

// =========================================================================
// Nested composition tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_head_of_tail_of_tail() {
    // Head(Tail(Tail(s))) where s = <<10, 20, 30, 40>> should be 30
    let mut trans = setup_int_seq("s", 4);
    constrain_seq(&mut trans, "s", &[10, 20, 30, 40]);

    let tail1 = make_apply("Tail", vec![make_ident("s")]);
    let tail2 = make_apply("Tail", vec![tail1]);

    let func = spanned(Expr::Ident(
        "Head".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let head_term = trans
        .try_translate_seq_op_int(&func, &[tail2])
        .unwrap()
        .unwrap();

    let thirty = trans.solver_mut().int_const(30);
    let eq = trans.solver_mut().try_eq(head_term, thirty).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_len_of_append_of_tail() {
    // Len(Append(Tail(s), 99)) where s = <<10, 20, 30>> should be 3
    // Tail(<<10,20,30>>) = <<20,30>> (len 2), Append that => len 3
    let mut trans = setup_int_seq("s", 3);
    constrain_seq(&mut trans, "s", &[10, 20, 30]);

    let tail = make_apply("Tail", vec![make_ident("s")]);
    let append = make_apply("Append", vec![tail, make_int(99)]);

    let func = spanned(Expr::Ident(
        "Len".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let len_term = trans
        .try_translate_seq_op_int(&func, &[append])
        .unwrap()
        .unwrap();

    let three = trans.solver_mut().int_const(3);
    let eq = trans.solver_mut().try_eq(len_term, three).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_head_of_concat() {
    // Head(s \o t) where s = <<1>> and t = <<2>> should be 1
    let mut trans = setup_two_int_seqs("s", 1, "t", 1);
    constrain_seq(&mut trans, "s", &[1]);
    constrain_seq(&mut trans, "t", &[2]);

    let concat = make_apply("\\o", vec![make_ident("s"), make_ident("t")]);
    let func = spanned(Expr::Ident(
        "Head".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let head_term = trans
        .try_translate_seq_op_int(&func, &[concat])
        .unwrap()
        .unwrap();

    let one = trans.solver_mut().int_const(1);
    let eq = trans.solver_mut().try_eq(head_term, one).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

// =========================================================================
// Error handling tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tail_of_nonexistent_var_fails() {
    let mut trans = Z4Translator::new_with_arrays();
    let tail_expr = make_apply("Tail", vec![make_ident("nonexistent")]);
    let result = trans.resolve_seq_term_with_sort(&tail_expr);
    assert!(result.is_err(), "Tail of undeclared variable should fail");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_append_of_nonexistent_var_fails() {
    let mut trans = Z4Translator::new_with_arrays();
    let append_expr = make_apply("Append", vec![make_ident("nonexistent"), make_int(1)]);
    let result = trans.resolve_seq_term_with_sort(&append_expr);
    assert!(
        result.is_err(),
        "Append on undeclared variable should fail"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unrecognized_apply_fails() {
    let mut trans = setup_int_seq("s", 3);
    let expr = make_apply("UnknownOp", vec![make_ident("s")]);
    let result = trans.resolve_seq_term_with_sort(&expr);
    assert!(
        result.is_err(),
        "Unknown operation should fail seq resolution"
    );
}

// =========================================================================
// Debug / regression tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_concat_basic_sat() {
    // Just verify that resolving s \o t produces a SAT result
    // without constraining length equality
    let mut trans = setup_two_int_seqs("s", 2, "t", 2);

    // Set concrete values: s = <<1,2>>, t = <<3,4>>
    constrain_seq(&mut trans, "s", &[1, 2]);
    constrain_seq(&mut trans, "t", &[3, 4]);

    let concat_expr = make_apply("\\o", vec![make_ident("s"), make_ident("t")]);
    let result = trans.resolve_seq_term_with_sort(&concat_expr);
    assert!(result.is_ok(), "resolve should succeed: {:?}", result.err());

    // Just check basic SAT without additional constraints
    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_tail_basic_sat() {
    // Just verify that resolving Tail(s) produces a SAT result
    let mut trans = setup_int_seq("s", 3);
    constrain_seq(&mut trans, "s", &[10, 20, 30]);

    let tail_expr = make_apply("Tail", vec![make_ident("s")]);
    let result = trans.resolve_seq_term_with_sort(&tail_expr);
    assert!(result.is_ok(), "resolve should succeed: {:?}", result.err());

    // Just check basic SAT
    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_resolve_tail_tail_basic_sat() {
    // Just verify that resolving Tail(Tail(s)) produces a SAT result
    let mut trans = setup_int_seq("s", 4);
    constrain_seq(&mut trans, "s", &[10, 20, 30, 40]);

    let tail1 = make_apply("Tail", vec![make_ident("s")]);
    let tail2 = make_apply("Tail", vec![tail1]);
    let result = trans.resolve_seq_term_with_sort(&tail2);
    assert!(result.is_ok(), "resolve should succeed: {:?}", result.err());

    // Just check basic SAT
    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_encoder_single_tail_sat() {
    // Use the encoder directly to check if single Tail produces SAT
    let mut trans = Z4Translator::new_with_arrays();
    let enc = SequenceEncoder::new(z4_dpll::api::Sort::Int);

    let e1 = trans.solver_mut().int_const(10);
    let e2 = trans.solver_mut().int_const(20);
    let e3 = trans.solver_mut().int_const(30);
    let e4 = trans.solver_mut().int_const(40);
    let seq = enc.encode_seq_enum(&mut trans, &[e1, e2, e3, e4]).unwrap();

    let tail1 = enc.encode_tail(&mut trans, &seq, 4).unwrap();

    assert_eq!(trans.check_sat(), SolveResult::Sat, "single tail should be SAT");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_encoder_double_tail_sat() {
    // Use the encoder directly to check if double Tail produces SAT
    let mut trans = Z4Translator::new_with_arrays();
    let enc = SequenceEncoder::new(z4_dpll::api::Sort::Int);

    // Create <<10, 20, 30, 40>>
    let e1 = trans.solver_mut().int_const(10);
    let e2 = trans.solver_mut().int_const(20);
    let e3 = trans.solver_mut().int_const(30);
    let e4 = trans.solver_mut().int_const(40);
    let seq = enc.encode_seq_enum(&mut trans, &[e1, e2, e3, e4]).unwrap();

    // Tail(Tail(seq))
    let tail1 = enc.encode_tail(&mut trans, &seq, 4).unwrap();
    let tail2 = enc.encode_tail(&mut trans, &tail1, 4).unwrap();

    // Just check SAT
    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_z4_arithmetic_lt_sub() {
    // Debug: check if z4-dpll handles 1 < (4 - 1) correctly
    let mut trans = Z4Translator::new_with_arrays();
    let four = trans.solver_mut().int_const(4);
    let one = trans.solver_mut().int_const(1);
    let three_expr = trans.solver_mut().try_sub(four, one).unwrap();
    let lt = trans.solver_mut().try_lt(one, three_expr).unwrap();
    trans.assert(lt);
    assert_eq!(trans.check_sat(), SolveResult::Sat, "1 < (4-1) should be SAT");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_z4_implies_with_array_select() {
    // Debug: check if implies(true, select(a,i) = select(b,j)) works
    let mut trans = Z4Translator::new_with_arrays();
    let arr_sort = z4_dpll::api::Sort::array(z4_dpll::api::Sort::Int, z4_dpll::api::Sort::Int);
    let a = trans.solver_mut().declare_const("a", arr_sort.clone());
    let b = trans.solver_mut().declare_const("b", arr_sort);
    let t = trans.solver_mut().bool_const(true);
    let two = trans.solver_mut().int_const(2);
    let three = trans.solver_mut().int_const(3);
    let a2 = trans.solver_mut().try_select(a, two).unwrap();
    let b3 = trans.solver_mut().try_select(b, three).unwrap();
    let eq = trans.solver_mut().try_eq(a2, b3).unwrap();
    let imp = trans.solver_mut().try_implies(t, eq).unwrap();
    trans.assert(imp);
    assert_eq!(trans.check_sat(), SolveResult::Sat, "implies(true, a[2]=b[3]) should be SAT");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_z4_chained_implies_select() {
    // Debug: chain of implies on selects (simulating double-tail)
    let mut trans = Z4Translator::new_with_arrays();
    let arr_sort = z4_dpll::api::Sort::array(z4_dpll::api::Sort::Int, z4_dpll::api::Sort::Int);

    // Base array with stores
    let base = trans.solver_mut().declare_const("base", arr_sort.clone());
    let ten = trans.solver_mut().int_const(10);
    let twenty = trans.solver_mut().int_const(20);
    let thirty = trans.solver_mut().int_const(30);
    let idx1 = trans.solver_mut().int_const(1);
    let idx2 = trans.solver_mut().int_const(2);
    let idx3 = trans.solver_mut().int_const(3);
    let base = trans.solver_mut().try_store(base, idx1, ten).unwrap();
    let base = trans.solver_mut().try_store(base, idx2, twenty).unwrap();
    let base = trans.solver_mut().try_store(base, idx3, thirty).unwrap();

    // First "tail" array: arr1[1] = base[2], arr1[2] = base[3]
    let arr1 = trans.solver_mut().declare_const("arr1", arr_sort.clone());
    let b2 = trans.solver_mut().try_select(base, idx2).unwrap();
    let a1_1 = trans.solver_mut().try_select(arr1, idx1).unwrap();
    let eq1 = trans.solver_mut().try_eq(a1_1, b2).unwrap();
    trans.assert(eq1);

    let b3 = trans.solver_mut().try_select(base, idx3).unwrap();
    let a1_2 = trans.solver_mut().try_select(arr1, idx2).unwrap();
    let eq2 = trans.solver_mut().try_eq(a1_2, b3).unwrap();
    trans.assert(eq2);

    // Second "tail" array: arr2[1] = arr1[2]
    let arr2 = trans.solver_mut().declare_const("arr2", arr_sort);
    let a1_2_again = trans.solver_mut().try_select(arr1, idx2).unwrap();
    let a2_1 = trans.solver_mut().try_select(arr2, idx1).unwrap();
    let eq3 = trans.solver_mut().try_eq(a2_1, a1_2_again).unwrap();
    trans.assert(eq3);

    // arr2[1] should = 30
    let a2_1_val = trans.solver_mut().try_select(arr2, idx1).unwrap();
    let eq_check = trans.solver_mut().try_eq(a2_1_val, thirty).unwrap();
    trans.assert(eq_check);

    assert_eq!(trans.check_sat(), SolveResult::Sat, "chained array select should be SAT");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_z4_implies_lt_sub_array() {
    // Simulate double-tail encoding pattern:
    // implies(i < (4-1), select(arr1, i) = select(arr0, i+1))
    let mut trans = Z4Translator::new_with_arrays();
    let arr_sort = z4_dpll::api::Sort::array(z4_dpll::api::Sort::Int, z4_dpll::api::Sort::Int);

    // Concrete base array
    let arr0 = trans.solver_mut().declare_const("arr0", arr_sort.clone());
    let c10 = trans.solver_mut().int_const(10);
    let c20 = trans.solver_mut().int_const(20);
    let c30 = trans.solver_mut().int_const(30);
    let idx1 = trans.solver_mut().int_const(1);
    let idx2 = trans.solver_mut().int_const(2);
    let idx3 = trans.solver_mut().int_const(3);
    let arr0 = trans.solver_mut().try_store(arr0, idx1, c10).unwrap();
    let arr0 = trans.solver_mut().try_store(arr0, idx2, c20).unwrap();
    let arr0 = trans.solver_mut().try_store(arr0, idx3, c30).unwrap();

    // First tail: arr1 fresh, for i=1,2: i < 3 => arr1[i] = arr0[i+1]
    let arr1 = trans.solver_mut().declare_const("arr1", arr_sort.clone());
    let three = trans.solver_mut().int_const(3);
    for i in 1..3usize {
        let i_t = trans.solver_mut().int_const(i as i64);
        let ip1 = trans.solver_mut().int_const((i + 1) as i64);
        let in_bounds = trans.solver_mut().try_lt(i_t, three).unwrap();
        let src = trans.solver_mut().try_select(arr0, ip1).unwrap();
        let dst = trans.solver_mut().try_select(arr1, i_t).unwrap();
        let eq = trans.solver_mut().try_eq(dst, src).unwrap();
        let imp = trans.solver_mut().try_implies(in_bounds, eq).unwrap();
        trans.assert(imp);
    }
    // len1 = 3 - 1 = 2
    let one = trans.solver_mut().int_const(1);
    let len1 = trans.solver_mut().try_sub(three, one).unwrap();

    // Second tail: arr2 fresh, for i=1: i < len1 => arr2[i] = arr1[i+1]
    let arr2 = trans.solver_mut().declare_const("arr2", arr_sort);
    for i in 1..3usize {
        let i_t = trans.solver_mut().int_const(i as i64);
        let ip1 = trans.solver_mut().int_const((i + 1) as i64);
        let in_bounds = trans.solver_mut().try_lt(i_t, len1).unwrap();
        let src = trans.solver_mut().try_select(arr1, ip1).unwrap();
        let dst = trans.solver_mut().try_select(arr2, i_t).unwrap();
        let eq = trans.solver_mut().try_eq(dst, src).unwrap();
        let imp = trans.solver_mut().try_implies(in_bounds, eq).unwrap();
        trans.assert(imp);
    }

    assert_eq!(trans.check_sat(), SolveResult::Sat, "double-tail pattern should be SAT");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_encoder_double_tail_small() {
    // Minimal: Tail(Tail(<<10, 20, 30>>)) — 3 elements, double tail
    let mut trans = Z4Translator::new_with_arrays();
    let enc = SequenceEncoder::new(z4_dpll::api::Sort::Int);

    let e1 = trans.solver_mut().int_const(10);
    let e2 = trans.solver_mut().int_const(20);
    let e3 = trans.solver_mut().int_const(30);
    let seq = enc.encode_seq_enum(&mut trans, &[e1, e2, e3]).unwrap();

    // First tail: max_len=3, loops i=1,2
    let tail1 = enc.encode_tail(&mut trans, &seq, 3).unwrap();

    // Do NOT call check_sat() here to avoid any solver state mutation

    // Second tail: max_len=3, loops i=1,2
    let _tail2 = enc.encode_tail(&mut trans, &tail1, 3).unwrap();

    assert_eq!(trans.check_sat(), SolveResult::Sat, "double tail should be SAT");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_encoder_double_tail_minimal() {
    // Even more minimal: Tail(Tail(<<1, 2>>)) with max_len=2
    let mut trans = Z4Translator::new_with_arrays();
    let enc = SequenceEncoder::new(z4_dpll::api::Sort::Int);

    let e1 = trans.solver_mut().int_const(1);
    let e2 = trans.solver_mut().int_const(2);
    let seq = enc.encode_seq_enum(&mut trans, &[e1, e2]).unwrap();

    // First tail: max_len=2, loops i=1 (1..2)
    let tail1 = enc.encode_tail(&mut trans, &seq, 2).unwrap();

    // Second tail: max_len=2, loops i=1 (1..2)
    let _tail2 = enc.encode_tail(&mut trans, &tail1, 2).unwrap();

    assert_eq!(trans.check_sat(), SolveResult::Sat, "double tail of 2-element seq");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_z4_double_tail_manual_constraints() {
    // Manually build the exact constraints that encode_tail would produce
    // for <<10, 20, 30>> with double tail
    let mut trans = Z4Translator::new_with_arrays();
    let arr_sort = z4_dpll::api::Sort::array(z4_dpll::api::Sort::Int, z4_dpll::api::Sort::Int);

    // Build <<10, 20, 30>> as store chain
    let base = trans.solver_mut().declare_const("base", arr_sort.clone());
    let c1 = trans.solver_mut().int_const(1);
    let c2 = trans.solver_mut().int_const(2);
    let c3 = trans.solver_mut().int_const(3);
    let c10 = trans.solver_mut().int_const(10);
    let c20 = trans.solver_mut().int_const(20);
    let c30 = trans.solver_mut().int_const(30);
    let seq_arr = trans.solver_mut().try_store(base, c1, c10).unwrap();
    let seq_arr = trans.solver_mut().try_store(seq_arr, c2, c20).unwrap();
    let seq_arr = trans.solver_mut().try_store(seq_arr, c3, c30).unwrap();
    let seq_len = trans.solver_mut().int_const(3);

    // First tail: tail1_arr, for i=1,2: i < 3 => tail1[i] = seq[i+1]
    let tail1_arr = trans.solver_mut().declare_const("t1", arr_sort.clone());
    for i in 1..3usize {
        let i_t = trans.solver_mut().int_const(i as i64);
        let ip1 = trans.solver_mut().int_const((i + 1) as i64);
        let guard = trans.solver_mut().try_lt(i_t, seq_len).unwrap();
        let src = trans.solver_mut().try_select(seq_arr, ip1).unwrap();
        let dst = trans.solver_mut().try_select(tail1_arr, i_t).unwrap();
        let eq = trans.solver_mut().try_eq(dst, src).unwrap();
        let imp = trans.solver_mut().try_implies(guard, eq).unwrap();
        trans.assert(imp);
    }
    let one = trans.solver_mut().int_const(1);
    let tail1_len = trans.solver_mut().try_sub(seq_len, one).unwrap();

    // Second tail: tail2_arr, for i=1,2: i < tail1_len => tail2[i] = tail1[i+1]
    let tail2_arr = trans.solver_mut().declare_const("t2", arr_sort);
    for i in 1..3usize {
        let i_t = trans.solver_mut().int_const(i as i64);
        let ip1 = trans.solver_mut().int_const((i + 1) as i64);
        let guard = trans.solver_mut().try_lt(i_t, tail1_len).unwrap();
        let src = trans.solver_mut().try_select(tail1_arr, ip1).unwrap();
        let dst = trans.solver_mut().try_select(tail2_arr, i_t).unwrap();
        let eq = trans.solver_mut().try_eq(dst, src).unwrap();
        let imp = trans.solver_mut().try_implies(guard, eq).unwrap();
        trans.assert(imp);
    }

    assert_eq!(trans.check_sat(), SolveResult::Sat, "manual double-tail");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_z4_declare_const_same_name_is_same_term() {
    // Check if declare_const with same name returns same or different term
    let mut trans = Z4Translator::new_with_arrays();
    let arr_sort = z4_dpll::api::Sort::array(z4_dpll::api::Sort::Int, z4_dpll::api::Sort::Int);
    let a1 = trans.solver_mut().declare_const("arr", arr_sort.clone());
    let a2 = trans.solver_mut().declare_const("arr", arr_sort);
    // If they're the same term, storing different values at the same index
    // should be UNSAT. If different, should be SAT.
    let idx = trans.solver_mut().int_const(1);
    let v1 = trans.solver_mut().int_const(10);
    let v2 = trans.solver_mut().int_const(20);
    let stored1 = trans.solver_mut().try_store(a1, idx, v1).unwrap();
    let stored2 = trans.solver_mut().try_store(a2, idx, v2).unwrap();
    let sel1 = trans.solver_mut().try_select(stored1, idx).unwrap();
    let sel2 = trans.solver_mut().try_select(stored2, idx).unwrap();
    let eq = trans.solver_mut().try_eq(sel1, sel2).unwrap();
    trans.assert(eq);
    let result = trans.check_sat();
    // If same term: UNSAT (10 = 20 is false). If different: SAT (no conflict)
    eprintln!("Same-name declare_const result: {result:?}");
    // This test is diagnostic — just print the result
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_concat_via_seq_var_to_seq_term() {
    // Reproduce the exact sequence of operations translate_concat_seq does
    let mut trans = setup_two_int_seqs("s", 2, "t", 2);
    constrain_seq(&mut trans, "s", &[1, 2]);
    constrain_seq(&mut trans, "t", &[3, 4]);

    // Manually do what resolve_seq_term_with_sort does
    let info_s = trans.get_seq_var("s").unwrap().clone();
    let z4_sort_s = info_s.element_sort.to_z4().unwrap();
    let seq_s = trans.seq_var_to_seq_term(&info_s, &z4_sort_s).unwrap();

    let info_t = trans.get_seq_var("t").unwrap().clone();
    let z4_sort_t = info_t.element_sort.to_z4().unwrap();
    let seq_t = trans.seq_var_to_seq_term(&info_t, &z4_sort_t).unwrap();

    // Skip pre-check to avoid solver state mutation
    // Now do concat
    let enc = SequenceEncoder::new(z4_sort_s);
    let _cat = enc.encode_concat(&mut trans, &seq_s, &seq_t, 4).unwrap();

    assert_eq!(trans.check_sat(), SolveResult::Sat, "after concat should be SAT");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_encoder_concat_two_concrete_sat() {
    // Use the encoder directly to check if concat of two concrete sequences is SAT
    let mut trans = Z4Translator::new_with_arrays();
    let enc = SequenceEncoder::new(z4_dpll::api::Sort::Int);

    let e1 = trans.solver_mut().int_const(1);
    let e2 = trans.solver_mut().int_const(2);
    let s = enc.encode_seq_enum(&mut trans, &[e1, e2]).unwrap();

    let e3 = trans.solver_mut().int_const(3);
    let e4 = trans.solver_mut().int_const(4);
    let t = enc.encode_seq_enum(&mut trans, &[e3, e4]).unwrap();

    let cat = enc.encode_concat(&mut trans, &s, &t, 4).unwrap();

    assert_eq!(trans.check_sat(), SolveResult::Sat, "concat should be SAT");
}

// =========================================================================
// Symbolic (unconstrained) tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tail_symbolic_len_bound() {
    // For symbolic s with max_len=5, Len(Tail(s)) should be Len(s) - 1
    // Constrain Len(s) = 3, then Len(Tail(s)) should be satisfiable at 2
    let mut trans = setup_int_seq("s", 5);

    // Constrain Len(s) = 3
    let len = trans.get_seq_var("s").unwrap().len_term;
    let three = trans.solver_mut().int_const(3);
    let len_eq = trans.solver_mut().try_eq(len, three).unwrap();
    trans.assert(len_eq);

    let func = spanned(Expr::Ident(
        "Len".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let tail_arg = make_apply("Tail", vec![make_ident("s")]);
    let tail_len = trans
        .try_translate_seq_op_int(&func, &[tail_arg])
        .unwrap()
        .unwrap();

    // Assert Len(Tail(s)) = 2
    let two = trans.solver_mut().int_const(2);
    let eq = trans.solver_mut().try_eq(tail_len, two).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_append_symbolic_len_bound() {
    // For symbolic s with Len(s) = 3, Len(Append(s, 99)) should be 4
    let mut trans = setup_int_seq("s", 5);

    let len = trans.get_seq_var("s").unwrap().len_term;
    let three = trans.solver_mut().int_const(3);
    let len_eq = trans.solver_mut().try_eq(len, three).unwrap();
    trans.assert(len_eq);

    let func = spanned(Expr::Ident(
        "Len".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let append_arg = make_apply("Append", vec![make_ident("s"), make_int(99)]);
    let append_len = trans
        .try_translate_seq_op_int(&func, &[append_arg])
        .unwrap()
        .unwrap();

    // Assert Len(Append(s, 99)) = 4
    let four = trans.solver_mut().int_const(4);
    let eq = trans.solver_mut().try_eq(append_len, four).unwrap();
    trans.assert(eq);

    assert_eq!(trans.check_sat(), SolveResult::Sat);
}
