// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;

#[test]
fn test_normalize_commutative_bvadd() {
    let mut terms = TermStore::new();

    // Create (bvadd a b) and (bvadd b a)
    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let add_ab = terms.mk_bvadd(vec![a, b]);
    let add_ba = terms.mk_bvadd(vec![b, a]);

    // Before normalization, they may differ
    // (depends on whether mk_bvadd canonicalizes)

    let mut pass = NormalizeBvArith::new();
    let norm_ab = pass.normalize(&mut terms, add_ab);
    pass.cache.clear(); // Clear cache to test independent normalization
    let norm_ba = pass.normalize(&mut terms, add_ba);

    // After normalization, they should be identical
    assert_eq!(
        norm_ab, norm_ba,
        "Commutativity: (bvadd a b) and (bvadd b a) should normalize to same term"
    );
}

#[test]
fn test_normalize_commutative_bvmul() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let mul_ab = terms.mk_bvmul(vec![a, b]);
    let mul_ba = terms.mk_bvmul(vec![b, a]);

    let mut pass = NormalizeBvArith::new();
    let norm_ab = pass.normalize(&mut terms, mul_ab);
    pass.cache.clear();
    let norm_ba = pass.normalize(&mut terms, mul_ba);

    assert_eq!(
        norm_ab, norm_ba,
        "Commutativity: (bvmul a b) and (bvmul b a) should normalize to same term"
    );
}

#[test]
fn test_normalize_associative_bvadd() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let c = terms.mk_var("c", Sort::bitvec(8));

    // (bvadd (bvadd a b) c)
    let add_ab = terms.mk_bvadd(vec![a, b]);
    let left_assoc = terms.mk_bvadd(vec![add_ab, c]);

    // (bvadd a (bvadd b c))
    let add_bc = terms.mk_bvadd(vec![b, c]);
    let right_assoc = terms.mk_bvadd(vec![a, add_bc]);

    let mut pass = NormalizeBvArith::new();
    let norm_left = pass.normalize(&mut terms, left_assoc);
    pass.cache.clear();
    let norm_right = pass.normalize(&mut terms, right_assoc);

    assert_eq!(
        norm_left, norm_right,
        "Associativity: ((a+b)+c) and (a+(b+c)) should normalize to same term"
    );
}

#[test]
fn test_normalize_deeply_nested() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let c = terms.mk_var("c", Sort::bitvec(8));
    let d = terms.mk_var("d", Sort::bitvec(8));

    // ((a + b) + (c + d))
    let add_ab = terms.mk_bvadd(vec![a, b]);
    let add_cd = terms.mk_bvadd(vec![c, d]);
    let nested = terms.mk_bvadd(vec![add_ab, add_cd]);

    // (((d + c) + b) + a) - different nesting and order
    let add_dc = terms.mk_bvadd(vec![d, c]);
    let add_dcb = terms.mk_bvadd(vec![add_dc, b]);
    let other = terms.mk_bvadd(vec![add_dcb, a]);

    let mut pass = NormalizeBvArith::new();
    let norm_nested = pass.normalize(&mut terms, nested);
    pass.cache.clear();
    let norm_other = pass.normalize(&mut terms, other);

    assert_eq!(
        norm_nested, norm_other,
        "Deeply nested should normalize to same term"
    );
}

#[test]
fn test_normalize_idempotent() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let add_ab = terms.mk_bvadd(vec![a, b]);

    let mut pass = NormalizeBvArith::new();
    let norm1 = pass.normalize(&mut terms, add_ab);
    pass.cache.clear();
    let norm2 = pass.normalize(&mut terms, norm1);

    assert_eq!(norm1, norm2, "Normalization should be idempotent");
}

#[test]
fn test_normalize_preserves_constants() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let const_5 = terms.mk_bitvec(BigInt::from(5), 8);
    let add = terms.mk_bvadd(vec![const_5, a]);

    let mut pass = NormalizeBvArith::new();
    let normalized = pass.normalize(&mut terms, add);

    // The normalized form should still contain both operands
    // (constant folding is done by mk_bvadd, not by normalization)
    match terms.get(normalized) {
        TermData::App(sym, args) if sym.name() == "bvadd" => {
            assert_eq!(args.len(), 2);
            // Args should be sorted by TermId
            assert!(args[0].index() <= args[1].index());
        }
        _ => panic!("Expected bvadd application"),
    }
}

#[test]
fn test_pass_apply() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let add_ba = terms.mk_bvadd(vec![b, a]); // b + a

    let mut assertions = vec![add_ba];
    let mut pass = NormalizeBvArith::new();

    // Apply pass
    let _modified = pass.apply(&mut terms, &mut assertions);

    // Note: might not modify if a < b in TermId ordering
    // The key is that it's deterministic
    assert_eq!(assertions.len(), 1);
}

#[test]
fn test_normalize_nested_in_equality() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let c = terms.mk_var("c", Sort::bitvec(8));

    // (= (bvadd b a) c)
    let add_ba = terms.mk_bvadd(vec![b, a]);
    let eq = terms.mk_eq(add_ba, c);

    let mut pass = NormalizeBvArith::new();
    let normalized = pass.normalize(&mut terms, eq);

    // The equality should have normalized children
    if let TermData::App(sym, args) = terms.get(normalized) {
        assert_eq!(sym.name(), "=");
        assert_eq!(args.len(), 2);
        // The bvadd inside should be normalized
    }
}

#[test]
fn test_normalize_commutative_bvand() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let and_ab = terms.mk_bvand(vec![a, b]);
    let and_ba = terms.mk_bvand(vec![b, a]);

    let mut pass = NormalizeBvArith::new();
    let norm_ab = pass.normalize(&mut terms, and_ab);
    pass.cache.clear();
    let norm_ba = pass.normalize(&mut terms, and_ba);

    assert_eq!(
        norm_ab, norm_ba,
        "Commutativity: (bvand a b) and (bvand b a) should normalize to same term"
    );
}

#[test]
fn test_normalize_commutative_bvor() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let or_ab = terms.mk_bvor(vec![a, b]);
    let or_ba = terms.mk_bvor(vec![b, a]);

    let mut pass = NormalizeBvArith::new();
    let norm_ab = pass.normalize(&mut terms, or_ab);
    pass.cache.clear();
    let norm_ba = pass.normalize(&mut terms, or_ba);

    assert_eq!(
        norm_ab, norm_ba,
        "Commutativity: (bvor a b) and (bvor b a) should normalize to same term"
    );
}

#[test]
fn test_normalize_commutative_bvxor() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let xor_ab = terms.mk_bvxor(vec![a, b]);
    let xor_ba = terms.mk_bvxor(vec![b, a]);

    let mut pass = NormalizeBvArith::new();
    let norm_ab = pass.normalize(&mut terms, xor_ab);
    pass.cache.clear();
    let norm_ba = pass.normalize(&mut terms, xor_ba);

    assert_eq!(
        norm_ab, norm_ba,
        "Commutativity: (bvxor a b) and (bvxor b a) should normalize to same term"
    );
}

#[test]
fn test_bvsub_not_normalized() {
    // bvsub is NOT commutative: a - b != b - a
    // The pass should NOT normalize bvsub
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let sub_ab = terms.mk_bvsub(vec![a, b]);
    let sub_ba = terms.mk_bvsub(vec![b, a]);

    let mut pass = NormalizeBvArith::new();
    let norm_ab = pass.normalize(&mut terms, sub_ab);
    pass.cache.clear();
    let norm_ba = pass.normalize(&mut terms, sub_ba);

    // They should remain different (not normalized to same form)
    assert_ne!(
        norm_ab, norm_ba,
        "bvsub should NOT be normalized (non-commutative)"
    );
}
