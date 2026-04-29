// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;
use num_integer::Integer;

// P26: Integer Arithmetic - Commutativity

#[kani::proof]
fn verify_int_add_commutative() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    let a_big = BigInt::from(a as i64);
    let b_big = BigInt::from(b as i64);
    let sum_ab = &a_big + &b_big;
    let sum_ba = &b_big + &a_big;
    assert!(sum_ab == sum_ba, "Integer addition must be commutative");
}

#[kani::proof]
fn verify_int_mul_commutative() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    let a_big = BigInt::from(a as i64);
    let b_big = BigInt::from(b as i64);
    let prod_ab = &a_big * &b_big;
    let prod_ba = &b_big * &a_big;
    assert!(
        prod_ab == prod_ba,
        "Integer multiplication must be commutative"
    );
}

// P27: Associativity

#[kani::proof]
fn verify_int_add_associative() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    let c: i8 = kani::any();
    kani::assume(a.checked_add(b).is_some());
    kani::assume(b.checked_add(c).is_some());
    let a_big = BigInt::from(a as i64);
    let b_big = BigInt::from(b as i64);
    let c_big = BigInt::from(c as i64);
    let left = (&a_big + &b_big) + &c_big;
    let right = &a_big + (&b_big + &c_big);
    assert!(left == right, "Integer addition must be associative");
}

#[kani::proof]
fn verify_int_mul_associative() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    let c: i8 = kani::any();
    let a_big = BigInt::from(a as i64);
    let b_big = BigInt::from(b as i64);
    let c_big = BigInt::from(c as i64);
    let left = (&a_big * &b_big) * &c_big;
    let right = &a_big * (&b_big * &c_big);
    assert!(left == right, "Integer multiplication must be associative");
}

// P28: Identity Elements

#[kani::proof]
fn verify_int_add_identity() {
    let a: i8 = kani::any();
    let a_big = BigInt::from(a as i64);
    let zero = BigInt::from(0);
    let result = &a_big + &zero;
    assert!(result == a_big, "Zero is additive identity");
}

#[kani::proof]
fn verify_int_mul_identity() {
    let a: i8 = kani::any();
    let a_big = BigInt::from(a as i64);
    let one = BigInt::from(1);
    let result = &a_big * &one;
    assert!(result == a_big, "One is multiplicative identity");
}

// P29: Additive Inverse

#[kani::proof]
fn verify_int_add_inverse() {
    let a: i8 = kani::any();
    let a_big = BigInt::from(a as i64);
    let neg_a = -&a_big;
    let result = &a_big + &neg_a;
    assert!(result == BigInt::from(0), "a + (-a) = 0");
}

// P30: Distributivity

#[kani::proof]
fn verify_int_mul_distributes_over_add() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    let c: i8 = kani::any();
    let a_big = BigInt::from(a as i64);
    let b_big = BigInt::from(b as i64);
    let c_big = BigInt::from(c as i64);
    let left = &a_big * (&b_big + &c_big);
    let right = (&a_big * &b_big) + (&a_big * &c_big);
    assert!(
        left == right,
        "Multiplication distributes over addition: a*(b+c) = a*b + a*c"
    );
}

// P31: Division Properties

#[kani::proof]
fn verify_int_div_mod_relationship() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    kani::assume(b != 0);
    let a_big = BigInt::from(a as i64);
    let b_big = BigInt::from(b as i64);
    let quotient = a_big.div_floor(&b_big);
    let remainder = a_big.mod_floor(&b_big);
    let reconstructed = &quotient * &b_big + &remainder;
    assert!(reconstructed == a_big, "a = (a div b) * b + (a mod b)");
}

#[kani::proof]
fn verify_int_mod_range() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    kani::assume(b != 0);
    let a_big = BigInt::from(a as i64);
    let b_big = BigInt::from(b as i64);
    let abs_b = if b_big < BigInt::from(0) {
        -&b_big
    } else {
        b_big.clone()
    };
    let remainder = ((&a_big % &abs_b) + &abs_b) % &abs_b;
    assert!(
        remainder >= BigInt::from(0) && remainder < abs_b,
        "0 <= (a mod b) < |b|"
    );
}

// P32-P39: Boolean Algebra

#[kani::proof]
fn verify_bool_and_commutative() {
    let a: bool = kani::any();
    let b: bool = kani::any();
    assert!((a && b) == (b && a), "Boolean AND must be commutative");
}

#[kani::proof]
fn verify_bool_or_commutative() {
    let a: bool = kani::any();
    let b: bool = kani::any();
    assert!((a || b) == (b || a), "Boolean OR must be commutative");
}

#[kani::proof]
fn verify_bool_and_associative() {
    let a: bool = kani::any();
    let b: bool = kani::any();
    let c: bool = kani::any();
    assert!(
        ((a && b) && c) == (a && (b && c)),
        "Boolean AND must be associative"
    );
}

#[kani::proof]
fn verify_bool_or_associative() {
    let a: bool = kani::any();
    let b: bool = kani::any();
    let c: bool = kani::any();
    assert!(
        ((a || b) || c) == (a || (b || c)),
        "Boolean OR must be associative"
    );
}

#[kani::proof]
fn verify_bool_and_identity() {
    let a: bool = kani::any();
    assert!((a && true) == a, "TRUE is AND identity");
}

#[kani::proof]
fn verify_bool_or_identity() {
    let a: bool = kani::any();
    assert!((a || false) == a, "FALSE is OR identity");
}

#[kani::proof]
fn verify_bool_and_annihilator() {
    let a: bool = kani::any();
    assert!((a && false) == false, "FALSE is AND annihilator");
}

#[kani::proof]
fn verify_bool_or_annihilator() {
    let a: bool = kani::any();
    assert!((a || true) == true, "TRUE is OR annihilator");
}

#[kani::proof]
fn verify_bool_and_complement() {
    let a: bool = kani::any();
    assert!((a && !a) == false, "a AND (NOT a) = FALSE");
}

#[kani::proof]
fn verify_bool_or_complement() {
    let a: bool = kani::any();
    assert!((a || !a) == true, "a OR (NOT a) = TRUE");
}

#[kani::proof]
fn verify_bool_double_negation() {
    let a: bool = kani::any();
    assert!(!!a == a, "Double negation: NOT(NOT a) = a");
}

#[kani::proof]
fn verify_de_morgan_and() {
    let a: bool = kani::any();
    let b: bool = kani::any();
    assert!(
        !(a && b) == (!a || !b),
        "De Morgan: NOT(a AND b) = (NOT a) OR (NOT b)"
    );
}

#[kani::proof]
fn verify_de_morgan_or() {
    let a: bool = kani::any();
    let b: bool = kani::any();
    assert!(
        !(a || b) == (!a && !b),
        "De Morgan: NOT(a OR b) = (NOT a) AND (NOT b)"
    );
}

#[kani::proof]
fn verify_implies_definition() {
    let a: bool = kani::any();
    let b: bool = kani::any();
    let implies_ab = !a || b;
    let material_impl = if a { b } else { true };
    assert!(implies_ab == material_impl, "a => b iff (NOT a) OR b");
}

#[kani::proof]
fn verify_implies_reflexive() {
    let a: bool = kani::any();
    let implies_aa = !a || a;
    assert!(implies_aa, "a => a is always TRUE");
}

#[kani::proof]
fn verify_equiv_definition() {
    let a: bool = kani::any();
    let b: bool = kani::any();
    let equiv = a == b;
    let impl_both = (!a || b) && (!b || a);
    assert!(equiv == impl_both, "(a <=> b) = (a => b) AND (b => a)");
}

#[kani::proof]
fn verify_equiv_reflexive() {
    let a: bool = kani::any();
    assert!(a == a, "a <=> a is always TRUE");
}

#[kani::proof]
fn verify_equiv_symmetric() {
    let a: bool = kani::any();
    let b: bool = kani::any();
    assert!((a == b) == (b == a), "Equivalence is symmetric");
}
