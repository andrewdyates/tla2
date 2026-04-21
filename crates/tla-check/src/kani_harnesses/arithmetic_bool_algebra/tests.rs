// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_add_commutative() {
    for (a, b) in [(-128i64, 127), (0, 0), (1, -1), (42, 17)] {
        let a_big = BigInt::from(a);
        let b_big = BigInt::from(b);
        assert_eq!(
            &a_big + &b_big,
            &b_big + &a_big,
            "Addition must be commutative"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_mul_commutative() {
    for (a, b) in [(-10i64, 10), (0, 5), (1, -1), (7, 8)] {
        let a_big = BigInt::from(a);
        let b_big = BigInt::from(b);
        assert_eq!(
            &a_big * &b_big,
            &b_big * &a_big,
            "Multiplication must be commutative"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_add_associative() {
    for (a, b, c) in [(-10i64, 20, -5), (0, 0, 0), (1, 2, 3)] {
        let a_big = BigInt::from(a);
        let b_big = BigInt::from(b);
        let c_big = BigInt::from(c);
        assert_eq!(
            (&a_big + &b_big) + &c_big,
            &a_big + (&b_big + &c_big),
            "Addition must be associative"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_mul_associative() {
    for (a, b, c) in [(-2i64, 3, 4), (1, 1, 1), (2, 0, 5)] {
        let a_big = BigInt::from(a);
        let b_big = BigInt::from(b);
        let c_big = BigInt::from(c);
        assert_eq!(
            (&a_big * &b_big) * &c_big,
            &a_big * (&b_big * &c_big),
            "Multiplication must be associative"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_identity_elements() {
    use num_traits::{One, Zero};

    for a in [-100i64, -1, 0, 1, 100] {
        let a_big = BigInt::from(a);
        let zero: BigInt = Zero::zero();
        let one: BigInt = One::one();
        assert_eq!(&a_big + &zero, a_big, "0 is additive identity");
        assert_eq!(&a_big * &one, a_big, "1 is multiplicative identity");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_additive_inverse() {
    use num_traits::Zero;

    for a in [-100i64, -1, 0, 1, 100] {
        let a_big = BigInt::from(a);
        let neg_a = -&a_big;
        let zero: BigInt = Zero::zero();
        assert_eq!(&a_big + &neg_a, zero, "a + (-a) = 0");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_distributivity() {
    for (a, b, c) in [(2i64, 3, 4), (-1, 5, -3), (0, 1, 2)] {
        let a_big = BigInt::from(a);
        let b_big = BigInt::from(b);
        let c_big = BigInt::from(c);
        let left = &a_big * (&b_big + &c_big);
        let right = (&a_big * &b_big) + (&a_big * &c_big);
        assert_eq!(left, right, "a*(b+c) = a*b + a*c");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_div_mod_relationship() {
    use num_integer::Integer;

    for (a, b) in [(-7i64, 3), (7, 3), (10, -3), (-10, -3), (0, 5)] {
        let a_big = BigInt::from(a);
        let b_big = BigInt::from(b);
        let quotient = a_big.div_floor(&b_big);
        let remainder = a_big.mod_floor(&b_big);
        let reconstructed = &quotient * &b_big + &remainder;
        assert_eq!(reconstructed, a_big, "a = (a div b) * b + (a mod b)");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_mod_range() {
    use num_traits::Zero;

    for (a, b) in [(-7i64, 3), (7, 3), (10, -3), (-10, -3)] {
        let a_big = BigInt::from(a);
        let b_big = BigInt::from(b);
        let abs_b = if b_big < Zero::zero() {
            -&b_big
        } else {
            b_big.clone()
        };
        let remainder = ((&a_big % &abs_b) + &abs_b) % &abs_b;
        assert!(
            remainder >= Zero::zero() && remainder < abs_b,
            "0 <= (a mod b) < |b| for a={}, b={}",
            a,
            b
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bool_commutativity() {
    for (a, b) in [(true, true), (true, false), (false, true), (false, false)] {
        assert_eq!(a && b, b && a, "AND must be commutative");
        assert_eq!(a || b, b || a, "OR must be commutative");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bool_associativity() {
    for (a, b, c) in [
        (true, true, true),
        (true, true, false),
        (true, false, false),
        (false, false, false),
    ] {
        assert_eq!((a && b) && c, a && (b && c), "AND must be associative");
        assert_eq!((a || b) || c, a || (b || c), "OR must be associative");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[allow(clippy::nonminimal_bool, clippy::overly_complex_bool_expr)]
fn test_bool_identity_annihilator() {
    for a in [true, false] {
        let and_identity = a && true;
        assert_eq!(and_identity, a, "TRUE is AND identity");
        let or_identity = a || false;
        assert_eq!(or_identity, a, "FALSE is OR identity");
        let and_annihilator = a && false;
        assert!(!and_annihilator, "FALSE is AND annihilator");
        let or_annihilator = a || true;
        assert!(or_annihilator, "TRUE is OR annihilator");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[allow(clippy::overly_complex_bool_expr, clippy::nonminimal_bool)]
fn test_bool_complement() {
    for a in [true, false] {
        let and_complement = a && !a;
        assert!(!and_complement, "a AND (NOT a) = FALSE");
        let or_complement = a || !a;
        assert!(or_complement, "a OR (NOT a) = TRUE");
        let double_neg = !!a;
        assert_eq!(double_neg, a, "Double negation: NOT(NOT a) = a");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_de_morgan_laws() {
    for (a, b) in [(true, true), (true, false), (false, true), (false, false)] {
        assert_eq!(!(a && b), !a || !b, "NOT(a AND b) = (NOT a) OR (NOT b)");
        assert_eq!(!(a || b), !a && !b, "NOT(a OR b) = (NOT a) AND (NOT b)");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[allow(clippy::overly_complex_bool_expr)]
fn test_bool_implication() {
    for (a, b) in [(true, true), (true, false), (false, true), (false, false)] {
        let implies = !a || b;
        let expected = if a { b } else { true };
        assert_eq!(implies, expected, "a => b iff (NOT a) OR b");
    }
    for a in [true, false] {
        let reflexive = !a || a;
        assert!(reflexive, "a => a is always TRUE");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bool_equivalence() {
    for (a, b) in [(true, true), (true, false), (false, true), (false, false)] {
        let equiv = a == b;
        let impl_both = (!a || b) && (!b || a);
        assert_eq!(equiv, impl_both, "(a <=> b) = (a => b) AND (b => a)");
        assert_eq!((a == b), (b == a), "Equivalence is symmetric");
    }
}
