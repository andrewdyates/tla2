// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic operator implementations for [`Rational`].

use crate::rational::{gcd_u64, normalize_small, Rational};
use num_traits::Zero;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

// ─── Helpers ────────────────────────────────────────────────────────────────

/// Binary GCD for u128 (no allocation, no division).
/// #8782: Used by try_add/sub/mul_small to reduce i128 intermediates back to i64.
#[inline]
fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    if a == 0 {
        return b;
    }
    if b == 0 {
        return a;
    }
    let shift = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop {
        b >>= b.trailing_zeros();
        if a > b {
            std::mem::swap(&mut a, &mut b);
        }
        b -= a;
        if b == 0 {
            return a << shift;
        }
    }
}

// ─── Fused multiply-add ──────────────────────────────────────────────────────

impl Rational {
    /// Fused multiply-add: `self += a * b`.
    ///
    /// When all three operands are `Small(i64, i64)`, computes `self + a * b`
    /// entirely in i128 arithmetic with a single GCD reduction, instead of the
    /// two separate reductions that `self += &(&a * &b)` would require. This
    /// delays the i64 overflow point by eliminating intermediate normalization.
    ///
    /// Hot path: called per-coefficient in `compute_implied_bounds` row
    /// accumulation (#8003). Profile data shows 32% of time in
    /// compute_implied_bounds with 10% in `Rational::to_big()` → `BigRational::new()`
    /// → `BigUint::gcd()` from overflow in the separate mul+add path.
    ///
    /// Returns the product `a * b` as a Rational for callers that also need it
    /// (the contribution value stored in lb_contribs/ub_contribs).
    #[inline]
    pub fn add_product(&mut self, a: &Rational, b: &Rational) -> Rational {
        if let (
            Rational::Small(sn, sd),
            Rational::Small(an, ad),
            Rational::Small(bn, bd),
        ) = (&*self, a, b)
        {
            // Product: a * b = (an*bn) / (ad*bd)
            // Pre-reduce to minimize intermediate magnitude:
            // gcd(an, bd) and gcd(bn, ad)
            let g1 = gcd_u64(an.unsigned_abs(), bd.unsigned_abs());
            let g2 = gcd_u64(bn.unsigned_abs(), ad.unsigned_abs());
            let anr = *an / g1 as i64;
            let bdr = *bd / g1 as i64;
            let bnr = *bn / g2 as i64;
            let adr = *ad / g2 as i64;

            let prod_n = i128::from(anr) * i128::from(bnr); // up to ~126 bits
            let prod_d = i128::from(adr) * i128::from(bdr); // up to ~126 bits, positive

            // self + prod = sn/sd + prod_n/prod_d
            // = (sn * prod_d + prod_n * sd) / (sd * prod_d)
            let sum_d = i128::from(*sd) * prod_d; // sd(63) * prod_d(126) could be 189 bits
            // Check for i128 overflow in denominator
            if sum_d == 0 {
                // Fall back to default path
                let product = a * b;
                *self += &product;
                return product;
            }

            let term1 = i128::from(*sn).checked_mul(prod_d);
            let term2 = prod_n.checked_mul(i128::from(*sd));
            if let (Some(t1), Some(t2)) = (term1, term2) {
                if let Some(sum_n) = t1.checked_add(t2) {
                    // GCD reduce and try to fit in i64
                    let g = gcd_u128(sum_n.unsigned_abs(), sum_d.unsigned_abs());
                    let rn = sum_n / g as i128;
                    let rd = sum_d / g as i128;
                    let (rn, rd) = if rd < 0 { (-rn, -rd) } else { (rn, rd) };
                    if let (Ok(n), Ok(d)) = (i64::try_from(rn), i64::try_from(rd)) {
                        *self = Rational::Small(n, d);
                        // Also produce the product for the caller
                        // Reduce prod_n/prod_d to Rational
                        let pg = gcd_u128(prod_n.unsigned_abs(), prod_d.unsigned_abs());
                        let pn = prod_n / pg as i128;
                        let pd = prod_d / pg as i128;
                        let (pn, pd) = if pd < 0 { (-pn, -pd) } else { (pn, pd) };
                        let product = if let (Ok(pn64), Ok(pd64)) = (i64::try_from(pn), i64::try_from(pd)) {
                            Rational::Small(pn64, pd64)
                        } else {
                            a * b
                        };
                        return product;
                    }
                }
            }
        }
        // Fallback: separate multiply and add
        let product = a * b;
        *self += &product;
        product
    }
}

// ─── Add ────────────────────────────────────────────────────────────────────

/// Try small addition: a/b + c/d = (a*d + c*b) / (b*d)
/// #8782: Pre-reduce denominators by GCD to keep intermediates in i64 range
/// for coefficients like 999/1000 + 1001/1000 that blow up without reduction.
/// Falls back to i128 with GCD reduction before attempting i64 conversion.
#[inline]
fn try_add_small(n1: i64, d1: i64, n2: i64, d2: i64) -> Option<Rational> {
    if d1 == d2 {
        let n = n1.checked_add(n2)?;
        return normalize_small(n, d1).map(|(n, d)| Rational::Small(n, d));
    }
    // Pre-reduce denominators: gcd(d1,d2) shrinks cross-products
    let dg = gcd_u64(d1.unsigned_abs(), d2.unsigned_abs());
    let d1g = d1 / dg as i64;
    let d2g = d2 / dg as i64;
    // a/b + c/d = (a*(d/g) + c*(b/g)) / (b/g * d)
    let num = i128::from(n1) * i128::from(d2g) + i128::from(n2) * i128::from(d1g);
    let den = i128::from(d1g) * i128::from(d2);
    if den == 0 {
        return None;
    }
    // Reduce by GCD to maximize chance of fitting in i64
    let g = gcd_u128(num.unsigned_abs(), den.unsigned_abs());
    let rn = num / g as i128;
    let rd = den / g as i128;
    let (rn, rd) = if rd < 0 { (-rn, -rd) } else { (rn, rd) };
    if let (Ok(n), Ok(d)) = (i64::try_from(rn), i64::try_from(rd)) {
        Some(Rational::Small(n, d))
    } else {
        None
    }
}

impl Add for Rational {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        if let (Self::Small(n1, d1), Self::Small(n2, d2)) = (&self, &rhs) {
            if let Some(r) = try_add_small(*n1, *d1, *n2, *d2) {
                return r;
            }
        }
        Self::from_big(self.to_big() + rhs.to_big())
    }
}

impl Add for &Rational {
    type Output = Rational;
    #[inline]
    fn add(self, rhs: &Rational) -> Rational {
        if let (Rational::Small(n1, d1), Rational::Small(n2, d2)) = (self, rhs) {
            if let Some(r) = try_add_small(*n1, *d1, *n2, *d2) {
                return r;
            }
        }
        Rational::from_big(self.to_big() + rhs.to_big())
    }
}

impl AddAssign for Rational {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        // #7973: Skip when adding zero.
        if rhs.is_zero() {
            return;
        }
        if self.is_zero() {
            *self = rhs;
            return;
        }
        *self = std::mem::take(self) + rhs;
    }
}

impl AddAssign<&Self> for Rational {
    #[inline]
    fn add_assign(&mut self, rhs: &Self) {
        // #7973: Skip when adding zero.
        if rhs.is_zero() {
            return;
        }
        if self.is_zero() {
            *self = rhs.clone();
            return;
        }
        *self = &*self + rhs;
    }
}

// ─── Sub ────────────────────────────────────────────────────────────────────

/// Try small subtraction: a/b - c/d = (a*d - c*b) / (b*d)
/// #8782: Same denominator pre-reduction as try_add_small.
#[inline]
fn try_sub_small(n1: i64, d1: i64, n2: i64, d2: i64) -> Option<Rational> {
    if d1 == d2 {
        let n = n1.checked_sub(n2)?;
        return normalize_small(n, d1).map(|(n, d)| Rational::Small(n, d));
    }
    let dg = gcd_u64(d1.unsigned_abs(), d2.unsigned_abs());
    let d1g = d1 / dg as i64;
    let d2g = d2 / dg as i64;
    let num = i128::from(n1) * i128::from(d2g) - i128::from(n2) * i128::from(d1g);
    let den = i128::from(d1g) * i128::from(d2);
    if den == 0 {
        return None;
    }
    let g = gcd_u128(num.unsigned_abs(), den.unsigned_abs());
    let rn = num / g as i128;
    let rd = den / g as i128;
    let (rn, rd) = if rd < 0 { (-rn, -rd) } else { (rn, rd) };
    if let (Ok(n), Ok(d)) = (i64::try_from(rn), i64::try_from(rd)) {
        Some(Rational::Small(n, d))
    } else {
        None
    }
}

impl Sub for Rational {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        if let (Self::Small(n1, d1), Self::Small(n2, d2)) = (&self, &rhs) {
            if let Some(r) = try_sub_small(*n1, *d1, *n2, *d2) {
                return r;
            }
        }
        self + (-rhs)
    }
}

impl Sub for &Rational {
    type Output = Rational;
    #[inline]
    fn sub(self, rhs: &Rational) -> Rational {
        if let (Rational::Small(n1, d1), Rational::Small(n2, d2)) = (self, rhs) {
            if let Some(r) = try_sub_small(*n1, *d1, *n2, *d2) {
                return r;
            }
        }
        Rational::from_big(self.to_big() - rhs.to_big())
    }
}

impl SubAssign for Rational {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        if rhs.is_zero() {
            return;
        }
        *self = std::mem::take(self) - rhs;
    }
}

impl SubAssign<&Self> for Rational {
    #[inline]
    fn sub_assign(&mut self, rhs: &Self) {
        if rhs.is_zero() {
            return;
        }
        *self = &*self - rhs;
    }
}

// ─── Mul ────────────────────────────────────────────────────────────────────

/// Try small multiplication: (a/b) * (c/d) = (a*c) / (b*d)
/// Pre-reduce to avoid overflow: gcd(a,d) and gcd(c,b).
/// #8782: Falls back to i128 when i64 checked_mul overflows.
#[inline]
fn try_mul_small(n1: i64, d1: i64, n2: i64, d2: i64) -> Option<Rational> {
    let g1 = gcd_u64(n1.unsigned_abs(), d2.unsigned_abs());
    let g2 = gcd_u64(n2.unsigned_abs(), d1.unsigned_abs());
    let n1r = n1 / g1 as i64;
    let d2r = d2 / g1 as i64;
    let n2r = n2 / g2 as i64;
    let d1r = d1 / g2 as i64;
    if let (Some(num), Some(den)) = (n1r.checked_mul(n2r), d1r.checked_mul(d2r)) {
        return normalize_small(num, den).map(|(n, d)| Rational::Small(n, d));
    }
    // i64 overflow after pre-reduction: try i128 with GCD reduction
    let num128 = i128::from(n1r) * i128::from(n2r);
    let den128 = i128::from(d1r) * i128::from(d2r);
    if den128 == 0 {
        return None;
    }
    let g = gcd_u128(num128.unsigned_abs(), den128.unsigned_abs());
    let rn = num128 / g as i128;
    let rd = den128 / g as i128;
    let (rn, rd) = if rd < 0 { (-rn, -rd) } else { (rn, rd) };
    if let (Ok(n), Ok(d)) = (i64::try_from(rn), i64::try_from(rd)) {
        Some(Rational::Small(n, d))
    } else {
        None
    }
}

impl Mul for Rational {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        if let (Self::Small(n1, d1), Self::Small(n2, d2)) = (&self, &rhs) {
            if let Some(r) = try_mul_small(*n1, *d1, *n2, *d2) {
                return r;
            }
        }
        Self::from_big(self.to_big() * rhs.to_big())
    }
}

impl Mul for &Rational {
    type Output = Rational;
    #[inline]
    fn mul(self, rhs: &Rational) -> Rational {
        // #7973: Fast-path for zero and ±1 (common in implied bounds).
        if self.is_zero() || rhs.is_zero() {
            return Rational::zero();
        }
        if matches!(self, Rational::Small(1, 1)) {
            return rhs.clone();
        }
        if matches!(self, Rational::Small(-1, 1)) {
            return -rhs;
        }
        if matches!(rhs, Rational::Small(1, 1)) {
            return self.clone();
        }
        if matches!(rhs, Rational::Small(-1, 1)) {
            return -self;
        }
        if let (Rational::Small(n1, d1), Rational::Small(n2, d2)) = (self, rhs) {
            if let Some(r) = try_mul_small(*n1, *d1, *n2, *d2) {
                return r;
            }
        }
        Rational::from_big(self.to_big() * rhs.to_big())
    }
}

impl Mul<&Self> for Rational {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: &Self) -> Self {
        (&self).mul(rhs)
    }
}

impl MulAssign for Rational {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = std::mem::take(self) * rhs;
    }
}

impl MulAssign<&Self> for Rational {
    #[inline]
    fn mul_assign(&mut self, rhs: &Self) {
        *self = &*self * rhs;
    }
}

// ─── Div ────────────────────────────────────────────────────────────────────

impl Div for Rational {
    type Output = Self;
    #[inline]
    fn div(self, rhs: Self) -> Self {
        assert!(!rhs.is_zero(), "Rational: division by zero");
        // #7973: Fast-path for divisor = ±1.
        if let Self::Small(n2, 1) = &rhs {
            if *n2 == 1 {
                return self;
            }
            if *n2 == -1 {
                return -self;
            }
        }
        if let (Self::Small(n1, d1), Self::Small(n2, d2)) = (&self, &rhs) {
            if let Some(r) = try_mul_small(*n1, *d1, *d2, *n2) {
                return r;
            }
        }
        Self::from_big(self.to_big() / rhs.to_big())
    }
}

impl Div for &Rational {
    type Output = Rational;
    #[inline]
    fn div(self, rhs: &Rational) -> Rational {
        assert!(!rhs.is_zero(), "Rational: division by zero");
        // #7973: Fast-path for divisor = ±1 (common in implied bounds for basic
        // variable coefficient). Avoids all arithmetic including BigRational GCD.
        if let Rational::Small(n2, 1) = rhs {
            if *n2 == 1 {
                return self.clone();
            }
            if *n2 == -1 {
                return -self;
            }
        }
        if let (Rational::Small(n1, d1), Rational::Small(n2, d2)) = (self, rhs) {
            // a/b / c/d = a/b * d/c = (a*d) / (b*c)
            if let Some(r) = try_mul_small(*n1, *d1, *d2, *n2) {
                return r;
            }
        }
        Rational::from_big(self.to_big() / rhs.to_big())
    }
}

impl DivAssign for Rational {
    #[inline]
    fn div_assign(&mut self, rhs: Self) {
        *self = std::mem::take(self) / rhs;
    }
}

impl DivAssign<&Self> for Rational {
    #[inline]
    fn div_assign(&mut self, rhs: &Self) {
        *self = &*self / rhs;
    }
}

// ─── Neg ────────────────────────────────────────────────────────────────────

impl Neg for Rational {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        match self {
            Self::Small(0, _) => Self::Small(0, 1),
            Self::Small(n, d) => {
                if let Some(neg_n) = n.checked_neg() {
                    Self::Small(neg_n, d)
                } else {
                    Self::from_big(-self.to_big())
                }
            }
            Self::Big(br) => Self::from_big(-*br),
        }
    }
}

impl Neg for &Rational {
    type Output = Rational;
    #[inline]
    fn neg(self) -> Rational {
        match self {
            Rational::Small(0, _) => Rational::Small(0, 1),
            Rational::Small(n, d) => {
                if let Some(neg_n) = n.checked_neg() {
                    Rational::Small(neg_n, *d)
                } else {
                    Rational::from_big(-self.to_big())
                }
            }
            Rational::Big(br) => Rational::from_big(-(**br).clone()),
        }
    }
}

// ─── BigRational interop ────────────────────────────────────────────────────
//
// These enable `implied_bounds` (Vec<(Option<Rational>, Option<Rational>)>)
// to be compared against BigRational values from Bound.value and AtomRef.bound_value
// without converting the Rational to BigRational first (#4919).

use num_rational::BigRational;
use std::cmp::Ordering;

impl Rational {
    /// Multiply by a BigRational, returning Rational (shrinks result if possible).
    #[inline]
    pub fn mul_big_to_rational(&self, other: &BigRational) -> Self {
        Self::from_big(self.mul_bigrational(other))
    }
}

/// Cross-type multiply: `&BigRational * &Rational` → `BigRational`.
/// Used in farkas/gomory/optimization code after Bound.value migration to Rational.
impl Mul<&Rational> for &BigRational {
    type Output = BigRational;
    #[inline]
    fn mul(self, rhs: &Rational) -> BigRational {
        self * &rhs.to_big()
    }
}

/// Cross-type subtract: `Rational - &BigRational` → `Rational`.
impl Sub<&BigRational> for Rational {
    type Output = Rational;
    #[inline]
    fn sub(self, rhs: &BigRational) -> Rational {
        Rational::from(self.to_big() - rhs)
    }
}

/// Cross-type add: `Rational + &BigRational` → `Rational`.
impl Add<&BigRational> for Rational {
    type Output = Rational;
    #[inline]
    fn add(self, rhs: &BigRational) -> Rational {
        Rational::from(self.to_big() + rhs)
    }
}

/// Cross-type subtract: `BigRational - &Rational` → `BigRational`.
impl Sub<&Rational> for BigRational {
    type Output = BigRational;
    #[inline]
    fn sub(self, rhs: &Rational) -> BigRational {
        self - &rhs.to_big()
    }
}

/// Cross-type subtract: `&BigRational - &Rational` → `BigRational`.
impl Sub<&Rational> for &BigRational {
    type Output = BigRational;
    #[inline]
    fn sub(self, rhs: &Rational) -> BigRational {
        self - &rhs.to_big()
    }
}

/// Cross-type add: `BigRational + &Rational` → `BigRational`.
impl Add<&Rational> for BigRational {
    type Output = BigRational;
    #[inline]
    fn add(self, rhs: &Rational) -> BigRational {
        self + &rhs.to_big()
    }
}

/// PartialEq with BigRational for comparison in compute_bound_propagations.
impl PartialEq<BigRational> for Rational {
    #[inline]
    fn eq(&self, other: &BigRational) -> bool {
        match self {
            Self::Small(n, d) => {
                // Compare without allocating: n/d == p/q iff n*q == p*d
                if let (Ok(p), Ok(q)) = (i64::try_from(other.numer()), i64::try_from(other.denom()))
                {
                    i128::from(*n) * i128::from(q) == i128::from(p) * i128::from(*d)
                } else {
                    self.to_big() == *other
                }
            }
            Self::Big(br) => **br == *other,
        }
    }
}

/// PartialOrd with BigRational for comparison in compute_bound_propagations.
impl PartialOrd<BigRational> for Rational {
    #[inline]
    fn partial_cmp(&self, other: &BigRational) -> Option<Ordering> {
        match self {
            Self::Small(n, d) => {
                if let (Ok(p), Ok(q)) = (i64::try_from(other.numer()), i64::try_from(other.denom()))
                {
                    let lhs = i128::from(*n) * i128::from(q);
                    let rhs = i128::from(p) * i128::from(*d);
                    Some(lhs.cmp(&rhs))
                } else {
                    Some(self.to_big().cmp(other))
                }
            }
            Self::Big(br) => Some((**br).cmp(other)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Verify that `add_product` produces identical results to separate mul+add.
    #[test]
    fn test_add_product_matches_separate_ops() {
        let cases: Vec<(Rational, Rational, Rational)> = vec![
            // Simple integers
            (Rational::from(10i64), Rational::from(3i64), Rational::from(7i64)),
            // Fractions
            (Rational::new(1, 3), Rational::new(2, 5), Rational::new(7, 11)),
            // Negative coefficients (common in implied bounds: eq_c = -coeff)
            (Rational::from(100i64), Rational::new(-3, 7), Rational::new(50, 3)),
            // Zero accumulator
            (Rational::zero(), Rational::new(999, 1000), Rational::new(1001, 1000)),
            // Large values near i64 overflow
            (
                Rational::from(i64::MAX / 2),
                Rational::from(2i64),
                Rational::from(i64::MAX / 4),
            ),
            // Product that would overflow i64 but fits in i128
            (
                Rational::from(1_000_000_000i64),
                Rational::from(3_000_000_000i64),
                Rational::from(4_000_000_000i64),
            ),
        ];

        for (acc_init, a, b) in &cases {
            // Fused path
            let mut acc_fused = acc_init.clone();
            let product_fused = acc_fused.add_product(a, b);

            // Separate path
            let product_separate = a * b;
            let mut acc_separate = acc_init.clone();
            acc_separate += &product_separate;

            assert_eq!(
                acc_fused, acc_separate,
                "add_product mismatch for acc={acc_init:?}, a={a:?}, b={b:?}: \
                 fused={acc_fused:?} vs separate={acc_separate:?}"
            );
            assert_eq!(
                product_fused, product_separate,
                "product mismatch for a={a:?}, b={b:?}: \
                 fused={product_fused:?} vs separate={product_separate:?}"
            );
        }
    }

    /// Verify add_product with accumulation of many terms (simulates row bound computation).
    #[test]
    fn test_add_product_accumulation() {
        // Simulate: total = sum(coeff_i * bound_i) for 20 terms
        let coeffs: Vec<Rational> = (1..=20).map(|i| Rational::new(i, i + 1)).collect();
        let bounds: Vec<Rational> = (1..=20).map(|i| Rational::new(i * 3, i * 2 + 1)).collect();

        let mut total_fused = Rational::zero();
        let mut total_separate = Rational::zero();

        for (c, b) in coeffs.iter().zip(bounds.iter()) {
            total_fused.add_product(c, b);

            let product = c * b;
            total_separate += &product;
        }

        assert_eq!(
            total_fused, total_separate,
            "Accumulated totals differ: fused={total_fused:?} vs separate={total_separate:?}"
        );
        // Both should stay in Small representation for these values
        assert!(
            total_fused.is_small(),
            "Expected Small representation, got Big"
        );
    }
}
