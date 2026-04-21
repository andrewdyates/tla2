// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fast rational arithmetic with inline i64/i64 representation.
//!
//! Z3 uses `mpq_inf` (GMP rationals with machine-word fast-path).
//! Z4's LRA simplex spends 76% of time in `BigRational` heap allocation
//! (GCD, reduce, alloc) for coefficients that fit in machine words.
//!
//! This module provides `Rational`: an inline `(i64, i64)` for small values
//! with fallback to `BigRational` for overflow. Benchmarks show QF_LRA
//! problems have coefficients like 1, 2, 3, 15, 30 — all fit in i64.
//!
//! Reference: Z3 `src/util/mpq.h`, OpenSMT2 `src/common/FastRational.h`.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed as _, ToPrimitive as _, Zero};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

/// A rational number optimized for small values.
///
/// Most LRA simplex coefficients fit in 64-bit integers. This type avoids
/// heap allocation for the common case while preserving exact arithmetic
/// via fallback to `BigRational`.
#[derive(Clone)]
pub enum Rational {
    /// Inline representation: numerator / denominator.
    /// Invariants: denom > 0, gcd(|numer|, denom) == 1, denom != 0.
    /// Zero is represented as Small(0, 1).
    Small(i64, i64),
    /// Heap-allocated arbitrary-precision fallback.
    Big(Box<BigRational>),
}

/// Binary GCD for u64 (no allocation, no division).
#[inline]
pub(crate) fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
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

/// Normalize a (numer, denom) pair: positive denom, reduced by GCD.
/// Returns None if overflow would occur during normalization.
#[inline]
pub(crate) fn normalize_small(mut n: i64, mut d: i64) -> Option<(i64, i64)> {
    if d == 0 {
        return None;
    }
    if n == 0 {
        return Some((0, 1));
    }
    if d < 0 {
        n = n.checked_neg()?;
        d = d.checked_neg()?;
    }
    let g = gcd_u64(n.unsigned_abs(), d.unsigned_abs());
    if g > 1 {
        Some((n / g as i64, d / g as i64))
    } else {
        Some((n, d))
    }
}

/// Try to shrink a BigRational back to Small.
fn try_shrink(br: &BigRational) -> Option<Rational> {
    let n: i64 = br.numer().try_into().ok()?;
    let d: i64 = br.denom().try_into().ok()?;
    if d > 0 {
        Some(Rational::Small(n, d))
    } else if d < 0 {
        Some(Rational::Small(n.checked_neg()?, d.checked_neg()?))
    } else {
        None
    }
}

// ─── Construction ───────────────────────────────────────────────────────────

impl Rational {
    /// Create from numerator and denominator. Panics if denom == 0.
    #[inline]
    pub fn new(numer: i64, denom: i64) -> Self {
        assert!(denom != 0, "Rational: zero denominator");
        match normalize_small(numer, denom) {
            Some((n, d)) => Self::Small(n, d),
            None => Self::Big(Box::new(BigRational::new(
                BigInt::from(numer),
                BigInt::from(denom),
            ))),
        }
    }

    /// Wrap a BigRational, shrinking to Small if possible.
    #[inline]
    pub fn from_big(br: BigRational) -> Self {
        try_shrink(&br).unwrap_or_else(|| Self::Big(Box::new(br)))
    }

    /// Convert to BigRational (always succeeds).
    #[inline]
    pub fn to_big(&self) -> BigRational {
        match self {
            Self::Small(n, d) => BigRational::new(BigInt::from(*n), BigInt::from(*d)),
            Self::Big(br) => (**br).clone(),
        }
    }

    /// Compare `self` against a `BigRational` without allocating.
    ///
    /// For `Small(n, d)` vs `p/q`: compares `n*q` vs `p*d` using mixed-precision
    /// integer multiplication (BigInt × i64 → BigInt), which avoids the full
    /// `to_big()` allocation path.
    ///
    /// Hot path: called per-atom in `bound_is_interesting` (#6615).
    #[inline]
    pub fn cmp_big(&self, other: &BigRational) -> Ordering {
        match self {
            Self::Small(n, d) => {
                // n/d vs p/q ⟺ n*q vs p*d  (d > 0, q > 0 by invariant)
                // Fast path: when other also fits in i64, use i128 arithmetic
                // to avoid BigInt allocation entirely. This is the common case
                // since most LRA bound values have small coefficients.
                if let (Ok(p), Ok(q)) =
                    (i64::try_from(other.numer()), i64::try_from(other.denom()))
                {
                    let lhs = i128::from(*n) * i128::from(q);
                    let rhs = i128::from(p) * i128::from(*d);
                    return lhs.cmp(&rhs);
                }
                // Fallback: BigInt multiply when other doesn't fit in i64
                let lhs = other.denom() * *n; // BigInt * i64 → BigInt
                let rhs = other.numer() * *d; // BigInt * i64 → BigInt
                lhs.cmp(&rhs)
            }
            Self::Big(br) => (**br).cmp(other),
        }
    }

    /// Multiply a `&BigRational` by this `Rational`, returning a `BigRational`.
    ///
    /// For `Small(n, d)`, this avoids allocating a temporary `BigRational` for
    /// the coefficient — it directly computes `(n * other.numer) / (d * other.denom)`
    /// via mixed-precision integer multiply, which is cheaper than the full
    /// `to_big()` path (which does BigInt::from + GCD reduction).
    ///
    /// Hot path: called per-coefficient in `check_row_strict_infeasibility` (#4919).
    #[inline]
    pub fn mul_bigrational(&self, other: &BigRational) -> BigRational {
        match self {
            Self::Small(n, d) => {
                // n/d * p/q = (n*p) / (d*q)
                // Since self is already reduced (gcd(|n|,d)==1), and other is
                // reduced, BigRational::new will do one GCD on the product.
                // But we skip the GCD on creating self as BigRational.
                let numer = BigInt::from(*n) * other.numer();
                let denom = BigInt::from(*d) * other.denom();
                BigRational::new(numer, denom)
            }
            Self::Big(br) => &**br * other,
        }
    }

    /// Multiply this `Rational` by a `&BigRational`, returning `Rational`.
    ///
    /// When both operands fit in i64 (Small coeff, small BigRational), the
    /// entire computation stays in i128 → i64 without heap allocation.
    /// Falls back to BigRational multiply + shrink otherwise.
    ///
    /// Hot path: used in `check_row_strict_infeasibility` accumulator (#4919).
    #[inline]
    pub fn mul_bigrational_to_rat(&self, other: &BigRational) -> Self {
        match self {
            Self::Small(n, d) => {
                // Try fast path: if other also fits in i64, do i128 arithmetic
                if let (Ok(p), Ok(q)) = (i64::try_from(other.numer()), i64::try_from(other.denom()))
                {
                    // n/d * p/q — pre-reduce via GCD to minimize overflow
                    let g1 = gcd_u64(n.unsigned_abs(), q.unsigned_abs());
                    let g2 = gcd_u64(p.unsigned_abs(), d.unsigned_abs());
                    let nr = *n / g1 as i64;
                    let qr = q / g1 as i64;
                    let pr = p / g2 as i64;
                    let dr = *d / g2 as i64;
                    if let (Some(num), Some(den)) = (nr.checked_mul(pr), dr.checked_mul(qr)) {
                        if let Some((rn, rd)) = normalize_small(num, den) {
                            return Self::Small(rn, rd);
                        }
                    }
                }
                // Fallback: BigRational multiply + try to shrink
                Self::from_big(self.mul_bigrational(other))
            }
            Self::Big(br) => Self::from_big(&**br * other),
        }
    }

    /// Compute the absolute value of this `Rational`, returning a `BigRational`.
    ///
    /// For `Small(n, d)`, avoids the `to_big()` + `abs()` chain.
    #[inline]
    pub fn abs_bigrational(&self) -> BigRational {
        match self {
            Self::Small(n, d) => BigRational::new(BigInt::from(n.unsigned_abs()), BigInt::from(*d)),
            Self::Big(br) => br.abs(),
        }
    }

    /// Borrow as BigRational (allocates for Small — use sparingly).
    #[inline]
    pub fn as_big(&self) -> std::borrow::Cow<'_, BigRational> {
        match self {
            Self::Small(n, d) => {
                std::borrow::Cow::Owned(BigRational::new(BigInt::from(*n), BigInt::from(*d)))
            }
            Self::Big(br) => std::borrow::Cow::Borrowed(br),
        }
    }

    /// Check if this is the inline representation.
    #[inline]
    pub fn is_small(&self) -> bool {
        matches!(self, Self::Small(_, _))
    }

    /// Extract numerator as BigInt.
    pub fn numer_big(&self) -> BigInt {
        match self {
            Self::Small(n, _) => BigInt::from(*n),
            Self::Big(br) => br.numer().clone(),
        }
    }

    /// Alias for `numer_big()` — compatible with `BigRational::numer()`.
    #[inline]
    pub fn numer(&self) -> BigInt {
        self.numer_big()
    }

    /// Extract denominator as BigInt.
    pub fn denom_big(&self) -> BigInt {
        match self {
            Self::Small(_, d) => BigInt::from(*d),
            Self::Big(br) => br.denom().clone(),
        }
    }

    /// Alias for `denom_big()` — compatible with `BigRational::denom()`.
    #[inline]
    pub fn denom(&self) -> BigInt {
        self.denom_big()
    }

    /// Create from integer value (alias for `From<BigInt>`).
    #[inline]
    pub fn from_integer(n: BigInt) -> Self {
        Self::from(n)
    }

    /// Create from BigInt numerator and denominator.
    pub fn new_big(numer: BigInt, denom: BigInt) -> Self {
        Self::from_big(BigRational::new(numer, denom))
    }

    /// Convert to BigInt by truncation (floor for non-negative, ceil for negative).
    /// Matches `BigRational::to_integer()` semantics.
    pub fn to_integer(&self) -> BigInt {
        match self {
            Self::Small(n, 1) => BigInt::from(*n),
            Self::Small(n, d) => BigInt::from(*n / *d),
            Self::Big(br) => br.to_integer(),
        }
    }
}

// ─── Standard trait impls ───────────────────────────────────────────────────

impl Default for Rational {
    #[inline]
    fn default() -> Self {
        Self::Small(0, 1)
    }
}

impl fmt::Debug for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Small(n, 1) => write!(f, "{n}"),
            Self::Small(n, d) => write!(f, "{n}/{d}"),
            Self::Big(br) => write!(f, "Big({br})"),
        }
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Small(n, 1) => write!(f, "{n}"),
            Self::Small(n, d) => write!(f, "{n}/{d}"),
            Self::Big(br) => write!(f, "{br}"),
        }
    }
}

impl PartialEq for Rational {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Small(n1, d1), Self::Small(n2, d2)) => n1 == n2 && d1 == d2,
            _ => self.to_big() == other.to_big(),
        }
    }
}

impl Eq for Rational {}

impl PartialOrd for Rational {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rational {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::Small(n1, d1), Self::Small(n2, d2)) => {
                // a/b cmp c/d = a*d cmp c*b (b,d > 0, use i128 to avoid overflow)
                let lhs = i128::from(*n1) * i128::from(*d2);
                let rhs = i128::from(*n2) * i128::from(*d1);
                lhs.cmp(&rhs)
            }
            _ => self.to_big().cmp(&other.to_big()),
        }
    }
}

impl Hash for Rational {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Small(n, d) => {
                0u8.hash(state);
                n.hash(state);
                d.hash(state);
            }
            Self::Big(br) => {
                if let Some(Self::Small(n, d)) = try_shrink(br) {
                    0u8.hash(state);
                    n.hash(state);
                    d.hash(state);
                } else {
                    1u8.hash(state);
                    br.numer().hash(state);
                    br.denom().hash(state);
                }
            }
        }
    }
}

// ─── Utility methods ────────────────────────────────────────────────────────

impl Rational {
    /// Absolute value.
    #[inline]
    pub fn abs(&self) -> Self {
        match self {
            Self::Small(n, d) => {
                if *n >= 0 {
                    self.clone()
                } else if let Some(abs_n) = n.checked_neg() {
                    Self::Small(abs_n, *d)
                } else {
                    Self::from_big(self.to_big().abs())
                }
            }
            Self::Big(br) => Self::from_big(br.abs()),
        }
    }

    /// Signum: 1 for positive, 0 for zero, -1 for negative.
    #[inline]
    pub fn signum(&self) -> Self {
        match self.cmp(&Self::zero()) {
            Ordering::Greater => Self::one(),
            Ordering::Equal => Self::zero(),
            Ordering::Less => Self::Small(-1, 1),
        }
    }

    /// True if strictly positive.
    #[inline]
    pub fn is_positive(&self) -> bool {
        match self {
            Self::Small(n, _) => *n > 0,
            Self::Big(br) => num_traits::Signed::is_positive(&**br),
        }
    }

    /// True if strictly negative.
    #[inline]
    pub fn is_negative(&self) -> bool {
        match self {
            Self::Small(n, _) => *n < 0,
            Self::Big(br) => num_traits::Signed::is_negative(&**br),
        }
    }

    /// Check if the rational is an integer (denominator == 1).
    #[inline]
    pub fn is_integer(&self) -> bool {
        match self {
            Self::Small(_, 1) => true,
            Self::Small(_, _) => false,
            Self::Big(br) => br.is_integer(),
        }
    }

    /// Approximate as f64 (no heap allocation for Small variant).
    /// Used for heuristic heap keys where exact arithmetic is not needed.
    #[inline]
    pub fn approx_f64(&self) -> f64 {
        match self {
            Self::Small(n, d) => *n as f64 / *d as f64,
            Self::Big(br) => {
                br.numer().to_f64().unwrap_or(f64::MAX) / br.denom().to_f64().unwrap_or(1.0)
            }
        }
    }

    /// Floor: largest integer <= self.
    pub fn floor(&self) -> BigInt {
        match self {
            Self::Small(n, 1) => BigInt::from(*n),
            Self::Small(n, d) => {
                let q = n / d;
                let r = n % d;
                if r < 0 {
                    BigInt::from(q - 1)
                } else {
                    BigInt::from(q)
                }
            }
            Self::Big(br) => br.floor().to_integer(),
        }
    }

    /// Ceil: smallest integer >= self.
    pub fn ceil(&self) -> BigInt {
        match self {
            Self::Small(n, 1) => BigInt::from(*n),
            Self::Small(n, d) => {
                let q = n / d;
                let r = n % d;
                if r > 0 {
                    BigInt::from(q + 1)
                } else {
                    BigInt::from(q)
                }
            }
            Self::Big(br) => br.ceil().to_integer(),
        }
    }

    /// Reciprocal: 1/self. Panics if zero.
    pub fn recip(&self) -> Self {
        assert!(!self.is_zero(), "Rational: reciprocal of zero");
        match self {
            Self::Small(n, d) => {
                if *n > 0 {
                    Self::Small(*d, *n)
                } else if let (Some(neg_d), Some(neg_n)) = (d.checked_neg(), n.checked_neg()) {
                    Self::Small(neg_d, neg_n)
                } else {
                    Self::from_big(self.to_big().recip())
                }
            }
            Self::Big(br) => Self::from_big(br.recip()),
        }
    }
}

// ─── Conversions ────────────────────────────────────────────────────────────

impl From<i32> for Rational {
    #[inline]
    fn from(n: i32) -> Self {
        Self::Small(i64::from(n), 1)
    }
}

impl From<i64> for Rational {
    #[inline]
    fn from(n: i64) -> Self {
        Self::Small(n, 1)
    }
}

impl From<BigInt> for Rational {
    fn from(n: BigInt) -> Self {
        if let Ok(small) = i64::try_from(&n) {
            Self::Small(small, 1)
        } else {
            Self::Big(Box::new(BigRational::from(n)))
        }
    }
}

impl From<BigRational> for Rational {
    #[inline]
    fn from(br: BigRational) -> Self {
        Self::from_big(br)
    }
}

impl From<&BigRational> for Rational {
    #[inline]
    fn from(br: &BigRational) -> Self {
        Self::from_big(br.clone())
    }
}

// ─── Zero / One ─────────────────────────────────────────────────────────────

impl Zero for Rational {
    #[inline]
    fn zero() -> Self {
        Self::Small(0, 1)
    }
    #[inline]
    fn is_zero(&self) -> bool {
        match self {
            Self::Small(0, _) => true,
            Self::Small(_, _) => false,
            Self::Big(br) => br.is_zero(),
        }
    }
}

impl One for Rational {
    #[inline]
    fn one() -> Self {
        Self::Small(1, 1)
    }
    #[inline]
    fn is_one(&self) -> bool {
        match self {
            Self::Small(1, 1) => true,
            Self::Small(_, _) => false,
            Self::Big(br) => br.is_one(),
        }
    }
}

impl Rational {
    /// Returns true when this rational is exactly `-1`.
    #[inline]
    pub fn is_neg_one(&self) -> bool {
        match self {
            Self::Small(-1, 1) => true,
            Self::Small(_, _) => false,
            Self::Big(br) => br.numer() == &BigInt::from(-1) && br.denom() == &BigInt::from(1),
        }
    }
}

/// Clone-based `From` for `&Rational` → `Rational`.
/// Required by code that does `Rational::from(&bound.value)`.
impl From<&Rational> for Rational {
    #[inline]
    fn from(r: &Rational) -> Self {
        r.clone()
    }
}

// BigRational interop traits (PartialEq, PartialOrd, mul_big_to_rational)
// are in rational_ops.rs to keep this file under 500 lines.
