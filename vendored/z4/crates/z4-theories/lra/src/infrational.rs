// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Infinitesimal-extended rational numbers for strict bound handling.
//!
//! Implements the `x + y*ε` representation from Dutertre & de Moura (CAV 2006).
//! Strict inequality `v > c` becomes non-strict `v >= (c, +1)`, eliminating
//! simplex cycling from degenerate strict bounds.
//!
//! Uses `Rational` (i64/i64 fast path) internally instead of `BigRational`
//! to avoid heap allocation in the common case.

use crate::rational::Rational;
use crate::types::BoundType;
use num_rational::BigRational;
use num_traits::Zero;
use std::cmp::Ordering;

/// Infinitesimal-extended rational: x + y*ε
///
/// Ordered lexicographically: `(x1, y1) < (x2, y2)` iff `x1 < x2` or
/// `(x1 == x2 && y1 < y2)`. This captures the semantics of ε being
/// infinitesimally small but positive.
#[derive(Clone, Default)]
pub(crate) struct InfRational {
    x: Rational,
    y: Rational,
}

impl InfRational {
    /// Backward-compatible constructor from BigRational values.
    pub(crate) fn new(x: BigRational, y: BigRational) -> Self {
        Self {
            x: Rational::from(x),
            y: Rational::from(y),
        }
    }
    /// Backward-compatible: construct from BigRational (epsilon = 0).
    pub(crate) fn from_rational(x: BigRational) -> Self {
        Self {
            x: Rational::from(x),
            y: Rational::zero(),
        }
    }
    /// Construct from Rational without BigRational allocation.
    #[inline]
    pub(crate) fn from_rat(x: Rational) -> Self {
        Self {
            x,
            y: Rational::zero(),
        }
    }
    /// Construct from Rational with epsilon component.
    #[inline]
    pub(crate) fn new_rat(x: Rational, y: Rational) -> Self {
        Self { x, y }
    }
    /// Backward-compatible: get rational part as BigRational (allocates).
    pub(crate) fn rational(&self) -> BigRational {
        self.x.to_big()
    }
    /// Backward-compatible: get epsilon as BigRational (allocates).
    pub(crate) fn epsilon(&self) -> BigRational {
        self.y.to_big()
    }
    pub(crate) fn is_zero(&self) -> bool {
        self.x.is_zero() && self.y.is_zero()
    }
    pub(crate) fn is_integer(&self) -> bool {
        self.y.is_zero() && self.x.is_integer()
    }
    /// Multiply by a Rational coefficient (hot-path version).
    #[inline]
    pub(crate) fn mul_rat(&self, c: &Rational) -> Self {
        // Fast path: when epsilon component is zero (common for non-strict bounds),
        // skip the second multiply entirely.
        if self.y.is_zero() {
            Self {
                x: &self.x * c,
                y: Rational::zero(),
            }
        } else {
            Self {
                x: &self.x * c,
                y: &self.y * c,
            }
        }
    }
    /// Backward-compatible: multiply by BigRational coefficient.
    pub(crate) fn mul_rational(&self, c: &BigRational) -> Self {
        let c_rat = Rational::from(c.clone());
        self.mul_rat(&c_rat)
    }
    /// Materialize to concrete Rational: `x + y*δ`
    pub(crate) fn materialize_rat(&self, delta: &Rational) -> Rational {
        if self.y.is_zero() {
            self.x.clone()
        } else {
            &self.x + &(&self.y * delta)
        }
    }
    /// Backward-compatible: materialize to BigRational.
    pub(crate) fn materialize(&self, delta: &BigRational) -> BigRational {
        let delta_rat = Rational::from(delta.clone());
        self.materialize_rat(&delta_rat).to_big()
    }

    /// Compare `self` against a bound without allocating an `InfRational`.
    ///
    /// A bound `(value, strict, bound_type)` maps to the InfRational:
    /// - Lower strict:  `(value, +1ε)`
    /// - Upper strict:  `(value, -1ε)`
    /// - Non-strict:    `(value,  0ε)`
    ///
    /// This avoids the heap allocation in `Bound::as_inf()` which clones
    /// `BigRational`. Hot path: called per-variable in `violates_bounds`.
    #[inline]
    pub(crate) fn cmp_bound(
        &self,
        bound_value: &Rational,
        strict: bool,
        bound_type: BoundType,
    ) -> Ordering {
        // First compare the rational parts
        let x_ord = self.x.cmp(bound_value);
        if x_ord != Ordering::Equal {
            return x_ord;
        }
        // Rational parts are equal; compare epsilon parts.
        // Bound epsilon is: strict lower → +1, strict upper → -1, non-strict → 0
        if !strict {
            // Bound epsilon = 0, so compare self.y vs 0
            if self.y.is_positive() {
                Ordering::Greater
            } else if self.y.is_negative() {
                Ordering::Less
            } else {
                Ordering::Equal
            }
        } else {
            // Strict bound: epsilon is +1 (lower) or -1 (upper).
            // These are Small(1,1) and Small(-1,1) — always the fast i128 path.
            match bound_type {
                BoundType::Lower => self.y.cmp(&Rational::Small(1, 1)),
                BoundType::Upper => self.y.cmp(&Rational::Small(-1, 1)),
            }
        }
    }

    /// Check if `self < bound` without allocating.
    #[inline]
    pub(crate) fn lt_bound(
        &self,
        bound_value: &Rational,
        strict: bool,
        bound_type: BoundType,
    ) -> bool {
        self.cmp_bound(bound_value, strict, bound_type) == Ordering::Less
    }

    /// Check if `self > bound` without allocating.
    #[inline]
    pub(crate) fn gt_bound(
        &self,
        bound_value: &Rational,
        strict: bool,
        bound_type: BoundType,
    ) -> bool {
        self.cmp_bound(bound_value, strict, bound_type) == Ordering::Greater
    }

    /// Approximate the rational (x) component as f64, no allocation for Small.
    /// Used for heuristic violation magnitudes in heap key computation.
    #[inline]
    pub(crate) fn x_approx_f64(&self) -> f64 {
        self.x.approx_f64()
    }
}

impl std::fmt::Debug for InfRational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.y.is_zero() {
            write!(f, "{}", self.x)
        } else if self.x.is_zero() {
            write!(f, "{}*e", self.y)
        } else {
            write!(f, "{} + {}*e", self.x, self.y)
        }
    }
}

impl std::fmt::Display for InfRational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

impl PartialEq for InfRational {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl Eq for InfRational {}

impl PartialOrd for InfRational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for InfRational {
    fn cmp(&self, other: &Self) -> Ordering {
        self.x.cmp(&other.x).then_with(|| self.y.cmp(&other.y))
    }
}

impl std::ops::Add for &InfRational {
    type Output = InfRational;
    #[inline]
    fn add(self, rhs: Self) -> InfRational {
        let y = if self.y.is_zero() && rhs.y.is_zero() {
            Rational::zero()
        } else {
            &self.y + &rhs.y
        };
        InfRational {
            x: &self.x + &rhs.x,
            y,
        }
    }
}

impl std::ops::Sub for &InfRational {
    type Output = InfRational;
    #[inline]
    fn sub(self, rhs: Self) -> InfRational {
        let y = if self.y.is_zero() && rhs.y.is_zero() {
            Rational::zero()
        } else {
            &self.y - &rhs.y
        };
        InfRational {
            x: &self.x - &rhs.x,
            y,
        }
    }
}

impl std::ops::Neg for InfRational {
    type Output = Self;
    fn neg(self) -> Self {
        Self {
            x: -self.x,
            y: -self.y,
        }
    }
}

impl std::ops::AddAssign<&Self> for InfRational {
    #[inline]
    fn add_assign(&mut self, rhs: &Self) {
        self.x += &rhs.x;
        // Skip epsilon add when RHS has no epsilon component (common case:
        // non-strict bounds produce zero epsilon in mul_rat results).
        if !rhs.y.is_zero() {
            self.y += &rhs.y;
        }
    }
}

impl std::ops::SubAssign<&Self> for InfRational {
    #[inline]
    fn sub_assign(&mut self, rhs: &Self) {
        self.x -= &rhs.x;
        if !rhs.y.is_zero() {
            self.y -= &rhs.y;
        }
    }
}

impl std::ops::AddAssign<BigRational> for InfRational {
    fn add_assign(&mut self, rhs: BigRational) {
        self.x += &Rational::from(rhs);
    }
}
