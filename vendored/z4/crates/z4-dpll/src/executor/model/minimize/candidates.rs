// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Candidate value generation and array minimization for counterexample shrinking.
//!
//! Extracted from `mod.rs` for code health (#5970). Contains the pure
//! functions that generate candidate replacement values for LIA, LRA, and BV
//! variables, plus the structural array interpretation minimizer.

use std::collections::HashMap;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use z4_arrays::ArrayInterpretation;

/// Maximum number of candidate attempts per variable to bound minimization cost.
pub(super) const MAX_CANDIDATES_PER_VAR: usize = 12;

/// Minimize an array interpretation by choosing the optimal default value.
///
/// Strategy: pick the most frequent value among stores as the new default,
/// then remove all stores that match it. If the array has no default, the
/// most frequent store value becomes the default.
///
/// For ties, prefers "zero-like" values (#x0000, 0, "") as default, since
/// these are more readable in counterexamples.
pub(super) fn minimize_array_interpretation(interp: &mut ArrayInterpretation) {
    if interp.stores.is_empty() {
        return;
    }

    // Count occurrences of each value.
    let mut freq: HashMap<&str, usize> = HashMap::new();
    for (_, val) in &interp.stores {
        *freq.entry(val.as_str()).or_insert(0) += 1;
    }

    let current_default = interp.default.as_deref();

    // Find the best candidate default: highest frequency, tie-break by
    // preferring the current default (avoids changing it) or zero-like values.
    let best_val = freq
        .iter()
        .max_by(|(val_a, cnt_a), (val_b, cnt_b)| {
            cnt_a
                .cmp(cnt_b)
                .then_with(|| {
                    // Tie-break: prefer current default (avoids changing it).
                    let a_is_cur = Some(**val_a) == current_default;
                    let b_is_cur = Some(**val_b) == current_default;
                    a_is_cur.cmp(&b_is_cur)
                })
                .then_with(|| {
                    // Tie-break: prefer zero-like values for readability.
                    let a_zero = is_zero_like(val_a);
                    let b_zero = is_zero_like(val_b);
                    a_zero.cmp(&b_zero)
                })
        })
        .map(|(val, _)| (*val).to_owned());

    let new_default = match best_val {
        Some(v) => v,
        None => return,
    };

    // Only change the default if it produces fewer stores.
    let new_default_removes = freq.get(new_default.as_str()).copied().unwrap_or(0);
    let current_default_removes = current_default
        .and_then(|d| freq.get(d))
        .copied()
        .unwrap_or(0);

    if new_default_removes > current_default_removes
        || (interp.default.is_none() && new_default_removes > 0)
    {
        interp.default = Some(new_default);
    }

    // Remove stores where value matches the (possibly new) default.
    if let Some(ref default) = interp.default {
        interp.stores.retain(|(_, val)| val != default);
    }
}

/// Check if a string value looks like zero (for tie-breaking).
pub(super) fn is_zero_like(val: &str) -> bool {
    val == "0"
        || val == "#x00"
        || val == "#x0000"
        || val == "#x00000000"
        || val == "#b0"
        || val == "#b00000000"
        || val
            .chars()
            .all(|c| c == '0' || c == '#' || c == 'x' || c == 'b')
}

/// Generate candidate integer values in preference order: 0, 1, -1, 2, -2, ...
/// For large values (|v| > 4), also includes sign-preserving powers of 10
/// to help find boundary conditions (e.g., x >= 100 with original=847293847
/// would try 0, 1, -1, 2, -2, 3, -3, 4, -4, 10, 100, 1000, ...).
pub(super) fn int_candidates(original: &BigInt) -> Vec<BigInt> {
    if original.is_zero() {
        return vec![BigInt::zero()];
    }

    let mut candidates = Vec::with_capacity(MAX_CANDIDATES_PER_VAR);
    candidates.push(BigInt::zero());
    candidates.push(BigInt::one());
    candidates.push(-BigInt::one());

    for i in 2i64..=4 {
        if candidates.len() >= MAX_CANDIDATES_PER_VAR {
            break;
        }
        candidates.push(BigInt::from(i));
        if candidates.len() < MAX_CANDIDATES_PER_VAR {
            candidates.push(BigInt::from(-i));
        }
    }

    // For large values, add sign-preserving powers of 10 as candidates.
    // This helps find boundary conditions like x >= 100.
    let orig_mag = original.magnitude().clone();
    if orig_mag > num_bigint::BigUint::from(4u32) {
        let sign = if original.is_positive() { 1i64 } else { -1i64 };
        let mut power = BigInt::from(10i64);
        while candidates.len() < MAX_CANDIDATES_PER_VAR {
            let candidate = &power * sign;
            if candidate.magnitude() >= &orig_mag {
                break;
            }
            if !candidates.contains(&candidate) {
                candidates.push(candidate);
            }
            power *= 10i64;
        }
    }

    candidates.retain(|c| c.magnitude() <= &orig_mag);

    candidates
}

/// Generate candidate rational values in preference order.
pub(super) fn rational_candidates(original: &BigRational) -> Vec<BigRational> {
    if original.is_zero() {
        return vec![BigRational::zero()];
    }

    let mut candidates = Vec::with_capacity(MAX_CANDIDATES_PER_VAR);
    candidates.push(BigRational::zero());
    candidates.push(BigRational::one());
    candidates.push(-BigRational::one());

    let half = BigRational::new(BigInt::one(), BigInt::from(2));
    candidates.push(half.clone());
    candidates.push(-half);

    for i in 2i64..=3 {
        if candidates.len() >= MAX_CANDIDATES_PER_VAR {
            break;
        }
        candidates.push(BigRational::from(BigInt::from(i)));
        if candidates.len() < MAX_CANDIDATES_PER_VAR {
            candidates.push(BigRational::from(BigInt::from(-i)));
        }
    }

    let orig_abs = original.abs();
    candidates.retain(|c| c.abs() <= orig_abs);

    candidates
}

/// Generate candidate bitvector values: 0, 1, MAX, MIN_SIGNED, powers of 2.
pub(super) fn bv_candidates(original: &BigInt, width: u32) -> Vec<BigInt> {
    if original.is_zero() {
        return vec![BigInt::zero()];
    }

    let max_unsigned: BigInt = (BigInt::one() << width) - 1;
    let min_signed: BigInt = BigInt::one() << (width - 1);

    let mut candidates = Vec::with_capacity(MAX_CANDIDATES_PER_VAR);
    candidates.push(BigInt::zero());
    candidates.push(BigInt::one());
    candidates.push(max_unsigned.clone());
    candidates.push(min_signed);

    for pow in 1..width.min(8) {
        if candidates.len() >= MAX_CANDIDATES_PER_VAR {
            break;
        }
        let val = BigInt::one() << pow;
        if val <= max_unsigned && !candidates.contains(&val) {
            candidates.push(val);
        }
    }

    candidates.retain(|c| *c >= BigInt::zero() && *c <= max_unsigned);

    candidates
}
