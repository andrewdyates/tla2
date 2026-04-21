// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interpolation helpers, expression utilities, and ITE splitting.

use rustc_hash::FxHashMap;

mod case_split;
mod constant_detection;
mod interpolation;
mod invariants_affine;
mod invariants_diff;
mod invariants_scaled_diff;
mod invariants_sum;
mod ite_blocking;
mod linear_decomposition;
mod sampling;
mod sum_preservation;
mod utils;

pub(super) fn model_key(values: &FxHashMap<String, i64>) -> String {
    let mut pairs: Vec<(&String, &i64)> = values.iter().collect();
    pairs.sort_by(|(a, _), (b, _)| a.cmp(b));
    let mut s = String::new();
    for (name, value) in pairs {
        s.push_str(name);
        s.push('=');
        s.push_str(&value.to_string());
        s.push(';');
    }
    s
}

#[cfg(test)]
mod tests;
