// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT model-value parsing helpers.

use super::types::SmtValue;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;
use z4_core::Sort;

fn parse_symbolic_model_value(s: &str) -> Option<SmtValue> {
    let trimmed = s.trim();
    if trimmed
        .strip_prefix("@arr")
        .is_some_and(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()))
    {
        return Some(SmtValue::Opaque(trimmed.to_owned()));
    }

    trimmed
        .rsplit_once("_(")
        .filter(|(name, suffix)| !name.is_empty() && !suffix.is_empty() && trimmed.ends_with(')'))
        .map(|(name, _)| SmtValue::Opaque(name.to_owned()))
}

/// Parse a string model value into an `SmtValue` based on the expected sort.
///
/// Returns `None` on parse failure with a warning logged to stderr.
/// Callers should fall back to `default_smt_value` on `None`.
pub(super) fn parse_smt_value_str(s: &str, sort: &Sort) -> Option<SmtValue> {
    let trimmed = s.trim();
    match sort {
        Sort::Bool => match trimmed {
            "true" => Some(SmtValue::Bool(true)),
            "false" => Some(SmtValue::Bool(false)),
            _ => parse_symbolic_model_value(trimmed).or_else(|| {
                safe_eprintln!(
                    "[CHC-SMT] WARNING: parse_smt_value_str: \
                     unparseable Bool: {s:?}"
                );
                None
            }),
        },
        Sort::Int => {
            if let Ok(v) = trimmed.parse::<i64>() {
                Some(SmtValue::Int(v))
            } else if let Some(inner) = trimmed
                .strip_prefix("(- ")
                .and_then(|s| s.strip_suffix(')'))
            {
                if let Ok(v) = inner.trim().parse::<i64>() {
                    Some(SmtValue::Int(-v))
                } else if let Some(symbol) = parse_symbolic_model_value(trimmed) {
                    Some(symbol)
                } else {
                    safe_eprintln!(
                        "[CHC-SMT] WARNING: parse_smt_value_str: \
                         unparseable negative Int: {s:?}"
                    );
                    None
                }
            } else if let Some(symbol) = parse_symbolic_model_value(trimmed) {
                Some(symbol)
            } else {
                safe_eprintln!(
                    "[CHC-SMT] WARNING: parse_smt_value_str: \
                     unparseable Int: {s:?}"
                );
                None
            }
        }
        Sort::BitVec(bvs) => {
            // Wide BV (>128-bit) values are truncated to low 128 bits because
            // SmtValue::BitVec stores u128. The internal solver decomposes wide
            // BV into ≤128-bit chunks, so this truncation only affects executor
            // fallback model values and is semantically harmless (#7040).
            let val = if let Some(hex) = trimmed.strip_prefix("#x") {
                if hex.len() > 32 {
                    let low = &hex[hex.len() - 32..];
                    u128::from_str_radix(low, 16).unwrap_or(0)
                } else {
                    match u128::from_str_radix(hex, 16) {
                        Ok(v) => v,
                        Err(_) => {
                            safe_eprintln!(
                                "[CHC-SMT] WARNING: parse_smt_value_str: \
                                 unparseable BV hex: {s:?}"
                            );
                            return None;
                        }
                    }
                }
            } else if let Some(bin) = trimmed.strip_prefix("#b") {
                if bin.len() > 128 {
                    let low = &bin[bin.len() - 128..];
                    u128::from_str_radix(low, 2).unwrap_or(0)
                } else {
                    match u128::from_str_radix(bin, 2) {
                        Ok(v) => v,
                        Err(_) => {
                            safe_eprintln!(
                                "[CHC-SMT] WARNING: parse_smt_value_str: \
                                 unparseable BV binary: {s:?}"
                            );
                            return None;
                        }
                    }
                }
            } else {
                match trimmed.parse::<u128>() {
                    Ok(v) => v,
                    Err(_) => {
                        return parse_symbolic_model_value(trimmed).or_else(|| {
                            safe_eprintln!(
                                "[CHC-SMT] WARNING: parse_smt_value_str: \
                                 unparseable BV decimal: {s:?}"
                            );
                            None
                        });
                    }
                }
            };
            Some(SmtValue::BitVec(val, bvs.width))
        }
        Sort::Real => parse_real_value(trimmed)
            .or_else(|| parse_symbolic_model_value(trimmed))
            .or_else(|| {
                safe_eprintln!(
                    "[CHC-SMT] WARNING: parse_smt_value_str: \
                     unparseable Real: {s:?}"
                );
                None
            }),
        _ => {
            safe_eprintln!(
                "[CHC-SMT] WARNING: parse_smt_value_str: \
                 unsupported sort {sort:?} for value {s:?}"
            );
            None
        }
    }
}

/// Parse an SMT-LIB Real value string into an `SmtValue::Real`.
///
/// Handles integer literals, decimals, `(- N)`, `(/ N D)`, and `(- (/ N D))`.
fn parse_real_value(s: &str) -> Option<SmtValue> {
    let trimmed = s.trim();

    if let Some(inner) = trimmed
        .strip_prefix("(- ")
        .and_then(|s| s.strip_suffix(')'))
    {
        return parse_real_value(inner.trim()).map(|v| match v {
            SmtValue::Real(r) => SmtValue::Real(-r),
            other => other,
        });
    }

    if let Some(inner) = trimmed.strip_prefix('-') {
        return parse_real_value(inner.trim()).map(|v| match v {
            SmtValue::Real(r) => SmtValue::Real(-r),
            other => other,
        });
    }

    if let Some(inner) = trimmed
        .strip_prefix("(/ ")
        .and_then(|s| s.strip_suffix(')'))
    {
        let parts: Vec<&str> = inner.trim().splitn(2, ' ').collect();
        if parts.len() == 2 {
            if let (Ok(n), Ok(d)) = (
                parts[0].trim().parse::<BigInt>(),
                parts[1].trim().parse::<BigInt>(),
            ) {
                if !d.is_zero() {
                    return Some(SmtValue::Real(BigRational::new(n, d)));
                }
            }
        }
        safe_eprintln!(
            "[CHC-SMT] WARNING: parse_real_value: \
             unparseable rational: {s:?}"
        );
        return None;
    }

    if let Some(dot_pos) = trimmed.find('.') {
        let int_part = &trimmed[..dot_pos];
        let frac_part = &trimmed[dot_pos + 1..];
        let denom = BigInt::from(10i64).pow(frac_part.len() as u32);
        if let (Ok(ip), Ok(fp)) = (int_part.parse::<BigInt>(), frac_part.parse::<BigInt>()) {
            let numer = ip * &denom + fp;
            return Some(SmtValue::Real(BigRational::new(numer, denom)));
        }
    }

    if let Ok(v) = trimmed.parse::<i64>() {
        return Some(SmtValue::Real(BigRational::from_integer(BigInt::from(v))));
    }

    safe_eprintln!(
        "[CHC-SMT] WARNING: parse_real_value: \
         unparseable Real: {s:?}"
    );
    None
}

/// Provide a default `SmtValue` for a given sort.
pub(super) fn default_smt_value(sort: &Sort) -> SmtValue {
    match sort {
        Sort::Bool => SmtValue::Bool(false),
        Sort::Int => SmtValue::Int(0),
        Sort::BitVec(bvs) => SmtValue::BitVec(0, bvs.width),
        Sort::Real => SmtValue::Real(BigRational::from_integer(BigInt::from(0i64))),
        _ => SmtValue::Int(0),
    }
}

#[cfg(test)]
#[path = "value_parse_tests.rs"]
mod tests;
