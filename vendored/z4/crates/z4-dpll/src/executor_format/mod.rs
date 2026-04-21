// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Formatting helpers for SMT-LIB output.
//!
//! These helpers are shared between the `Executor` and combined theory solvers
//! for rendering numeric model values and sorts.

use num_rational::BigRational;
use z4_core::term::Symbol;
use z4_core::{quote_symbol, Sort, TermStore};

/// Format a `Sort` as an SMT-LIB sort string.
pub(crate) fn format_sort(sort: &Sort) -> String {
    match sort {
        Sort::Bool => "Bool".to_string(),
        Sort::Int => "Int".to_string(),
        Sort::Real => "Real".to_string(),
        Sort::String => "String".to_string(),
        Sort::RegLan => "RegLan".to_string(),
        Sort::BitVec(bv) => format!("(_ BitVec {})", bv.width),
        Sort::FloatingPoint(eb, sb) => format!("(_ FloatingPoint {eb} {sb})"),
        Sort::Array(arr) => format!(
            "(Array {} {})",
            format_sort(&arr.index_sort),
            format_sort(&arr.element_sort)
        ),
        Sort::Uninterpreted(name) => quote_symbol(name),
        Sort::Datatype(dt) => quote_symbol(&dt.name),
        Sort::Seq(elem) => format!("(Seq {})", format_sort(elem)),
        // All current Sort variants handled above (#5692).
        // Wildcard covers future variants from #[non_exhaustive].
        other => unreachable!("unhandled Sort variant in format_sort(): {other:?}"),
    }
}

/// Format a `Symbol` (function/constant name) for SMT-LIB output.
pub(crate) fn format_symbol(sym: &Symbol) -> String {
    match sym {
        Symbol::Named(name) => quote_symbol(name),
        Symbol::Indexed(name, indices) => {
            let indices_str: Vec<String> = indices.iter().map(ToString::to_string).collect();
            format!("(_ {} {})", quote_symbol(name), indices_str.join(" "))
        }
        // All current Symbol variants handled above (#5692).
        // Wildcard covers future variants from #[non_exhaustive].
        other => unreachable!("unhandled Symbol variant in format_symbol(): {other:?}"),
    }
}

/// Format a model atom for SMT-LIB output.
pub(crate) fn format_model_atom(sort: &Sort, value: &str) -> String {
    match sort {
        Sort::Uninterpreted(_) | Sort::Datatype(_) => quote_symbol(value),
        _ => value.to_string(),
    }
}

/// Format a value for SMT-LIB output based on sort.
pub(crate) fn format_value(sort: &Sort, value: Option<bool>, _terms: &TermStore) -> String {
    match sort {
        Sort::Bool => match value {
            Some(true) => "true".to_string(),
            Some(false) => "false".to_string(),
            None => "false".to_string(), // Default to false for unassigned
        },
        Sort::Int => {
            // For Int, we'd need to look up the actual value from the model
            // For now, return a placeholder since we only have Boolean model
            "0".to_string()
        }
        Sort::Real => "0.0".to_string(),
        Sort::String => "\"\"".to_string(),
        Sort::RegLan => "re.none".to_string(),
        Sort::BitVec(w) => format_bitvec(&num_bigint::BigInt::from(0), w.width),
        Sort::FloatingPoint(eb, sb) => format!("(_ +zero {eb} {sb})"),
        Sort::Array(arr) => {
            // Return a constant array
            format!(
                "((as const {}) {})",
                format_sort(sort),
                format_value(&arr.element_sort, None, _terms)
            )
        }
        Sort::Uninterpreted(name) => {
            // For uninterpreted sorts, return a fresh element identifier
            format_model_atom(sort, &format!("@{name}!0"))
        }
        Sort::Datatype(dt) => {
            // For datatype sorts, return a fresh element identifier
            format_model_atom(sort, &format!("@{}!0", dt.name))
        }
        Sort::Seq(_) => {
            // Empty sequence with correct element sort
            format!("(as seq.empty {})", format_sort(sort))
        }
        // All current Sort variants handled above (#5692).
        other => unreachable!("unhandled Sort variant in format_value(): {other:?}"),
    }
}

/// Format a default value for a sort (used for array elements).
pub(crate) fn format_default_value(sort: &Sort) -> String {
    match sort {
        Sort::Bool => "false".to_string(),
        Sort::Int => "0".to_string(),
        Sort::Real => "0.0".to_string(),
        Sort::String => "\"\"".to_string(),
        Sort::RegLan => "re.none".to_string(),
        Sort::BitVec(w) => format_bitvec(&num_bigint::BigInt::from(0), w.width),
        Sort::FloatingPoint(eb, sb) => format!("(_ +zero {eb} {sb})"),
        Sort::Array(arr) => {
            // Recursive: const-array of default element value
            format!(
                "((as const {}) {})",
                format_sort(sort),
                format_default_value(&arr.element_sort)
            )
        }
        Sort::Uninterpreted(name) => format_model_atom(sort, &format!("@{name}!0")),
        Sort::Datatype(dt) => format_model_atom(sort, &format!("@{}!0", dt.name)),
        Sort::Seq(_) => format!("(as seq.empty {})", format_sort(sort)),
        // All current Sort variants handled above (#5692).
        other => unreachable!("unhandled Sort variant in format_default_value(): {other:?}"),
    }
}

/// Format a `BigRational` as an SMT-LIB Real value.
pub(crate) fn format_rational(val: &BigRational) -> String {
    if val.is_integer() {
        // Integer value: format as decimal
        let numer = val.numer();
        if numer.sign() == num_bigint::Sign::Minus {
            format!("(- {}.0)", numer.magnitude())
        } else {
            format!("{numer}.0")
        }
    } else {
        // Fractional value: format as (/ num denom)
        let numer = val.numer();
        let denom = val.denom();
        if numer.sign() == num_bigint::Sign::Minus {
            format!("(- (/ {} {}))", numer.magnitude(), denom)
        } else {
            format!("(/ {numer} {denom})")
        }
    }
}

/// Format a `BigInt` as an SMT-LIB Int value.
pub(crate) fn format_bigint(val: &num_bigint::BigInt) -> String {
    use num_bigint::Sign;

    match val.sign() {
        Sign::Minus => format!("(- {})", val.magnitude()),
        Sign::NoSign | Sign::Plus => val.to_string(),
    }
}

/// Format a `BigInt` as an SMT-LIB BitVec literal.
///
/// SMT-LIB hex literals (#x...) are always 4*k bits wide, so we use:
/// - `#x...` for widths divisible by 4
/// - `#b...` for small widths (<=64 bits, not divisible by 4)
/// - `(_ bv<value> <width>)` for large widths not divisible by 4
///
/// (#1793)
pub(crate) fn format_bitvec(val: &num_bigint::BigInt, width: u32) -> String {
    use num_traits::ToPrimitive;

    // Compute mask for the given width
    let mask = if width >= 64 {
        num_bigint::BigInt::from(1) << width
    } else {
        num_bigint::BigInt::from(1u64 << width)
    };

    // Apply mask to get unsigned value
    let unsigned_val: num_bigint::BigInt = val & (&mask - 1);

    // Use hex only when width is divisible by 4
    if width.is_multiple_of(4) {
        let hex_digits = (width / 4) as usize;
        let hex_str = format!("{unsigned_val:x}");
        let padded = format!("{hex_str:0>hex_digits$}");
        return format!("#x{padded}");
    }

    // For small non-divisible-by-4 widths, use binary format
    if width <= 64 {
        let v = unsigned_val.to_u64().unwrap_or(0);
        return format!("#b{:0width$b}", v, width = width as usize);
    }

    // For large non-divisible-by-4 widths, use indexed bv format
    format!("(_ bv{unsigned_val} {width})")
}

#[cfg(test)]
mod tests;
