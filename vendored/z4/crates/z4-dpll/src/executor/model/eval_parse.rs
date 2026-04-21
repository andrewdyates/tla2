// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model value parsing and utility functions.
//!
//! Extracted from `mod.rs` to reduce file size (code-health split).
//! All methods are `impl Executor` — they share the same method namespace.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;
use z4_core::Sort;

use super::EvalValue;

use super::Executor;

impl Executor {
    /// Parse a string value from the array model back into an EvalValue.
    pub(super) fn parse_model_value_string(
        &self,
        s: &str,
        element_sort: &Option<Sort>,
    ) -> EvalValue {
        // Try to determine the expected sort
        match element_sort {
            Some(Sort::Int) => {
                // Try parsing as integer
                if let Ok(n) = s.parse::<BigInt>() {
                    return EvalValue::Rational(BigRational::from(n));
                }
                // Try negative integers like "(- 5)"
                let trimmed = s.trim();
                if trimmed.starts_with("(- ") && trimmed.ends_with(')') {
                    if let Ok(n) = trimmed[3..trimmed.len() - 1].trim().parse::<BigInt>() {
                        return EvalValue::Rational(BigRational::from(-n));
                    }
                }
                EvalValue::Unknown
            }
            Some(Sort::Real) => Self::parse_real_string(s),
            Some(Sort::BitVec(bv)) => Self::parse_bitvec_string(s, bv.width),
            Some(Sort::Bool) => match s {
                "true" => EvalValue::Bool(true),
                "false" => EvalValue::Bool(false),
                _ => EvalValue::Unknown,
            },
            Some(Sort::String) => {
                let trimmed = s.trim();
                if trimmed.starts_with('"') && trimmed.ends_with('"') && trimmed.len() >= 2 {
                    EvalValue::String(trimmed[1..trimmed.len() - 1].to_string())
                } else {
                    EvalValue::String(trimmed.to_string())
                }
            }
            Some(Sort::Uninterpreted(_)) | Some(Sort::Datatype(_)) | Some(Sort::Array(_)) => {
                EvalValue::Element(s.trim().to_string())
            }
            _ => {
                // Try integer parse as best-effort
                if let Ok(n) = s.parse::<BigInt>() {
                    return EvalValue::Rational(BigRational::from(n));
                }
                EvalValue::Unknown
            }
        }
    }

    /// Parse an SMT-LIB Real value string into an EvalValue.
    ///
    /// Handles: integer, `(- n)`, `(/ n d)`, `(/ (- n) d)`, `(- (/ n d))`,
    /// and decimal forms like `1.0` or `1.5`.
    pub(super) fn parse_real_string(s: &str) -> EvalValue {
        let trimmed = s.trim();
        // Integer
        if let Ok(n) = trimmed.parse::<BigInt>() {
            return EvalValue::Rational(BigRational::from(n));
        }
        // Decimal like "1.0" or "1.5"
        if let Some(dot_pos) = trimmed.find('.') {
            let int_part = &trimmed[..dot_pos];
            let frac_part = &trimmed[dot_pos + 1..];
            if let (Ok(ip), Ok(fp)) = (int_part.parse::<BigInt>(), frac_part.parse::<BigInt>()) {
                let scale = BigInt::from(10).pow(frac_part.len() as u32);
                let numer = &ip * &scale + &fp;
                return EvalValue::Rational(BigRational::new(numer, scale));
            }
        }
        // Negation: "(- expr)"
        if trimmed.starts_with("(- ") && trimmed.ends_with(')') {
            let inner = trimmed[3..trimmed.len() - 1].trim();
            if let EvalValue::Rational(r) = Self::parse_real_string(inner) {
                return EvalValue::Rational(-r);
            }
        }
        // Division: "(/ num den)"
        if trimmed.starts_with("(/ ") && trimmed.ends_with(')') {
            let inner = trimmed[3..trimmed.len() - 1].trim();
            // Find split point: numerator and denominator separated by space
            // but numerator might be "(- n)" so find the last top-level space
            if let Some((num_s, den_s)) = Self::split_smt_pair(inner) {
                if let (EvalValue::Rational(n), Ok(d)) =
                    (Self::parse_real_string(num_s), den_s.parse::<BigInt>())
                {
                    if !d.is_zero() {
                        return EvalValue::Rational(n / BigRational::from(d));
                    }
                }
            }
        }
        EvalValue::Unknown
    }

    /// Parse an SMT-LIB bitvector value string into an EvalValue.
    ///
    /// Handles: `#x..`, `#b..`, decimal integers, and `(_ bvN W)`.
    pub(super) fn parse_bitvec_string(s: &str, width: u32) -> EvalValue {
        let trimmed = s.trim();
        if let Some(hex) = trimmed.strip_prefix("#x") {
            if let Some(value) = BigInt::parse_bytes(hex.as_bytes(), 16) {
                return EvalValue::BitVec {
                    value: Self::normalize_bv_value(value, width),
                    width,
                };
            }
            return EvalValue::Unknown;
        }
        if let Some(bin) = trimmed.strip_prefix("#b") {
            if let Some(value) = BigInt::parse_bytes(bin.as_bytes(), 2) {
                return EvalValue::BitVec {
                    value: Self::normalize_bv_value(value, width),
                    width,
                };
            }
            return EvalValue::Unknown;
        }
        if let Ok(value) = trimmed.parse::<BigInt>() {
            return EvalValue::BitVec {
                value: Self::normalize_bv_value(value, width),
                width,
            };
        }
        if let Some(rest) = trimmed.strip_prefix("(_ bv") {
            let mut parts = rest.split_whitespace();
            if let (Some(value_part), Some(width_part)) = (parts.next(), parts.next()) {
                let width_token = width_part.trim_end_matches(')');
                if let (Ok(value), Ok(parsed_width)) =
                    (value_part.parse::<BigInt>(), width_token.parse::<u32>())
                {
                    let final_width = if parsed_width == width {
                        width
                    } else {
                        parsed_width
                    };
                    return EvalValue::BitVec {
                        value: Self::normalize_bv_value(value, final_width),
                        width: final_width,
                    };
                }
            }
        }
        EvalValue::Unknown
    }

    /// Split an SMT-LIB pair like "3 5" or "(- 3) 5" into two parts.
    /// Respects parenthesis nesting.
    pub(super) fn split_smt_pair(s: &str) -> Option<(&str, &str)> {
        let mut depth = 0;
        for (i, c) in s.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                ' ' if depth == 0 => {
                    return Some((s[..i].trim(), s[i + 1..].trim()));
                }
                _ => {}
            }
        }
        None
    }

    pub(super) fn is_known_theory_symbol(name: &str) -> bool {
        matches!(
            name,
            "and"
                | "or"
                | "xor"
                | "not"
                | "="
                | "=>"
                | "distinct"
                | "true"
                | "false"
                | "+"
                | "-"
                | "*"
                | "/"
                | "mod"
                | "abs"
                | "div"
                | "<"
                | "<="
                | ">"
                | ">="
                | "bvadd"
                | "bvand"
                | "bvashr"
                | "bvcomp"
                | "bvlshr"
                | "bvmul"
                | "bvnand"
                | "bvneg"
                | "bvnor"
                | "bvnot"
                | "bvor"
                | "bvxnor"
                | "bvsdiv"
                | "bvsge"
                | "bvsgt"
                | "bvshl"
                | "bvsle"
                | "bvslt"
                | "bvsmod"
                | "bvsrem"
                | "bvsub"
                | "bvudiv"
                | "bvuge"
                | "bvugt"
                | "bvule"
                | "bvult"
                | "bvurem"
                | "bvxor"
                | "concat"
                | "extract"
                | "sign_extend"
                | "zero_extend"
                | "int2bv"
                | "repeat"
                | "rotate_left"
                | "rotate_right"
                | "select"
                | "store"
                | "const-array"
                | "str.len"
                | "str.++"
                | "str.substr"
                | "str.at"
                | "str.contains"
                | "str.indexof"
                | "str.replace"
                | "str.replace_all"
                | "str.replace_re"
                | "str.replace_re_all"
                | "str.prefixof"
                | "str.suffixof"
                | "str.<"
                | "str.<="
                | "str.to_int"
                | "str.from_int"
                | "int.to.str"
                | "str.to.int"
                | "str.to_code"
                | "str.from_code"
                | "str.to_lower"
                | "str.to_upper"
                | "str.is_digit"
                | "str.in_re"
                | "str.to_re"
                | "re.++"
                | "re.*"
                | "re.+"
                | "re.opt"
                | "re.comp"
                | "re.union"
                | "re.inter"
                | "re.diff"
                | "re.range"
                | "re.none"
                | "re.all"
                | "re.allchar"
                | "fp.isNaN"
                | "fp.isInfinite"
                | "fp.isZero"
                | "fp.isNormal"
                | "fp.isSubnormal"
                | "fp.isPositive"
                | "fp.isNegative"
                | "fp.eq"
                | "fp.lt"
                | "fp.leq"
                | "fp.gt"
                | "fp.geq"
                | "fp.add"
                | "fp.sub"
                | "fp.mul"
                | "fp.div"
                | "fp.rem"
                | "fp.sqrt"
                | "fp.neg"
                | "fp.abs"
                | "fp.min"
                | "fp.max"
                | "fp.roundToIntegral"
                | "fp.fma"
                | "fp.to_ubv"
                | "fp.to_sbv"
                | "fp.to_ieee_bv"
                | "fp.to_real"
                | "fp"
                | "to_fp"
                | "to_fp_unsigned"
                | "bv2nat"
                | "ite"
                | "if"
                | "seq.unit"
                | "seq.empty"
                | "seq.++"
                | "seq.len"
                | "seq.nth"
                | "seq.extract"
                | "seq.contains"
                | "seq.prefixof"
                | "seq.suffixof"
                | "seq.indexof"
                | "seq.last_indexof"
                | "seq.replace"
                | "seq.replace_all"
        ) || name.starts_with("__z4_")
    }
}
