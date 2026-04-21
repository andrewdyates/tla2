// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sequence evaluation helpers for model evaluation.
//!
//! Extracted from `mod.rs` to reduce file size (Wave C2 of #2998 module splits).

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{ToPrimitive, Zero};
use z4_core::TermId;

use super::{EvalValue, Executor, Model};

impl Executor {
    /// Evaluate a sequence application term.
    ///
    /// Handles all `seq.*` operations including construction,
    /// indexing, slicing, search, and replacement.
    pub(super) fn evaluate_seq_app(&self, model: &Model, name: &str, args: &[TermId]) -> EvalValue {
        match name {
            // === Sequence operations (ground evaluation, #5997) ===
            "seq.unit" if args.len() == 1 => {
                let elem = self.evaluate_term(model, args[0]);
                match elem {
                    EvalValue::Unknown => EvalValue::Unknown,
                    v => EvalValue::Seq(vec![v]),
                }
            }
            "seq.empty" => EvalValue::Seq(vec![]),
            "seq.++" => {
                let mut result = Vec::new();
                for &arg in args {
                    match self.evaluate_term(model, arg) {
                        EvalValue::Seq(elems) => result.extend(elems),
                        _ => return EvalValue::Unknown,
                    }
                }
                EvalValue::Seq(result)
            }
            "seq.len" if args.len() == 1 => match self.evaluate_term(model, args[0]) {
                EvalValue::Seq(elems) => {
                    EvalValue::Rational(BigRational::from(BigInt::from(elems.len())))
                }
                _ => EvalValue::Unknown,
            },
            "seq.nth" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Seq(elems), EvalValue::Rational(i_rat)) => {
                        if let Some(i) = i_rat.to_integer().to_usize() {
                            if i < elems.len() {
                                elems.into_iter().nth(i).unwrap_or(EvalValue::Unknown)
                            } else {
                                // Out of bounds: unspecified per SMT-LIB
                                EvalValue::Unknown
                            }
                        } else {
                            EvalValue::Unknown
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.extract" if args.len() == 3 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                    self.evaluate_term(model, args[2]),
                ) {
                    (
                        EvalValue::Seq(elems),
                        EvalValue::Rational(i_rat),
                        EvalValue::Rational(n_rat),
                    ) => {
                        let i = i_rat.to_integer();
                        let n = n_rat.to_integer();
                        let len = BigInt::from(elems.len());
                        // SMT-LIB: out-of-bounds returns empty
                        if i < BigInt::zero() || n <= BigInt::zero() || i >= len {
                            EvalValue::Seq(vec![])
                        } else if let (Some(start), Some(count)) = (i.to_usize(), n.to_usize()) {
                            let end = std::cmp::min(start + count, elems.len());
                            EvalValue::Seq(elems[start..end].to_vec())
                        } else {
                            EvalValue::Unknown
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.contains" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Seq(haystack), EvalValue::Seq(needle)) => {
                        if needle.is_empty() {
                            EvalValue::Bool(true)
                        } else if needle.len() > haystack.len() {
                            EvalValue::Bool(false)
                        } else {
                            let found = haystack
                                .windows(needle.len())
                                .any(|w| w == needle.as_slice());
                            EvalValue::Bool(found)
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.prefixof" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Seq(prefix), EvalValue::Seq(s)) => {
                        EvalValue::Bool(s.starts_with(prefix.as_slice()))
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.suffixof" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Seq(suffix), EvalValue::Seq(s)) => {
                        EvalValue::Bool(s.ends_with(suffix.as_slice()))
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.indexof" if args.len() == 3 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                    self.evaluate_term(model, args[2]),
                ) {
                    (EvalValue::Seq(s), EvalValue::Seq(t), EvalValue::Rational(offset_rat)) => {
                        let offset = offset_rat.to_integer();
                        if offset < BigInt::zero() || offset > BigInt::from(s.len()) {
                            EvalValue::Rational(BigRational::from(BigInt::from(-1)))
                        } else if t.is_empty() {
                            // Empty needle: return offset (clamped to len)
                            let o = std::cmp::min(offset.to_usize().unwrap_or(s.len()), s.len());
                            EvalValue::Rational(BigRational::from(BigInt::from(o)))
                        } else if let Some(start) = offset.to_usize() {
                            let mut result = -1i64;
                            if start + t.len() <= s.len() {
                                for i in start..=(s.len() - t.len()) {
                                    if s[i..i + t.len()] == *t.as_slice() {
                                        result = i as i64;
                                        break;
                                    }
                                }
                            }
                            EvalValue::Rational(BigRational::from(BigInt::from(result)))
                        } else {
                            EvalValue::Rational(BigRational::from(BigInt::from(-1)))
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.last_indexof" if args.len() == 2 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                ) {
                    (EvalValue::Seq(haystack), EvalValue::Seq(needle)) => {
                        if needle.is_empty() {
                            // Empty needle: return len(haystack)
                            EvalValue::Rational(BigRational::from(BigInt::from(haystack.len())))
                        } else if needle.len() > haystack.len() {
                            EvalValue::Rational(BigRational::from(BigInt::from(-1)))
                        } else {
                            // Scan from right to left
                            let mut result = -1i64;
                            for i in (0..=(haystack.len() - needle.len())).rev() {
                                if haystack[i..i + needle.len()] == *needle.as_slice() {
                                    result = i as i64;
                                    break;
                                }
                            }
                            EvalValue::Rational(BigRational::from(BigInt::from(result)))
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.replace" if args.len() == 3 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                    self.evaluate_term(model, args[2]),
                ) {
                    (EvalValue::Seq(s), EvalValue::Seq(src), EvalValue::Seq(dst)) => {
                        if src.is_empty() {
                            // Replace empty: prepend dst
                            let mut result = dst;
                            result.extend(s);
                            EvalValue::Seq(result)
                        } else if let Some(pos) =
                            s.windows(src.len()).position(|w| w == src.as_slice())
                        {
                            let mut result = s[..pos].to_vec();
                            result.extend(dst);
                            result.extend(s[pos + src.len()..].to_vec());
                            EvalValue::Seq(result)
                        } else {
                            // Not found: return original
                            EvalValue::Seq(s)
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            "seq.replace_all" if args.len() == 3 => {
                match (
                    self.evaluate_term(model, args[0]),
                    self.evaluate_term(model, args[1]),
                    self.evaluate_term(model, args[2]),
                ) {
                    (EvalValue::Seq(s), EvalValue::Seq(src), EvalValue::Seq(dst)) => {
                        if src.is_empty() {
                            // Replace empty with all: unchanged
                            EvalValue::Seq(s)
                        } else {
                            // Replace all non-overlapping occurrences left to right
                            let mut result = Vec::new();
                            let mut i = 0;
                            while i < s.len() {
                                if i + src.len() <= s.len()
                                    && s[i..i + src.len()] == *src.as_slice()
                                {
                                    result.extend_from_slice(&dst);
                                    i += src.len();
                                } else {
                                    result.push(s[i].clone());
                                    i += 1;
                                }
                            }
                            EvalValue::Seq(result)
                        }
                    }
                    _ => EvalValue::Unknown,
                }
            }
            _ => EvalValue::Unknown,
        }
    }
}
