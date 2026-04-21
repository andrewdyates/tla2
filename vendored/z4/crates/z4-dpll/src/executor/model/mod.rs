// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model construction, evaluation, and formatting.
//!
//! This module contains:
//! - `Model` struct representing a satisfying assignment
//! - `EvalValue` enum for evaluated term values
//! - Model evaluation functions for term interpretation
//! - Model formatting functions for SMT-LIB output

use std::sync::OnceLock;

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
use num_bigint::BigInt;
use num_rational::BigRational;
use z4_arrays::ArrayModel;
use z4_bv::BvModel;
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::term::{Constant, TermData};
use z4_core::{Sort, TermId};
use z4_euf::EufModel;
use z4_fp::{FpModel, FpModelValue};
use z4_lia::LiaModel;
use z4_lra::LraModel;
use z4_seq::SeqModel;
use z4_strings::StringModel;

#[cfg(test)]
use crate::executor_types::ModelValidationError;
use crate::executor_types::{ExecutorError, Result};

use super::Executor;
mod dt_bounds;
mod dt_model;
mod eval_arith;
mod eval_array;
mod eval_bv;
mod eval_bv_structural;
mod eval_fp;
mod eval_parse;
mod eval_seq;
mod eval_string;
mod eval_uf;
mod eval_var;
mod minimize;
mod output;
mod output_format;
mod validation;

pub(crate) use validation::ValidationStats;

/// Red zone size for `stacker::maybe_grow` in model evaluation (#4602).
pub(super) const EVAL_STACK_RED_ZONE: usize = if cfg!(debug_assertions) {
    128 * 1024
} else {
    32 * 1024
};

/// Stack segment size allocated by stacker for model evaluation recursion.
pub(super) const EVAL_STACK_SIZE: usize = 2 * 1024 * 1024;

/// Normalized array representation: (default value, sorted index→value pairs).
/// Used by `normalize_array_to_stores` for semantic equality comparison of array models.
type NormalizedArray = (Option<String>, Vec<(String, String)>);

/// Cached `Z4_DEBUG_MODEL` env var (checked once per process).
pub(super) fn debug_model() -> bool {
    static CACHED: OnceLock<bool> = OnceLock::new();
    *CACHED.get_or_init(|| std::env::var("Z4_DEBUG_MODEL").is_ok())
}

/// A satisfying model from check-sat
#[derive(Debug, Clone)]
pub(super) struct Model {
    /// SAT variable assignments (indexed by variable)
    pub(super) sat_model: Vec<bool>,
    /// Reverse mapping from term IDs to SAT variables (for efficient lookup)
    pub(super) term_to_var: HashMap<TermId, u32>,
    /// Optional EUF model (for QF_UF and related logics)
    pub(super) euf_model: Option<EufModel>,
    /// Optional array model (for QF_AX and related logics)
    pub(super) array_model: Option<ArrayModel>,
    /// Optional LRA model (for QF_LRA and related logics)
    pub(super) lra_model: Option<LraModel>,
    /// Optional LIA model (for QF_LIA and related logics)
    pub(super) lia_model: Option<LiaModel>,
    /// Optional BV model (for QF_BV and related logics)
    pub(super) bv_model: Option<BvModel>,
    /// Optional FP model (for QF_FP and related logics)
    pub(super) fp_model: Option<FpModel>,
    /// Optional String model (for QF_S and related logics)
    pub(super) string_model: Option<StringModel>,
    /// Optional Seq model (for QF_SEQ and related logics).
    pub(super) seq_model: Option<SeqModel>,
}

/// Evaluated value from model evaluation
#[derive(Debug, Clone)]
pub(crate) enum EvalValue {
    /// Boolean value
    Bool(bool),
    /// Element from an uninterpreted sort (by name, e.g., "@U!0")
    Element(String),
    /// Rational/integer value (BigRational can represent both)
    Rational(BigRational),
    /// Bitvector value with width
    BitVec {
        /// The numeric value of the bitvector
        value: BigInt,
        /// The bit width of the bitvector
        width: u32,
    },
    /// IEEE 754 floating-point value (as SMT-LIB string)
    Fp(FpModelValue),
    /// String value
    String(String),
    /// Sequence value (parametric: elements can be any EvalValue)
    Seq(Vec<Self>),
    /// Unknown/undefined value
    Unknown,
}

impl PartialEq for EvalValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bool(a), Self::Bool(b)) => a == b,
            (Self::Element(a), Self::Element(b)) => a == b,
            (Self::Rational(a), Self::Rational(b)) => a == b,
            (
                Self::BitVec {
                    value: v1,
                    width: w1,
                },
                Self::BitVec {
                    value: v2,
                    width: w2,
                },
            ) => v1 == v2 && w1 == w2,
            (Self::Fp(a), Self::Fp(b)) => a.to_smtlib() == b.to_smtlib(),
            (Self::String(a), Self::String(b)) => a == b,
            (Self::Seq(a), Self::Seq(b)) => a == b,
            (Self::Unknown, Self::Unknown) => true,
            _ => false,
        }
    }
}

impl Eq for EvalValue {}

impl Executor {
    /// Evaluate a term that should return an integer value
    pub(super) fn evaluate_int_term(&self, model: &Model, term: TermId) -> Result<BigInt> {
        match self.evaluate_term(model, term) {
            EvalValue::Rational(r) => {
                if r.is_integer() {
                    Ok(r.numer().clone())
                } else {
                    Err(ExecutorError::UnsupportedOptimization(
                        "objective evaluated to non-integer rational".to_string(),
                    ))
                }
            }
            EvalValue::Unknown => Err(ExecutorError::UnsupportedOptimization(
                "objective could not be evaluated".to_string(),
            )),
            _ => Err(ExecutorError::UnsupportedOptimization(
                "objective did not evaluate to a number".to_string(),
            )),
        }
    }

    /// Get the value of a term from the model (simple SAT lookup)
    pub(super) fn term_value(
        &self,
        sat_model: &[bool],
        term_to_var: &HashMap<TermId, u32>,
        term_id: TermId,
    ) -> Option<bool> {
        // Use the cached reverse mapping for O(1) amortized lookup (HashMap)
        // Note: Model.term_to_var is always 0-indexed (converted from DIMACS 1-indexed)
        if let Some(&var) = term_to_var.get(&term_id) {
            return sat_model.get(var as usize).copied();
        }
        // Term not in model - could be eliminated or not relevant
        None
    }

    /// Evaluate a term under the current model, recursively handling composite terms.
    ///
    /// This handles Boolean connectives (and, or, not, ite), equality/distinct,
    /// and looks up values for variables and function applications.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#4602).
    pub(super) fn evaluate_term(&self, model: &Model, term_id: TermId) -> EvalValue {
        stacker::maybe_grow(EVAL_STACK_RED_ZONE, EVAL_STACK_SIZE, || {
            let term = self.ctx.terms.get(term_id);
            let sort = self.ctx.terms.sort(term_id);

            match term {
                // Constants evaluate to themselves
                TermData::Const(Constant::Bool(b)) => EvalValue::Bool(*b),
                TermData::Const(Constant::Int(n)) => {
                    EvalValue::Rational(BigRational::from(n.clone()))
                }
                TermData::Const(Constant::Rational(r)) => EvalValue::Rational(r.0.clone()),
                TermData::Const(Constant::BitVec { value, width }) => EvalValue::BitVec {
                    value: value.clone(),
                    width: *width,
                },
                TermData::Const(Constant::String(s)) => EvalValue::String(s.clone()),

                // Variables: look up in appropriate model (eval_var.rs)
                TermData::Var(_, _) => self.evaluate_var(model, term_id, sort),

                // Negation
                TermData::Not(inner) => match self.evaluate_term(model, *inner) {
                    EvalValue::Bool(b) => EvalValue::Bool(!b),
                    _ => EvalValue::Unknown,
                },

                // If-then-else
                TermData::Ite(cond, then_br, else_br) => match self.evaluate_term(model, *cond) {
                    EvalValue::Bool(true) => self.evaluate_term(model, *then_br),
                    EvalValue::Bool(false) => self.evaluate_term(model, *else_br),
                    _ => EvalValue::Unknown,
                },

                // Function applications
                TermData::App(sym, args) => {
                    let name = sym.name();
                    match name {
                        "and" => {
                            // All arguments must be true
                            for &arg in args {
                                match self.evaluate_term(model, arg) {
                                    EvalValue::Bool(false) => return EvalValue::Bool(false),
                                    EvalValue::Bool(true) => {}
                                    _ => return EvalValue::Unknown,
                                }
                            }
                            EvalValue::Bool(true)
                        }
                        "or" => {
                            // Any argument must be true
                            for &arg in args {
                                match self.evaluate_term(model, arg) {
                                    EvalValue::Bool(true) => return EvalValue::Bool(true),
                                    EvalValue::Bool(false) => {}
                                    _ => return EvalValue::Unknown,
                                }
                            }
                            EvalValue::Bool(false)
                        }
                        "=>" => {
                            // Implication: a => b is (not a) or b
                            if args.len() == 2 {
                                let a = self.evaluate_term(model, args[0]);
                                let b = self.evaluate_term(model, args[1]);
                                match (a, b) {
                                    (EvalValue::Bool(false), _) => EvalValue::Bool(true),
                                    (EvalValue::Bool(true), EvalValue::Bool(b)) => {
                                        EvalValue::Bool(b)
                                    }
                                    _ => EvalValue::Unknown,
                                }
                            } else {
                                EvalValue::Unknown
                            }
                        }
                        "=" => {
                            // Equality: both arguments must evaluate to same value
                            if args.len() == 2 {
                                let v1 = self.evaluate_term(model, args[0]);
                                let v2 = self.evaluate_term(model, args[1]);
                                let eq_result = match (&v1, &v2) {
                                    (EvalValue::Bool(b1), EvalValue::Bool(b2)) => {
                                        EvalValue::Bool(b1 == b2)
                                    }
                                    (EvalValue::Element(e1), EvalValue::Element(e2)) => {
                                        EvalValue::Bool(e1 == e2)
                                    }
                                    (EvalValue::Rational(r1), EvalValue::Rational(r2)) => {
                                        EvalValue::Bool(r1 == r2)
                                    }
                                    (
                                        EvalValue::BitVec {
                                            value: v1,
                                            width: w1,
                                        },
                                        EvalValue::BitVec {
                                            value: v2,
                                            width: w2,
                                        },
                                    ) => {
                                        let n1 = Self::normalize_bv_value(v1.clone(), *w1);
                                        let n2 = Self::normalize_bv_value(v2.clone(), *w2);
                                        EvalValue::Bool(n1 == n2 && w1 == w2)
                                    }
                                    (EvalValue::String(s1), EvalValue::String(s2)) => {
                                        EvalValue::Bool(s1 == s2)
                                    }
                                    (EvalValue::Seq(a), EvalValue::Seq(b)) => {
                                        EvalValue::Bool(a == b)
                                    }
                                    // FP structural equality for SMT-LIB `=`:
                                    // NaN == NaN (reflexive), +0 != -0 (distinct bit patterns).
                                    // This differs from `fp.eq` (IEEE 754) which has NaN != NaN, +0 == -0.
                                    (EvalValue::Fp(ref a), EvalValue::Fp(ref b)) => {
                                        EvalValue::Bool(a.structural_eq(b))
                                    }
                                    // Cross-type: Rational vs BitVec (#5356).
                                    // Can arise when the evaluator returns mismatched
                                    // types for a well-typed equality (e.g., DT+BV
                                    // combined theories, or int2bv/bv2nat boundaries).
                                    // Compare numerically: Rational must be a non-negative
                                    // integer that fits in the BV width.
                                    (
                                        EvalValue::Rational(r),
                                        EvalValue::BitVec { value: bv, width },
                                    )
                                    | (
                                        EvalValue::BitVec { value: bv, width },
                                        EvalValue::Rational(r),
                                    ) => {
                                        if r.is_integer() {
                                            let int_val = r.to_integer();
                                            let bv_normalized =
                                                Self::normalize_bv_value(bv.clone(), *width);
                                            EvalValue::Bool(int_val == bv_normalized)
                                        } else {
                                            // Non-integer rational can never equal a bitvector
                                            EvalValue::Bool(false)
                                        }
                                    }
                                    _ => {
                                        if matches!(self.ctx.terms.sort(args[0]), Sort::Array(_))
                                            && matches!(
                                                self.ctx.terms.sort(args[1]),
                                                Sort::Array(_)
                                            )
                                        {
                                            self.evaluate_array_equality(model, term_id, args)
                                        } else {
                                            // (#5499) Return Unknown instead of falling
                                            // back to the SAT model. The SAT model is
                                            // the thing being validated; using it as
                                            // evidence is circular. validate_model
                                            // handles Unknown appropriately.
                                            EvalValue::Unknown
                                        }
                                    }
                                };
                                // (#6282) Removed unsound SAT-model fallback for equalities
                                // involving array subterms. The previous code fell back to the
                                // SAT solver's truth value when (= (select a i) 42) evaluated
                                // to Bool(false)/Unknown. This was unsound: the theory solver
                                // returning SAT means "no conflict in the conjunction," not
                                // "every individual equality is correct." The downstream guards
                                // in validate_model correctly handle Bool(false)/Unknown for
                                // array assertions via sat_fallback_count or Unknown degradation.
                                eq_result
                            } else {
                                EvalValue::Unknown
                            }
                        }
                        "distinct" => {
                            // All arguments must have different values
                            let values: Vec<EvalValue> =
                                args.iter().map(|&a| self.evaluate_term(model, a)).collect();

                            // Check for any unknown values
                            if values.iter().any(|v| matches!(v, EvalValue::Unknown)) {
                                return EvalValue::Unknown;
                            }

                            // Check all pairs are distinct
                            let mut seen: HashSet<String> = HashSet::new();
                            for v in &values {
                                let key = match v {
                                    EvalValue::Bool(b) => format!("bool:{b}"),
                                    EvalValue::Element(e) => format!("elem:{e}"),
                                    EvalValue::Rational(r) => format!("rat:{r}"),
                                    EvalValue::BitVec { value, width } => {
                                        let nv = Self::normalize_bv_value(value.clone(), *width);
                                        format!("bv:{width}:{nv}")
                                    }
                                    EvalValue::Fp(fp_val) => {
                                        format!("fp:{}", fp_val.to_smtlib())
                                    }
                                    EvalValue::String(s) => format!("str:{s}"),
                                    EvalValue::Seq(elems) => format!("seq:{elems:?}"),
                                    EvalValue::Unknown => unreachable!(),
                                };
                                if seen.contains(&key) {
                                    return EvalValue::Bool(false);
                                }
                                seen.insert(key);
                            }
                            EvalValue::Bool(true)
                        }
                        "xor" => {
                            // XOR: exactly one of the two arguments must be true
                            if args.len() == 2 {
                                let a = self.evaluate_term(model, args[0]);
                                let b = self.evaluate_term(model, args[1]);
                                match (a, b) {
                                    (EvalValue::Bool(a_val), EvalValue::Bool(b_val)) => {
                                        EvalValue::Bool(a_val != b_val)
                                    }
                                    _ => EvalValue::Unknown,
                                }
                            } else {
                                EvalValue::Unknown
                            }
                        }
                        // Arithmetic operations — delegated to eval_arith.rs
                        "+" | "-" | "*" | "/" | "div" | "mod" | "abs" | "to_real" | "to_int"
                        | "is_int" | "<" | "<=" | ">" | ">=" => {
                            self.evaluate_arith_app(model, name, args)
                        }
                        // BV operations — delegated to eval_bv.rs
                        "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt"
                        | "bvsge" | "bvadd" | "bvsub" | "bvmul" | "bvneg" | "bvand" | "bvor"
                        | "bvxor" | "bvnot" | "bvnand" | "bvnor" | "bvxnor" | "bvshl"
                        | "bvlshr" | "bvashr" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem"
                        | "bvsmod" | "concat" | "extract" | "zero_extend" | "sign_extend"
                        | "rotate_left" | "rotate_right" | "repeat" | "int2bv" | "bv2nat"
                        | "bvcomp" => self.evaluate_bv_app(model, sym, name, args, sort, term_id),
                        // Array select: select(a, i) -> evaluate using array axioms,
                        // falling back to BV model for bitblasted select terms (#4087).
                        "select" if args.len() == 2 => {
                            let result = self.evaluate_select(model, args[0], args[1]);
                            if matches!(result, EvalValue::Unknown) {
                                // (#6191) LIA/LRA model fallback: in AUFLIA, the LIA
                                // solver treats select terms as opaque variables and
                                // assigns integer values. When the array model cannot
                                // resolve the select (no concrete store entry), use
                                // the LIA model's value directly.
                                if matches!(sort, Sort::Int) {
                                    if let Some(ref lia_model) = model.lia_model {
                                        if let Some(val) = lia_model.values.get(&term_id) {
                                            return EvalValue::Rational(BigRational::from(
                                                val.clone(),
                                            ));
                                        }
                                    }
                                    if let Some(ref lra_model) = model.lra_model {
                                        if let Some(val) = lra_model.values.get(&term_id) {
                                            return EvalValue::Rational(val.clone());
                                        }
                                    }
                                }
                                if matches!(sort, Sort::Real) {
                                    if let Some(ref lra_model) = model.lra_model {
                                        if let Some(val) = lra_model.values.get(&term_id) {
                                            return EvalValue::Rational(val.clone());
                                        }
                                    }
                                }
                                // BV model cache fallback (#4087, unified in #5627).
                                let bv_fallback =
                                    self.bv_model_cache_fallback(model, term_id, sort);
                                if !matches!(bv_fallback, EvalValue::Unknown) {
                                    return bv_fallback;
                                }
                                if matches!(sort, Sort::Bool) {
                                    if let Some(b) = self.term_value(
                                        &model.sat_model,
                                        &model.term_to_var,
                                        term_id,
                                    ) {
                                        return EvalValue::Bool(b);
                                    }
                                }
                            }
                            result
                        }
                        // Array store is array-sorted; we can't reduce it to a scalar.
                        // But we still need to handle it so select(store(...)) works.
                        "store" if args.len() == 3 => EvalValue::Unknown,
                        // === String operations (ground evaluation) ===
                        // String operations — delegated to eval_string.rs
                        "str.len" | "str.++" | "str.substr" | "str.at" | "str.contains"
                        | "str.prefixof" | "str.suffixof" | "str.<" | "str.<=" | "str.replace"
                        | "str.replace_all" | "str.indexof" | "str.to_int" | "str.from_int"
                        | "str.to_code" | "str.from_code" | "str.is_digit" | "str.to_lower"
                        | "str.to_upper" | "str.in_re" | "str.replace_re"
                        | "str.replace_re_all" => self.evaluate_str_app(model, name, args),
                        // Sequence operations — delegated to eval_seq.rs
                        "seq.unit" | "seq.empty" | "seq.++" | "seq.len" | "seq.nth"
                        | "seq.extract" | "seq.contains" | "seq.prefixof" | "seq.suffixof"
                        | "seq.indexof" | "seq.last_indexof" | "seq.replace"
                        | "seq.replace_all" => self.evaluate_seq_app(model, name, args),
                        // FP operations — delegated to eval_fp.rs
                        "fp.isNaN" | "fp.isInfinite" | "fp.isZero" | "fp.isNormal"
                        | "fp.isSubnormal" | "fp.isPositive" | "fp.isNegative" | "fp.neg"
                        | "fp.abs" | "fp.eq" | "fp.lt" | "fp.leq" | "fp.gt" | "fp.geq"
                        | "fp.add" | "fp.sub" | "fp.mul" | "fp.div" | "fp.rem" | "fp.sqrt"
                        | "fp.min" | "fp.max" | "fp.roundToIntegral" | "fp.fma" | "fp"
                        | "to_fp" | "to_fp_unsigned" | "fp.to_ubv" | "fp.to_sbv" | "fp.to_real"
                        | "fp.to_ieee_bv" => {
                            self.evaluate_fp_app(model, sym, name, args, sort, term_id)
                        }

                        // Uninterpreted function application — delegated to eval_uf.rs
                        _ => self.evaluate_uninterpreted_app(model, name, args, sort, term_id),
                    }
                }

                // Let bindings should be expanded, but handle just in case
                TermData::Let(_, body) => self.evaluate_term(model, *body),

                // Quantifiers: can't evaluate without full model - return Unknown
                TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => EvalValue::Unknown,
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => unreachable!("unhandled TermData variant in evaluate_term(): {other:?}"),
            }
        }) // stacker::maybe_grow
    }
}

#[cfg(test)]
mod tests;
