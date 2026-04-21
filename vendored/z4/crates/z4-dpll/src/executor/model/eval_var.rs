// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Variable evaluation: look up a `TermData::Var` in the appropriate theory model.
//!
//! Extracted from `mod.rs` for code health (#5970). Each sort (Bool, Int, Real,
//! BitVec, FP, String, Seq, Uninterpreted, Datatype) has its own lookup chain
//! with fallbacks across theory models.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;
use z4_core::term::TermData;
use z4_core::{Sort, TermId};

use super::{EvalValue, Model};
use crate::executor::Executor;

impl Executor {
    /// Evaluate a `TermData::Var` by looking up the term in the appropriate theory model.
    ///
    /// The lookup chain depends on the variable's sort:
    /// - Bool: SAT model → BV bool_overrides → Unknown
    /// - Int: LIA → LRA → EUF term_values/int_values → default 0
    /// - Real: LRA → EUF term_values → default 0
    /// - BitVec: BV model → default 0 (or Unknown if no BV model)
    /// - FP: FP model → Unknown
    /// - String: String model → Unknown
    /// - Seq: Seq model → Unknown
    /// - Uninterpreted: EUF term_values → Unknown
    /// - Datatype: constructor name resolution → Unknown
    pub(super) fn evaluate_var(&self, model: &Model, term_id: TermId, sort: &Sort) -> EvalValue {
        if matches!(sort, Sort::Bool) {
            // Boolean variable: check SAT model
            match self.term_value(&model.sat_model, &model.term_to_var, term_id) {
                Some(b) => EvalValue::Bool(b),
                None => {
                    // Check BV model bool_overrides for variables recovered
                    // from preprocessing substitution (e.g., p -> (bvult x #x42)) (#5524)
                    if let Some(ref bv_model) = model.bv_model {
                        if let Some(&b) = bv_model.bool_overrides.get(&term_id) {
                            return EvalValue::Bool(b);
                        }
                    }
                    // (#5542) Return Unknown for Bool variables not in any model.
                    // Previously defaulted to false, which could mask missing model
                    // entries as valid false assignments. Matches Int/Real behavior.
                    EvalValue::Unknown
                }
            }
        } else if matches!(sort, Sort::Int) {
            // Integer variable: check LIA model first, then LRA model
            if let Some(ref lia_model) = model.lia_model {
                if let Some(val) = lia_model.values.get(&term_id) {
                    return EvalValue::Rational(BigRational::from(val.clone()));
                }
            }
            // Fall back to LRA model (when using pure LRA solver for arithmetic)
            if let Some(ref lra_model) = model.lra_model {
                if let Some(val) = lra_model.values.get(&term_id) {
                    return EvalValue::Rational(val.clone());
                }
            }
            let has_arith_model = model.lia_model.is_some() || model.lra_model.is_some();
            // Fall back to merged EUF model values for model completion.
            // Combined AUF* solvers merge arithmetic assignments into EUF model
            // term-values, so this covers Int terms omitted by LIA/LRA extraction.
            if let Some(ref euf_model) = model.euf_model {
                if let Some(raw) = euf_model.term_values.get(&term_id) {
                    if let EvalValue::Rational(r) =
                        self.parse_model_value_string(raw, &Some(Sort::Int))
                    {
                        return EvalValue::Rational(r);
                    }
                }
                if let Some(val) = euf_model.int_values.get(&term_id) {
                    return EvalValue::Rational(BigRational::from(val.clone()));
                }
            }
            if has_arith_model {
                // If arithmetic theories and merged EUF values did not assign this term,
                // keep the result Unknown instead of inventing a value.
                return EvalValue::Unknown;
            }
            // Default to 0 for unassigned integer variables
            EvalValue::Rational(BigRational::zero())
        } else if matches!(sort, Sort::Real) {
            // Real variable: check LRA model first
            if let Some(ref lra_model) = model.lra_model {
                if let Some(val) = lra_model.values.get(&term_id) {
                    return EvalValue::Rational(val.clone());
                }
            }
            let has_arith_model = model.lra_model.is_some();
            // Fall back to merged EUF model values for model completion.
            // Combined AUF* solvers merge LRA assignments into EUF model
            // term-values via merge_lra_values(), so this covers Real terms
            // omitted by LRA extraction in combined logics (QF_UFLRA, etc.).
            if let Some(ref euf_model) = model.euf_model {
                if let Some(raw) = euf_model.term_values.get(&term_id) {
                    if let EvalValue::Rational(r) =
                        self.parse_model_value_string(raw, &Some(Sort::Real))
                    {
                        return EvalValue::Rational(r);
                    }
                }
            }
            if has_arith_model {
                return EvalValue::Unknown;
            }
            // Default to 0 for unassigned real variables
            EvalValue::Rational(BigRational::zero())
        } else if let Sort::BitVec(bv) = sort {
            // BitVec variable: check BV model
            if let Some(ref bv_model) = model.bv_model {
                if let Some(val) = bv_model.values.get(&term_id) {
                    return EvalValue::BitVec {
                        value: val.clone(),
                        width: bv.width,
                    };
                }
                // BV model exists but variable is missing: default to 0
                // (model completion for unassigned variables).
                return EvalValue::BitVec {
                    value: BigInt::zero(),
                    width: bv.width,
                };
            }
            // No BV model (solved via AUFLIA as uninterpreted): return
            // Unknown. The AUFLIA solver treats BV terms as uninterpreted
            // and does not produce BV-semantic values, so defaulting to 0
            // would give wrong evaluation results for BV operations like
            // extract, concat, etc. (#5356)
            EvalValue::Unknown
        } else if matches!(sort, Sort::FloatingPoint(..)) {
            // FloatingPoint variable: check FP model
            if let Some(ref fp_model) = model.fp_model {
                if let Some(val) = fp_model.values.get(&term_id) {
                    return EvalValue::Fp(val.clone());
                }
            }
            EvalValue::Unknown
        } else if matches!(sort, Sort::String) {
            // String variable: check String model.
            if let Some(ref string_model) = model.string_model {
                if let Some(value) = string_model.values.get(&term_id) {
                    return EvalValue::String(value.clone());
                }
            }
            EvalValue::Unknown
        } else if let Sort::Seq(ref elem_sort) = sort {
            // Seq variable: check Seq model (#5995).
            // SeqModel stores Vec<String> per variable; convert each
            // element string to EvalValue using the element sort.
            if let Some(ref seq_model) = model.seq_model {
                if let Some(elems) = seq_model.values.get(&term_id) {
                    let eval_elems: Vec<EvalValue> = elems
                        .iter()
                        .map(|s| {
                            self.parse_model_value_string(s, &Some(elem_sort.as_ref().clone()))
                        })
                        .collect();
                    // Only return Seq if all elements resolved
                    if eval_elems.iter().all(|e| !matches!(e, EvalValue::Unknown)) {
                        return EvalValue::Seq(eval_elems);
                    }
                }
            }
            EvalValue::Unknown
        } else if let Some(ref euf_model) = model.euf_model {
            // Uninterpreted sort: check EUF model
            if let Some(elem) = euf_model.term_values.get(&term_id) {
                return EvalValue::Element(elem.clone());
            }
            EvalValue::Unknown
        } else {
            // Nullary DT constructors are stored as Var terms (#1745).
            // In pure QF_DT (no EUF model), resolve them to their
            // constructor names so assertion-based value extraction
            // works (#5450).
            if let TermData::Var(name, _) = self.ctx.terms.get(term_id) {
                if self.ctx.is_constructor(name).is_some() {
                    return EvalValue::Element(name.clone());
                }
            }
            EvalValue::Unknown
        }
    }
}
