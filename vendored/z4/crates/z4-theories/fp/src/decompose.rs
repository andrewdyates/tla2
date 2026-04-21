// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FP term decomposition into sign/exponent/significand bitvectors.

use z4_core::term::{Symbol, TermData, TermId};
use z4_core::{CnfLit, Sort};

use super::{FpDecomposed, FpPrecision, FpSolver};

impl FpSolver<'_> {
    /// Encode a Bool-sorted term as a CNF literal for use in FP ITE conditions.
    fn encode_bool_condition(&mut self, bool_term: TermId) -> CnfLit {
        if let Some(cond_lit) = self.linked_condition_lit(bool_term) {
            return cond_lit;
        }

        match self.terms.get(bool_term).clone() {
            TermData::App(sym, args) => self.encode_bool_app_condition(bool_term, &sym, &args),
            TermData::Not(inner) => -self.encode_bool_condition(inner),
            data => self.encode_bool_condition_gap(bool_term, &data),
        }
    }

    fn linked_condition_lit(&mut self, bool_term: TermId) -> Option<CnfLit> {
        let tseitin_var = self.term_to_cnf.as_ref()?.get(&bool_term).copied()?;
        let fp_var = self.fresh_var();
        self.pending_condition_links
            .push((fp_var as u32, tseitin_var));
        Some(fp_var)
    }

    fn encode_bool_app_condition(
        &mut self,
        bool_term: TermId,
        sym: &Symbol,
        args: &[TermId],
    ) -> CnfLit {
        match sym.name() {
            "fp.lt" if args.len() == 2 => self.bitblast_fp_lt(args[0], args[1]),
            "fp.leq" if args.len() == 2 => self.bitblast_fp_le(args[0], args[1]),
            "fp.eq" if args.len() == 2 => self.bitblast_fp_eq(args[0], args[1]),
            "fp.gt" if args.len() == 2 => self.bitblast_fp_gt(args[0], args[1]),
            "fp.geq" if args.len() == 2 => self.bitblast_fp_ge(args[0], args[1]),
            "fp.isNaN" if args.len() == 1 => self.bitblast_is_nan(args[0]),
            "fp.isZero" if args.len() == 1 => self.bitblast_is_zero(args[0]),
            "fp.isInfinite" if args.len() == 1 => self.bitblast_is_infinite(args[0]),
            "fp.isNormal" if args.len() == 1 => self.bitblast_is_normal(args[0]),
            "fp.isSubnormal" if args.len() == 1 => self.bitblast_is_subnormal(args[0]),
            "fp.isPositive" if args.len() == 1 => self.bitblast_is_positive(args[0]),
            "fp.isNegative" if args.len() == 1 => self.bitblast_is_negative(args[0]),
            "=" if args.len() == 2
                && matches!(self.terms.sort(args[0]), Sort::FloatingPoint(..)) =>
            {
                self.bitblast_fp_structural_eq(args[0], args[1])
            }
            _ => {
                tracing::warn!(
                    ?bool_term,
                    name = sym.name(),
                    "ITE condition: non-FP App not in Tseitin map — encoding gap"
                );
                self.has_encoding_gap = true;
                self.fresh_var()
            }
        }
    }

    fn encode_bool_condition_gap(&mut self, bool_term: TermId, data: &TermData) -> CnfLit {
        tracing::warn!(
            ?bool_term,
            ?data,
            "ITE condition: unresolvable — encoding gap"
        );
        self.has_encoding_gap = true;
        self.fresh_var()
    }

    /// Get or create decomposed FP representation for a term.
    pub fn get_fp(&mut self, term: TermId) -> FpDecomposed {
        if let Some(fp) = self.term_to_fp.get(&term) {
            return fp.clone();
        }

        let fp = self.decompose_fp(term);
        self.term_to_fp.insert(term, fp.clone());
        fp
    }

    /// Decompose an FP term into sign, exponent, and significand.
    fn decompose_fp(&mut self, term: TermId) -> FpDecomposed {
        let sort = self.terms.sort(term).clone();
        debug_assert!(
            matches!(sort, Sort::FloatingPoint(..)),
            "Expected FloatingPoint sort, got {sort:?}"
        );
        let Sort::FloatingPoint(eb, sb) = sort else {
            tracing::warn!(?term, ?sort, "decompose_fp called on non-FP sort");
            return self.fresh_decomposed(FpPrecision::Float32);
        };

        let precision = FpPrecision::from_eb_sb(eb, sb);
        let data = self.terms.get(term).clone();

        match data {
            TermData::App(ref sym, ref args) => self.decompose_fp_app(term, sym, args, precision),
            TermData::Ite(cond, then_term, else_term) => {
                let cond_lit = self.encode_bool_condition(cond);
                let then_fp = self.get_fp(then_term);
                let else_fp = self.get_fp(else_term);
                self.make_ite_fp(cond_lit, &then_fp, &else_fp, precision)
            }
            _ => {
                tracing::warn!(
                    ?term,
                    ?data,
                    "FP bit-blasting: non-App/non-Ite FP term, returning unconstrained variables"
                );
                self.fresh_decomposed(precision)
            }
        }
    }

    /// Decompose a function application on FP.
    fn decompose_fp_app(
        &mut self,
        _term: TermId,
        sym: &Symbol,
        args: &[TermId],
        precision: FpPrecision,
    ) -> FpDecomposed {
        match sym.name() {
            "fp.zero" | "+zero" => self.make_zero(precision, false),
            "-zero" => self.make_zero(precision, true),
            "fp.inf" | "+oo" => self.make_infinity(precision, false),
            "-oo" => self.make_infinity(precision, true),
            "fp.nan" | "NaN" => self.make_nan_value(precision),
            "fp.neg" => {
                let x = self.get_fp(args[0]);
                self.make_neg(&x)
            }
            "fp.abs" => {
                let x = self.get_fp(args[0]);
                self.make_abs(&x)
            }
            "fp.add" => {
                let rm = self.get_rounding_mode(args[0]);
                let x = self.get_fp(args[1]);
                let y = self.get_fp(args[2]);
                self.make_add(&x, &y, rm)
            }
            "fp.sub" => {
                let rm = self.get_rounding_mode(args[0]);
                let x = self.get_fp(args[1]);
                let y = self.get_fp(args[2]);
                self.make_sub(&x, &y, rm)
            }
            "fp.mul" => {
                let rm = self.get_rounding_mode(args[0]);
                let x = self.get_fp(args[1]);
                let y = self.get_fp(args[2]);
                self.make_mul(&x, &y, rm)
            }
            "fp.div" => {
                let rm = self.get_rounding_mode(args[0]);
                let x = self.get_fp(args[1]);
                let y = self.get_fp(args[2]);
                self.make_div(&x, &y, rm)
            }
            "fp.sqrt" => {
                let rm = self.get_rounding_mode(args[0]);
                let x = self.get_fp(args[1]);
                self.make_sqrt(&x, rm)
            }
            "fp.fma" => {
                let rm = self.get_rounding_mode(args[0]);
                let x = self.get_fp(args[1]);
                let y = self.get_fp(args[2]);
                let z = self.get_fp(args[3]);
                self.make_fma(&x, &y, &z, rm)
            }
            "fp.roundToIntegral" => {
                let rm = self.get_rounding_mode(args[0]);
                let x = self.get_fp(args[1]);
                self.make_round_to_integral(&x, rm)
            }
            "fp.rem" => {
                let x = self.get_fp(args[0]);
                let y = self.get_fp(args[1]);
                self.make_rem(&x, &y)
            }
            "fp.min" => {
                let x = self.get_fp(args[0]);
                let y = self.get_fp(args[1]);
                self.make_min(&x, &y)
            }
            "fp.max" => {
                let x = self.get_fp(args[0]);
                let y = self.get_fp(args[1]);
                self.make_max(&x, &y)
            }
            "fp" if args.len() == 3 => self.decompose_fp_constructor(args, precision),
            "to_fp" => self.decompose_to_fp(args, precision),
            "to_fp_unsigned" => self.decompose_to_fp_unsigned(args, precision),
            other => {
                tracing::warn!(
                    op = other,
                    "FP bit-blasting: unrecognized operation, returning unconstrained variables"
                );
                self.fresh_decomposed(precision)
            }
        }
    }
}
