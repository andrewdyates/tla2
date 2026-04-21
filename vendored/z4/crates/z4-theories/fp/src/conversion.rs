// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FP conversion helpers: rounding-mode decoding and `to_fp` encodings.

use z4_core::term::{TermData, TermId};
use z4_core::{CnfLit, Sort};

use super::{FpDecomposed, FpPrecision, FpSolver, RoundingMode};

impl FpSolver<'_> {
    /// Get rounding mode from a term.
    /// Handles both `TermData::App("RNE", _)` (from parser/API) and
    /// `TermData::Var("RNE", _)` (from some frontends). See #6203.
    pub(crate) fn get_rounding_mode(&self, term: TermId) -> RoundingMode {
        let data = self.terms.get(term);
        match data {
            TermData::App(sym, _) => match RoundingMode::from_name(sym.name()) {
                Some(rm) => rm,
                None => {
                    tracing::warn!(
                        name = sym.name(),
                        "unrecognized rounding mode, defaulting to RNE"
                    );
                    RoundingMode::default()
                }
            },
            TermData::Var(name, _) => match RoundingMode::from_name(name) {
                Some(rm) => rm,
                None => {
                    tracing::warn!(
                        name,
                        "unrecognized rounding mode variable, defaulting to RNE"
                    );
                    RoundingMode::default()
                }
            },
            _ => {
                tracing::warn!(?term, "non-symbolic rounding mode term, defaulting to RNE");
                RoundingMode::default()
            }
        }
    }

    /// Decompose a concrete FP constant `(fp sign_bv exp_bv sig_bv)` into
    /// constrained CNF variables. The three arguments must be BV constants;
    /// if any is non-constant, returns unconstrained variables with a warning.
    pub(crate) fn decompose_fp_constructor(
        &mut self,
        args: &[TermId],
        precision: FpPrecision,
    ) -> FpDecomposed {
        let sign_val = self.extract_bv_const(args[0]);
        let exp_val = self.extract_bv_const(args[1]);
        let sig_val = self.extract_bv_const(args[2]);

        match (sign_val, exp_val, sig_val) {
            (Some(s), Some(e), Some(m)) => {
                let fp = self.fresh_decomposed(precision);
                let negative = s.bit(0);
                self.constrain_constant(
                    &fp,
                    negative,
                    |i| e.bit(u64::from(i)),
                    |i| m.bit(u64::from(i)),
                );
                fp
            }
            _ => {
                tracing::warn!(
                    "FP bit-blasting: (fp ...) with non-constant BV arguments, \
                     returning unconstrained variables"
                );
                self.fresh_decomposed(precision)
            }
        }
    }

    /// Decompose `(_ to_fp eb sb)` based on argument count and sorts.
    pub(crate) fn decompose_to_fp(
        &mut self,
        args: &[TermId],
        precision: FpPrecision,
    ) -> FpDecomposed {
        match args.len() {
            1 => self.make_to_fp_from_bv_reinterpret(args[0], precision),
            2 => {
                let rm = self.get_rounding_mode(args[0]);
                let arg_sort = self.terms.sort(args[1]).clone();
                match arg_sort {
                    Sort::FloatingPoint(..) => {
                        let x = self.get_fp(args[1]);
                        self.make_to_fp_float(&x, rm, precision)
                    }
                    Sort::BitVec(_) => self.make_to_fp_signed(args[1], rm, precision),
                    _ => {
                        tracing::warn!(
                            ?arg_sort,
                            "to_fp: unsupported argument sort for 2-arg variant"
                        );
                        self.fresh_decomposed(precision)
                    }
                }
            }
            3 => self.decompose_fp_constructor(args, precision),
            _ => {
                tracing::warn!(nargs = args.len(), "to_fp: unexpected argument count");
                self.fresh_decomposed(precision)
            }
        }
    }

    /// Decompose `(_ to_fp_unsigned eb sb) rm bv` — unsigned BV-to-FP.
    pub(crate) fn decompose_to_fp_unsigned(
        &mut self,
        args: &[TermId],
        precision: FpPrecision,
    ) -> FpDecomposed {
        if args.len() != 2 {
            tracing::warn!(
                nargs = args.len(),
                "to_fp_unsigned: expected 2 arguments (rm, bv)"
            );
            return self.fresh_decomposed(precision);
        }
        let rm = self.get_rounding_mode(args[0]);
        self.make_to_fp_unsigned(args[1], rm, precision)
    }

    /// Reinterpret a bitvector as an IEEE 754 floating-point bit pattern.
    fn make_to_fp_from_bv_reinterpret(
        &mut self,
        bv_term: TermId,
        precision: FpPrecision,
    ) -> FpDecomposed {
        let eb = precision.exponent_bits() as usize;
        let sb = precision.significand_bits() as usize;
        let total = 1 + eb + (sb - 1);

        if let Some(bv_val) = self.extract_bv_const(bv_term) {
            let fp = self.fresh_decomposed(precision);
            let sign_val = bv_val.bit((total - 1) as u64);
            self.constrain_constant(
                &fp,
                sign_val,
                |i| bv_val.bit(u64::from(i) + (sb as u64 - 1)),
                |i| bv_val.bit(u64::from(i)),
            );
            return fp;
        }

        let bv_bits = self.bitblast_bv_term(bv_term, total);
        FpDecomposed {
            sign: bv_bits[total - 1],
            exponent: bv_bits[sb - 1..sb - 1 + eb].to_vec(),
            significand: bv_bits[0..sb - 1].to_vec(),
            precision,
        }
    }

    /// Convert a signed bitvector to floating-point with rounding.
    fn make_to_fp_signed(
        &mut self,
        bv_term: TermId,
        rm: RoundingMode,
        precision: FpPrecision,
    ) -> FpDecomposed {
        let eb = precision.exponent_bits() as usize;
        let sb = precision.significand_bits() as usize;
        let exp_sz = eb + 2;
        let sig_sz = sb + 4;

        let bv_sz = match self.terms.sort(bv_term).clone() {
            Sort::BitVec(bvs) => bvs.width as usize,
            _ => {
                tracing::warn!("to_fp signed: argument is not BitVec");
                return self.fresh_decomposed(precision);
            }
        };

        let bv_bits = self.bitblast_bv_term(bv_term, bv_sz);
        let is_zero = self.make_all_zero(&bv_bits);
        let zero_fp = self.make_zero(precision, false);

        let sign_bit = bv_bits[bv_sz - 1];
        let neg_bv = self.bv_neg(&bv_bits);
        let abs_bv = self.make_ite_bits(sign_bit, &neg_bv, &bv_bits);

        let lz = self.bv_leading_zeros(&abs_bv, exp_sz);
        let lz_extended = if bv_sz > exp_sz {
            self.zero_extend(&lz, bv_sz - exp_sz)
        } else if bv_sz < exp_sz {
            lz[..bv_sz].to_vec()
        } else {
            lz.clone()
        };
        let shifted = self.bv_shl(&abs_bv, &lz_extended);

        let mut sig_bits = Vec::with_capacity(sig_sz);
        if bv_sz >= sig_sz {
            let top_start = bv_sz - (sig_sz - 1);
            let sticky_bits: Vec<CnfLit> = shifted[..top_start].to_vec();
            let sticky = self.bv_or_reduce(&sticky_bits);
            sig_bits.push(sticky);
            sig_bits.extend_from_slice(&shifted[top_start..]);
        } else {
            let pad = sig_sz - bv_sz;
            let zero = self.const_false();
            for _ in 0..pad {
                sig_bits.push(zero);
            }
            sig_bits.extend_from_slice(&shifted);
        }
        debug_assert_eq!(sig_bits.len(), sig_sz);

        let base_exp = self.const_bv((bv_sz as u64).wrapping_sub(2), exp_sz);
        let exp_bits = self.bv_sub(&base_exp, &lz);

        let rounded = self.fp_round(precision, rm, sign_bit, &sig_bits, &exp_bits);
        self.make_ite_fp(is_zero, &zero_fp, &rounded, precision)
    }

    /// Convert an unsigned bitvector to floating-point with rounding.
    fn make_to_fp_unsigned(
        &mut self,
        bv_term: TermId,
        rm: RoundingMode,
        precision: FpPrecision,
    ) -> FpDecomposed {
        let eb = precision.exponent_bits() as usize;
        let sb = precision.significand_bits() as usize;
        let exp_sz = eb + 2;
        let sig_sz = sb + 4;

        let bv_sz = match self.terms.sort(bv_term).clone() {
            Sort::BitVec(bvs) => bvs.width as usize,
            _ => {
                tracing::warn!("to_fp_unsigned: argument is not BitVec");
                return self.fresh_decomposed(precision);
            }
        };

        let bv_bits = self.bitblast_bv_term(bv_term, bv_sz);
        let result_sign = self.const_false();
        let is_zero = self.make_all_zero(&bv_bits);
        let zero_fp = self.make_zero(precision, false);

        let lz = self.bv_leading_zeros(&bv_bits, exp_sz);
        let lz_extended = if bv_sz > exp_sz {
            self.zero_extend(&lz, bv_sz - exp_sz)
        } else if bv_sz < exp_sz {
            lz[..bv_sz].to_vec()
        } else {
            lz.clone()
        };
        let shifted = self.bv_shl(&bv_bits, &lz_extended);

        let mut sig_bits = Vec::with_capacity(sig_sz);
        if bv_sz >= sig_sz {
            let top_start = bv_sz - (sig_sz - 1);
            let sticky_bits: Vec<CnfLit> = shifted[..top_start].to_vec();
            let sticky = self.bv_or_reduce(&sticky_bits);
            sig_bits.push(sticky);
            sig_bits.extend_from_slice(&shifted[top_start..]);
        } else {
            let pad = sig_sz - bv_sz;
            let zero = self.const_false();
            for _ in 0..pad {
                sig_bits.push(zero);
            }
            sig_bits.extend_from_slice(&shifted);
        }
        debug_assert_eq!(sig_bits.len(), sig_sz);

        let base_exp = self.const_bv((bv_sz as u64).wrapping_sub(2), exp_sz);
        let exp_bits = self.bv_sub(&base_exp, &lz);

        let rounded = self.fp_round(precision, rm, result_sign, &sig_bits, &exp_bits);
        self.make_ite_fp(is_zero, &zero_fp, &rounded, precision)
    }

    /// Convert FP to FP with different precision.
    fn make_to_fp_float(
        &mut self,
        x: &FpDecomposed,
        rm: RoundingMode,
        to_precision: FpPrecision,
    ) -> FpDecomposed {
        let from_precision = x.precision;
        let from_eb = from_precision.exponent_bits() as usize;
        let from_sb = from_precision.significand_bits() as usize;
        let to_eb = to_precision.exponent_bits() as usize;
        let to_sb = to_precision.significand_bits() as usize;

        if from_eb == to_eb && from_sb == to_sb {
            return x.clone();
        }

        let x_nan = self.is_nan(x);
        let x_inf = self.is_infinite(x);
        let x_zero = self.is_zero(x);
        let result = self.fresh_decomposed(to_precision);

        let nan = self.make_nan_value(to_precision);
        self.constrain_fp_when(x_nan, &result, &nan);

        let pos_inf = self.make_infinity(to_precision, false);
        let neg_inf = self.make_infinity(to_precision, true);
        let pos_inf_cond = {
            let not_sign = -x.sign;
            self.make_and(x_inf, not_sign)
        };
        let neg_inf_cond = self.make_and(x_inf, x.sign);
        self.constrain_fp_when(pos_inf_cond, &result, &pos_inf);
        self.constrain_fp_when(neg_inf_cond, &result, &neg_inf);

        let pos_zero = self.make_zero(to_precision, false);
        let neg_zero = self.make_zero(to_precision, true);
        let pos_zero_cond = {
            let not_sign = -x.sign;
            self.make_and(x_zero, not_sign)
        };
        let neg_zero_cond = self.make_and(x_zero, x.sign);
        self.constrain_fp_when(pos_zero_cond, &result, &pos_zero);
        self.constrain_fp_when(neg_zero_cond, &result, &neg_zero);

        let (sgn, sig, exp, lz) = self.unpack(x, true);

        let sig_sz = to_sb + 4;
        let res_sig = if from_sb < (to_sb + 3) {
            let pad = to_sb + 3 - from_sb;
            let zero = self.const_false();
            let mut res = vec![zero; pad];
            res.extend_from_slice(&sig);
            res.push(zero);
            debug_assert_eq!(res.len(), sig_sz);
            res
        } else if from_sb > (to_sb + 3) {
            let keep = to_sb + 2;
            let high: Vec<CnfLit> = sig[from_sb - keep..from_sb].to_vec();
            let low: Vec<CnfLit> = sig[..from_sb - keep].to_vec();
            let sticky = self.bv_or_reduce(&low);
            let zero = self.const_false();
            let mut res = vec![sticky];
            res.extend_from_slice(&high);
            res.push(zero);
            debug_assert_eq!(res.len(), sig_sz);
            res
        } else {
            let zero = self.const_false();
            let mut res = sig;
            res.push(zero);
            debug_assert_eq!(res.len(), sig_sz);
            res
        };

        let exp_sz = to_eb + 2;
        let res_exp = if from_eb < exp_sz {
            self.sign_extend(&exp, exp_sz - from_eb)
        } else if from_eb > exp_sz {
            exp[..exp_sz].to_vec()
        } else {
            exp
        };

        let lz_ext = if lz.len() < exp_sz {
            self.zero_extend(&lz, exp_sz - lz.len())
        } else {
            lz[..exp_sz].to_vec()
        };
        let res_exp = self.bv_sub(&res_exp, &lz_ext);

        let normal_result = self.fp_round(to_precision, rm, sgn, &res_sig, &res_exp);
        let special = {
            let nan_or_inf = self.make_or(x_nan, x_inf);
            self.make_or(nan_or_inf, x_zero)
        };
        let not_special = -special;
        self.constrain_fp_when(not_special, &result, &normal_result);

        result
    }
}
