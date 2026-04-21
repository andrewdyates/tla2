// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Remaining FP operations: remainder, min, and max.

use z4_core::CnfLit;

use super::{FpDecomposed, FpPrecision, FpSolver, RoundingMode};

struct RemSpecialCases {
    nan: FpDecomposed,
    pzero: FpDecomposed,
    c1: CnfLit,
    c2: CnfLit,
    c3: CnfLit,
    c4: CnfLit,
    c5: CnfLit,
    c6: CnfLit,
}

struct RemCore {
    rndd: FpDecomposed,
    adj_cnd: CnfLit,
    b_sgn: CnfLit,
}

impl FpSolver<'_> {
    /// IEEE 754 remainder: `fp.rem(x, y)`.
    pub fn make_rem(&mut self, x: &FpDecomposed, y: &FpDecomposed) -> FpDecomposed {
        let precision = x.precision;
        let special_cases = self.rem_special_cases(x, y);
        let core = self.rem_round_down_candidate(x, y);
        let signs_differ = self.make_xor(core.rndd.sign, core.b_sgn);
        let rounded_add = self.make_add(&core.rndd, y, RoundingMode::RNE);
        let rounded_sub = self.make_sub(&core.rndd, y, RoundingMode::RNE);
        let adjusted = self.make_ite_fp(signs_differ, &rounded_add, &rounded_sub, precision);
        let base = self.make_ite_fp(core.adj_cnd, &adjusted, &core.rndd, precision);
        let result = self.rem_apply_special_cases(x, &special_cases, &base, precision);
        self.rem_fix_zero_sign(x, &result, precision)
    }

    fn rem_special_cases(&mut self, x: &FpDecomposed, y: &FpDecomposed) -> RemSpecialCases {
        let precision = x.precision;
        let eb = precision.exponent_bits() as usize;
        let x_nan = self.is_nan(x);
        let y_nan = self.is_nan(y);
        let c1 = self.make_or(x_nan, y_nan);
        let c2 = self.is_infinite(x);
        let c3 = self.is_infinite(y);
        let c4 = self.is_zero(y);
        let c5 = self.is_zero(x);

        let y_exp_zero = self.make_all_zero(&y.exponent);
        let one_eb = self.const_bv(1, eb);
        let y_exp_m1 = self.bv_sub(&y.exponent, &one_eb);
        let xe_lt_yem1 = self.make_unsigned_lt(&x.exponent, &y_exp_m1);
        let c6 = self.make_and(-y_exp_zero, xe_lt_yem1);

        RemSpecialCases {
            nan: self.make_nan_value(precision),
            pzero: self.make_zero(precision, false),
            c1,
            c2,
            c3,
            c4,
            c5,
            c6,
        }
    }

    fn rem_round_down_candidate(&mut self, x: &FpDecomposed, y: &FpDecomposed) -> RemCore {
        let precision = x.precision;
        let eb = precision.exponent_bits() as usize;
        let sb = precision.significand_bits() as usize;
        let (a_sgn, a_sig, a_exp, a_lz) = self.unpack(x, true);
        let (b_sgn, b_sig, b_exp, b_lz) = self.unpack(y, true);

        let a_exp_ext = self.sign_extend(&a_exp, 2);
        let b_exp_ext = self.sign_extend(&b_exp, 2);
        let a_lz_ext = self.zero_extend(&a_lz, 2);
        let b_lz_ext = self.zero_extend(&b_lz, 2);
        let a_eff_exp = self.bv_sub(&a_exp_ext, &a_lz_ext);
        let b_eff_exp = self.bv_sub(&b_exp_ext, &b_lz_ext);
        let exp_diff = self.bv_sub(&a_eff_exp, &b_eff_exp);
        let ext_width = (1usize << eb) - 3;

        let three_zeros = self.const_bv(0, 3);
        let a_sig_ext = self.zero_extend(&a_sig, ext_width);
        let b_sig_ext = self.zero_extend(&b_sig, ext_width);
        let a_sig_full = Self::bv_concat(&three_zeros, &a_sig_ext);
        let b_sig_full = Self::bv_concat(&three_zeros, &b_sig_ext);
        let shifted = self.rem_shifted_dividend(&a_sig_full, &exp_diff, eb + 2);

        let (huge_div, huge_rem) = self.bv_udiv_urem(&shifted, &b_sig_full);
        let adj_cnd = self.rem_adjustment_condition(&huge_div, &huge_rem, &b_sig, sb, eb);
        let rndd_sig: Vec<CnfLit> = huge_rem[..sb + 4].to_vec();
        let rndd = self.fp_round(precision, RoundingMode::RNE, a_sgn, &rndd_sig, &b_eff_exp);
        RemCore {
            rndd,
            adj_cnd,
            b_sgn,
        }
    }

    fn rem_shifted_dividend(
        &mut self,
        a_sig_full: &[CnfLit],
        exp_diff: &[CnfLit],
        exp_width: usize,
    ) -> Vec<CnfLit> {
        let total_width = a_sig_full.len();
        let zero_ed = self.const_bv(0, exp_width);
        let exp_diff_is_neg = self.bv_slt(exp_diff, &zero_ed);
        let neg_exp_diff = self.bv_neg(exp_diff);

        let lshift_amt = if exp_width < total_width {
            self.zero_extend(exp_diff, total_width - exp_width)
        } else {
            exp_diff[..total_width].to_vec()
        };
        let rshift_amt = if exp_width < total_width {
            self.zero_extend(&neg_exp_diff, total_width - exp_width)
        } else {
            neg_exp_diff[..total_width].to_vec()
        };
        let lshifted = self.bv_shl(a_sig_full, &lshift_amt);
        let rshifted = self.bv_lshr(a_sig_full, &rshift_amt);
        self.make_ite_bits(exp_diff_is_neg, &rshifted, &lshifted)
    }

    fn rem_adjustment_condition(
        &mut self,
        huge_div: &[CnfLit],
        huge_rem: &[CnfLit],
        b_sig: &[CnfLit],
        sb: usize,
        eb: usize,
    ) -> CnfLit {
        let rndd_sig: Vec<CnfLit> = huge_rem[..sb + 4].to_vec();
        let rndd_sig_lz = self.bv_leading_zeros(&rndd_sig, eb + 2);
        let one_lz = self.const_bv(1, eb + 2);
        let two_lz = self.const_bv(2, eb + 2);
        let rndd_exp_eq_y_exp = self.make_bv_eq(&rndd_sig_lz, &one_lz);
        let rndd_exp_eq_y_exp_m1 = self.make_bv_eq(&rndd_sig_lz, &two_lz);

        let two_zeros = self.const_bv(0, 2);
        let b_sig_pad = Self::bv_concat(&two_zeros, &self.zero_extend(b_sig, 2));
        let y_sig_le_rndd = self.bv_sle(&b_sig_pad, &rndd_sig);
        let y_sig_eq_rndd = self.make_bv_eq(&b_sig_pad, &rndd_sig);

        let case1 = self.make_and(rndd_exp_eq_y_exp, y_sig_le_rndd);
        let case2_inner = self.make_and(y_sig_le_rndd, -y_sig_eq_rndd);
        let case2 = self.make_and(rndd_exp_eq_y_exp_m1, case2_inner);
        let case3_inner = self.make_and(y_sig_eq_rndd, huge_div[0]);
        let case3 = self.make_and(rndd_exp_eq_y_exp_m1, case3_inner);
        let case2_or_3 = self.make_or(case2, case3);
        self.make_or(case1, case2_or_3)
    }

    fn rem_apply_special_cases(
        &mut self,
        x: &FpDecomposed,
        special_cases: &RemSpecialCases,
        base: &FpDecomposed,
        precision: FpPrecision,
    ) -> FpDecomposed {
        let mut result = base.clone();
        result = self.make_ite_fp(special_cases.c6, x, &result, precision);
        result = self.make_ite_fp(special_cases.c5, &special_cases.pzero, &result, precision);
        result = self.make_ite_fp(special_cases.c4, &special_cases.nan, &result, precision);
        result = self.make_ite_fp(special_cases.c3, x, &result, precision);
        result = self.make_ite_fp(special_cases.c2, &special_cases.nan, &result, precision);
        self.make_ite_fp(special_cases.c1, &special_cases.nan, &result, precision)
    }

    fn rem_fix_zero_sign(
        &mut self,
        x: &FpDecomposed,
        result: &FpDecomposed,
        precision: FpPrecision,
    ) -> FpDecomposed {
        let pos_zero = self.make_zero(precision, false);
        let neg_zero = self.make_zero(precision, true);
        let correct_zero = self.make_ite_fp(-x.sign, &pos_zero, &neg_zero, precision);
        let result_is_zero = self.is_zero(result);
        self.make_ite_fp(result_is_zero, &correct_zero, result, precision)
    }

    /// Minimum of two FP values.
    pub fn make_min(&mut self, x: &FpDecomposed, y: &FpDecomposed) -> FpDecomposed {
        let precision = x.precision;
        let x_nan = self.is_nan(x);
        let y_lt = self.make_lt_result(y, x);
        let use_y = self.make_or(x_nan, y_lt);

        let sign = self.make_ite(use_y, y.sign, x.sign);
        let exponent = self.make_ite_bits(use_y, &y.exponent, &x.exponent);
        let significand = self.make_ite_bits(use_y, &y.significand, &x.significand);

        FpDecomposed {
            sign,
            exponent,
            significand,
            precision,
        }
    }

    /// Maximum of two FP values.
    pub fn make_max(&mut self, x: &FpDecomposed, y: &FpDecomposed) -> FpDecomposed {
        let precision = x.precision;
        let x_nan = self.is_nan(x);
        let y_gt = self.make_lt_result(x, y);
        let use_y = self.make_or(x_nan, y_gt);

        let sign = self.make_ite(use_y, y.sign, x.sign);
        let exponent = self.make_ite_bits(use_y, &y.exponent, &x.exponent);
        let significand = self.make_ite_bits(use_y, &y.significand, &x.significand);

        FpDecomposed {
            sign,
            exponent,
            significand,
            precision,
        }
    }
}
