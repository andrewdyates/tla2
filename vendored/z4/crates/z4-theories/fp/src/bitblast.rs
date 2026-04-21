// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bit-blast query helpers for FP predicates and FP/BV conversions.

use z4_core::term::{Symbol, TermData, TermId};
use z4_core::{CnfLit, Sort};

use super::{FpSolver, HashMap, RoundingMode};

impl FpSolver<'_> {
    /// Bit-blast `fp.isNaN`.
    pub fn bitblast_is_nan(&mut self, term: TermId) -> CnfLit {
        let fp = self.get_fp(term);
        self.is_nan(&fp)
    }

    /// Bit-blast `fp.isInfinite`.
    pub fn bitblast_is_infinite(&mut self, term: TermId) -> CnfLit {
        let fp = self.get_fp(term);
        self.is_infinite(&fp)
    }

    /// Bit-blast `fp.isZero`.
    pub fn bitblast_is_zero(&mut self, term: TermId) -> CnfLit {
        let fp = self.get_fp(term);
        self.is_zero(&fp)
    }

    /// Bit-blast `fp.isNormal`.
    pub fn bitblast_is_normal(&mut self, term: TermId) -> CnfLit {
        let fp = self.get_fp(term);
        self.is_normal(&fp)
    }

    /// Bit-blast `fp.isSubnormal`.
    pub fn bitblast_is_subnormal(&mut self, term: TermId) -> CnfLit {
        let fp = self.get_fp(term);
        self.is_subnormal(&fp)
    }

    /// Bit-blast `fp.isPositive`.
    pub fn bitblast_is_positive(&mut self, term: TermId) -> CnfLit {
        let fp = self.get_fp(term);
        let is_nan = self.is_nan(&fp);
        let not_nan = -is_nan;
        let not_sign = -fp.sign;
        self.make_and(not_nan, not_sign)
    }

    /// Bit-blast `fp.isNegative`.
    pub fn bitblast_is_negative(&mut self, term: TermId) -> CnfLit {
        let fp = self.get_fp(term);
        let is_nan = self.is_nan(&fp);
        let not_nan = -is_nan;
        self.make_and(not_nan, fp.sign)
    }

    /// Bit-blast SMT-LIB structural equality `(=)` on FP sort.
    pub fn bitblast_fp_structural_eq(&mut self, x: TermId, y: TermId) -> CnfLit {
        let fp_x = self.get_fp(x);
        let fp_y = self.get_fp(y);

        let sign_eq = self.make_xnor(fp_x.sign, fp_y.sign);
        let exp_eq = self.make_bits_equal(&fp_x.exponent, &fp_y.exponent);
        let sig_eq = self.make_bits_equal(&fp_x.significand, &fp_y.significand);
        let exp_sig_eq = self.make_and(exp_eq, sig_eq);
        self.make_and(sign_eq, exp_sig_eq)
    }

    /// Bit-blast `fp.eq`.
    pub fn bitblast_fp_eq(&mut self, x: TermId, y: TermId) -> CnfLit {
        let fp_x = self.get_fp(x);
        let fp_y = self.get_fp(y);

        let x_nan = self.is_nan(&fp_x);
        let y_nan = self.is_nan(&fp_y);
        let either_nan = self.make_or(x_nan, y_nan);

        let x_zero = self.is_zero(&fp_x);
        let y_zero = self.is_zero(&fp_y);
        let both_zero = self.make_and(x_zero, y_zero);

        let sign_eq = self.make_xnor(fp_x.sign, fp_y.sign);
        let exp_eq = self.make_bits_equal(&fp_x.exponent, &fp_y.exponent);
        let sig_eq = self.make_bits_equal(&fp_x.significand, &fp_y.significand);
        let exp_sig_eq = self.make_and(exp_eq, sig_eq);
        let bit_equal = self.make_and(sign_eq, exp_sig_eq);

        let eq = self.make_or(both_zero, bit_equal);
        let not_nan = -either_nan;
        self.make_and(not_nan, eq)
    }

    /// Bit-blast `fp.lt`.
    pub fn bitblast_fp_lt(&mut self, x: TermId, y: TermId) -> CnfLit {
        let fp_x = self.get_fp(x);
        let fp_y = self.get_fp(y);
        self.make_lt_result(&fp_x, &fp_y)
    }

    /// Bit-blast `fp.leq`.
    pub fn bitblast_fp_le(&mut self, x: TermId, y: TermId) -> CnfLit {
        let lt = self.bitblast_fp_lt(x, y);
        let eq = self.bitblast_fp_eq(x, y);
        self.make_or(lt, eq)
    }

    /// Bit-blast `fp.gt`.
    pub fn bitblast_fp_gt(&mut self, x: TermId, y: TermId) -> CnfLit {
        self.bitblast_fp_lt(y, x)
    }

    /// Bit-blast `fp.geq`.
    pub fn bitblast_fp_ge(&mut self, x: TermId, y: TermId) -> CnfLit {
        self.bitblast_fp_le(y, x)
    }

    /// Bit-blast `fp.to_ubv` or `fp.to_sbv`.
    pub fn bitblast_to_bv(
        &mut self,
        fp_term: TermId,
        rm: RoundingMode,
        bv_sz: usize,
        is_signed: bool,
    ) -> Vec<CnfLit> {
        let fp = self.get_fp(fp_term);
        let (sgn, sig, exp, lz) = self.unpack(&fp, true);

        let ebits = fp.precision.exponent_bits() as usize;
        let sbits = fp.precision.significand_bits() as usize;
        let unspec = self.const_bv(0, bv_sz);

        let x_is_nan = self.is_nan(&fp);
        let x_is_inf = self.is_infinite(&fp);
        let x_is_zero = self.is_zero(&fp);
        let c1 = self.make_or(x_is_nan, x_is_inf);
        let v2 = self.const_bv(0, bv_sz);

        let mut sig_ext = sig;
        debug_assert_eq!(sig_ext.len(), sbits);
        if sig_ext.len() < (bv_sz + 3) {
            let zero = self.const_false();
            let pad = bv_sz + 3 - sig_ext.len();
            let mut new_sig = vec![zero; pad];
            new_sig.extend_from_slice(&sig_ext);
            sig_ext = new_sig;
        }

        let exp_ext = self.sign_extend(&exp, 2);
        let lz_ext = self.zero_extend(&lz, 2);
        let exp_m_lz = self.bv_sub(&exp_ext, &lz_ext);

        let zero = self.const_false();
        let mut big_sig = vec![zero];
        big_sig.extend_from_slice(&sig_ext);
        for _ in 0..(bv_sz + 2) {
            big_sig.push(zero);
        }
        let big_sig_sz = big_sig.len();

        let zero_exp = self.const_bv(0, ebits + 2);
        let is_neg_shift = self.bv_sle(&exp_m_lz, &zero_exp);
        let neg_exp_m_lz = self.bv_neg(&exp_m_lz);
        let shift_mag = self.make_ite_bits(is_neg_shift, &neg_exp_m_lz, &exp_m_lz);

        let shift = if ebits + 2 < big_sig_sz {
            self.zero_extend(&shift_mag, big_sig_sz - ebits - 2)
        } else if ebits + 2 > big_sig_sz {
            let upper = &shift_mag[big_sig_sz..];
            let lower: Vec<CnfLit> = shift_mag[..big_sig_sz].to_vec();
            let upper_zero = self.make_all_zero(upper);
            let cap = self.const_bv((big_sig_sz - 1) as u64, big_sig_sz);
            self.make_ite_bits(upper_zero, &lower, &cap)
        } else {
            shift_mag
        };

        let shift_limit = self.const_bv((bv_sz + 2) as u64, big_sig_sz);
        let shift_exceeds = self.make_unsigned_lt(&shift_limit, &shift);
        let capped_shift = self.make_ite_bits(shift_exceeds, &shift_limit, &shift);

        let right_shifted = self.bv_lshr(&big_sig, &capped_shift);
        let left_shifted = self.bv_shl(&big_sig, &capped_shift);
        let big_sig_shifted = self.make_ite_bits(is_neg_shift, &right_shifted, &left_shifted);

        let int_start = big_sig_sz - (bv_sz + 3);
        let int_part: Vec<CnfLit> = big_sig_shifted[int_start..big_sig_sz].to_vec();
        let last = big_sig_shifted[big_sig_sz - (bv_sz + 3)];
        let round = big_sig_shifted[big_sig_sz - (bv_sz + 4)];
        let stickies: Vec<CnfLit> = big_sig_shifted[..big_sig_sz - (bv_sz + 4)].to_vec();
        let sticky = if stickies.is_empty() {
            self.const_false()
        } else {
            self.bv_or_reduce(&stickies)
        };

        let inc = self.make_rounding_decision(rm, sgn, last, round, sticky);
        let mut inc_bv = self.const_bv(0, bv_sz + 3);
        inc_bv[0] = inc;
        let pre_rounded = self.bv_add(&int_part, &inc_bv);

        let pre_rounded_zero = self.make_all_zero(&pre_rounded);
        let ovfl = self.make_and(inc, pre_rounded_zero);

        let in_range = if !is_signed {
            let not_neg = -sgn;
            let ok_sign = self.make_or(not_neg, pre_rounded_zero);
            let not_ovfl = -ovfl;
            let max_val = if bv_sz < 64 {
                (1u64 << bv_sz) - 1
            } else {
                u64::MAX
            };
            let ul = self.const_bv(max_val, bv_sz + 3);
            let exceeds = self.make_unsigned_lt(&ul, &pre_rounded);
            let not_exceeds = -exceeds;
            let t = self.make_and(ok_sign, not_ovfl);
            self.make_and(t, not_exceeds)
        } else {
            let one_bv = self.const_bv(1, bv_sz + 3);
            let neg1 = self.bv_neg(&one_bv);
            let pre_all_neg_one = self.bv_sle(&pre_rounded, &neg1);
            let ovfl_signed = self.make_or(ovfl, pre_all_neg_one);

            let neg_pre_rounded = self.bv_neg(&pre_rounded);
            let signed_result = self.make_ite_bits(sgn, &neg_pre_rounded, &pre_rounded);
            let not_ovfl = -ovfl_signed;

            let min_signed = 1u64 << (bv_sz - 1);
            let ll_mag = self.const_bv(min_signed, bv_sz + 3);
            let ll = self.bv_neg(&ll_mag);
            let max_signed = min_signed - 1;
            let ul = self.const_bv(max_signed, bv_sz + 3);

            let below_min = self.bv_slt(&signed_result, &ll);
            let above_min = -below_min;
            let above_max = self.bv_slt(&ul, &signed_result);
            let below_max = -above_max;

            let in_bounds = self.make_and(above_min, below_max);
            self.make_and(not_ovfl, in_bounds)
        };

        let rounded: Vec<CnfLit> = if is_signed {
            let neg_pre = self.bv_neg(&pre_rounded);
            let signed_val = self.make_ite_bits(sgn, &neg_pre, &pre_rounded);
            signed_val[..bv_sz].to_vec()
        } else {
            pre_rounded[..bv_sz].to_vec()
        };

        let not_in_range = -in_range;
        let r1 = self.make_ite_bits(not_in_range, &unspec, &rounded);
        let r2 = self.make_ite_bits(x_is_zero, &v2, &r1);
        self.make_ite_bits(c1, &unspec, &r2)
    }

    /// Bit-blast equality between a BV-returning FP operation and another BV term.
    pub fn bitblast_bv_eq_with_to_bv(&mut self, to_bv_term: TermId, other_term: TermId) -> CnfLit {
        let data = self.terms.get(to_bv_term).clone();

        if let TermData::App(ref sym, ref args) = data {
            if sym.name() == "fp.to_ieee_bv" && args.len() == 1 {
                let bv_result = self.bitblast_to_ieee_bv(args[0]);
                let bv_sz = bv_result.len();
                let other_bv = self.bitblast_bv_term(other_term, bv_sz);
                return self.make_bits_equal(&bv_result, &other_bv);
            }
        }

        let (is_signed, rm, fp_term, bv_sz) = match data {
            TermData::App(ref sym, ref args) if args.len() == 2 => {
                let name = sym.name();
                let is_signed = name == "fp.to_sbv";
                let rm = self.get_rounding_mode(args[0]);
                let bv_width = match sym {
                    Symbol::Indexed(_, indices) if !indices.is_empty() => indices[0] as usize,
                    _ => match self.terms.sort(to_bv_term) {
                        Sort::BitVec(bv) => bv.width as usize,
                        _ => 32,
                    },
                };
                (is_signed, rm, args[1], bv_width)
            }
            _ => return self.const_false(),
        };

        let bv_result = self.bitblast_to_bv(fp_term, rm, bv_sz, is_signed);
        let other_bv = self.bitblast_bv_term(other_term, bv_sz);
        self.make_bits_equal(&bv_result, &other_bv)
    }

    /// Bit-blast `fp.to_ieee_bv`.
    pub fn bitblast_to_ieee_bv(&mut self, fp_term: TermId) -> Vec<CnfLit> {
        let fp = self.get_fp(fp_term);
        let exp_and_sig = Self::bv_concat(&fp.significand, &fp.exponent);
        Self::bv_concat(&exp_and_sig, &[fp.sign])
    }

    /// Get BV bits for a term (constant or cached fresh variables).
    pub(crate) fn bitblast_bv_term(&mut self, term: TermId, expected_sz: usize) -> Vec<CnfLit> {
        if let Some(val) = self.extract_bv_const(term) {
            let mut bits = Vec::with_capacity(expected_sz);
            for i in 0..expected_sz {
                let bit_val = val.bit(i as u64);
                bits.push(if bit_val {
                    self.const_true()
                } else {
                    self.const_false()
                });
            }
            bits
        } else if let Some(cached) = self.bv_term_bits.get(&term) {
            cached.clone()
        } else {
            let mut bits = Vec::with_capacity(expected_sz);
            for _ in 0..expected_sz {
                bits.push(self.fresh_var());
            }
            self.bv_term_bits.insert(term, bits.clone());
            bits
        }
    }

    /// Check if a BV term has cached bits from a prior `bitblast_bv_term` call.
    pub fn has_bv_bits(&self, term: TermId) -> bool {
        self.bv_term_bits.contains_key(&term)
    }

    /// Get the cached BV term -> CNF bit mappings.
    pub fn bv_term_bits(&self) -> &HashMap<TermId, Vec<CnfLit>> {
        &self.bv_term_bits
    }

    /// Bit-blast a BV equality `(= a b)` in the FP solver's variable space.
    pub fn bitblast_bv_eq(&mut self, a: TermId, b: TermId) -> CnfLit {
        let a_sort = self.terms.sort(a).clone();
        let bv_sz = match a_sort {
            Sort::BitVec(bvs) => bvs.width as usize,
            _ => return self.const_false(),
        };
        let a_bits = self.bitblast_bv_term(a, bv_sz);
        let b_bits = self.bitblast_bv_term(b, bv_sz);
        self.make_bits_equal(&a_bits, &b_bits)
    }
}
