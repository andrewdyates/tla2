// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV division, remainder, and signed modulo bit-blasting operations.

use super::*;

impl BvSolver<'_> {
    /// Bit-blast unsigned division and remainder together
    /// Returns (quotient, remainder)
    pub(crate) fn bitblast_udiv_urem(&mut self, a: &BvBits, b: &BvBits) -> (BvBits, BvBits) {
        assert_eq!(a.len(), b.len());
        let n = a.len();

        if n == 0 {
            return (Vec::new(), Vec::new());
        }

        // Restoring division:
        // rem = 0
        // for i = n-1..0:
        //   rem = (rem << 1) | a[i]
        //   if rem >= b:
        //     rem = rem - b
        //     q[i] = 1
        //   else:
        //     q[i] = 0
        //
        // For b = 0, this naturally yields q = all_ones and r = a.

        let mut rem = self.const_bits(0, n);
        let mut q_msb_first: Vec<CnfLit> = Vec::with_capacity(n);

        for i in (0..n).rev() {
            // rem = (rem << 1) | a[i]
            let mut shifted = Vec::with_capacity(n);
            shifted.push(a[i]);
            shifted.extend_from_slice(&rem[..n - 1]);
            rem = shifted;

            // rem_ge_b = (rem >= b) = NOT(rem < b)
            let rem_lt_b = self.bitblast_ult(&rem, b);
            let rem_ge_b = -rem_lt_b;

            let rem_minus_b = self.bitblast_sub(&rem, b);
            rem = self.bitwise_mux(&rem_minus_b, &rem, rem_ge_b);

            q_msb_first.push(rem_ge_b);
        }

        q_msb_first.reverse();
        (q_msb_first, rem)
    }

    /// Check if a bitvector is zero
    pub(crate) fn is_zero(&mut self, bits: &BvBits) -> CnfLit {
        // All bits must be 0
        // is_zero = NOT(bit[0] OR bit[1] OR ... OR bit[n-1])
        if bits.is_empty() {
            return self.fresh_true();
        }

        // Create OR of all bits, then negate
        let any_set = self.mk_or_many(bits);
        -any_set
    }

    /// Create OR of many literals
    pub(super) fn mk_or_many(&mut self, lits: &[CnfLit]) -> CnfLit {
        if lits.is_empty() {
            return self.fresh_false();
        }
        if lits.len() == 1 {
            return lits[0];
        }

        let mut result = lits[0];
        for &lit in &lits[1..] {
            result = self.mk_or(result, lit);
        }
        result
    }

    /// Cached unsigned division+remainder: shares one `bitblast_udiv_urem`
    /// circuit between `bvudiv(x,y)` and `bvurem(x,y)` (#4873).
    pub(super) fn bitblast_udiv_urem_cached(
        &mut self,
        a_term: TermId,
        b_term: TermId,
    ) -> (BvBits, BvBits) {
        if let Some(cached) = self.unsigned_div_cache.get(&(a_term, b_term)) {
            return cached.clone();
        }
        let a = self.get_bits(a_term);
        let b = self.get_bits(b_term);
        let result = self.bitblast_udiv_urem(&a, &b);
        self.unsigned_div_cache
            .insert((a_term, b_term), result.clone());
        result
    }

    /// Cached signed division+remainder: shares abs-value computation and
    /// the unsigned division circuit between `bvsdiv(x,y)` and `bvsrem(x,y)`
    /// (#4873). Returns (abs_quotient, abs_remainder, sign_a, sign_b).
    pub(super) fn bitblast_signed_div_rem_cached(
        &mut self,
        a_term: TermId,
        b_term: TermId,
    ) -> (BvBits, BvBits, CnfLit, CnfLit) {
        if let Some(cached) = self.signed_div_cache.get(&(a_term, b_term)) {
            return cached.clone();
        }
        let a = self.get_bits(a_term);
        let b = self.get_bits(b_term);
        let n = a.len();
        if n == 0 {
            let dummy: CnfLit = 1;
            let result = (Vec::new(), Vec::new(), dummy, dummy);
            self.signed_div_cache
                .insert((a_term, b_term), result.clone());
            return result;
        }
        let sign_a = a[n - 1];
        let sign_b = b[n - 1];
        let abs_a = self.conditional_neg(&a, sign_a);
        let abs_b = self.conditional_neg(&b, sign_b);
        let (abs_q, abs_r) = self.bitblast_udiv_urem(&abs_a, &abs_b);
        let result = (abs_q, abs_r, sign_a, sign_b);
        self.signed_div_cache
            .insert((a_term, b_term), result.clone());
        result
    }

    /// Bit-blast unsigned remainder (used by `bitblast_smod`).
    fn bitblast_urem(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        let (_q, r) = self.bitblast_udiv_urem(a, b);
        r
    }

    /// Bit-blast signed modulo.
    ///
    /// SMT-LIB semantics: sign of the result matches the divisor.
    pub(super) fn bitblast_smod(&mut self, a: &BvBits, b: &BvBits) -> BvBits {
        assert_eq!(a.len(), b.len());
        let n = a.len();
        if n == 0 {
            return Vec::new();
        }

        let sign_a = a[n - 1];
        let sign_b = b[n - 1];

        let abs_a = self.conditional_neg(a, sign_a);
        let abs_b = self.conditional_neg(b, sign_b);

        // u = abs(a) mod abs(b) (also handles b=0 via bvurem semantics)
        let u = self.bitblast_urem(&abs_a, &abs_b);
        let u_is_zero = self.is_zero(&u);
        let zero = self.const_bits(0, n);

        // If u=0 then result=0, otherwise select based on signs.
        // Cases (u != 0):
        //  a >= 0, b >= 0  =>  u
        //  a <  0, b >= 0  =>  |b| - u
        //  a >= 0, b <  0  =>  u - |b|
        //  a <  0, b <  0  =>  -u
        let abs_b_minus_u = self.bitblast_sub(&abs_b, &u);
        let u_minus_abs_b = self.bitblast_sub(&u, &abs_b);
        let neg_u = self.bitblast_neg(&u);

        // When b >= 0: if a is negative, choose |b|-u else u
        let res_b_pos = self.bitwise_mux(&abs_b_minus_u, &u, sign_a);
        // When b < 0: if a is negative, choose -u else u-|b|
        let res_b_neg = self.bitwise_mux(&neg_u, &u_minus_abs_b, sign_a);
        // Select based on sign(b)
        let res = self.bitwise_mux(&res_b_neg, &res_b_pos, sign_b);

        self.bitwise_mux(&zero, &res, u_is_zero)
    }

    /// Conditionally negate a bitvector
    /// Returns: if cond then -bits else bits
    pub(super) fn conditional_neg(&mut self, bits: &BvBits, cond: CnfLit) -> BvBits {
        let neg = self.bitblast_neg(bits);
        self.bitwise_mux(&neg, bits, cond)
    }
}
