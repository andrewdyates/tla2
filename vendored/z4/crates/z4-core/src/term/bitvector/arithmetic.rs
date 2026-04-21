// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl TermStore {
    /// Create bitvector addition with constant folding and simplifications
    ///
    /// Simplifications:
    /// - Constant folding: bvadd(#x01, #x02) → #x03
    /// - Identity: bvadd(x, 0) → x, bvadd(0, x) → x
    pub fn mk_bvadd(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvadd", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            let result = Self::bv_mask(&(v1 + v2), w1);
            return self.mk_bitvec(result, w1);
        }

        // Identity: x + 0 = x
        if let Some((v, _)) = self.get_bitvec(b) {
            if v.is_zero() {
                return a;
            }
        }
        if let Some((v, _)) = self.get_bitvec(a) {
            if v.is_zero() {
                return b;
            }
        }

        self.mk_bv_binary_app("bvadd", args, width)
    }

    /// Create bitvector subtraction with constant folding and simplifications
    ///
    /// Simplifications:
    /// - Constant folding: bvsub(#x03, #x01) → #x02
    /// - Identity: bvsub(x, 0) → x
    /// - Self-subtraction: bvsub(x, x) → 0
    pub fn mk_bvsub(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvsub", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };

        // Constant folding (subtraction wraps around)
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            let modulus = BigInt::one() << w1;
            let result = Self::bv_mask(&((v1 - v2) % &modulus + &modulus), w1);
            return self.mk_bitvec(result, w1);
        }

        // Identity: x - 0 = x
        if let Some((v, _)) = self.get_bitvec(b) {
            if v.is_zero() {
                return a;
            }
        }

        // Self-subtraction: x - x = 0
        if a == b {
            return self.mk_bitvec(BigInt::zero(), width);
        }

        self.mk_bv_binary_app("bvsub", args, width)
    }

    /// Create bitvector multiplication with constant folding and simplifications
    ///
    /// Simplifications:
    /// - Constant folding: bvmul(#x02, #x03) → #x06
    /// - Zero: bvmul(x, 0) → 0, bvmul(0, x) → 0
    /// - Identity: bvmul(x, 1) → x, bvmul(1, x) → x
    /// - Power-of-2 multiply to shift (mul2concat):
    ///   bvmul(x, 2^k) → concat(extract(x, n-k-1, 0), bv_zero(k))
    ///   Eliminates multiplier circuit for power-of-2 constants.
    ///   Reference: Z3 bv_rewriter.cpp:2483-2492
    pub fn mk_bvmul(&mut self, args: Vec<TermId>) -> TermId {
        let (a, b, width, args) = match self.prepare_bv_binary_op("bvmul", args) {
            Ok(parts) => parts,
            Err(fallback) => return fallback,
        };
        let zero = BigInt::zero();
        let one = BigInt::one();

        // Constant folding
        if let (Some((v1, w1)), Some((v2, _))) = (self.get_bitvec(a), self.get_bitvec(b)) {
            let result = Self::bv_mask(&(v1 * v2), w1);
            return self.mk_bitvec(result, w1);
        }

        // Zero: x * 0 = 0, Identity: x * 1 = x, Power-of-2: x * 2^k = shl(x, k)
        if let Some((v, _)) = self.get_bitvec(b) {
            if *v == zero {
                return self.mk_bitvec(zero, width);
            }
            if *v == one {
                return a;
            }
            // mul2concat: if v is a power of 2, rewrite to shift-left
            if let Some(k) = Self::bv_log2_exact(v) {
                if k >= width {
                    return self.mk_bitvec(BigInt::zero(), width);
                }
                // bvmul(x, 2^k) → concat(extract(x, n-k-1, 0), bv_zero(k))
                let extracted = self.mk_bvextract(width - k - 1, 0, a);
                let zero_bits = self.mk_bitvec(BigInt::zero(), k);
                return self.mk_bvconcat(vec![extracted, zero_bits]);
            }
        }
        if let Some((v, _)) = self.get_bitvec(a) {
            if *v == zero {
                return self.mk_bitvec(zero, width);
            }
            if *v == one {
                return b;
            }
            // mul2concat: if v is a power of 2, rewrite to shift-left
            if let Some(k) = Self::bv_log2_exact(v) {
                if k >= width {
                    return self.mk_bitvec(BigInt::zero(), width);
                }
                // bvmul(2^k, x) → concat(extract(x, n-k-1, 0), bv_zero(k))
                let extracted = self.mk_bvextract(width - k - 1, 0, b);
                let zero_bits = self.mk_bitvec(BigInt::zero(), k);
                return self.mk_bvconcat(vec![extracted, zero_bits]);
            }
        }

        self.mk_bv_binary_app("bvmul", args, width)
    }
}
