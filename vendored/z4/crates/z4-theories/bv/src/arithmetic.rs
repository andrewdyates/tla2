// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV function application dispatch and concat flattening.
//!
//! Routes BV operations to their bit-blasting implementations.
//! Arithmetic, bitwise, and multiplication primitives are in
//! `arithmetic_ops`.

use super::*;

impl BvSolver<'_> {
    /// Bit-blast a function application
    pub(super) fn bitblast_app(&mut self, term: TermId, sym: &Symbol, args: &[TermId]) -> BvBits {
        let name = sym.name();

        // Check if this operation should be delayed (#7015).
        // For expensive operations (mul/div/rem on wide BV with 2+ variable args),
        // allocate fresh unconstrained bits and record the operation for later
        // checking against the SAT model.
        if let Sort::BitVec(bv) = self.terms.sort(term) {
            if self.should_delay(name, args, bv.width) {
                let width = bv.width as usize;
                let mut bits = Vec::with_capacity(width);
                for _ in 0..width {
                    bits.push(self.fresh_var());
                }
                // Ensure argument bits are materialized (needed for model evaluation)
                for &arg in args {
                    if matches!(self.terms.sort(arg), Sort::BitVec(_)) {
                        let _ = self.get_bits(arg);
                    }
                }
                let op_name = match name {
                    "bvmul" => "bvmul",
                    "bvadd" => "bvadd",
                    "bvudiv" => "bvudiv",
                    "bvurem" => "bvurem",
                    "bvsdiv" => "bvsdiv",
                    "bvsrem" => "bvsrem",
                    "bvsmod" => "bvsmod",
                    _ => "unknown",
                };
                self.delayed_ops.push(DelayedBvOp {
                    term,
                    op: op_name,
                    args: args.to_vec(),
                    result_bits: bits.clone(),
                    circuit_built: false,
                    cheap_tries: 0,
                });

                // Proactive structural clauses for delayed multiplication (#7015).
                //
                // For z = x * y, encode the trailing-zero necessary condition
                // using auxiliary OR-chain variables for efficient SAT propagation.
                //
                // Define aux_j(arg) = arg_0 ∨ arg_1 ∨ ... ∨ arg_j
                // Chain: aux_0 = arg_0, aux_j = aux_{j-1} ∨ arg_j
                // Then: aux_j ∨ ¬z_j  (2 literals — efficient propagation)
                //
                // This encodes: if arg has > j trailing zeros, z_j = 0.
                // Z3 adds the equivalent (y|-y)&z = z as a small circuit.
                //
                // Also adds z_0 = x_0 ∧ y_0 (exact encoding of bit 0).
                if op_name == "bvmul" && args.len() == 2 {
                    let x_bits = self.term_to_bits.get(&args[0]).cloned();
                    let y_bits = self.term_to_bits.get(&args[1]).cloned();

                    if let (Some(xb), Some(yb)) = (x_bits, y_bits) {
                        let w = bits.len().min(xb.len()).min(yb.len());

                        // Build OR-chain and propagation clauses for each arg
                        for arg_bits in [&xb, &yb] {
                            let mut prev_aux = arg_bits[0]; // aux_0 = arg_0
                                                            // Propagation for bit 0: arg_0 ∨ ¬z_0
                            self.add_clause(CnfClause::new(vec![prev_aux, -bits[0]]));
                            for j in 1..w {
                                // aux_j = aux_{j-1} ∨ arg_j
                                let aux_j = self.fresh_var();
                                // aux_{j-1} → aux_j
                                self.add_clause(CnfClause::new(vec![-prev_aux, aux_j]));
                                // arg_j → aux_j
                                self.add_clause(CnfClause::new(vec![-arg_bits[j], aux_j]));
                                // ¬aux_{j-1} ∧ ¬arg_j → ¬aux_j
                                self.add_clause(CnfClause::new(vec![
                                    prev_aux,
                                    arg_bits[j],
                                    -aux_j,
                                ]));
                                // Propagation: aux_j ∨ ¬z_j
                                self.add_clause(CnfClause::new(vec![aux_j, -bits[j]]));
                                prev_aux = aux_j;
                            }
                        }
                        // Exact bit-0 AND gate: z_0 = x_0 ∧ y_0
                        // x_0 ∧ y_0 → z_0
                        if w > 0 {
                            self.add_clause(CnfClause::new(vec![bits[0], -xb[0], -yb[0]]));
                        }
                    }
                }

                return bits;
            }
        }

        match name {
            "bvadd" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_add(&a, &b)
            }
            "bvsub" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_sub(&a, &b)
            }
            "bvmul" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_mul(&a, &b)
            }
            "bvand" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_and(&a, &b)
            }
            "bvor" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_or(&a, &b)
            }
            "bvxor" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_xor(&a, &b)
            }
            "bvnand" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_nand(&a, &b)
            }
            "bvnor" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_nor(&a, &b)
            }
            "bvxnor" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_xnor(&a, &b)
            }
            "bvnot" => {
                let a = self.get_bits(args[0]);
                Self::bitblast_not(&a)
            }
            "bvneg" => {
                let a = self.get_bits(args[0]);
                self.bitblast_neg(&a)
            }
            "bvcomp" => {
                let a = self.get_bits(args[0]);
                let b = self.get_bits(args[1]);
                // SMT-LIB requires both operands to have the same width.
                // Guard against upstream sort mismatch (#5602).
                debug_assert_eq!(
                    a.len(),
                    b.len(),
                    "bvcomp operands have different widths: {} vs {}",
                    a.len(),
                    b.len()
                );
                if a.len() != b.len() {
                    // Fallback: return unconstrained variable rather than panic.
                    vec![self.fresh_var()]
                } else {
                    let eq = self.bitblast_eq(&a, &b);
                    vec![eq]
                }
            }
            "bvshl" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_shl(&a, &b)
            }
            "bvlshr" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_lshr(&a, &b)
            }
            "bvashr" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_ashr(&a, &b)
            }
            "bvudiv" => {
                // Share division circuit with bvurem (#4873)
                let (q, _) = self.bitblast_udiv_urem_cached(args[0], args[1]);
                q
            }
            "bvurem" => {
                // Share division circuit with bvudiv (#4873)
                let (_, r) = self.bitblast_udiv_urem_cached(args[0], args[1]);
                r
            }
            "bvsdiv" => {
                // Share signed division circuit with bvsrem (#4873)
                let (abs_q, _, sign_a, sign_b) =
                    self.bitblast_signed_div_rem_cached(args[0], args[1]);
                if abs_q.is_empty() {
                    return Vec::new();
                }
                let result_neg = self.mk_xor(sign_a, sign_b);
                self.conditional_neg(&abs_q, result_neg)
            }
            "bvsrem" => {
                // Share signed division circuit with bvsdiv (#4873)
                let (_, abs_r, sign_a, _) = self.bitblast_signed_div_rem_cached(args[0], args[1]);
                if abs_r.is_empty() {
                    return Vec::new();
                }
                self.conditional_neg(&abs_r, sign_a)
            }
            "bvsmod" => {
                let Some((a, b)) = self.get_binary_bits(args[0], args[1]) else {
                    return self.fresh_bits_for_term(term);
                };
                self.bitblast_smod(&a, &b)
            }
            "concat" => self.bitblast_concat_flattened(term),
            "extract" => {
                let x_bits = self.get_bits(args[0]);
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() >= 2 {
                        let hi = indices[0] as usize;
                        let lo = indices[1] as usize;
                        if lo <= hi && hi < x_bits.len() {
                            return x_bits[lo..=hi].to_vec();
                        }
                    }
                }
                self.fresh_bits_for_term(term)
            }
            "zero_extend" => {
                let x_bits = self.get_bits(args[0]);
                if let Symbol::Indexed(_, indices) = &sym {
                    if let Some(&i) = indices.first() {
                        let extension_bits = i as usize;
                        let mut result = x_bits;
                        let false_lit = self.fresh_false();
                        for _ in 0..extension_bits {
                            result.push(false_lit);
                        }
                        return result;
                    }
                }
                x_bits
            }
            "sign_extend" => {
                let x_bits = self.get_bits(args[0]);
                if let Symbol::Indexed(_, indices) = &sym {
                    if let Some(&i) = indices.first() {
                        let extension_bits = i as usize;
                        let mut result = x_bits.clone();
                        let sign_bit = if let Some(&bit) = x_bits.last() {
                            bit
                        } else {
                            self.fresh_false()
                        };
                        for _ in 0..extension_bits {
                            result.push(sign_bit);
                        }
                        return result;
                    }
                }
                x_bits
            }
            "repeat" => {
                let x_bits = self.get_bits(args[0]);
                let copies = if let Symbol::Indexed(_, indices) = &sym {
                    indices.first().copied().unwrap_or(1)
                } else {
                    1
                } as usize;

                if copies == 0 || x_bits.is_empty() {
                    return Vec::new();
                }
                if copies == 1 {
                    return x_bits;
                }

                let mut result = Vec::with_capacity(x_bits.len() * copies);
                for _ in 0..copies {
                    result.extend_from_slice(&x_bits);
                }
                result
            }
            "rotate_left" => {
                let x_bits = self.get_bits(args[0]);
                let n = x_bits.len();
                if n <= 1 {
                    return x_bits;
                }

                let k = if let Symbol::Indexed(_, indices) = &sym {
                    indices.first().copied().unwrap_or(0) as usize
                } else {
                    0
                } % n;

                if k == 0 {
                    return x_bits;
                }

                let mut result = Vec::with_capacity(n);
                for i in 0..n {
                    let src = (i + n - k) % n;
                    result.push(x_bits[src]);
                }
                result
            }
            "rotate_right" => {
                let x_bits = self.get_bits(args[0]);
                let n = x_bits.len();
                if n <= 1 {
                    return x_bits;
                }

                let k = if let Symbol::Indexed(_, indices) = &sym {
                    indices.first().copied().unwrap_or(0) as usize
                } else {
                    0
                } % n;

                if k == 0 {
                    return x_bits;
                }

                let mut result = Vec::with_capacity(n);
                for i in 0..n {
                    let src = (i + k) % n;
                    result.push(x_bits[src]);
                }
                result
            }
            _ => {
                let width = match self.terms.sort(term) {
                    Sort::BitVec(bv) => bv.width,
                    other => panic!("bitblast requires BV sort for {term:?}, got {other:?}"),
                };
                let mut bits = Vec::with_capacity(width as usize);
                for _ in 0..width {
                    bits.push(self.fresh_var());
                }
                bits
            }
        }
    }

    /// Flatten nested concat and bitblast in one pass.
    fn bitblast_concat_flattened(&mut self, term: TermId) -> BvBits {
        let mut stack = vec![term];
        let mut leaves = Vec::new();
        let mut total_width = 0usize;

        while let Some(t) = stack.pop() {
            match self.terms.get(t) {
                TermData::App(sym, args) if sym.name() == "concat" && !args.is_empty() => {
                    for &arg in args {
                        stack.push(arg);
                    }
                    continue;
                }
                _ => {}
            }
            let width = match self.terms.sort(t) {
                Sort::BitVec(bv) => bv.width as usize,
                _ => 0,
            };
            total_width += width;
            leaves.push(t);
        }

        let mut result = Vec::with_capacity(total_width);
        for leaf in leaves {
            let bits = self.get_bits(leaf);
            result.extend(bits);
        }
        result
    }
}
