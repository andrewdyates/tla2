// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cheap axiom checks for delayed BV operations.
//!
//! These are the per-operation checks (zero, one, invertibility, div/rem
//! special cases) that provide cheap conflict clauses before escalating
//! to full circuit construction.
//!
//! Core evaluation helpers (`eval_lit`, `eval_bits`, `eval_op`) and the
//! main `check()` method are in the parent module.

use super::*;

impl DelayedBvState {
    /// Check multiplication zero axiom. Returns clauses in BV literal space.
    pub(super) fn check_mul_zero(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        let zero = num_bigint::BigInt::from(0);
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);

        if result_val == zero {
            return None;
        }

        for &arg in &op.args {
            if let Some(bits) = self.term_to_bits.get(&arg) {
                let arg_val = self.eval_bits(bits, model, var_offset);
                if arg_val == zero {
                    // arg=0 but result!=0: clause: (some arg bit true) OR (all result bits false)
                    let mut lits: Vec<CnfLit> = Vec::new();
                    for &bit in bits {
                        lits.push(bit); // arg bit must be true
                    }
                    for &bit in &op.result_bits {
                        lits.push(-bit); // result bit must be false
                    }
                    return Some(vec![CnfClause::new(lits)]);
                }
            }
        }
        None
    }

    /// Check multiplication one axiom. Returns clauses in BV literal space.
    pub(super) fn check_mul_one(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let one = num_bigint::BigInt::from(1);

        for i in 0..2 {
            if let Some(bits) = self.term_to_bits.get(&op.args[i]) {
                let arg_val = self.eval_bits(bits, model, var_offset);
                if arg_val == one {
                    let other_idx = 1 - i;
                    if let Some(other_bits) = self.term_to_bits.get(&op.args[other_idx]) {
                        let other_val = self.eval_bits(other_bits, model, var_offset);
                        let result_val = self.eval_bits(&op.result_bits, model, var_offset);

                        if result_val == other_val {
                            return None; // Consistent
                        }

                        // Bit-wise equality: result[j] <=> other[j]
                        let mut clauses = Vec::new();
                        for (&r, &o) in op.result_bits.iter().zip(other_bits.iter()) {
                            clauses.push(CnfClause::new(vec![-r, o]));
                            clauses.push(CnfClause::new(vec![r, -o]));
                        }
                        return Some(clauses);
                    }
                }
            }
        }
        None
    }

    /// Check multiplication invertibility: (y | -y) & z = z.
    /// Returns clauses in BV literal space.
    pub(super) fn check_mul_invertibility(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }

        let width = op.result_bits.len() as u32;
        let mask = (num_bigint::BigInt::from(1) << width) - 1;
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);

        for &arg in &op.args {
            if let Some(bits) = self.term_to_bits.get(&arg) {
                let arg_val = self.eval_bits(bits, model, var_offset);
                let neg_arg = ((!&arg_val) + 1) & &mask;
                let reach_mask = (&arg_val | &neg_arg) & &mask;
                let check = &reach_mask & &result_val;

                if check != result_val {
                    // Invertibility violated: block current assignment
                    let mut lits: Vec<CnfLit> = Vec::new();
                    for &bit in &op.result_bits {
                        let val = self.eval_lit(bit, model, var_offset);
                        lits.push(if val { -bit } else { bit });
                    }
                    for &bit in bits {
                        let val = self.eval_lit(bit, model, var_offset);
                        lits.push(if val { -bit } else { bit });
                    }
                    return Some(vec![CnfClause::new(lits)]);
                }
            }
        }
        None
    }

    /// Check div-by-one axiom: if divisor=1, then quotient=dividend.
    /// Applies to both bvudiv and bvsdiv. Returns clauses in BV literal space.
    pub(super) fn check_div_by_one(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let divisor_bits = self.term_to_bits.get(&op.args[1])?;
        let divisor_val = self.eval_bits(divisor_bits, model, var_offset);
        if divisor_val != num_bigint::BigInt::from(1) {
            return None;
        }

        // divisor=1 => quotient = dividend
        let dividend_bits = self.term_to_bits.get(&op.args[0])?;
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        let dividend_val = self.eval_bits(dividend_bits, model, var_offset);
        if result_val == dividend_val {
            return None; // Already consistent
        }

        // Implicational clauses: (divisor != 1) OR (result[j] <=> dividend[j])
        // Antecedent negated: bit[0]=0 OR bit[1]=1 OR ... OR consequent
        let mut antecedent: Vec<CnfLit> = Vec::with_capacity(divisor_bits.len());
        antecedent.push(-divisor_bits[0]); // bit 0 must be true (negated)
        for &b in &divisor_bits[1..] {
            antecedent.push(b); // higher bits must be false (positive = negated false)
        }
        let mut clauses = Vec::new();
        for (&res_bit, &div_bit) in op.result_bits.iter().zip(dividend_bits.iter()) {
            let mut c1 = antecedent.clone();
            c1.push(-res_bit);
            c1.push(div_bit);
            clauses.push(CnfClause::new(c1));
            let mut c2 = antecedent.clone();
            c2.push(res_bit);
            c2.push(-div_bit);
            clauses.push(CnfClause::new(c2));
        }
        Some(clauses)
    }

    /// Check rem-by-one axiom: if divisor=1, then remainder=0.
    /// Applies to both bvurem and bvsrem. Returns clauses in BV literal space.
    pub(super) fn check_rem_by_one(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let divisor_bits = self.term_to_bits.get(&op.args[1])?;
        let divisor_val = self.eval_bits(divisor_bits, model, var_offset);
        if divisor_val != num_bigint::BigInt::from(1) {
            return None;
        }

        // divisor=1 => remainder = 0
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        if result_val == num_bigint::BigInt::from(0) {
            return None; // Already consistent
        }

        // Implicational clauses: (divisor != 1) OR (result[j] = false)
        let mut antecedent: Vec<CnfLit> = Vec::with_capacity(divisor_bits.len());
        antecedent.push(-divisor_bits[0]);
        for &b in &divisor_bits[1..] {
            antecedent.push(b);
        }
        let mut clauses = Vec::new();
        for &r_bit in &op.result_bits {
            let mut c = antecedent.clone();
            c.push(-r_bit); // result bit must be false
            clauses.push(CnfClause::new(c));
        }
        Some(clauses)
    }

    /// Check unsigned div-by-zero axiom: bvudiv(a, 0) = ~0 (all ones).
    /// SMT-LIB BV semantics. Returns clauses in BV literal space.
    pub(super) fn check_udiv_by_zero(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let divisor_bits = self.term_to_bits.get(&op.args[1])?;
        let divisor_val = self.eval_bits(divisor_bits, model, var_offset);
        if divisor_val != num_bigint::BigInt::from(0) {
            return None;
        }

        // divisor=0 => result = all ones
        let width = op.result_bits.len() as u32;
        let all_ones = (num_bigint::BigInt::from(1) << width) - 1;
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        if result_val == all_ones {
            return None; // Already consistent
        }

        // Implicational clauses: (some divisor bit true) OR (result[j] = true)
        let mut clauses = Vec::new();
        for &r_bit in &op.result_bits {
            let mut c: Vec<CnfLit> = divisor_bits.clone();
            c.push(r_bit); // result bit must be true
            clauses.push(CnfClause::new(c));
        }
        Some(clauses)
    }

    /// Check unsigned rem-by-zero axiom: bvurem(a, 0) = a (dividend).
    /// SMT-LIB BV semantics. Returns clauses in BV literal space.
    pub(super) fn check_urem_by_zero(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let divisor_bits = self.term_to_bits.get(&op.args[1])?;
        let divisor_val = self.eval_bits(divisor_bits, model, var_offset);
        if divisor_val != num_bigint::BigInt::from(0) {
            return None;
        }

        // divisor=0 => remainder = dividend
        let dividend_bits = self.term_to_bits.get(&op.args[0])?;
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        let dividend_val = self.eval_bits(dividend_bits, model, var_offset);
        if result_val == dividend_val {
            return None; // Already consistent
        }

        // Implicational clauses: (some divisor bit true) OR (result[j] <=> dividend[j])
        let mut clauses = Vec::new();
        for (&res_bit, &div_bit) in op.result_bits.iter().zip(dividend_bits.iter()) {
            let mut c1: Vec<CnfLit> = divisor_bits.clone();
            c1.push(-res_bit);
            c1.push(div_bit);
            clauses.push(CnfClause::new(c1));
            let mut c2: Vec<CnfLit> = divisor_bits.clone();
            c2.push(res_bit);
            c2.push(-div_bit);
            clauses.push(CnfClause::new(c2));
        }
        Some(clauses)
    }

    /// Check smod-by-one (or -1) axiom: bvsmod(a, 1) = 0 and bvsmod(a, -1) = 0.
    /// Returns clauses in BV literal space.
    pub(super) fn check_smod_by_one(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let divisor_bits = self.term_to_bits.get(&op.args[1])?;
        let divisor_val = self.eval_bits(divisor_bits, model, var_offset);

        let width = op.result_bits.len() as u32;
        let mask = (num_bigint::BigInt::from(1) << width) - 1;
        let one = num_bigint::BigInt::from(1);
        // -1 in two's complement = all ones
        let neg_one = &mask;

        if divisor_val != one && divisor_val != *neg_one {
            return None;
        }

        // divisor is 1 or -1 => result must be 0
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        if result_val == num_bigint::BigInt::from(0) {
            return None; // Already consistent
        }

        // Implicational: block current divisor assignment OR force result=0
        let mut divisor_block: Vec<CnfLit> = Vec::new();
        for &bit in divisor_bits.iter() {
            let val = self.eval_lit(bit, model, var_offset);
            divisor_block.push(if val { -bit } else { bit });
        }
        let mut clauses = Vec::new();
        for &r_bit in &op.result_bits {
            let mut c = divisor_block.clone();
            c.push(-r_bit); // result bit must be false (zero)
            clauses.push(CnfClause::new(c));
        }
        Some(clauses)
    }

    /// Check smod-by-zero axiom: bvsmod(a, 0) = a (dividend).
    /// SMT-LIB BV semantics. Returns clauses in BV literal space.
    pub(super) fn check_smod_by_zero(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let divisor_bits = self.term_to_bits.get(&op.args[1])?;
        let divisor_val = self.eval_bits(divisor_bits, model, var_offset);
        if divisor_val != num_bigint::BigInt::from(0) {
            return None;
        }

        // divisor=0 => result = dividend
        let dividend_bits = self.term_to_bits.get(&op.args[0])?;
        let result_val = self.eval_bits(&op.result_bits, model, var_offset);
        let dividend_val = self.eval_bits(dividend_bits, model, var_offset);
        if result_val == dividend_val {
            return None; // Already consistent
        }

        // Implicational clauses: (some divisor bit true) OR (result[j] <=> dividend[j])
        let width = op.result_bits.len().min(dividend_bits.len());
        let mut clauses = Vec::new();
        for (&rb, &db) in op.result_bits[..width].iter().zip(&dividend_bits[..width]) {
            let mut c1 = divisor_bits.clone();
            c1.push(-rb);
            c1.push(db);
            clauses.push(CnfClause::new(c1));
            let mut c2 = divisor_bits.clone();
            c2.push(rb);
            c2.push(-db);
            clauses.push(CnfClause::new(c2));
        }
        Some(clauses)
    }

    /// Check add-by-zero axiom: bvadd(a, 0) = a or bvadd(0, b) = b.
    /// Returns clauses in BV literal space.
    pub(super) fn check_add_zero(
        &self,
        op_idx: usize,
        model: &[bool],
        var_offset: i32,
    ) -> Option<Vec<CnfClause>> {
        let op = &self.delayed_ops[op_idx];
        if op.args.len() != 2 {
            return None;
        }
        let zero = num_bigint::BigInt::from(0);

        for i in 0..2 {
            if let Some(bits) = self.term_to_bits.get(&op.args[i]) {
                let arg_val = self.eval_bits(bits, model, var_offset);
                if arg_val == zero {
                    let other_idx = 1 - i;
                    if let Some(other_bits) = self.term_to_bits.get(&op.args[other_idx]) {
                        let other_val = self.eval_bits(other_bits, model, var_offset);
                        let result_val = self.eval_bits(&op.result_bits, model, var_offset);

                        if result_val == other_val {
                            return None; // Consistent
                        }

                        // arg=0 => result = other: antecedent negation of all-zero
                        let mut antecedent: Vec<CnfLit> = Vec::new();
                        for &b in bits.iter() {
                            antecedent.push(b); // positive = "some bit is true"
                        }
                        let width = op.result_bits.len().min(other_bits.len());
                        let mut clauses = Vec::new();
                        for (&rb, &ob) in op.result_bits[..width].iter().zip(&other_bits[..width]) {
                            let mut c1 = antecedent.clone();
                            c1.push(-rb);
                            c1.push(ob);
                            clauses.push(CnfClause::new(c1));
                            let mut c2 = antecedent.clone();
                            c2.push(rb);
                            c2.push(-ob);
                            clauses.push(CnfClause::new(c2));
                        }
                        return Some(clauses);
                    }
                }
            }
        }
        None
    }
}
