// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CNF gate and mux encoding helpers.

use super::*;

impl BvSolver<'_> {
    pub(super) fn const_bits(&mut self, value: u64, width: usize) -> BvBits {
        let mut bits = Vec::with_capacity(width);
        for i in 0..width {
            // `value` is a `u64`, but BV widths can exceed 64. Treat higher bits as 0.
            let bit_set = if i < u64::BITS as usize {
                (value >> i) & 1 == 1
            } else {
                false
            };
            let var = if bit_set {
                let v = self.fresh_var();
                self.add_clause(CnfClause::unit(v));
                v
            } else {
                self.fresh_false()
            };
            bits.push(var);
        }
        bits
    }

    /// Create AND gate: out = a AND b
    ///
    /// Uses structural hashing to avoid duplicate gates. (#1774)
    /// Constant propagation: if either input is known true/false, the gate
    /// is resolved without allocating a fresh variable or adding clauses.
    /// This is critical for QF_ABV where BV constants produce many
    /// known-constant bits flowing through arithmetic circuits.
    pub(super) fn mk_and(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        // Trivial simplifications
        // a AND a = a
        if a == b {
            return a;
        }
        // a AND NOT(a) = false
        if a == -b {
            return self.fresh_false();
        }
        // Constant propagation: true AND b = b, false AND b = false
        if self.is_known_true(a) {
            return b;
        }
        if self.is_known_true(b) {
            return a;
        }
        if self.is_known_false(a) {
            return a; // a is already a known-false literal
        }
        if self.is_known_false(b) {
            return b;
        }

        // Normalize key for cache lookup (commutative operation)
        let key = if a < b { (a, b) } else { (b, a) };

        // Check cache first
        if let Some(&cached) = self.and_cache.get(&key) {
            return cached;
        }

        let out = self.fresh_var();
        // out => a: (-out OR a)
        // out => b: (-out OR b)
        // a AND b => out: (-a OR -b OR out)
        self.add_clause(CnfClause::binary(-out, a));
        self.add_clause(CnfClause::binary(-out, b));
        self.add_clause(CnfClause::new(vec![-a, -b, out]));

        // Cache the result
        self.and_cache.insert(key, out);
        out
    }

    /// Create OR gate: out = a OR b
    ///
    /// Uses structural hashing to avoid duplicate gates. (#1774)
    /// Constant propagation: if either input is known true/false, the gate
    /// is resolved without allocating a fresh variable or adding clauses.
    pub(super) fn mk_or(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        // Trivial simplifications
        // a OR a = a
        if a == b {
            return a;
        }
        // a OR NOT(a) = true
        if a == -b {
            return self.fresh_true();
        }
        // Constant propagation: false OR b = b, true OR b = true
        if self.is_known_false(a) {
            return b;
        }
        if self.is_known_false(b) {
            return a;
        }
        if self.is_known_true(a) {
            return a; // a is already a known-true literal
        }
        if self.is_known_true(b) {
            return b;
        }

        // Normalize key for cache lookup (commutative operation)
        let key = if a < b { (a, b) } else { (b, a) };

        // Check cache first
        if let Some(&cached) = self.or_cache.get(&key) {
            return cached;
        }

        let out = self.fresh_var();
        // a => out: (-a OR out)
        // b => out: (-b OR out)
        // out => a OR b: (-out OR a OR b)
        self.add_clause(CnfClause::binary(-a, out));
        self.add_clause(CnfClause::binary(-b, out));
        self.add_clause(CnfClause::new(vec![-out, a, b]));

        // Cache the result
        self.or_cache.insert(key, out);
        out
    }

    /// Create XOR gate: out = a XOR b
    ///
    /// Uses structural hashing to avoid duplicate gates. (#1774)
    /// Constant propagation: false XOR b = b, true XOR b = NOT(b).
    pub(super) fn mk_xor(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        // Trivial simplifications
        // a XOR a = false
        if a == b {
            return self.fresh_false();
        }
        // a XOR NOT(a) = true
        if a == -b {
            return self.fresh_true();
        }
        // Constant propagation: false XOR b = b, true XOR b = NOT(b)
        if self.is_known_false(a) {
            return b;
        }
        if self.is_known_false(b) {
            return a;
        }
        if self.is_known_true(a) {
            return -b; // true XOR b = NOT(b)
        }
        if self.is_known_true(b) {
            return -a; // a XOR true = NOT(a)
        }

        // Normalize key for cache lookup (commutative operation)
        let key = if a < b { (a, b) } else { (b, a) };

        // Check cache first
        if let Some(&cached) = self.xor_cache.get(&key) {
            return cached;
        }

        let out = self.fresh_var();
        // XOR truth table:
        // a=0, b=0 => out=0
        // a=0, b=1 => out=1
        // a=1, b=0 => out=1
        // a=1, b=1 => out=0
        // Clauses:
        // (-a OR -b OR -out)
        // (-a OR b OR out)
        // (a OR -b OR out)
        // (a OR b OR -out)
        self.add_clause(CnfClause::new(vec![-a, -b, -out]));
        self.add_clause(CnfClause::new(vec![-a, b, out]));
        self.add_clause(CnfClause::new(vec![a, -b, out]));
        self.add_clause(CnfClause::new(vec![a, b, -out]));

        // Cache the result
        self.xor_cache.insert(key, out);
        out
    }

    /// Create XNOR gate: out = a XNOR b = NOT(a XOR b)
    pub(super) fn mk_xnor(&mut self, a: CnfLit, b: CnfLit) -> CnfLit {
        let xor = self.mk_xor(a, b);
        -xor
    }

    /// Create AND of many literals
    pub(super) fn mk_and_many(&mut self, lits: &[CnfLit]) -> CnfLit {
        if lits.is_empty() {
            return self.fresh_true();
        }
        if lits.len() == 1 {
            return lits[0];
        }

        let mut result = lits[0];
        for &lit in &lits[1..] {
            result = self.mk_and(result, lit);
        }
        result
    }

    /// Create MUX: if sel then a else b (bitwise)
    pub(super) fn bitwise_mux(&mut self, a: &BvBits, b: &BvBits, sel: CnfLit) -> BvBits {
        assert_eq!(a.len(), b.len());
        a.iter()
            .zip(b.iter())
            .map(|(&ai, &bi)| self.mk_mux(ai, bi, sel))
            .collect()
    }

    /// Create MUX: if sel then a else b
    ///
    /// Constant propagation: known selector, equal inputs, and known data
    /// inputs are resolved without allocating a fresh variable.
    pub(super) fn mk_mux(&mut self, a: CnfLit, b: CnfLit, sel: CnfLit) -> CnfLit {
        // Known selector: sel=true => a, sel=false => b
        if self.is_known_true(sel) {
            return a;
        }
        if self.is_known_false(sel) {
            return b;
        }
        // Both branches equal: result is just that value
        if a == b {
            return a;
        }
        // Branches are complements: (ite sel a (NOT a)) ≡ (sel ↔ a) ≡ XNOR(sel, a)
        // Since b = ¬a, we must use `a` (not `b`) for the XNOR.
        // Using `b` would compute XNOR(sel, ¬a) = ¬(sel ↔ a), which is inverted.
        if a == -b {
            return self.mk_xnor(sel, a);
        }
        let out = self.fresh_var();
        // out = (sel AND a) OR (NOT sel AND b)
        // Clauses:
        // (-sel OR -a OR out)  -- sel=1, a=1 => out=1
        // (-sel OR a OR -out)  -- sel=1, a=0 => out=0
        // (sel OR -b OR out)   -- sel=0, b=1 => out=1
        // (sel OR b OR -out)   -- sel=0, b=0 => out=0
        self.add_clause(CnfClause::new(vec![-sel, -a, out]));
        self.add_clause(CnfClause::new(vec![-sel, a, -out]));
        self.add_clause(CnfClause::new(vec![sel, -b, out]));
        self.add_clause(CnfClause::new(vec![sel, b, -out]));
        out
    }
}
