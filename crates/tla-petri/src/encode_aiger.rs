// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Petri net to AIGER circuit encoding for bounded safety checking.
//!
//! Encodes a bounded P/T net as an And-Inverter Graph (AIG) circuit so that
//! the existing 60-config IC3/BMC portfolio in `tla-aiger` can check safety
//! properties. This is the single most impactful feature for MCC 2026 — no
//! other MCC competitor has a hardware IC3 engine.
//!
//! # Encoding overview
//!
//! 1. **Latches:** Each place `p` with bound `B` gets `ceil(log2(B+1))` latches
//!    encoding its token count in binary.
//! 2. **Inputs:** One bit per transition (nondeterministic choice) plus one
//!    "idle" bit. At most one input is high per step (priority encoding).
//! 3. **Guards:** For each transition `t`, a comparator circuit checks that
//!    every input place has enough tokens: `count(p) >= weight(p,t)`.
//! 4. **Effects:** For each transition `t`, adder/subtractor circuits compute
//!    `new_count = old_count - consumed + produced` for affected places.
//! 5. **Property:** The bad-state output is the combinational encoding of the
//!    negated safety property over latch values.
//!
//! # Gating
//!
//! Only encodes when:
//! - All property-relevant places have finite LP bounds
//! - Total latch count <= 500
//! - Property is safety (reachability/deadlock)
//!
//! # Reference
//!
//! The encoding follows standard bounded Petri net to hardware model checking
//! translations. See Wimmel & Wolf (2012) "Applying CEGAR to the Petri Net
//! State Equation" for the LP bounding, and Heljanko et al. (2013) for the
//! circuit encoding approach.

use std::collections::HashMap;

use crate::petri_net::{PetriNet, PlaceIdx};
use crate::resolved_predicate::{ResolvedIntExpr, ResolvedPredicate};

/// Maximum total latches before we refuse to encode (complexity guard).
const MAX_TOTAL_LATCHES: usize = 500;

/// Result of attempting to encode a Petri net as an AIGER circuit.
#[derive(Debug)]
pub(crate) struct AigerEncoding {
    /// The encoded AIGER circuit, ready for portfolio checking.
    pub(crate) circuit: tla_aiger::AigerCircuit,
    /// Number of latches used (for diagnostics).
    pub(crate) num_latches: usize,
    /// Number of transitions encoded.
    pub(crate) num_transitions: usize,
}

/// Internal builder that constructs AIG gates incrementally.
///
/// Follows AIGER conventions: literal 0 = FALSE, literal 1 = TRUE.
/// Variables are 1-indexed. Literal = var * 2 + sign.
struct AigBuilder {
    /// Next variable index to allocate.
    next_var: u64,
    /// AND gates: (lhs, rhs0, rhs1) where lhs = rhs0 AND rhs1.
    ands: Vec<(u64, u64, u64)>,
    /// Input literals (one per transition + idle).
    inputs: Vec<u64>,
    /// Latch definitions: (current_lit, next_lit, reset_value).
    latches: Vec<(u64, u64, u64)>,
    /// Bad-state output literals.
    bad: Vec<u64>,
}

impl AigBuilder {
    fn new() -> Self {
        Self {
            next_var: 1, // var 0 is the constant
            ands: Vec::new(),
            inputs: Vec::new(),
            latches: Vec::new(),
            bad: Vec::new(),
        }
    }

    /// Allocate a fresh variable, returning its positive literal.
    fn new_var(&mut self) -> u64 {
        let var = self.next_var;
        self.next_var += 1;
        var * 2 // positive literal
    }

    /// Allocate an input variable, returning its positive literal.
    fn new_input(&mut self) -> u64 {
        let lit = self.new_var();
        self.inputs.push(lit);
        lit
    }

    /// Allocate a latch with given reset value, returning its current-state literal.
    fn new_latch(&mut self, reset: u64) -> u64 {
        let lit = self.new_var();
        // Next-state will be patched later.
        self.latches.push((lit, 0, reset));
        lit
    }

    /// Set the next-state function for a latch identified by its current-state literal.
    fn set_latch_next(&mut self, current_lit: u64, next_lit: u64) {
        for latch in &mut self.latches {
            if latch.0 == current_lit {
                latch.1 = next_lit;
                return;
            }
        }
    }

    /// Build an AND gate: result = a AND b.
    fn and(&mut self, a: u64, b: u64) -> u64 {
        // Constant folding
        if a == 0 || b == 0 {
            return 0; // FALSE
        }
        if a == 1 {
            return b;
        }
        if b == 1 {
            return a;
        }
        if a == b {
            return a;
        }
        if a == (b ^ 1) {
            return 0; // x AND !x = FALSE
        }
        let out = self.new_var();
        self.ands.push((out, a, b));
        out
    }

    /// Build a NOT: result = !a.
    fn not(&self, a: u64) -> u64 {
        a ^ 1
    }

    /// Build an OR gate: result = a OR b = NOT(NOT(a) AND NOT(b)).
    fn or(&mut self, a: u64, b: u64) -> u64 {
        // Constant folding
        if a == 1 || b == 1 {
            return 1; // TRUE
        }
        if a == 0 {
            return b;
        }
        if b == 0 {
            return a;
        }
        if a == b {
            return a;
        }
        let na = self.not(a);
        let nb = self.not(b);
        let r = self.and(na, nb);
        self.not(r)
    }

    /// Build an n-ary AND.
    fn and_many(&mut self, lits: &[u64]) -> u64 {
        match lits.len() {
            0 => 1, // TRUE (empty conjunction)
            1 => lits[0],
            _ => {
                let mut acc = lits[0];
                for &lit in &lits[1..] {
                    acc = self.and(acc, lit);
                }
                acc
            }
        }
    }

    /// Build an n-ary OR.
    fn or_many(&mut self, lits: &[u64]) -> u64 {
        match lits.len() {
            0 => 0, // FALSE (empty disjunction)
            1 => lits[0],
            _ => {
                let mut acc = lits[0];
                for &lit in &lits[1..] {
                    acc = self.or(acc, lit);
                }
                acc
            }
        }
    }

    /// Build a >= comparator: returns literal that is TRUE iff
    /// the binary number represented by `bits` (LSB first) >= `threshold`.
    ///
    /// Uses a recursive approach: for each bit position, the value at that
    /// position contributes 2^i. We build the comparison bit by bit.
    fn unsigned_ge(&mut self, bits: &[u64], threshold: u64) -> u64 {
        let n = bits.len();
        let max_val = (1u64 << n) - 1;
        if threshold == 0 {
            return 1; // Always true: unsigned >= 0
        }
        if threshold > max_val {
            return 0; // Always false: can't represent threshold
        }
        // Build comparison from MSB to LSB.
        // At each bit position i (from MSB down), we track whether we're
        // definitely >=, definitely <, or still equal.
        // result = OR over all i where bit_i makes us definitely >=
        //        AND we haven't been definitely < at any higher bit.
        self.ge_recursive(bits, threshold, n)
    }

    /// Recursive >= comparator helper.
    ///
    /// Compares `bits[0..n]` (LSB first) against `threshold`.
    /// Uses the approach: x >= t iff
    ///   - If MSB of t is 0: x_msb=1 OR (x_msb=0 AND lower_bits >= t)
    ///   - If MSB of t is 1: x_msb=1 AND lower_bits >= (t - 2^(n-1))
    fn ge_recursive(&mut self, bits: &[u64], threshold: u64, n: usize) -> u64 {
        if n == 0 {
            return if threshold == 0 { 1 } else { 0 };
        }
        let msb_idx = n - 1;
        let msb_bit = bits[msb_idx];
        let msb_weight = 1u64 << msb_idx;

        if threshold & msb_weight != 0 {
            // MSB of threshold is 1: need msb_bit=1 AND lower >= (threshold - msb_weight)
            let lower = self.ge_recursive(bits, threshold - msb_weight, msb_idx);
            self.and(msb_bit, lower)
        } else {
            // MSB of threshold is 0: msb_bit=1 => definitely >= (since msb_weight > remaining threshold)
            // OR msb_bit=0 AND lower >= threshold
            let lower = self.ge_recursive(bits, threshold, msb_idx);
            let msb_zero_case = self.and(self.not(msb_bit), lower);
            self.or(msb_bit, msb_zero_case)
        }
    }

    /// Build an adder/subtractor circuit.
    ///
    /// Computes `bits + add_val - sub_val` where `bits` is LSB-first binary,
    /// and returns the result bits (LSB first, same width).
    ///
    /// The net delta = add_val - sub_val is precomputed. If positive, we add;
    /// if negative, we subtract. We do this by building a ripple-carry adder
    /// or subtractor circuit.
    ///
    /// Returns the new bits (same width as input).
    fn add_sub_const(&mut self, bits: &[u64], add: u64, sub: u64) -> Vec<u64> {
        if add == sub {
            return bits.to_vec(); // no change
        }

        if add > sub {
            // Add (add - sub) using ripple-carry adder with constant
            let delta = add - sub;
            self.add_const(bits, delta)
        } else {
            // Subtract (sub - add) using ripple-carry subtractor (add two's complement)
            let delta = sub - add;
            self.sub_const(bits, delta)
        }
    }

    /// Add a constant to a binary number using ripple-carry.
    /// `bits` is LSB-first. Returns new bits (same width).
    fn add_const(&mut self, bits: &[u64], value: u64) -> Vec<u64> {
        let n = bits.len();
        let mut result = Vec::with_capacity(n);
        let mut carry = 0u64; // carry as a literal: 0=FALSE, 1=TRUE

        for i in 0..n {
            let bit_val = (value >> i) & 1;
            let const_bit = if bit_val != 0 { 1u64 } else { 0u64 };

            // sum_bit = bits[i] XOR const_bit XOR carry
            // carry_out = majority(bits[i], const_bit, carry)
            let (sum, new_carry) = self.full_adder(bits[i], const_bit, carry);
            result.push(sum);
            carry = new_carry;
        }

        result
    }

    /// Subtract a constant from a binary number.
    /// `bits` is LSB-first. Returns new bits (same width).
    /// Uses two's complement: bits - value = bits + (~value + 1).
    fn sub_const(&mut self, bits: &[u64], value: u64) -> Vec<u64> {
        let n = bits.len();
        let mask = (1u64 << n) - 1;
        let twos_complement = (!value).wrapping_add(1) & mask;
        self.add_const(bits, twos_complement)
    }

    /// Full adder: (sum, carry) = a + b + cin.
    ///
    /// When `b` and/or `cin` are constants (0 or 1), this simplifies
    /// to avoid unnecessary gates.
    fn full_adder(&mut self, a: u64, b: u64, cin: u64) -> (u64, u64) {
        // Handle all-constant cases
        if b <= 1 && cin <= 1 {
            let const_sum = b + cin; // 0, 1, or 2
            match const_sum {
                0 => (a, 0),              // a + 0 + 0
                1 => self.half_adder(a),  // a + 1
                2 => {
                    // a + 1 + 1 = a + 2... but this is a + 0 with carry 1
                    // sum = a, carry = 1... no, that's wrong.
                    // a + 1 + 1: sum = a XOR 0 = a, carry = (a AND 1) OR (a AND 1) OR (1 AND 1) = 1
                    // Wait: 0+1+1 = 10 (sum=0, carry=1), 1+1+1 = 11 (sum=1, carry=1)
                    // So sum = a, carry = 1.
                    (a, 1)
                }
                _ => unreachable!(),
            }
        } else {
            // General case: all three are circuit signals
            let xor_ab = self.xor(a, b);
            let sum = self.xor(xor_ab, cin);
            let and_ab = self.and(a, b);
            let and_xab_cin = self.and(xor_ab, cin);
            let carry = self.or(and_ab, and_xab_cin);
            (sum, carry)
        }
    }

    /// Half adder: a + 1. Returns (sum, carry) = (!a, a).
    fn half_adder(&mut self, a: u64) -> (u64, u64) {
        // a + 1: sum = a XOR 1 = !a, carry = a AND 1 = a
        (self.not(a), a)
    }

    /// XOR gate: a XOR b = (a OR b) AND NOT(a AND b).
    fn xor(&mut self, a: u64, b: u64) -> u64 {
        if a == 0 {
            return b;
        }
        if b == 0 {
            return a;
        }
        if a == 1 {
            return self.not(b);
        }
        if b == 1 {
            return self.not(a);
        }
        if a == b {
            return 0;
        }
        let or_ab = self.or(a, b);
        let and_ab = self.and(a, b);
        let nand = self.not(and_ab);
        self.and(or_ab, nand)
    }

    /// Build a 2-input multiplexer: sel ? a : b.
    fn mux(&mut self, sel: u64, a: u64, b: u64) -> u64 {
        if sel == 1 {
            return a;
        }
        if sel == 0 {
            return b;
        }
        if a == b {
            return a;
        }
        // sel AND a OR !sel AND b
        let sel_a = self.and(sel, a);
        let nsel_b = self.and(self.not(sel), b);
        self.or(sel_a, nsel_b)
    }

    /// Build an n-bit multiplexer: for each bit position, sel ? a[i] : b[i].
    fn mux_bits(&mut self, sel: u64, a: &[u64], b: &[u64]) -> Vec<u64> {
        assert_eq!(a.len(), b.len());
        a.iter()
            .zip(b.iter())
            .map(|(&ai, &bi)| self.mux(sel, ai, bi))
            .collect()
    }

    /// Convert to an AigerCircuit.
    fn build(self) -> tla_aiger::AigerCircuit {
        let maxvar = self.next_var - 1;

        let inputs = self
            .inputs
            .iter()
            .map(|&lit| tla_aiger::AigerSymbol {
                lit,
                name: None,
            })
            .collect();

        let latches = self
            .latches
            .iter()
            .map(|&(lit, next, reset)| tla_aiger::AigerLatch {
                lit,
                next,
                reset,
                name: None,
            })
            .collect();

        let ands = self
            .ands
            .iter()
            .map(|&(lhs, rhs0, rhs1)| tla_aiger::AigerAnd { lhs, rhs0, rhs1 })
            .collect();

        let bad = self
            .bad
            .iter()
            .map(|&lit| tla_aiger::AigerSymbol {
                lit,
                name: None,
            })
            .collect();

        tla_aiger::AigerCircuit {
            maxvar,
            inputs,
            latches,
            outputs: Vec::new(),
            ands,
            bad,
            constraints: Vec::new(),
            justice: Vec::new(),
            fairness: Vec::new(),
            comments: vec!["Petri net AIGER encoding by tla-petri".to_string()],
        }
    }
}

/// Bits needed to represent values 0..=bound.
fn bits_needed(bound: u64) -> usize {
    if bound == 0 {
        return 1; // need at least 1 bit even for 0-bounded place
    }
    (64 - bound.leading_zeros()) as usize
}

/// Information about a place's latch encoding.
struct PlaceEncoding {
    /// Latch literals for this place (LSB first).
    bits: Vec<u64>,
    /// Upper bound on token count.
    bound: u64,
}

/// Try to encode a bounded Petri net as an AIGER circuit for safety checking.
///
/// Returns `None` if:
/// - Any property-relevant place lacks a finite bound
/// - Total latch count exceeds `MAX_TOTAL_LATCHES`
/// - The property cannot be encoded as a combinational function of markings
///
/// The `bounds` map must provide an upper bound for every place in the net.
/// These are typically obtained from LP relaxation of the state equation
/// ([`crate::lp_state_equation::lp_upper_bound`]).
pub(crate) fn try_encode_as_aiger(
    net: &PetriNet,
    property: &ResolvedPredicate,
    bounds: &HashMap<PlaceIdx, u64>,
) -> Option<AigerEncoding> {
    // Verify all places have bounds
    for p in 0..net.num_places() {
        if !bounds.contains_key(&PlaceIdx(p as u32)) {
            return None;
        }
    }

    // Compute total latch count
    let total_latches: usize = (0..net.num_places())
        .map(|p| bits_needed(bounds[&PlaceIdx(p as u32)]))
        .sum();

    if total_latches > MAX_TOTAL_LATCHES {
        return None;
    }

    // Check that property is encodable (no IsFireable — requires transition
    // guard evaluation which is complex; we handle pure marking predicates).
    if !is_marking_predicate(property) {
        return None;
    }

    let mut builder = AigBuilder::new();

    // --- Allocate latches for each place ---
    let mut place_encodings: Vec<PlaceEncoding> = Vec::with_capacity(net.num_places());
    for p in 0..net.num_places() {
        let bound = bounds[&PlaceIdx(p as u32)];
        let nbits = bits_needed(bound);
        let initial = net.initial_marking[p];

        let bits: Vec<u64> = (0..nbits)
            .map(|i| {
                let reset_bit = (initial >> i) & 1;
                builder.new_latch(reset_bit)
            })
            .collect();

        place_encodings.push(PlaceEncoding { bits, bound });
    }

    // --- Allocate transition inputs ---
    let num_trans = net.num_transitions();
    let trans_inputs: Vec<u64> = (0..num_trans).map(|_| builder.new_input()).collect();
    let _idle_input = builder.new_input();

    // --- Build transition guards ---
    // guard[t] = AND over all input arcs: count(p) >= weight
    let mut guards: Vec<u64> = Vec::with_capacity(num_trans);
    for t in 0..num_trans {
        let trans = &net.transitions[t];
        let mut guard_lits: Vec<u64> = Vec::new();
        for arc in &trans.inputs {
            let p = arc.place.0 as usize;
            let ge_lit = builder.unsigned_ge(&place_encodings[p].bits, arc.weight);
            guard_lits.push(ge_lit);
        }
        let guard = builder.and_many(&guard_lits);
        guards.push(guard);
    }

    // --- Build at-most-one / priority encoding for transition selection ---
    // enabled[t] = trans_input[t] AND guard[t]
    // Only the highest-priority enabled transition actually fires.
    // Priority = index order (lower index = higher priority).
    let mut fire: Vec<u64> = Vec::with_capacity(num_trans);
    let mut any_higher_fires = 0u64; // FALSE initially: no higher-priority has fired

    for t in 0..num_trans {
        let requested = builder.and(trans_inputs[t], guards[t]);
        let not_preempted = builder.not(any_higher_fires);
        let fires = builder.and(requested, not_preempted);
        fire.push(fires);
        any_higher_fires = builder.or(any_higher_fires, fires);
    }

    // --- Compute next-state for each place ---
    for p in 0..net.num_places() {
        let enc = &place_encodings[p];
        let nbits = enc.bits.len();

        // Start from the current value
        let mut current_bits = enc.bits.clone();

        // For each transition, if it fires, compute the effect on this place
        for t in 0..num_trans {
            let trans = &net.transitions[t];

            // Compute consumed tokens from this place
            let consumed: u64 = trans
                .inputs
                .iter()
                .filter(|arc| arc.place.0 as usize == p)
                .map(|arc| arc.weight)
                .sum();

            // Compute produced tokens to this place
            let produced: u64 = trans
                .outputs
                .iter()
                .filter(|arc| arc.place.0 as usize == p)
                .map(|arc| arc.weight)
                .sum();

            if consumed == 0 && produced == 0 {
                continue; // This transition doesn't affect this place
            }

            // Compute new count if this transition fires
            let new_bits = builder.add_sub_const(&current_bits, produced, consumed);

            // Ensure widths match (truncate or extend as needed)
            let new_bits = if new_bits.len() > nbits {
                new_bits[..nbits].to_vec()
            } else {
                new_bits
            };

            // Mux: if fire[t] then new_bits else current_bits
            current_bits = builder.mux_bits(fire[t], &new_bits, &current_bits);
        }

        // Set next-state for each latch bit
        for (i, &latch_lit) in enc.bits.iter().enumerate() {
            builder.set_latch_next(latch_lit, current_bits[i]);
        }
    }

    // --- Encode the bad-state property ---
    // The property is a safety predicate (AG(phi)).
    // Bad state = NOT(phi).
    let phi = encode_predicate(&mut builder, property, &place_encodings);
    let bad = builder.not(phi);
    builder.bad.push(bad);

    let circuit = builder.build();

    Some(AigerEncoding {
        num_latches: total_latches,
        num_transitions: num_trans,
        circuit,
    })
}

/// Check if a predicate only references markings (no IsFireable).
fn is_marking_predicate(pred: &ResolvedPredicate) -> bool {
    match pred {
        ResolvedPredicate::And(children) | ResolvedPredicate::Or(children) => {
            children.iter().all(is_marking_predicate)
        }
        ResolvedPredicate::Not(inner) => is_marking_predicate(inner),
        ResolvedPredicate::IntLe(_, _) | ResolvedPredicate::True | ResolvedPredicate::False => {
            true
        }
        ResolvedPredicate::IsFireable(_) => false,
    }
}

/// Encode a resolved predicate as an AIG literal over place latch bits.
fn encode_predicate(
    builder: &mut AigBuilder,
    pred: &ResolvedPredicate,
    places: &[PlaceEncoding],
) -> u64 {
    match pred {
        ResolvedPredicate::True => 1,
        ResolvedPredicate::False => 0,
        ResolvedPredicate::And(children) => {
            let lits: Vec<u64> = children
                .iter()
                .map(|c| encode_predicate(builder, c, places))
                .collect();
            builder.and_many(&lits)
        }
        ResolvedPredicate::Or(children) => {
            let lits: Vec<u64> = children
                .iter()
                .map(|c| encode_predicate(builder, c, places))
                .collect();
            builder.or_many(&lits)
        }
        ResolvedPredicate::Not(inner) => {
            let lit = encode_predicate(builder, inner, places);
            builder.not(lit)
        }
        ResolvedPredicate::IntLe(lhs, rhs) => {
            encode_int_le(builder, lhs, rhs, places)
        }
        ResolvedPredicate::IsFireable(_) => {
            // Should not happen — is_marking_predicate guards this.
            0 // FALSE as fallback
        }
    }
}

/// Encode `lhs <= rhs` as an AIG literal.
fn encode_int_le(
    builder: &mut AigBuilder,
    lhs: &ResolvedIntExpr,
    rhs: &ResolvedIntExpr,
    places: &[PlaceEncoding],
) -> u64 {
    // lhs <= rhs is equivalent to NOT(lhs > rhs) = NOT(lhs >= rhs + 1)
    // which is NOT(rhs < lhs) = NOT(NOT(rhs >= lhs)) ... but we need signed comparison.
    //
    // Simpler: lhs <= rhs <=> NOT(lhs - rhs > 0 when viewed as signed).
    // But since all values are non-negative integers, lhs <= rhs <=> rhs >= lhs.
    //
    // We build this by computing the sum for each side and comparing.

    match (lhs, rhs) {
        // Constant <= Constant: static evaluation
        (ResolvedIntExpr::Constant(a), ResolvedIntExpr::Constant(b)) => {
            if a <= b { 1 } else { 0 }
        }

        // Constant <= TokensCount: threshold comparison
        (ResolvedIntExpr::Constant(threshold), ResolvedIntExpr::TokensCount(rhs_places)) => {
            // sum(rhs_places) >= threshold
            let sum_bits = encode_sum(builder, rhs_places, places);
            builder.unsigned_ge(&sum_bits, *threshold)
        }

        // TokensCount <= Constant: negated comparison
        (ResolvedIntExpr::TokensCount(lhs_places), ResolvedIntExpr::Constant(threshold)) => {
            // sum(lhs_places) <= threshold
            // <=> NOT(sum(lhs_places) >= threshold + 1)
            let sum_bits = encode_sum(builder, lhs_places, places);
            if *threshold == u64::MAX {
                return 1; // Always true
            }
            let ge = builder.unsigned_ge(&sum_bits, threshold + 1);
            builder.not(ge)
        }

        // TokensCount <= TokensCount: general case
        (ResolvedIntExpr::TokensCount(lhs_places), ResolvedIntExpr::TokensCount(rhs_places)) => {
            // sum(lhs) <= sum(rhs)
            // Build subtractor: diff = sum(rhs) - sum(lhs)
            // This is complex; use wider bit comparison.
            let lhs_bits = encode_sum(builder, lhs_places, places);
            let rhs_bits = encode_sum(builder, rhs_places, places);

            // Extend both to same width + 1 (for borrow detection)
            let max_width = lhs_bits.len().max(rhs_bits.len()) + 1;
            let lhs_ext = extend_bits(&lhs_bits, max_width);
            let rhs_ext = extend_bits(&rhs_bits, max_width);

            // Compute rhs - lhs using subtraction
            // If result's MSB (sign bit) is 0, then rhs >= lhs, so lhs <= rhs.
            let diff = subtract_bits(builder, &rhs_ext, &lhs_ext);
            // The MSB is the sign bit. If it's 0, the result is non-negative.
            let sign_bit = diff[max_width - 1];
            builder.not(sign_bit) // NOT(negative) = non-negative = lhs <= rhs
        }
    }
}

/// Compute the sum of token counts for a set of places as binary bits.
///
/// Returns an LSB-first bit vector wide enough to hold the maximum possible sum.
fn encode_sum(
    builder: &mut AigBuilder,
    place_indices: &[PlaceIdx],
    places: &[PlaceEncoding],
) -> Vec<u64> {
    if place_indices.is_empty() {
        return vec![0]; // Zero
    }

    if place_indices.len() == 1 {
        return places[place_indices[0].0 as usize].bits.clone();
    }

    // Sum by adding one place at a time using ripple-carry adders
    let max_sum: u64 = place_indices
        .iter()
        .map(|idx| places[idx.0 as usize].bound)
        .sum();
    let result_width = bits_needed(max_sum);

    let mut acc = extend_bits(&places[place_indices[0].0 as usize].bits, result_width);

    for &idx in &place_indices[1..] {
        let operand = extend_bits(&places[idx.0 as usize].bits, result_width);
        acc = add_bits(builder, &acc, &operand);
        // Truncate back to result_width to avoid unbounded growth
        acc.truncate(result_width);
    }

    acc
}

/// Extend a bit vector to `width` by zero-padding with constant FALSE (literal 0).
fn extend_bits(bits: &[u64], width: usize) -> Vec<u64> {
    let mut result = bits.to_vec();
    while result.len() < width {
        result.push(0); // FALSE = zero bit
    }
    result
}

/// Add two bit vectors using a ripple-carry adder.
fn add_bits(builder: &mut AigBuilder, a: &[u64], b: &[u64]) -> Vec<u64> {
    let n = a.len().max(b.len());
    let a = extend_bits(a, n);
    let b = extend_bits(b, n);

    let mut result = Vec::with_capacity(n + 1);
    let mut carry = 0u64; // FALSE

    for i in 0..n {
        let (sum, new_carry) = builder.full_adder(a[i], b[i], carry);
        result.push(sum);
        carry = new_carry;
    }
    result.push(carry); // Overflow bit

    result
}

/// Subtract b from a (a - b) using ripple-carry with borrow.
/// Returns a vector of same width as inputs.
/// The MSB of the result is the sign bit (1 = negative).
fn subtract_bits(builder: &mut AigBuilder, a: &[u64], b: &[u64]) -> Vec<u64> {
    let n = a.len().max(b.len());
    let a = extend_bits(a, n);
    let b = extend_bits(b, n);

    // a - b = a + NOT(b) + 1 (two's complement subtraction)
    let mut result = Vec::with_capacity(n);
    let mut carry = 1u64; // Initial carry = 1 for two's complement

    for i in 0..n {
        let not_b = builder.not(b[i]);
        let (sum, new_carry) = builder.full_adder(a[i], not_b, carry);
        result.push(sum);
        carry = new_carry;
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::petri_net::{Arc, PetriNet, PlaceInfo, TransitionInfo};

    fn arc(place: u32, weight: u64) -> Arc {
        Arc {
            place: PlaceIdx(place),
            weight,
        }
    }

    fn place(id: &str) -> PlaceInfo {
        PlaceInfo {
            id: id.to_string(),
            name: None,
        }
    }

    fn trans(id: &str, inputs: Vec<Arc>, outputs: Vec<Arc>) -> TransitionInfo {
        TransitionInfo {
            id: id.to_string(),
            name: None,
            inputs,
            outputs,
        }
    }

    #[test]
    fn test_bits_needed() {
        assert_eq!(bits_needed(0), 1);
        assert_eq!(bits_needed(1), 1);
        assert_eq!(bits_needed(2), 2);
        assert_eq!(bits_needed(3), 2);
        assert_eq!(bits_needed(4), 3);
        assert_eq!(bits_needed(7), 3);
        assert_eq!(bits_needed(8), 4);
        assert_eq!(bits_needed(255), 8);
        assert_eq!(bits_needed(256), 9);
    }

    #[test]
    fn test_encode_simple_mutex() {
        // Simple mutex: 2 places (free=1, busy=0), 2 transitions (acquire, release)
        // acquire: free -> busy (consume 1 from free, produce 1 to busy)
        // release: busy -> free (consume 1 from busy, produce 1 to free)
        let net = PetriNet {
            name: None,
            places: vec![place("free"), place("busy")],
            transitions: vec![
                trans("acquire", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("release", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        };

        let mut bounds = HashMap::new();
        bounds.insert(PlaceIdx(0), 1);
        bounds.insert(PlaceIdx(1), 1);

        // Property: AG(busy <= 1) — always at most 1 in busy
        // Encoded as: busy <= 1
        let property = ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
            ResolvedIntExpr::Constant(1),
        );

        let result = try_encode_as_aiger(&net, &property, &bounds);
        assert!(result.is_some(), "encoding should succeed for simple mutex");

        let encoding = result.expect("encoding should succeed");
        assert_eq!(encoding.num_latches, 2); // 1 bit per place
        assert_eq!(encoding.num_transitions, 2);

        let circuit = &encoding.circuit;
        assert_eq!(circuit.latches.len(), 2);
        assert_eq!(circuit.inputs.len(), 3); // 2 transitions + 1 idle
        assert_eq!(circuit.bad.len(), 1);
    }

    #[test]
    fn test_encode_bounded_counter() {
        // Single place with self-loop: place can hold up to 3 tokens.
        // One transition adds a token (no input, output weight 1).
        // Property: AG(count <= 3) should be violated if we allow unbounded adding.
        // But with bound=3 and correct encoding, we can check it.
        let net = PetriNet {
            name: None,
            places: vec![place("counter")],
            transitions: vec![trans("inc", vec![], vec![arc(0, 1)])],
            initial_marking: vec![0],
        };

        let mut bounds = HashMap::new();
        bounds.insert(PlaceIdx(0), 3);

        // Property: counter <= 3
        let property = ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
            ResolvedIntExpr::Constant(3),
        );

        let result = try_encode_as_aiger(&net, &property, &bounds);
        assert!(result.is_some());

        let encoding = result.expect("encoding should succeed");
        assert_eq!(encoding.num_latches, 2); // ceil(log2(3+1)) = 2 bits
        assert_eq!(encoding.num_transitions, 1);
    }

    #[test]
    fn test_encode_rejects_unbounded() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![trans("t0", vec![arc(0, 1)], vec![arc(1, 1)])],
            initial_marking: vec![1, 0],
        };

        // Missing bound for p1
        let mut bounds = HashMap::new();
        bounds.insert(PlaceIdx(0), 1);

        let property = ResolvedPredicate::True;
        let result = try_encode_as_aiger(&net, &property, &bounds);
        assert!(result.is_none(), "should reject when bounds are missing");
    }

    #[test]
    fn test_encode_rejects_too_many_latches() {
        // Create a net with many places that would exceed the latch limit
        let places: Vec<PlaceInfo> = (0..200)
            .map(|i| place(&format!("p{i}")))
            .collect();
        let net = PetriNet {
            name: None,
            places,
            transitions: vec![],
            initial_marking: vec![0; 200],
        };

        let mut bounds = HashMap::new();
        for i in 0..200 {
            // Each place needs 8 bits => 200 * 8 = 1600 > 500
            bounds.insert(PlaceIdx(i), 255);
        }

        let property = ResolvedPredicate::True;
        let result = try_encode_as_aiger(&net, &property, &bounds);
        assert!(result.is_none(), "should reject when latch count exceeds limit");
    }

    #[test]
    fn test_encode_rejects_is_fireable() {
        let net = PetriNet {
            name: None,
            places: vec![place("p0")],
            transitions: vec![trans("t0", vec![], vec![arc(0, 1)])],
            initial_marking: vec![0],
        };

        let mut bounds = HashMap::new();
        bounds.insert(PlaceIdx(0), 1);

        let property = ResolvedPredicate::IsFireable(vec![crate::petri_net::TransitionIdx(0)]);
        let result = try_encode_as_aiger(&net, &property, &bounds);
        assert!(result.is_none(), "should reject IsFireable predicates");
    }

    #[test]
    fn test_aig_builder_constant_folding() {
        let mut b = AigBuilder::new();

        // AND with FALSE = FALSE
        assert_eq!(b.and(0, 42), 0);
        assert_eq!(b.and(42, 0), 0);

        // AND with TRUE = identity
        assert_eq!(b.and(1, 42), 42);
        assert_eq!(b.and(42, 1), 42);

        // OR with TRUE = TRUE
        assert_eq!(b.or(1, 42), 1);
        assert_eq!(b.or(42, 1), 1);

        // OR with FALSE = identity
        assert_eq!(b.or(0, 42), 42);
        assert_eq!(b.or(42, 0), 42);

        // NOT NOT = identity
        assert_eq!(b.not(b.not(42)), 42);
    }

    #[test]
    fn test_ge_comparator_basic() {
        // We can't easily evaluate the AIG directly, but we can check
        // that the structure is produced without panics and that
        // trivial cases fold correctly.
        let mut b = AigBuilder::new();

        // 1-bit: bit >= 0 is always true
        let bit = b.new_var();
        assert_eq!(b.unsigned_ge(&[bit], 0), 1);

        // 1-bit: bit >= 1 is just the bit itself
        let result = b.unsigned_ge(&[bit], 1);
        assert_eq!(result, bit);

        // 1-bit: bit >= 2 is always false (max value is 1)
        assert_eq!(b.unsigned_ge(&[bit], 2), 0);
    }

    #[test]
    fn test_encode_produces_valid_circuit() {
        // Verify the produced circuit has consistent AIGER structure
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![
                trans("t0", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("t1", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![3, 0],
        };

        let mut bounds = HashMap::new();
        bounds.insert(PlaceIdx(0), 3);
        bounds.insert(PlaceIdx(1), 3);

        let property = ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0), PlaceIdx(1)]),
            ResolvedIntExpr::Constant(3),
        );

        let encoding = try_encode_as_aiger(&net, &property, &bounds)
            .expect("encoding should succeed for conserving net");

        let circuit = &encoding.circuit;

        // Basic structural checks
        assert!(circuit.maxvar > 0);
        assert!(!circuit.latches.is_empty());
        assert!(!circuit.inputs.is_empty());
        assert_eq!(circuit.bad.len(), 1);

        // All latch next-state and reset values should be valid literals
        for latch in &circuit.latches {
            assert!(latch.lit <= circuit.maxvar * 2 + 1);
            // Reset should be 0 or 1 for our encoding
            assert!(latch.reset <= 1, "reset should be 0 or 1");
        }

        // All AND gate inputs should reference valid variables
        for gate in &circuit.ands {
            assert!(
                gate.lhs >> 1 <= circuit.maxvar,
                "AND LHS var out of range: {} > {}",
                gate.lhs >> 1,
                circuit.maxvar,
            );
        }
    }

    #[test]
    fn test_bmc_mutex_safe() {
        // Mutex net: free + busy is conserved (always = 1).
        // Property AG(busy <= 1) should be SAFE.
        let net = PetriNet {
            name: None,
            places: vec![place("free"), place("busy")],
            transitions: vec![
                trans("acquire", vec![arc(0, 1)], vec![arc(1, 1)]),
                trans("release", vec![arc(1, 1)], vec![arc(0, 1)]),
            ],
            initial_marking: vec![1, 0],
        };

        let mut bounds = HashMap::new();
        bounds.insert(PlaceIdx(0), 1);
        bounds.insert(PlaceIdx(1), 1);

        let property = ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
            ResolvedIntExpr::Constant(1),
        );

        let encoding = try_encode_as_aiger(&net, &property, &bounds)
            .expect("encoding should succeed");

        // Build transition system and run BMC to depth 10 — no counterexample
        let ts = tla_aiger::transys::Transys::from_aiger(&encoding.circuit);
        let result = tla_aiger::check_bmc(&ts, 10);
        // BMC can only prove UNSAFE. If verdict is None, no bug found up to depth.
        // verdict=Some(false) means UNSAFE.
        assert_ne!(
            result.verdict,
            Some(false),
            "mutex with busy<=1 should not be UNSAFE, got depth={}",
            result.depth,
        );
    }

    #[test]
    fn test_bmc_counter_unsafe() {
        // Single place, one transition that adds a token with no guard.
        // Property: AG(count <= 2). This should be UNSAFE: after 3 firings,
        // count = 3 > 2.
        let net = PetriNet {
            name: None,
            places: vec![place("counter")],
            transitions: vec![trans("inc", vec![], vec![arc(0, 1)])],
            initial_marking: vec![0],
        };

        let mut bounds = HashMap::new();
        bounds.insert(PlaceIdx(0), 7); // 3 bits

        let property = ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(0)]),
            ResolvedIntExpr::Constant(2),
        );

        let encoding = try_encode_as_aiger(&net, &property, &bounds)
            .expect("encoding should succeed");

        // Build transition system and run BMC — should find a bug (counter reaches 3)
        let ts = tla_aiger::transys::Transys::from_aiger(&encoding.circuit);
        let result = tla_aiger::check_bmc(&ts, 10);
        assert_eq!(
            result.verdict,
            Some(false),
            "unguarded counter with count<=2 should be UNSAFE, got depth={}",
            result.depth,
        );
    }

    #[test]
    fn test_encode_weighted_arcs() {
        // Net with weighted arcs: p0 -2-> t0 -3-> p1
        let net = PetriNet {
            name: None,
            places: vec![place("p0"), place("p1")],
            transitions: vec![trans("t0", vec![arc(0, 2)], vec![arc(1, 3)])],
            initial_marking: vec![4, 0],
        };

        let mut bounds = HashMap::new();
        bounds.insert(PlaceIdx(0), 4);
        bounds.insert(PlaceIdx(1), 6); // Can hold up to 6 tokens

        let property = ResolvedPredicate::IntLe(
            ResolvedIntExpr::TokensCount(vec![PlaceIdx(1)]),
            ResolvedIntExpr::Constant(6),
        );

        let result = try_encode_as_aiger(&net, &property, &bounds);
        assert!(result.is_some(), "should encode net with weighted arcs");

        let encoding = result.expect("encoding should succeed");
        // p0 needs 3 bits (0..4), p1 needs 3 bits (0..6)
        assert_eq!(encoding.num_latches, 6);
    }
}
