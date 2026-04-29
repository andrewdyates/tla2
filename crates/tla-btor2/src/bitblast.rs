// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! BTOR2 to AIGER bit-blasting translator.
//!
//! Converts a word-level BTOR2 program into a bit-level AIGER circuit by
//! expanding each N-bit bitvector variable into N boolean (1-bit) AIG signals.
//! BTOR2 operations become networks of AND-inverter gates.
//!
//! This enables the fast SAT-based IC3/PDR engine (tla-aiger) to solve narrow
//! bitvector benchmarks that are slow via the CHC path.
//!
//! Supported operations:
//! - Boolean/bitwise: not, and, or, xor, nand, nor, xnor
//! - Comparison: eq, neq, ult, ulte, ugt, ugte, slt, slte, sgt, sgte
//! - Arithmetic: add, sub, neg, inc, dec
//! - Indexing: slice, uext, sext, concat
//! - Control: ite
//! - Reduction: redand, redor, redxor
//! - Constants: zero, one, ones, const, constd, consth
//!
//! Not yet supported (returns error):
//! - Multiplication, division, remainder (mul, udiv, sdiv, urem, srem, smod)
//! - Array operations (read, write)
//! - Overflow detection (saddo, sdivo, smulo, ssubo, uaddo, umulo, usubo)
//! - Rotate (rol, ror)
//! - Shift (sll, srl, sra) — requires mux-based barrel shifter

use std::collections::HashMap;

use crate::error::Btor2Error;
use crate::types::{Btor2Node, Btor2Program, Btor2Sort, NodeId};

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Result of bit-blasting: an AIGER-compatible circuit representation.
///
/// Uses the same literal encoding as AIGER: variable = lit/2, negated = lit%2.
/// Literal 0 = constant FALSE, literal 1 = constant TRUE.
#[derive(Debug, Clone)]
pub struct BitblastedCircuit {
    /// Maximum variable index (all vars in 1..=max_var).
    pub max_var: u64,
    /// Input literals (one per bit of each BTOR2 input). Always even.
    pub inputs: Vec<u64>,
    /// Latch definitions: (current_lit, next_lit, reset_value).
    /// current_lit is always even (positive literal for the latch variable).
    /// reset_value: 0 = reset to 0, 1 = reset to 1, current_lit = nondeterministic.
    pub latches: Vec<(u64, u64, u64)>,
    /// AND gates: (lhs, rhs0, rhs1) where lhs = rhs0 AND rhs1.
    /// lhs is always even.
    pub ands: Vec<(u64, u64, u64)>,
    /// Bad-state property literals (one per BTOR2 `bad` property).
    pub bad: Vec<u64>,
    /// Constraint literals (one per BTOR2 `constraint`).
    pub constraints: Vec<u64>,
}

/// Bit-blast a BTOR2 program into an AIGER-compatible circuit.
///
/// Returns an error if the program uses unsupported operations (e.g., arrays,
/// multiplication) or has bitvectors wider than `max_width` bits.
pub fn bitblast(program: &Btor2Program, max_width: u32) -> Result<BitblastedCircuit, Btor2Error> {
    let mut ctx = BitblastContext::new(max_width);
    ctx.translate(program)?;
    Ok(ctx.finish())
}

/// Check if a BTOR2 program is eligible for bit-blasting.
///
/// Returns `Ok(max_bv_width)` if all operations are supported and the maximum
/// bitvector width does not exceed `max_width`. Returns `Err` otherwise.
pub fn bitblast_eligible(program: &Btor2Program, max_width: u32) -> Result<u32, String> {
    let mut max_bv = 0u32;

    for line in &program.lines {
        // Check sort widths
        if let Some(sort) = program.sorts.get(&line.sort_id) {
            match sort {
                Btor2Sort::BitVec(w) => {
                    if *w > max_width {
                        return Err(format!("bitvector width {w} exceeds max_width {max_width}"));
                    }
                    max_bv = max_bv.max(*w);
                }
                Btor2Sort::Array { .. } => {
                    return Err("array sorts not supported for bit-blasting".into());
                }
            }
        }

        // Check for unsupported operations
        match &line.node {
            Btor2Node::Mul
            | Btor2Node::UDiv
            | Btor2Node::SDiv
            | Btor2Node::URem
            | Btor2Node::SRem
            | Btor2Node::SMod => {
                return Err(format!(
                    "unsupported arithmetic op {:?} for bit-blasting",
                    line.node
                ));
            }
            Btor2Node::Read | Btor2Node::Write => {
                return Err("array operations not supported for bit-blasting".into());
            }
            Btor2Node::Saddo
            | Btor2Node::Sdivo
            | Btor2Node::Smulo
            | Btor2Node::Ssubo
            | Btor2Node::Uaddo
            | Btor2Node::Umulo
            | Btor2Node::Usubo => {
                return Err("overflow detection not yet supported for bit-blasting".into());
            }
            Btor2Node::Rol | Btor2Node::Ror => {
                return Err("rotate not yet supported for bit-blasting".into());
            }
            Btor2Node::Sll | Btor2Node::Srl | Btor2Node::Sra => {
                return Err("shift not yet supported for bit-blasting".into());
            }
            _ => {}
        }
    }

    Ok(max_bv)
}

// ---------------------------------------------------------------------------
// Internal context
// ---------------------------------------------------------------------------

/// A bitvector signal: a vector of AIGER literals (LSB first).
type BvSignal = Vec<u64>;

struct BitblastContext {
    /// Next available variable index.
    next_var: u64,
    /// Maximum bitvector width allowed.
    max_width: u32,
    /// Maps BTOR2 node ID to its bit-blasted signal (vector of AIGER lits).
    signals: HashMap<NodeId, BvSignal>,
    /// AIGER inputs (flat list of input literals).
    inputs: Vec<u64>,
    /// Latch definitions.
    latches: Vec<(u64, u64, u64)>,
    /// AND gate definitions.
    ands: Vec<(u64, u64, u64)>,
    /// Bad-state property literals.
    bad: Vec<u64>,
    /// Constraint literals.
    constraints: Vec<u64>,
    /// Maps BTOR2 state node ID to latch bit literals (current state).
    state_lits: HashMap<NodeId, BvSignal>,
}

impl BitblastContext {
    fn new(max_width: u32) -> Self {
        BitblastContext {
            next_var: 1, // Var 0 is reserved for constant FALSE
            max_width,
            signals: HashMap::new(),
            inputs: Vec::new(),
            latches: Vec::new(),
            ands: Vec::new(),
            bad: Vec::new(),
            constraints: Vec::new(),
            state_lits: HashMap::new(),
        }
    }

    /// Allocate a fresh variable and return its positive literal.
    fn alloc_var(&mut self) -> u64 {
        let lit = self.next_var << 1;
        self.next_var += 1;
        lit
    }

    /// Negate a literal.
    #[inline]
    fn neg(lit: u64) -> u64 {
        lit ^ 1
    }

    /// Create an AND gate: returns lhs literal where lhs = a AND b.
    fn mk_and(&mut self, a: u64, b: u64) -> u64 {
        // Constant propagation
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
        if a == Self::neg(b) {
            return 0; // a AND !a = FALSE
        }

        let lhs = self.alloc_var();
        self.ands.push((lhs, a, b));
        lhs
    }

    /// Create an OR gate: a OR b = NOT(NOT(a) AND NOT(b)).
    fn mk_or(&mut self, a: u64, b: u64) -> u64 {
        // Constant propagation
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
        if a == Self::neg(b) {
            return 1; // a OR !a = TRUE
        }

        Self::neg(self.mk_and(Self::neg(a), Self::neg(b)))
    }

    /// Create an XOR gate: a XOR b = (a AND !b) OR (!a AND b).
    fn mk_xor(&mut self, a: u64, b: u64) -> u64 {
        if a == b {
            return 0;
        }
        if a == Self::neg(b) {
            return 1;
        }
        if a == 0 {
            return b;
        }
        if a == 1 {
            return Self::neg(b);
        }
        if b == 0 {
            return a;
        }
        if b == 1 {
            return Self::neg(a);
        }

        let and1 = self.mk_and(a, Self::neg(b));
        let and2 = self.mk_and(Self::neg(a), b);
        self.mk_or(and1, and2)
    }

    /// Create a MUX: if sel then a else b.
    fn mk_mux(&mut self, sel: u64, a: u64, b: u64) -> u64 {
        if sel == 1 {
            return a;
        }
        if sel == 0 {
            return b;
        }
        if a == b {
            return a;
        }

        // mux = (sel AND a) OR (!sel AND b)
        let t = self.mk_and(sel, a);
        let f = self.mk_and(Self::neg(sel), b);
        self.mk_or(t, f)
    }

    /// Get the sort width for a BTOR2 line.
    fn sort_width(&self, program: &Btor2Program, sort_id: i64) -> Result<u32, Btor2Error> {
        match program.sorts.get(&sort_id) {
            Some(Btor2Sort::BitVec(w)) => Ok(*w),
            Some(Btor2Sort::Array { .. }) => Err(Btor2Error::ParseError {
                line: 0,
                message: "array sort not supported in bit-blasting".into(),
            }),
            None => Err(Btor2Error::ParseError {
                line: 0,
                message: format!("undefined sort {sort_id}"),
            }),
        }
    }

    /// Get the signal for a BTOR2 node reference (may be negated).
    fn get_signal(&self, node_ref: NodeId) -> Result<BvSignal, Btor2Error> {
        let abs_id = node_ref.unsigned_abs() as i64;
        let signal = self
            .signals
            .get(&abs_id)
            .ok_or_else(|| Btor2Error::ParseError {
                line: 0,
                message: format!("signal for node {abs_id} not computed yet"),
            })?;

        if node_ref < 0 {
            // Negation: bitwise NOT of all bits
            Ok(signal.iter().map(|&lit| Self::neg(lit)).collect())
        } else {
            Ok(signal.clone())
        }
    }

    /// Translate the entire BTOR2 program.
    fn translate(&mut self, program: &Btor2Program) -> Result<(), Btor2Error> {
        // First pass: allocate variables for inputs and states.
        for line in &program.lines {
            match &line.node {
                Btor2Node::Input(sort_id, _) => {
                    let width = self.sort_width(program, *sort_id)?;
                    if width > self.max_width {
                        return Err(Btor2Error::ParseError {
                            line: 0,
                            message: format!("input width {width} exceeds max {}", self.max_width),
                        });
                    }
                    let mut bits = Vec::with_capacity(width as usize);
                    for _ in 0..width {
                        let lit = self.alloc_var();
                        self.inputs.push(lit);
                        bits.push(lit);
                    }
                    self.signals.insert(line.id, bits);
                }
                Btor2Node::State(sort_id, _) => {
                    let width = self.sort_width(program, *sort_id)?;
                    if width > self.max_width {
                        return Err(Btor2Error::ParseError {
                            line: 0,
                            message: format!("state width {width} exceeds max {}", self.max_width),
                        });
                    }
                    let mut bits = Vec::with_capacity(width as usize);
                    for _ in 0..width {
                        let lit = self.alloc_var();
                        bits.push(lit);
                    }
                    self.state_lits.insert(line.id, bits.clone());
                    self.signals.insert(line.id, bits);
                }
                _ => {}
            }
        }

        // Second pass: translate operations in source order.
        // We need init/next info collected after computing all signals.
        let mut inits: Vec<(NodeId, NodeId, i64)> = Vec::new(); // (sort_id, state_id, value_ref)
        let mut nexts: Vec<(NodeId, NodeId, i64)> = Vec::new(); // (sort_id, state_id, next_ref)

        for line in &program.lines {
            match &line.node {
                // Skip sorts, inputs, states (handled above).
                Btor2Node::SortBitVec(_)
                | Btor2Node::SortArray(_, _)
                | Btor2Node::Input(_, _)
                | Btor2Node::State(_, _) => {}

                // Init and Next: defer until all signals are computed.
                Btor2Node::Init(sort_id, state_id, value_ref) => {
                    inits.push((*sort_id, *state_id, *value_ref));
                }
                Btor2Node::Next(sort_id, state_id, next_ref) => {
                    nexts.push((*sort_id, *state_id, *next_ref));
                }

                // Constants
                Btor2Node::Zero => {
                    let width = self.sort_width(program, line.sort_id)?;
                    self.signals.insert(line.id, vec![0u64; width as usize]);
                }
                Btor2Node::One => {
                    let width = self.sort_width(program, line.sort_id)?;
                    let mut bits = vec![0u64; width as usize];
                    bits[0] = 1; // LSB = 1
                    self.signals.insert(line.id, bits);
                }
                Btor2Node::Ones => {
                    let width = self.sort_width(program, line.sort_id)?;
                    self.signals.insert(line.id, vec![1u64; width as usize]);
                }
                Btor2Node::Const(s) => {
                    let bits = self.const_from_binary(s);
                    self.signals.insert(line.id, bits);
                }
                Btor2Node::ConstD(s) => {
                    let width = self.sort_width(program, line.sort_id)?;
                    let bits = self.const_from_decimal(s, width)?;
                    self.signals.insert(line.id, bits);
                }
                Btor2Node::ConstH(s) => {
                    let width = self.sort_width(program, line.sort_id)?;
                    let bits = self.const_from_hex(s, width)?;
                    self.signals.insert(line.id, bits);
                }

                // Bitwise unary
                Btor2Node::Not => {
                    let a = self.get_signal(line.args[0])?;
                    let result: BvSignal = a.iter().map(|&lit| Self::neg(lit)).collect();
                    self.signals.insert(line.id, result);
                }
                Btor2Node::Neg => {
                    // Two's complement negation: ~a + 1
                    let a = self.get_signal(line.args[0])?;
                    let not_a: BvSignal = a.iter().map(|&lit| Self::neg(lit)).collect();
                    let one = self.const_one(a.len() as u32);
                    let result = self.add_signals(&not_a, &one);
                    self.signals.insert(line.id, result);
                }
                Btor2Node::Inc => {
                    let a = self.get_signal(line.args[0])?;
                    let one = self.const_one(a.len() as u32);
                    let result = self.add_signals(&a, &one);
                    self.signals.insert(line.id, result);
                }
                Btor2Node::Dec => {
                    let a = self.get_signal(line.args[0])?;
                    let ones = vec![1u64; a.len()]; // all-ones = -1 in two's complement
                    let result = self.add_signals(&a, &ones);
                    self.signals.insert(line.id, result);
                }

                // Reduction ops (produce 1-bit result)
                Btor2Node::Redand => {
                    let a = self.get_signal(line.args[0])?;
                    let result = self.reduce_and(&a);
                    self.signals.insert(line.id, vec![result]);
                }
                Btor2Node::Redor => {
                    let a = self.get_signal(line.args[0])?;
                    let result = self.reduce_or(&a);
                    self.signals.insert(line.id, vec![result]);
                }
                Btor2Node::Redxor => {
                    let a = self.get_signal(line.args[0])?;
                    let result = self.reduce_xor(&a);
                    self.signals.insert(line.id, vec![result]);
                }

                // Bitwise binary ops
                Btor2Node::And => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    let result = self.bitwise_and(&a, &b);
                    self.signals.insert(line.id, result);
                }
                Btor2Node::Or => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    let result = self.bitwise_or(&a, &b);
                    self.signals.insert(line.id, result);
                }
                Btor2Node::Xor => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    let result = self.bitwise_xor(&a, &b);
                    self.signals.insert(line.id, result);
                }
                Btor2Node::Nand => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    let and = self.bitwise_and(&a, &b);
                    let result: BvSignal = and.iter().map(|&lit| Self::neg(lit)).collect();
                    self.signals.insert(line.id, result);
                }
                Btor2Node::Nor => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    let or = self.bitwise_or(&a, &b);
                    let result: BvSignal = or.iter().map(|&lit| Self::neg(lit)).collect();
                    self.signals.insert(line.id, result);
                }
                Btor2Node::Xnor => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    let xor = self.bitwise_xor(&a, &b);
                    let result: BvSignal = xor.iter().map(|&lit| Self::neg(lit)).collect();
                    self.signals.insert(line.id, result);
                }

                // Arithmetic
                Btor2Node::Add => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    let result = self.add_signals(&a, &b);
                    self.signals.insert(line.id, result);
                }
                Btor2Node::Sub => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    let result = self.sub_signals(&a, &b);
                    self.signals.insert(line.id, result);
                }

                // Comparison (produce 1-bit result)
                Btor2Node::Eq => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    let result = self.eq_signals(&a, &b);
                    self.signals.insert(line.id, vec![result]);
                }
                Btor2Node::Neq => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    let eq = self.eq_signals(&a, &b);
                    self.signals.insert(line.id, vec![Self::neg(eq)]);
                }
                Btor2Node::Ult => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    let result = self.ult_signals(&a, &b);
                    self.signals.insert(line.id, vec![result]);
                }
                Btor2Node::Ulte => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    // a <= b  iff  !(b < a)
                    let b_lt_a = self.ult_signals(&b, &a);
                    self.signals.insert(line.id, vec![Self::neg(b_lt_a)]);
                }
                Btor2Node::Ugt => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    // a > b  iff  b < a
                    let result = self.ult_signals(&b, &a);
                    self.signals.insert(line.id, vec![result]);
                }
                Btor2Node::Ugte => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    // a >= b  iff  !(a < b)
                    let a_lt_b = self.ult_signals(&a, &b);
                    self.signals.insert(line.id, vec![Self::neg(a_lt_b)]);
                }
                Btor2Node::Slt => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    let result = self.slt_signals(&a, &b);
                    self.signals.insert(line.id, vec![result]);
                }
                Btor2Node::Slte => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    // a <= b  iff  !(b < a)
                    let b_lt_a = self.slt_signals(&b, &a);
                    self.signals.insert(line.id, vec![Self::neg(b_lt_a)]);
                }
                Btor2Node::Sgt => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    let result = self.slt_signals(&b, &a);
                    self.signals.insert(line.id, vec![result]);
                }
                Btor2Node::Sgte => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    let a_lt_b = self.slt_signals(&a, &b);
                    self.signals.insert(line.id, vec![Self::neg(a_lt_b)]);
                }

                // Boolean/1-bit ops
                Btor2Node::Iff => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    // iff = XNOR for 1-bit
                    let xor = self.bitwise_xor(&a, &b);
                    let result: BvSignal = xor.iter().map(|&lit| Self::neg(lit)).collect();
                    self.signals.insert(line.id, result);
                }
                Btor2Node::Implies => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    // a implies b = !a OR b
                    let not_a: BvSignal = a.iter().map(|&lit| Self::neg(lit)).collect();
                    let result = self.bitwise_or(&not_a, &b);
                    self.signals.insert(line.id, result);
                }

                // Concatenation
                Btor2Node::Concat => {
                    let a = self.get_signal(line.args[0])?;
                    let b = self.get_signal(line.args[1])?;
                    // BTOR2 concat: result = a ## b, where b is lower bits.
                    // Our BvSignal is LSB-first, so result = b ++ a.
                    let mut result = b;
                    result.extend_from_slice(&a);
                    self.signals.insert(line.id, result);
                }

                // Slice
                Btor2Node::Slice(upper, lower) => {
                    let a = self.get_signal(line.args[0])?;
                    let lo = *lower as usize;
                    let hi = *upper as usize;
                    let result = a[lo..=hi].to_vec();
                    self.signals.insert(line.id, result);
                }

                // Extension
                Btor2Node::Uext(extra) => {
                    let a = self.get_signal(line.args[0])?;
                    let mut result = a;
                    // Zero-extend: pad with 0 (FALSE literal) at MSB.
                    result.extend(std::iter::repeat(0u64).take(*extra as usize));
                    self.signals.insert(line.id, result);
                }
                Btor2Node::Sext(extra) => {
                    let a = self.get_signal(line.args[0])?;
                    let sign_bit = *a.last().unwrap_or(&0);
                    let mut result = a;
                    // Sign-extend: replicate MSB.
                    result.extend(std::iter::repeat(sign_bit).take(*extra as usize));
                    self.signals.insert(line.id, result);
                }

                // If-then-else
                Btor2Node::Ite => {
                    let cond = self.get_signal(line.args[0])?;
                    let then_sig = self.get_signal(line.args[1])?;
                    let else_sig = self.get_signal(line.args[2])?;
                    let sel = cond[0]; // condition is 1-bit
                    let mut result = Vec::with_capacity(then_sig.len());
                    for i in 0..then_sig.len() {
                        result.push(self.mk_mux(sel, then_sig[i], else_sig[i]));
                    }
                    self.signals.insert(line.id, result);
                }

                // Properties
                Btor2Node::Bad(cond_ref) => {
                    let sig = self.get_signal(*cond_ref)?;
                    self.bad.push(sig[0]); // bad is 1-bit
                }
                Btor2Node::Constraint(cond_ref) => {
                    let sig = self.get_signal(*cond_ref)?;
                    self.constraints.push(sig[0]); // constraint is 1-bit
                }
                Btor2Node::Fair(_) | Btor2Node::Justice(_) | Btor2Node::Output(_) => {
                    // Not needed for safety checking — skip.
                }

                // Unsupported ops — should have been caught by eligibility check.
                Btor2Node::Mul
                | Btor2Node::UDiv
                | Btor2Node::SDiv
                | Btor2Node::URem
                | Btor2Node::SRem
                | Btor2Node::SMod
                | Btor2Node::Read
                | Btor2Node::Write
                | Btor2Node::Saddo
                | Btor2Node::Sdivo
                | Btor2Node::Smulo
                | Btor2Node::Ssubo
                | Btor2Node::Uaddo
                | Btor2Node::Umulo
                | Btor2Node::Usubo
                | Btor2Node::Rol
                | Btor2Node::Ror
                | Btor2Node::Sll
                | Btor2Node::Srl
                | Btor2Node::Sra => {
                    return Err(Btor2Error::ParseError {
                        line: 0,
                        message: format!("unsupported operation {:?} in bit-blasting", line.node),
                    });
                }
            }
        }

        // Process init constraints: set latch reset values.
        // Default: all latches reset to 0.
        let state_ids: Vec<NodeId> = self.state_lits.keys().copied().collect();
        let mut latch_inits: HashMap<NodeId, BvSignal> = HashMap::new();

        for &state_id in &state_ids {
            let width = self.state_lits[&state_id].len();
            latch_inits.insert(state_id, vec![0u64; width]);
        }

        for (_, state_id, value_ref) in &inits {
            let value_sig = self.get_signal(*value_ref)?;
            latch_inits.insert(*state_id, value_sig);
        }

        // Process next-state functions.
        let mut latch_nexts: HashMap<NodeId, BvSignal> = HashMap::new();
        for (_, state_id, next_ref) in &nexts {
            let next_sig = self.get_signal(*next_ref)?;
            latch_nexts.insert(*state_id, next_sig);
        }

        // Build latch definitions.
        for &state_id in &state_ids {
            let curr_bits = &self.state_lits[&state_id];
            let width = curr_bits.len();

            let next_bits = latch_nexts
                .get(&state_id)
                .cloned()
                .unwrap_or_else(|| curr_bits.clone()); // No next = hold current value.

            let init_bits = &latch_inits[&state_id];

            for i in 0..width {
                let curr_lit = curr_bits[i];
                let next_lit = next_bits[i];
                // Reset value: 0 or 1 as constant literal, or curr_lit for nondeterministic.
                let reset = if init_bits[i] == 0 {
                    0 // Reset to 0
                } else if init_bits[i] == 1 {
                    1 // Reset to 1
                } else {
                    // Nondeterministic or complex init — use the init signal literal.
                    // For complex init expressions that depend on gates, we need to
                    // express as a constraint. Use nondeterministic and add init constraint.
                    curr_lit // Mark as nondeterministic for now.
                };
                self.latches.push((curr_lit, next_lit, reset));
            }
        }

        Ok(())
    }

    /// Finish and produce the circuit.
    fn finish(self) -> BitblastedCircuit {
        BitblastedCircuit {
            max_var: self.next_var - 1,
            inputs: self.inputs,
            latches: self.latches,
            ands: self.ands,
            bad: self.bad,
            constraints: self.constraints,
        }
    }

    // -----------------------------------------------------------------------
    // Constants
    // -----------------------------------------------------------------------

    fn const_from_binary(&self, s: &str) -> BvSignal {
        // Binary string is MSB-first. We store LSB-first.
        s.chars()
            .rev()
            .map(|c| if c == '1' { 1u64 } else { 0u64 })
            .collect()
    }

    fn const_from_decimal(&self, s: &str, width: u32) -> Result<BvSignal, Btor2Error> {
        let negative = s.starts_with('-');
        let digits = if negative { &s[1..] } else { s };

        // Parse as u128 for handling up to 128-bit constants.
        let abs_val: u128 = digits.parse().map_err(|_| Btor2Error::ParseError {
            line: 0,
            message: format!("invalid decimal constant: {s}"),
        })?;

        let val = if negative {
            // Two's complement: -x = 2^width - x
            let modulus = 1u128 << width;
            modulus.wrapping_sub(abs_val)
        } else {
            abs_val
        };

        let mut bits = Vec::with_capacity(width as usize);
        for i in 0..width {
            bits.push(if (val >> i) & 1 == 1 { 1u64 } else { 0u64 });
        }
        Ok(bits)
    }

    fn const_from_hex(&self, s: &str, width: u32) -> Result<BvSignal, Btor2Error> {
        let val = u128::from_str_radix(s, 16).map_err(|_| Btor2Error::ParseError {
            line: 0,
            message: format!("invalid hex constant: {s}"),
        })?;

        let mut bits = Vec::with_capacity(width as usize);
        for i in 0..width {
            bits.push(if (val >> i) & 1 == 1 { 1u64 } else { 0u64 });
        }
        Ok(bits)
    }

    fn const_one(&self, width: u32) -> BvSignal {
        let mut bits = vec![0u64; width as usize];
        if !bits.is_empty() {
            bits[0] = 1;
        }
        bits
    }

    // -----------------------------------------------------------------------
    // Arithmetic circuits
    // -----------------------------------------------------------------------

    /// Ripple-carry adder. Returns sum (same width as inputs, discards carry).
    fn add_signals(&mut self, a: &BvSignal, b: &BvSignal) -> BvSignal {
        let width = a.len();
        let mut result = Vec::with_capacity(width);
        let mut carry = 0u64; // FALSE

        for i in 0..width {
            // sum_i = a_i XOR b_i XOR carry
            // carry_out = (a_i AND b_i) OR (a_i AND carry) OR (b_i AND carry)
            //           = MAJ(a_i, b_i, carry)
            let xor_ab = self.mk_xor(a[i], b[i]);
            let sum = self.mk_xor(xor_ab, carry);
            result.push(sum);

            if i < width - 1 {
                // carry = (a AND b) OR (carry AND (a XOR b))
                let ab = self.mk_and(a[i], b[i]);
                let c_xor = self.mk_and(carry, xor_ab);
                carry = self.mk_or(ab, c_xor);
            }
        }

        result
    }

    /// Subtraction: a - b = a + (~b) + 1.
    fn sub_signals(&mut self, a: &BvSignal, b: &BvSignal) -> BvSignal {
        let width = a.len();
        let not_b: BvSignal = b.iter().map(|&lit| Self::neg(lit)).collect();

        // Add with carry-in = 1 (for two's complement subtraction).
        let mut result = Vec::with_capacity(width);
        let mut carry = 1u64; // TRUE (the +1)

        for i in 0..width {
            let xor_ab = self.mk_xor(a[i], not_b[i]);
            let sum = self.mk_xor(xor_ab, carry);
            result.push(sum);

            if i < width - 1 {
                let ab = self.mk_and(a[i], not_b[i]);
                let c_xor = self.mk_and(carry, xor_ab);
                carry = self.mk_or(ab, c_xor);
            }
        }

        result
    }

    // -----------------------------------------------------------------------
    // Comparison circuits
    // -----------------------------------------------------------------------

    /// Equality: all bits must be equal.
    fn eq_signals(&mut self, a: &BvSignal, b: &BvSignal) -> u64 {
        let width = a.len();
        if width == 0 {
            return 1; // vacuously true
        }

        // eq = AND(XNOR(a_i, b_i) for all i)
        let mut eq_bits: Vec<u64> = Vec::with_capacity(width);
        for i in 0..width {
            let xor_i = self.mk_xor(a[i], b[i]);
            eq_bits.push(Self::neg(xor_i)); // XNOR
        }

        self.reduce_and(&eq_bits)
    }

    /// Unsigned less-than: a < b.
    /// Uses subtraction: a < b iff the borrow out of (a - b) is 1,
    /// i.e., the carry out of (a + ~b + 1) is 0.
    fn ult_signals(&mut self, a: &BvSignal, b: &BvSignal) -> u64 {
        let width = a.len();
        if width == 0 {
            return 0; // can't be less than with 0 bits
        }

        let not_b: BvSignal = b.iter().map(|&lit| Self::neg(lit)).collect();

        // Compute carry chain for a + ~b + 1.
        // If final carry = 0, then a < b (borrow occurred).
        let mut carry = 1u64; // +1

        for i in 0..width {
            let xor_ab = self.mk_xor(a[i], not_b[i]);
            let ab = self.mk_and(a[i], not_b[i]);
            let c_xor = self.mk_and(carry, xor_ab);
            carry = self.mk_or(ab, c_xor);
        }

        // a < b iff carry_out == 0 (i.e., borrow)
        Self::neg(carry)
    }

    /// Signed less-than: a < b.
    /// Same as unsigned except the MSB comparison is flipped.
    fn slt_signals(&mut self, a: &BvSignal, b: &BvSignal) -> u64 {
        let width = a.len();
        if width == 0 {
            return 0;
        }
        if width == 1 {
            // 1-bit signed: -1 < 0, so a=1,b=0 means a < b.
            // Signed 1-bit: a < b iff a=1 and b=0
            return self.mk_and(a[0], Self::neg(b[0]));
        }

        // For signed comparison: flip sign bits and do unsigned compare.
        // a_signed < b_signed iff (a with flipped MSB) <_unsigned (b with flipped MSB)
        let mut a_flipped = a.clone();
        let mut b_flipped = b.clone();
        let last = width - 1;
        a_flipped[last] = Self::neg(a[last]);
        b_flipped[last] = Self::neg(b[last]);

        self.ult_signals(&a_flipped, &b_flipped)
    }

    // -----------------------------------------------------------------------
    // Reduction ops
    // -----------------------------------------------------------------------

    fn reduce_and(&mut self, bits: &[u64]) -> u64 {
        if bits.is_empty() {
            return 1; // vacuously true
        }
        let mut result = bits[0];
        for &bit in &bits[1..] {
            result = self.mk_and(result, bit);
        }
        result
    }

    fn reduce_or(&mut self, bits: &[u64]) -> u64 {
        if bits.is_empty() {
            return 0; // vacuously false
        }
        let mut result = bits[0];
        for &bit in &bits[1..] {
            result = self.mk_or(result, bit);
        }
        result
    }

    fn reduce_xor(&mut self, bits: &[u64]) -> u64 {
        if bits.is_empty() {
            return 0;
        }
        let mut result = bits[0];
        for &bit in &bits[1..] {
            result = self.mk_xor(result, bit);
        }
        result
    }

    // -----------------------------------------------------------------------
    // Bitwise binary ops
    // -----------------------------------------------------------------------

    fn bitwise_and(&mut self, a: &BvSignal, b: &BvSignal) -> BvSignal {
        a.iter()
            .zip(b.iter())
            .map(|(&ai, &bi)| self.mk_and(ai, bi))
            .collect()
    }

    fn bitwise_or(&mut self, a: &BvSignal, b: &BvSignal) -> BvSignal {
        a.iter()
            .zip(b.iter())
            .map(|(&ai, &bi)| self.mk_or(ai, bi))
            .collect()
    }

    fn bitwise_xor(&mut self, a: &BvSignal, b: &BvSignal) -> BvSignal {
        a.iter()
            .zip(b.iter())
            .map(|(&ai, &bi)| self.mk_xor(ai, bi))
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    #[test]
    fn test_bitblast_simple_counter() {
        // 8-bit counter, bad = (count == 0xFF)
        let input = "\
1 sort bitvec 8
2 zero 1
3 state 1 count
4 init 1 3 2
5 one 1
6 add 1 3 5
7 next 1 3 6
8 ones 1
9 eq 1 3 8
10 bad 9
";
        let prog = parse(input).expect("parse");
        let circuit = bitblast(&prog, 32).expect("bitblast");

        // 8 latch bits (one per bit of `count`)
        assert_eq!(circuit.latches.len(), 8);
        // 1 bad property
        assert_eq!(circuit.bad.len(), 1);
        // No inputs
        assert_eq!(circuit.inputs.len(), 0);
        // Should have AND gates for the adder + equality
        assert!(circuit.ands.len() > 0);
    }

    #[test]
    fn test_bitblast_eligible_rejects_arrays() {
        let input = "\
1 sort bitvec 8
2 sort bitvec 32
3 sort array 1 2
4 input 3 mem
5 input 1 addr
6 read 2 4 5
7 bad 6
";
        let prog = parse(input).expect("parse");
        let result = bitblast_eligible(&prog, 32);
        assert!(result.is_err());
    }

    #[test]
    fn test_bitblast_eligible_rejects_wide() {
        let input = "\
1 sort bitvec 64
2 input 1 x
3 bad 2
";
        let prog = parse(input).expect("parse");
        let result = bitblast_eligible(&prog, 32);
        assert!(result.is_err());
    }

    #[test]
    fn test_bitblast_1bit_and() {
        let input = "\
1 sort bitvec 1
2 input 1 a
3 input 1 b
4 and 1 2 3
5 bad 4
";
        let prog = parse(input).expect("parse");
        let circuit = bitblast(&prog, 32).expect("bitblast");

        assert_eq!(circuit.inputs.len(), 2);
        assert_eq!(circuit.bad.len(), 1);
        assert_eq!(circuit.latches.len(), 0);
        // AND of two inputs requires 1 AND gate
        assert_eq!(circuit.ands.len(), 1);
    }

    #[test]
    fn test_bitblast_negation() {
        let input = "\
1 sort bitvec 1
2 input 1 x
3 not 1 2
4 bad 3
";
        let prog = parse(input).expect("parse");
        let circuit = bitblast(&prog, 32).expect("bitblast");

        assert_eq!(circuit.inputs.len(), 1);
        assert_eq!(circuit.bad.len(), 1);
        // NOT requires no AND gates (just literal negation)
        assert_eq!(circuit.ands.len(), 0);
    }

    #[test]
    fn test_bitblast_concat_and_slice() {
        let input = "\
1 sort bitvec 4
2 sort bitvec 8
3 sort bitvec 2
4 input 1 lo
5 input 1 hi
6 concat 2 5 4
7 slice 3 6 3 2
8 redor 1 7
9 bad 8
";
        let prog = parse(input).expect("parse");
        let circuit = bitblast(&prog, 32).expect("bitblast");

        // 4+4 = 8 input bits
        assert_eq!(circuit.inputs.len(), 8);
        assert_eq!(circuit.bad.len(), 1);
    }

    #[test]
    fn test_bitblast_ite() {
        let input = "\
1 sort bitvec 1
2 sort bitvec 4
3 input 1 sel
4 input 2 a
5 input 2 b
6 ite 2 3 4 5
7 redor 1 6
8 bad 7
";
        let prog = parse(input).expect("parse");
        let circuit = bitblast(&prog, 32).expect("bitblast");

        // 1 + 4 + 4 = 9 input bits
        assert_eq!(circuit.inputs.len(), 9);
        assert_eq!(circuit.bad.len(), 1);
    }

    #[test]
    fn test_bitblast_constants() {
        let input = "\
1 sort bitvec 4
2 constd 1 10
3 const 1 1010
4 consth 1 a
5 eq 1 2 3
6 eq 1 3 4
7 and 1 5 6
8 bad 7
";
        let prog = parse(input).expect("parse");
        let circuit = bitblast(&prog, 32).expect("bitblast");

        // No inputs, no latches — all constants
        assert_eq!(circuit.inputs.len(), 0);
        assert_eq!(circuit.latches.len(), 0);
        assert_eq!(circuit.bad.len(), 1);
        // bad should be constant TRUE (10==0b1010, 0b1010==0xa — all equal)
        assert_eq!(circuit.bad[0], 1);
    }

    #[test]
    fn test_bitblast_comparison_ult() {
        let input = "\
1 sort bitvec 4
2 sort bitvec 1
3 input 1 a
4 input 1 b
5 ult 2 3 4
6 bad 5
";
        let prog = parse(input).expect("parse");
        let circuit = bitblast(&prog, 32).expect("bitblast");

        assert_eq!(circuit.inputs.len(), 8); // 4+4 bits
        assert_eq!(circuit.bad.len(), 1);
    }

    #[test]
    fn test_bitblast_constraint() {
        let input = "\
1 sort bitvec 1
2 input 1 x
3 input 1 y
4 and 1 2 3
5 constraint 4
6 bad 2
";
        let prog = parse(input).expect("parse");
        let circuit = bitblast(&prog, 32).expect("bitblast");

        assert_eq!(circuit.constraints.len(), 1);
        assert_eq!(circuit.bad.len(), 1);
    }
}
