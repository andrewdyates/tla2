// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates
// BTOR2 to CHC translation: converts parsed BTOR2 programs into z4-chc's
// `ChcProblem` format for the PDR/BMC/KIND portfolio solver.
//
// Translation scheme:
//   state    -> ChcVar in the invariant predicate
//   input    -> existentially quantified variable in the transition clause
//   init     -> init clause: init_constraint => Inv(state_vars)
//   next     -> transition clause: Inv(curr) /\ trans => Inv(next)
//   bad      -> query clause: Inv(curr) /\ bad => false
//   constraint -> conjoined with transition relation

use std::sync::Arc;
use std::time::Duration;

use rustc_hash::FxHashMap;
use z4_chc::{
    AdaptiveConfig, AdaptivePortfolio, ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody,
    ClauseHead, HornClause, VerifiedChcResult,
};

use crate::error::Btor2Error;
use crate::types::{Btor2Line, Btor2Node, Btor2Program, Btor2Sort, NodeId};

// ---------------------------------------------------------------------------
// Public result type
// ---------------------------------------------------------------------------

/// Result of translating a BTOR2 program to a CHC problem.
#[derive(Debug)]
pub struct TranslationResult {
    /// The CHC problem, ready for the portfolio solver.
    pub problem: ChcProblem,
    /// Mapping from BTOR2 state node ids to their CHC variables.
    pub state_vars: Vec<StateVarEntry>,
    /// Index of each `bad` property within the generated query clauses.
    /// `property_indices[i]` is the clause index for `bad_properties[i]`.
    pub property_indices: Vec<usize>,
}

/// A state variable entry in the translation result.
#[derive(Debug, Clone)]
pub struct StateVarEntry {
    /// BTOR2 node id for this state declaration.
    pub node_id: i64,
    /// Optional symbolic name from the BTOR2 source.
    pub name: Option<String>,
    /// The CHC variable (current-state).
    pub var: ChcVar,
    /// The CHC variable (next-state).
    pub next_var: ChcVar,
}

// ---------------------------------------------------------------------------
// Internal translator state
// ---------------------------------------------------------------------------

struct Translator<'a> {
    program: &'a Btor2Program,
    /// Resolved CHC sort for each BTOR2 sort id.
    sort_map: FxHashMap<i64, ChcSort>,
    /// Resolved CHC sort for each BTOR2 node id.
    node_sort: FxHashMap<i64, ChcSort>,
    /// BTOR2 line index: node_id -> &Btor2Line.
    line_index: FxHashMap<i64, &'a Btor2Line>,
    /// Memoized expression translation: node_id -> ChcExpr.
    expr_cache: FxHashMap<i64, ChcExpr>,

    state_entries: Vec<StateVarEntry>,
    state_id_to_idx: FxHashMap<i64, usize>,
    input_vars: FxHashMap<i64, ChcVar>,

    init_conjuncts: Vec<ChcExpr>,
    next_exprs: FxHashMap<i64, ChcExpr>,
    bad_exprs: Vec<ChcExpr>,
    constraint_exprs: Vec<ChcExpr>,
}

impl<'a> Translator<'a> {
    fn new(program: &'a Btor2Program) -> Self {
        let mut line_index = FxHashMap::default();
        for line in &program.lines {
            line_index.insert(line.id, line);
        }

        Self {
            program,
            sort_map: FxHashMap::default(),
            node_sort: FxHashMap::default(),
            line_index,
            expr_cache: FxHashMap::default(),
            state_entries: Vec::new(),
            state_id_to_idx: FxHashMap::default(),
            input_vars: FxHashMap::default(),
            init_conjuncts: Vec::new(),
            next_exprs: FxHashMap::default(),
            bad_exprs: Vec::new(),
            constraint_exprs: Vec::new(),
        }
    }

    // -----------------------------------------------------------------------
    // Sort resolution
    // -----------------------------------------------------------------------

    fn resolve_sorts(&mut self) {
        for (&sort_id, sort) in &self.program.sorts {
            self.sort_map.insert(sort_id, btor2_sort_to_chc(sort));
        }
    }

    fn get_sort(&self, sort_id: i64) -> Result<ChcSort, Btor2Error> {
        self.sort_map
            .get(&sort_id)
            .cloned()
            .ok_or(Btor2Error::InvalidSort { line: 0, sort_id })
    }

    fn get_node_sort(&self, node_id: i64) -> Result<ChcSort, Btor2Error> {
        let abs_id = node_id.unsigned_abs() as i64;
        if let Some(sort) = self.node_sort.get(&abs_id) {
            return Ok(sort.clone());
        }
        let line = self
            .line_index
            .get(&abs_id)
            .ok_or(Btor2Error::UndefinedNode {
                line: 0,
                node_id: abs_id,
            })?;
        self.get_sort(line.sort_id)
    }

    fn bit_width(&self, node_id: i64) -> Result<u32, Btor2Error> {
        match self.get_node_sort(node_id)? {
            ChcSort::BitVec(w) => Ok(w),
            _ => Ok(1),
        }
    }

    // -----------------------------------------------------------------------
    // Pass 1: collect state/input declarations
    // -----------------------------------------------------------------------

    fn collect_declarations(&mut self) -> Result<(), Btor2Error> {
        for line in &self.program.lines {
            match &line.node {
                Btor2Node::State(sort_id, name) => {
                    let sort = self.get_sort(*sort_id)?;
                    self.node_sort.insert(line.id, sort.clone());
                    let var_name = name.clone().unwrap_or_else(|| format!("s{}", line.id));
                    let var = ChcVar::new(&var_name, sort.clone());
                    let next_var = ChcVar::new(format!("{var_name}'"), sort);
                    let idx = self.state_entries.len();
                    self.state_entries.push(StateVarEntry {
                        node_id: line.id,
                        name: name.clone(),
                        var,
                        next_var,
                    });
                    self.state_id_to_idx.insert(line.id, idx);
                }
                Btor2Node::Input(sort_id, name) => {
                    let sort = self.get_sort(*sort_id)?;
                    self.node_sort.insert(line.id, sort.clone());
                    let var_name = name.clone().unwrap_or_else(|| format!("i{}", line.id));
                    self.input_vars.insert(line.id, ChcVar::new(var_name, sort));
                }
                Btor2Node::SortBitVec(_) | Btor2Node::SortArray(_, _) => {}
                _ => {
                    if line.sort_id > 0 {
                        if let Ok(sort) = self.get_sort(line.sort_id) {
                            self.node_sort.insert(line.id, sort);
                        }
                    }
                }
            }
        }
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Pass 2: collect init/next/bad/constraint
    // -----------------------------------------------------------------------

    fn collect_semantics(&mut self) -> Result<(), Btor2Error> {
        let lines: Vec<Btor2Line> = self.program.lines.clone();
        for line in &lines {
            match &line.node {
                Btor2Node::Init(sort_id, state_id, value_id) => {
                    let state_expr = self.translate_node(*state_id)?;
                    let value_expr = self.translate_node(*value_id)?;
                    // When initializing an array state with a scalar constant,
                    // lift the constant to a const-array expression.
                    let lifted = self.lift_to_array_if_needed(*sort_id, value_expr);
                    self.init_conjuncts.push(ChcExpr::eq(state_expr, lifted));
                }
                Btor2Node::Next(_sort_id, state_id, next_value_id) => {
                    let expr = self.translate_node(*next_value_id)?;
                    let abs_state = state_id.unsigned_abs() as i64;
                    self.next_exprs.insert(abs_state, expr);
                }
                Btor2Node::Bad(cond_id) => {
                    let expr = self.translate_node(*cond_id)?;
                    self.bad_exprs.push(expr);
                }
                Btor2Node::Constraint(cond_id) => {
                    let expr = self.translate_node(*cond_id)?;
                    self.constraint_exprs.push(expr);
                }
                _ => {}
            }
        }
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Expression translation (recursive with memoization)
    // -----------------------------------------------------------------------

    fn translate_node(&mut self, node_id: NodeId) -> Result<ChcExpr, Btor2Error> {
        let negated = node_id < 0;
        let abs_id = node_id.unsigned_abs() as i64;

        if let Some(expr) = self.expr_cache.get(&abs_id) {
            let expr = expr.clone();
            return Ok(if negated {
                self.apply_negation(abs_id, expr)?
            } else {
                expr
            });
        }

        let raw = self.translate_node_inner(abs_id)?;
        // Apply expression simplification (constant folding, identity elimination)
        // before caching. Since translation is memoized, each node is simplified
        // exactly once.
        let expr = crate::simplify::simplify_expr(&raw);
        self.expr_cache.insert(abs_id, expr.clone());

        Ok(if negated {
            self.apply_negation(abs_id, expr)?
        } else {
            expr
        })
    }

    /// Apply negation for a negative node reference.
    ///
    /// BTOR2 negative references always denote **bitwise** negation, even for
    /// 1-bit values. We must stay in the BV domain (BvNot) so that the
    /// `bv1_to_bool` / `bool_to_bv1` bridge functions can correctly convert
    /// between BV(1) and Bool when needed. Using `ChcExpr::not` (Bool NOT)
    /// here would create sort mismatches: Bool NOT applied to a BitVec(1)
    /// expression, which downstream `bv1_to_bool` cannot recognize as a
    /// peephole candidate, leading to ill-sorted `eq(Not(BV_var), 1bv1)`.
    ///
    /// This was the tla-btor2 side of the bakery.3.prop1 false positive (#3803).
    fn apply_negation(&self, _abs_id: i64, expr: ChcExpr) -> Result<ChcExpr, Btor2Error> {
        Ok(ChcExpr::Op(ChcOp::BvNot, vec![Arc::new(expr)]))
    }

    fn translate_node_inner(&mut self, node_id: i64) -> Result<ChcExpr, Btor2Error> {
        // State reference -> current-state variable.
        if let Some(&idx) = self.state_id_to_idx.get(&node_id) {
            return Ok(ChcExpr::var(self.state_entries[idx].var.clone()));
        }

        // Input reference -> input variable.
        if let Some(var) = self.input_vars.get(&node_id) {
            return Ok(ChcExpr::var(var.clone()));
        }

        let &line = self
            .line_index
            .get(&node_id)
            .ok_or(Btor2Error::UndefinedNode { line: 0, node_id })?;

        match &line.node {
            // Constants
            Btor2Node::Zero => {
                let sort = self.get_sort(line.sort_id)?;
                Ok(zero_const(&sort))
            }
            Btor2Node::One => {
                let sort = self.get_sort(line.sort_id)?;
                Ok(one_const(&sort))
            }
            Btor2Node::Ones => {
                let sort = self.get_sort(line.sort_id)?;
                Ok(ones_const(&sort))
            }
            Btor2Node::Const(bits) => {
                let sort = self.get_sort(line.sort_id)?;
                Ok(parse_binary_const(bits, &sort))
            }
            Btor2Node::ConstD(dec) => {
                let sort = self.get_sort(line.sort_id)?;
                Ok(parse_decimal_const(dec, &sort))
            }
            Btor2Node::ConstH(hex) => {
                let sort = self.get_sort(line.sort_id)?;
                Ok(parse_hex_const(hex, &sort))
            }

            // Unary BV ops — always use BvNot (stay in BV domain, see #3803).
            Btor2Node::Not => {
                let a = self.translate_arg(&line, 0)?;
                Ok(ChcExpr::Op(ChcOp::BvNot, vec![Arc::new(a)]))
            }
            Btor2Node::Neg => {
                let a = self.translate_arg(&line, 0)?;
                Ok(ChcExpr::Op(ChcOp::BvNeg, vec![Arc::new(a)]))
            }
            Btor2Node::Inc => {
                let a = self.translate_arg(&line, 0)?;
                let w = self.arg_width(&line, 0)?;
                Ok(ChcExpr::Op(
                    ChcOp::BvAdd,
                    vec![Arc::new(a), Arc::new(ChcExpr::BitVec(1, w))],
                ))
            }
            Btor2Node::Dec => {
                let a = self.translate_arg(&line, 0)?;
                let w = self.arg_width(&line, 0)?;
                Ok(ChcExpr::Op(
                    ChcOp::BvSub,
                    vec![Arc::new(a), Arc::new(ChcExpr::BitVec(1, w))],
                ))
            }
            Btor2Node::Redand => {
                let a = self.translate_arg(&line, 0)?;
                let w = self.arg_width(&line, 0)?;
                Ok(bool_to_bv1(ChcExpr::eq(a, ChcExpr::BitVec(bv_mask(w), w))))
            }
            Btor2Node::Redor => {
                let a = self.translate_arg(&line, 0)?;
                let w = self.arg_width(&line, 0)?;
                Ok(bool_to_bv1(ChcExpr::ne(a, ChcExpr::BitVec(0, w))))
            }
            Btor2Node::Redxor => {
                let a = self.translate_arg(&line, 0)?;
                let w = self.arg_width(&line, 0)?;
                if w == 1 {
                    return Ok(a);
                }
                let mut result = ChcExpr::Op(ChcOp::BvExtract(0, 0), vec![Arc::new(a.clone())]);
                for i in 1..w {
                    let bit = ChcExpr::Op(ChcOp::BvExtract(i, i), vec![Arc::new(a.clone())]);
                    result = ChcExpr::Op(ChcOp::BvXor, vec![Arc::new(result), Arc::new(bit)]);
                }
                Ok(result)
            }

            // Binary BV arithmetic
            Btor2Node::Add => self.translate_binary(&line, ChcOp::BvAdd),
            Btor2Node::Sub => self.translate_binary(&line, ChcOp::BvSub),
            Btor2Node::Mul => self.translate_binary(&line, ChcOp::BvMul),
            Btor2Node::UDiv => self.translate_binary(&line, ChcOp::BvUDiv),
            Btor2Node::SDiv => self.translate_binary(&line, ChcOp::BvSDiv),
            Btor2Node::URem => self.translate_binary(&line, ChcOp::BvURem),
            Btor2Node::SRem => self.translate_binary(&line, ChcOp::BvSRem),
            Btor2Node::SMod => self.translate_binary(&line, ChcOp::BvSMod),

            // Binary BV bitwise
            Btor2Node::And => {
                let a = self.translate_arg(&line, 0)?;
                let b = self.translate_arg(&line, 1)?;
                let w = self.arg_width(&line, 0)?;
                Ok(if w == 1 {
                    bool_to_bv1(ChcExpr::and(bv1_to_bool(a), bv1_to_bool(b)))
                } else {
                    ChcExpr::Op(ChcOp::BvAnd, vec![Arc::new(a), Arc::new(b)])
                })
            }
            Btor2Node::Or => {
                let a = self.translate_arg(&line, 0)?;
                let b = self.translate_arg(&line, 1)?;
                let w = self.arg_width(&line, 0)?;
                Ok(if w == 1 {
                    bool_to_bv1(ChcExpr::or(bv1_to_bool(a), bv1_to_bool(b)))
                } else {
                    ChcExpr::Op(ChcOp::BvOr, vec![Arc::new(a), Arc::new(b)])
                })
            }
            Btor2Node::Xor => self.translate_binary(&line, ChcOp::BvXor),
            Btor2Node::Nand => self.translate_binary(&line, ChcOp::BvNand),
            Btor2Node::Nor => self.translate_binary(&line, ChcOp::BvNor),
            Btor2Node::Xnor => self.translate_binary(&line, ChcOp::BvXnor),

            // Shifts
            Btor2Node::Sll => self.translate_binary(&line, ChcOp::BvShl),
            Btor2Node::Srl => self.translate_binary(&line, ChcOp::BvLShr),
            Btor2Node::Sra => self.translate_binary(&line, ChcOp::BvAShr),

            // Rotations: BTOR2 uses binary op (variable amount).
            // Lower to shift/or since ChcOp rotations take constant amount.
            Btor2Node::Rol => {
                let a = self.translate_arg(&line, 0)?;
                let b = self.translate_arg(&line, 1)?;
                let w = self.arg_width(&line, 0)?;
                let wc = ChcExpr::BitVec(u128::from(w), w);
                let diff = bv_op(ChcOp::BvSub, wc, b.clone());
                let left = bv_op(ChcOp::BvShl, a.clone(), b);
                let right = bv_op(ChcOp::BvLShr, a, diff);
                Ok(bv_op(ChcOp::BvOr, left, right))
            }
            Btor2Node::Ror => {
                let a = self.translate_arg(&line, 0)?;
                let b = self.translate_arg(&line, 1)?;
                let w = self.arg_width(&line, 0)?;
                let wc = ChcExpr::BitVec(u128::from(w), w);
                let diff = bv_op(ChcOp::BvSub, wc, b.clone());
                let right = bv_op(ChcOp::BvLShr, a.clone(), b);
                let left = bv_op(ChcOp::BvShl, a, diff);
                Ok(bv_op(ChcOp::BvOr, left, right))
            }

            // Comparisons: all return 1-bit BV in BTOR2
            Btor2Node::Eq => {
                let (a, b) = self.translate_binary_args(&line)?;
                Ok(bool_to_bv1(ChcExpr::eq(a, b)))
            }
            Btor2Node::Neq => {
                let (a, b) = self.translate_binary_args(&line)?;
                Ok(bool_to_bv1(ChcExpr::ne(a, b)))
            }
            Btor2Node::Ult => {
                let (a, b) = self.translate_binary_args(&line)?;
                Ok(bool_to_bv1(bv_op(ChcOp::BvULt, a, b)))
            }
            Btor2Node::Ulte => {
                let (a, b) = self.translate_binary_args(&line)?;
                Ok(bool_to_bv1(bv_op(ChcOp::BvULe, a, b)))
            }
            Btor2Node::Ugt => {
                let (a, b) = self.translate_binary_args(&line)?;
                Ok(bool_to_bv1(bv_op(ChcOp::BvUGt, a, b)))
            }
            Btor2Node::Ugte => {
                let (a, b) = self.translate_binary_args(&line)?;
                Ok(bool_to_bv1(bv_op(ChcOp::BvUGe, a, b)))
            }
            Btor2Node::Slt => {
                let (a, b) = self.translate_binary_args(&line)?;
                Ok(bool_to_bv1(bv_op(ChcOp::BvSLt, a, b)))
            }
            Btor2Node::Slte => {
                let (a, b) = self.translate_binary_args(&line)?;
                Ok(bool_to_bv1(bv_op(ChcOp::BvSLe, a, b)))
            }
            Btor2Node::Sgt => {
                let (a, b) = self.translate_binary_args(&line)?;
                Ok(bool_to_bv1(bv_op(ChcOp::BvSGt, a, b)))
            }
            Btor2Node::Sgte => {
                let (a, b) = self.translate_binary_args(&line)?;
                Ok(bool_to_bv1(bv_op(ChcOp::BvSGe, a, b)))
            }

            // Concat
            Btor2Node::Concat => self.translate_binary(&line, ChcOp::BvConcat),

            // Indexed ops
            Btor2Node::Slice(upper, lower) => {
                let a = self.translate_arg(&line, 0)?;
                Ok(ChcExpr::Op(
                    ChcOp::BvExtract(*upper, *lower),
                    vec![Arc::new(a)],
                ))
            }
            Btor2Node::Uext(n) => {
                let a = self.translate_arg(&line, 0)?;
                if *n == 0 {
                    return Ok(a);
                }
                Ok(ChcExpr::Op(ChcOp::BvZeroExtend(*n), vec![Arc::new(a)]))
            }
            Btor2Node::Sext(n) => {
                let a = self.translate_arg(&line, 0)?;
                if *n == 0 {
                    return Ok(a);
                }
                Ok(ChcExpr::Op(ChcOp::BvSignExtend(*n), vec![Arc::new(a)]))
            }

            // Ternary: ITE
            Btor2Node::Ite => {
                let cond = self.translate_arg(&line, 0)?;
                let then_ = self.translate_arg(&line, 1)?;
                let else_ = self.translate_arg(&line, 2)?;
                Ok(ChcExpr::ite(bv1_to_bool(cond), then_, else_))
            }

            // Array ops
            Btor2Node::Read => {
                let arr = self.translate_arg(&line, 0)?;
                let idx = self.translate_arg(&line, 1)?;
                Ok(ChcExpr::select(arr, idx))
            }
            Btor2Node::Write => {
                let arr = self.translate_arg(&line, 0)?;
                let idx = self.translate_arg(&line, 1)?;
                let val = self.translate_arg(&line, 2)?;
                Ok(ChcExpr::store(arr, idx, val))
            }

            // Boolean (1-bit) ops
            Btor2Node::Iff => {
                let (a, b) = self.translate_binary_args(&line)?;
                Ok(bool_to_bv1(ChcExpr::eq(a, b)))
            }
            Btor2Node::Implies => {
                let (a, b) = self.translate_binary_args(&line)?;
                Ok(bool_to_bv1(ChcExpr::implies(
                    bv1_to_bool(a),
                    bv1_to_bool(b),
                )))
            }

            // Overflow detection — precise semantics (#3885).
            // Each returns a 1-bit BV: 1 if overflow, 0 otherwise.

            // Saddo: signed addition overflow.
            // Overflow when sign(a) == sign(b) but sign(a+b) != sign(a).
            // sign bit = extract(w-1, w-1, x)
            Btor2Node::Saddo => {
                let (a, b) = self.translate_binary_args(&line)?;
                let w = self.arg_width(&line, 0)?;
                let sum = bv_op(ChcOp::BvAdd, a.clone(), b.clone());
                let sign_a = bv_extract_msb(a.clone(), w);
                let sign_b = bv_extract_msb(b, w);
                let sign_sum = bv_extract_msb(sum, w);
                // same_sign = sign_a == sign_b (as BV1)
                let same_sign = bv_op(ChcOp::BvXnor, sign_a.clone(), sign_b);
                // diff_result = sign_a != sign_sum (as BV1)
                let diff_result = bv_op(ChcOp::BvXor, sign_a, sign_sum);
                // overflow = same_sign AND diff_result
                Ok(bv_op(ChcOp::BvAnd, same_sign, diff_result))
            }

            // Ssubo: signed subtraction overflow.
            // Overflow when sign(a) != sign(b) and sign(a-b) != sign(a).
            Btor2Node::Ssubo => {
                let (a, b) = self.translate_binary_args(&line)?;
                let w = self.arg_width(&line, 0)?;
                let diff = bv_op(ChcOp::BvSub, a.clone(), b.clone());
                let sign_a = bv_extract_msb(a.clone(), w);
                let sign_b = bv_extract_msb(b, w);
                let sign_diff = bv_extract_msb(diff, w);
                // diff_sign = sign_a != sign_b (as BV1)
                let diff_sign = bv_op(ChcOp::BvXor, sign_a.clone(), sign_b);
                // diff_result = sign_a != sign_diff (as BV1)
                let diff_result = bv_op(ChcOp::BvXor, sign_a, sign_diff);
                // overflow = diff_sign AND diff_result
                Ok(bv_op(ChcOp::BvAnd, diff_sign, diff_result))
            }

            // Sdivo: signed division overflow.
            // Only overflows for INT_MIN / -1 (two's complement).
            Btor2Node::Sdivo => {
                let (a, b) = self.translate_binary_args(&line)?;
                let w = self.arg_width(&line, 0)?;
                // INT_MIN = 1 << (w-1), i.e. 0x800...0
                let int_min = ChcExpr::BitVec(1u128 << (w - 1), w);
                // -1 = all ones = bv_mask(w)
                let neg_one = ChcExpr::BitVec(bv_mask(w), w);
                let a_is_min = bool_to_bv1(ChcExpr::eq(a, int_min));
                let b_is_neg1 = bool_to_bv1(ChcExpr::eq(b, neg_one));
                Ok(bv_op(ChcOp::BvAnd, a_is_min, b_is_neg1))
            }

            // Smulo: signed multiplication overflow.
            // Sign-extend both operands to 2*w bits, multiply, then check
            // whether the upper w bits equal the sign-extension of bit w-1.
            Btor2Node::Smulo => {
                let (a, b) = self.translate_binary_args(&line)?;
                let w = self.arg_width(&line, 0)?;
                let ext_a = ChcExpr::Op(ChcOp::BvSignExtend(w), vec![Arc::new(a)]);
                let ext_b = ChcExpr::Op(ChcOp::BvSignExtend(w), vec![Arc::new(b)]);
                let wide_prod = bv_op(ChcOp::BvMul, ext_a, ext_b);
                // Upper w bits of the 2w-bit product
                let upper = ChcExpr::Op(
                    ChcOp::BvExtract(2 * w - 1, w),
                    vec![Arc::new(wide_prod.clone())],
                );
                // Sign extension of bit (w-1) of the product = all copies of that bit
                let sign_bit =
                    ChcExpr::Op(ChcOp::BvExtract(w - 1, w - 1), vec![Arc::new(wide_prod)]);
                let sign_ext = ChcExpr::Op(ChcOp::BvSignExtend(w - 1), vec![Arc::new(sign_bit)]);
                // Overflow if upper != sign_ext
                Ok(bool_to_bv1(ChcExpr::ne(upper, sign_ext)))
            }

            // Uaddo: unsigned addition overflow.
            // Zero-extend both to w+1 bits, add, check if bit w is set.
            Btor2Node::Uaddo => {
                let (a, b) = self.translate_binary_args(&line)?;
                let w = self.arg_width(&line, 0)?;
                let ext_a = ChcExpr::Op(ChcOp::BvZeroExtend(1), vec![Arc::new(a)]);
                let ext_b = ChcExpr::Op(ChcOp::BvZeroExtend(1), vec![Arc::new(b)]);
                let wide_sum = bv_op(ChcOp::BvAdd, ext_a, ext_b);
                // Extract carry bit (bit w of the (w+1)-bit result)
                Ok(ChcExpr::Op(
                    ChcOp::BvExtract(w, w),
                    vec![Arc::new(wide_sum)],
                ))
            }

            // Umulo: unsigned multiplication overflow.
            // Zero-extend both to 2*w bits, multiply, check upper w bits != 0.
            Btor2Node::Umulo => {
                let (a, b) = self.translate_binary_args(&line)?;
                let w = self.arg_width(&line, 0)?;
                let ext_a = ChcExpr::Op(ChcOp::BvZeroExtend(w), vec![Arc::new(a)]);
                let ext_b = ChcExpr::Op(ChcOp::BvZeroExtend(w), vec![Arc::new(b)]);
                let wide_prod = bv_op(ChcOp::BvMul, ext_a, ext_b);
                // Upper w bits
                let upper = ChcExpr::Op(ChcOp::BvExtract(2 * w - 1, w), vec![Arc::new(wide_prod)]);
                // Overflow if upper != 0
                Ok(bool_to_bv1(ChcExpr::ne(upper, ChcExpr::BitVec(0, w))))
            }

            // Usubo: unsigned subtraction overflow (borrow).
            // Overflow when b > a (unsigned).
            Btor2Node::Usubo => {
                let (a, b) = self.translate_binary_args(&line)?;
                Ok(bool_to_bv1(ChcExpr::Op(
                    ChcOp::BvULt,
                    vec![Arc::new(a), Arc::new(b)],
                )))
            }

            // Sort definitions, state/input (handled earlier), and semantic
            // nodes (init/next/bad/constraint) don't produce expressions.
            Btor2Node::SortBitVec(_)
            | Btor2Node::SortArray(_, _)
            | Btor2Node::State(_, _)
            | Btor2Node::Input(_, _)
            | Btor2Node::Init(_, _, _)
            | Btor2Node::Next(_, _, _)
            | Btor2Node::Bad(_)
            | Btor2Node::Constraint(_)
            | Btor2Node::Fair(_)
            | Btor2Node::Justice(_)
            | Btor2Node::Output(_) => Err(Btor2Error::UndefinedNode { line: 0, node_id }),
        }
    }

    // -----------------------------------------------------------------------
    // Argument helpers
    // -----------------------------------------------------------------------

    fn translate_arg(&mut self, line: &Btor2Line, idx: usize) -> Result<ChcExpr, Btor2Error> {
        let arg_id = *line.args.get(idx).ok_or(Btor2Error::InvalidArgCount {
            line: line.id as usize,
            op: format!("{:?}", line.node),
            expected: idx + 1,
            got: line.args.len(),
        })?;
        self.translate_node(arg_id)
    }

    fn translate_binary(&mut self, line: &Btor2Line, op: ChcOp) -> Result<ChcExpr, Btor2Error> {
        let a = self.translate_arg(line, 0)?;
        let b = self.translate_arg(line, 1)?;
        Ok(ChcExpr::Op(op, vec![Arc::new(a), Arc::new(b)]))
    }

    fn translate_binary_args(
        &mut self,
        line: &Btor2Line,
    ) -> Result<(ChcExpr, ChcExpr), Btor2Error> {
        let a = self.translate_arg(line, 0)?;
        let b = self.translate_arg(line, 1)?;
        Ok((a, b))
    }

    fn arg_width(&self, line: &Btor2Line, idx: usize) -> Result<u32, Btor2Error> {
        let arg_id = *line.args.get(idx).ok_or(Btor2Error::InvalidArgCount {
            line: line.id as usize,
            op: format!("{:?}", line.node),
            expected: idx + 1,
            got: line.args.len(),
        })?;
        self.bit_width(arg_id)
    }

    /// If `sort_id` refers to an array sort but `expr` is a scalar (bitvector)
    /// constant, lift it to a `ChcExpr::const_array`. This handles the common
    /// BTOR2 pattern where `init <array_sort> <state> <bv_const>` means
    /// "initialize every array element to this constant".
    fn lift_to_array_if_needed(&self, sort_id: i64, expr: ChcExpr) -> ChcExpr {
        if let Ok(sort) = self.get_sort(sort_id) {
            return lift_scalar_to_array(&sort, expr);
        }
        expr
    }

    // -----------------------------------------------------------------------
    // CHC problem assembly
    // -----------------------------------------------------------------------

    fn assemble(self) -> Result<TranslationResult, Btor2Error> {
        let mut problem = ChcProblem::new();

        let inv_sorts: Vec<ChcSort> = self
            .state_entries
            .iter()
            .map(|e| e.var.sort.clone())
            .collect();
        let inv_pred = problem.declare_predicate("Inv", inv_sorts);

        let curr_args: Vec<ChcExpr> = self
            .state_entries
            .iter()
            .map(|e| ChcExpr::var(e.var.clone()))
            .collect();
        let next_args: Vec<ChcExpr> = self
            .state_entries
            .iter()
            .map(|e| ChcExpr::var(e.next_var.clone()))
            .collect();

        // Init clause: init_constraint => Inv(state_vars)
        let init_constraint = if self.init_conjuncts.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::and_all(self.init_conjuncts)
        };
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(init_constraint),
            ClauseHead::Predicate(inv_pred, curr_args.clone()),
        ));

        // Transition clause: Inv(curr) /\ trans => Inv(next)
        let mut trans_conjuncts: Vec<ChcExpr> = Vec::new();

        for entry in &self.state_entries {
            if let Some(next_expr) = self.next_exprs.get(&entry.node_id) {
                trans_conjuncts.push(ChcExpr::eq(
                    ChcExpr::var(entry.next_var.clone()),
                    next_expr.clone(),
                ));
            }
        }

        // Constraints restrict the environment at every step.
        for c in &self.constraint_exprs {
            trans_conjuncts.push(bv1_to_bool(c.clone()));
        }

        let trans_constraint = if trans_conjuncts.is_empty() {
            None
        } else {
            Some(ChcExpr::and_all(trans_conjuncts))
        };

        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(inv_pred, curr_args.clone())], trans_constraint),
            ClauseHead::Predicate(inv_pred, next_args),
        ));

        // Query clauses: Inv(curr) /\ bad => false
        let mut property_indices = Vec::with_capacity(self.bad_exprs.len());
        for bad in &self.bad_exprs {
            let clause_idx = problem.clauses().len();
            property_indices.push(clause_idx);
            problem.add_clause(HornClause::new(
                ClauseBody::new(
                    vec![(inv_pred, curr_args.clone())],
                    Some(bv1_to_bool(bad.clone())),
                ),
                ClauseHead::False,
            ));
        }

        Ok(TranslationResult {
            problem,
            state_vars: self.state_entries,
            property_indices,
        })
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Translate a parsed BTOR2 program into a z4-chc `ChcProblem`.
///
/// The resulting `ChcProblem` has the standard 3-clause structure:
/// 1. Init clause: `init_constraint => Inv(state_vars)`
/// 2. Transition clause: `Inv(curr) /\ trans => Inv(next)`
/// 3. Query clause(s): `Inv(curr) /\ bad => false` (one per `bad` property)
///
/// Input variables are existentially quantified within the transition clause
/// (they appear free in the constraint but not in predicate arguments, so the
/// CHC solver treats them as existential).
pub fn translate_to_chc(program: &Btor2Program) -> Result<TranslationResult, Btor2Error> {
    let mut translator = Translator::new(program);
    translator.resolve_sorts();
    translator.collect_declarations()?;
    translator.collect_semantics()?;
    translator.assemble()
}

/// Translate and solve a BTOR2 program using the memoized translator +
/// `AdaptivePortfolio`.
///
/// This is the preferred entry point for HWMCC benchmarking: the memoized
/// translator avoids exponential DAG-to-tree blowup, and the adaptive
/// portfolio selects BV-native engine lanes.
pub fn check_btor2_adaptive(
    program: &Btor2Program,
    time_budget: Option<Duration>,
) -> Result<Vec<crate::translate::Btor2CheckResult>, Btor2Error> {
    use crate::translate::Btor2CheckResult;

    if program.bad_properties.is_empty() {
        return Ok(vec![]);
    }

    let translation = translate_to_chc(program)?;
    let config = match time_budget {
        Some(budget) => AdaptiveConfig::with_budget(budget, false),
        None => AdaptiveConfig::default(),
    };
    let portfolio = AdaptivePortfolio::new(translation.problem, config);
    let result = portfolio.solve();

    let n = program.bad_properties.len();
    match result {
        VerifiedChcResult::Safe(_) => Ok((0..n).map(|_| Btor2CheckResult::Unsat).collect()),
        VerifiedChcResult::Unsafe(cex) => {
            let trace: Vec<FxHashMap<String, i64>> = cex
                .counterexample()
                .steps
                .iter()
                .map(|step| step.assignments.clone())
                .collect();

            // Determine which bad property was violated by matching the
            // counterexample's query_clause index against our property_indices.
            let violated_prop = cex
                .counterexample()
                .witness
                .as_ref()
                .and_then(|w| w.query_clause)
                .and_then(|clause_idx| {
                    translation
                        .property_indices
                        .iter()
                        .position(|&pi| pi == clause_idx)
                });

            let mut results = Vec::with_capacity(n);
            if let Some(prop_idx) = violated_prop {
                // We know exactly which property was violated.
                // Mark the violated property as Sat and others as Unknown
                // (we cannot confirm them safe from an Unsafe result).
                for i in 0..n {
                    if i == prop_idx {
                        results.push(Btor2CheckResult::Sat {
                            trace: trace.clone(),
                        });
                    } else {
                        results.push(Btor2CheckResult::Unknown {
                            reason: "other property violated; this property not yet checked"
                                .to_string(),
                        });
                    }
                }
            } else if n == 1 {
                // Single property: the counterexample must be for it.
                results.push(Btor2CheckResult::Sat { trace });
            } else {
                // Multiple properties but no witness data to identify which.
                // Conservatively mark all as Unknown since we cannot correctly
                // attribute the counterexample to a specific property.
                for _ in 0..n {
                    results.push(Btor2CheckResult::Unknown {
                        reason: "counterexample found but violated property unknown".to_string(),
                    });
                }
            }
            Ok(results)
        }
        VerifiedChcResult::Unknown(_) | _ => Ok((0..n)
            .map(|_| Btor2CheckResult::Unknown {
                reason: "solver budget exhausted".to_string(),
            })
            .collect()),
    }
}

// ---------------------------------------------------------------------------
// Utility functions
// ---------------------------------------------------------------------------

fn btor2_sort_to_chc(sort: &Btor2Sort) -> ChcSort {
    match sort {
        Btor2Sort::BitVec(w) => ChcSort::BitVec(*w),
        Btor2Sort::Array { index, element } => ChcSort::Array(
            Box::new(btor2_sort_to_chc(index)),
            Box::new(btor2_sort_to_chc(element)),
        ),
    }
}

fn bv_mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// Convenience: build a binary BV operation.
fn bv_op(op: ChcOp, a: ChcExpr, b: ChcExpr) -> ChcExpr {
    ChcExpr::Op(op, vec![Arc::new(a), Arc::new(b)])
}

/// Extract the most-significant (sign) bit of a `w`-bit bitvector as a 1-bit BV.
fn bv_extract_msb(expr: ChcExpr, w: u32) -> ChcExpr {
    ChcExpr::Op(ChcOp::BvExtract(w - 1, w - 1), vec![Arc::new(expr)])
}

/// Convert a 1-bit BV expression to Bool.
///
/// BTOR2 represents all values as bitvectors; CHC distinguishes Bool from
/// BitVec(1). This bridges the gap: `bv1_to_bool(x) = (x == 1bv1)`.
/// Peephole-optimizes the round-trip with `bool_to_bv1`.
fn bv1_to_bool(expr: ChcExpr) -> ChcExpr {
    // Peephole: ite(cond, 1bv1, 0bv1) -> cond
    if let ChcExpr::Op(ChcOp::Ite, ref args) = expr {
        if args.len() == 3 {
            if let (ChcExpr::BitVec(1, 1), ChcExpr::BitVec(0, 1)) =
                (args[1].as_ref(), args[2].as_ref())
            {
                return args[0].as_ref().clone();
            }
        }
    }
    // Peephole: BvNot(x) on 1-bit -> NOT(bv1_to_bool(x)).
    // This keeps the expression well-sorted: BvNot stays in BV domain,
    // and we convert to Bool NOT here at the bridge point (#3803).
    if let ChcExpr::Op(ChcOp::BvNot, ref args) = expr {
        if args.len() == 1 {
            return ChcExpr::not(bv1_to_bool(args[0].as_ref().clone()));
        }
    }
    // Constant fold.
    if let ChcExpr::BitVec(v, 1) = &expr {
        return ChcExpr::Bool(*v != 0);
    }
    ChcExpr::eq(expr, ChcExpr::BitVec(1, 1))
}

/// Convert a Bool expression to 1-bit BV.
///
///   `bool_to_bv1(cond) = ite(cond, 1bv1, 0bv1)`
///
/// Peephole: `(x == 1bv1)` from `bv1_to_bool` -> `x`.
fn bool_to_bv1(expr: ChcExpr) -> ChcExpr {
    // Peephole: (x == 1bv1) -> x
    if let ChcExpr::Op(ChcOp::Eq, ref args) = expr {
        if args.len() == 2 {
            if let ChcExpr::BitVec(1, 1) = args[1].as_ref() {
                return args[0].as_ref().clone();
            }
            if let ChcExpr::BitVec(1, 1) = args[0].as_ref() {
                return args[1].as_ref().clone();
            }
        }
    }
    // Peephole: Bool NOT(x) -> BvNot(bool_to_bv1(x)).
    // Complements the bv1_to_bool peephole for BvNot (#3803).
    if let ChcExpr::Op(ChcOp::Not, ref args) = expr {
        if args.len() == 1 {
            let inner = bool_to_bv1(args[0].as_ref().clone());
            return ChcExpr::Op(ChcOp::BvNot, vec![Arc::new(inner)]);
        }
    }
    // Constant fold.
    if let ChcExpr::Bool(b) = &expr {
        return ChcExpr::BitVec(u128::from(*b), 1);
    }
    ChcExpr::ite(expr, ChcExpr::BitVec(1, 1), ChcExpr::BitVec(0, 1))
}

fn zero_const(sort: &ChcSort) -> ChcExpr {
    match sort {
        ChcSort::BitVec(w) => ChcExpr::BitVec(0, *w),
        _ => ChcExpr::BitVec(0, 1),
    }
}

fn one_const(sort: &ChcSort) -> ChcExpr {
    match sort {
        ChcSort::BitVec(w) => ChcExpr::BitVec(1, *w),
        _ => ChcExpr::BitVec(1, 1),
    }
}

fn ones_const(sort: &ChcSort) -> ChcExpr {
    match sort {
        ChcSort::BitVec(w) => ChcExpr::BitVec(bv_mask(*w), *w),
        _ => ChcExpr::BitVec(1, 1),
    }
}

fn parse_binary_const(bits: &str, sort: &ChcSort) -> ChcExpr {
    let width = match sort {
        ChcSort::BitVec(w) => *w,
        _ => bits.len() as u32,
    };
    let value = u128::from_str_radix(bits, 2).unwrap_or(0);
    ChcExpr::BitVec(value & bv_mask(width), width)
}

fn parse_decimal_const(dec: &str, sort: &ChcSort) -> ChcExpr {
    let width = match sort {
        ChcSort::BitVec(w) => *w,
        _ => 32,
    };
    let value = if let Some(stripped) = dec.strip_prefix('-') {
        let abs_val = stripped.parse::<u128>().unwrap_or(0);
        if width < 128 {
            ((1u128 << width) - abs_val) & bv_mask(width)
        } else {
            abs_val.wrapping_neg()
        }
    } else {
        dec.parse::<u128>().unwrap_or(0) & bv_mask(width)
    };
    ChcExpr::BitVec(value, width)
}

fn parse_hex_const(hex: &str, sort: &ChcSort) -> ChcExpr {
    let width = match sort {
        ChcSort::BitVec(w) => *w,
        _ => (hex.len() * 4) as u32,
    };
    let value = u128::from_str_radix(hex, 16).unwrap_or(0);
    ChcExpr::BitVec(value & bv_mask(width), width)
}

/// Lift a scalar expression to a const-array if the target sort is an array sort.
///
/// BTOR2 allows `init <array_sort> <state> <bv_const>`, meaning "initialize
/// every element to this constant". We detect the sort mismatch and wrap the
/// scalar in `ChcExpr::const_array(key_sort, scalar)`.
///
/// For nested arrays (array of arrays), this recursively wraps so that a
/// single bitvector constant becomes a const-array of const-arrays.
fn lift_scalar_to_array(target_sort: &ChcSort, expr: ChcExpr) -> ChcExpr {
    match target_sort {
        ChcSort::Array(key_sort, elem_sort) => {
            // Recursively lift: if the element sort is also an array,
            // the scalar needs to become a const-array of const-arrays.
            let inner = lift_scalar_to_array(elem_sort, expr);
            ChcExpr::const_array(key_sort.as_ref().clone(), inner)
        }
        _ => {
            // Target sort is scalar — no lifting needed.
            expr
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    /// Build a minimal BTOR2 program: 1-bit state starts at 0, stays at 0.
    /// Bad property: state == 1 (should be safe).
    fn make_trivial_safe_program() -> Btor2Program {
        let mut sorts = HashMap::new();
        sorts.insert(1, Btor2Sort::BitVec(1));

        let lines = vec![
            Btor2Line {
                id: 1,
                sort_id: 0,
                node: Btor2Node::SortBitVec(1),
                args: vec![],
            },
            Btor2Line {
                id: 2,
                sort_id: 1,
                node: Btor2Node::Zero,
                args: vec![],
            },
            Btor2Line {
                id: 3,
                sort_id: 1,
                node: Btor2Node::One,
                args: vec![],
            },
            Btor2Line {
                id: 4,
                sort_id: 1,
                node: Btor2Node::State(1, Some("x".to_string())),
                args: vec![],
            },
            Btor2Line {
                id: 5,
                sort_id: 1,
                node: Btor2Node::Init(1, 4, 2),
                args: vec![],
            },
            Btor2Line {
                id: 6,
                sort_id: 1,
                node: Btor2Node::Next(1, 4, 2),
                args: vec![],
            },
            Btor2Line {
                id: 7,
                sort_id: 0,
                node: Btor2Node::Bad(4),
                args: vec![],
            },
        ];

        Btor2Program {
            lines,
            sorts,
            num_inputs: 0,
            num_states: 1,
            bad_properties: vec![7],
            constraints: vec![],
            fairness: vec![],
            justice: vec![],
        }
    }

    #[test]
    fn test_trivial_safe_translation() {
        let program = make_trivial_safe_program();
        let result = translate_to_chc(&program).unwrap();

        assert_eq!(result.state_vars.len(), 1);
        assert_eq!(result.state_vars[0].name, Some("x".to_string()));
        // 3 clauses: init, transition, query.
        assert_eq!(result.problem.clauses().len(), 3);
        assert_eq!(result.property_indices.len(), 1);
        // Init clause is a fact (no predicates in body).
        assert!(result.problem.clauses()[0].is_fact());
        // Transition clause is not a fact.
        assert!(!result.problem.clauses()[1].is_fact());
        // Query clause has False head.
        assert!(result.problem.clauses()[2].is_query());
    }

    #[test]
    fn test_bv_mask_values() {
        assert_eq!(bv_mask(1), 1);
        assert_eq!(bv_mask(8), 0xFF);
        assert_eq!(bv_mask(32), 0xFFFF_FFFF);
        assert_eq!(bv_mask(64), 0xFFFF_FFFF_FFFF_FFFF);
        assert_eq!(bv_mask(128), u128::MAX);
    }

    #[test]
    fn test_bv1_bool_roundtrip() {
        // Constant roundtrip.
        let bv = bool_to_bv1(ChcExpr::Bool(true));
        assert_eq!(bv, ChcExpr::BitVec(1, 1));
        assert_eq!(bv1_to_bool(bv), ChcExpr::Bool(true));

        // Variable roundtrip: peephole should eliminate wrapping.
        let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(1)));
        assert_eq!(bv1_to_bool(bool_to_bv1(x.clone())), x);
        assert_eq!(bool_to_bv1(bv1_to_bool(x.clone())), x);
    }

    #[test]
    fn test_decimal_const_negative() {
        let sort = ChcSort::BitVec(8);
        assert_eq!(parse_decimal_const("-1", &sort), ChcExpr::BitVec(255, 8));
        assert_eq!(parse_decimal_const("42", &sort), ChcExpr::BitVec(42, 8));
    }

    #[test]
    fn test_add_counter_translation() {
        let mut sorts = HashMap::new();
        sorts.insert(1, Btor2Sort::BitVec(1));
        sorts.insert(2, Btor2Sort::BitVec(8));

        let lines = vec![
            Btor2Line {
                id: 1,
                sort_id: 0,
                node: Btor2Node::SortBitVec(8),
                args: vec![],
            },
            Btor2Line {
                id: 3,
                sort_id: 2,
                node: Btor2Node::Zero,
                args: vec![],
            },
            Btor2Line {
                id: 4,
                sort_id: 2,
                node: Btor2Node::ConstD("1".to_string()),
                args: vec![],
            },
            Btor2Line {
                id: 5,
                sort_id: 2,
                node: Btor2Node::State(2, Some("count".to_string())),
                args: vec![],
            },
            Btor2Line {
                id: 6,
                sort_id: 2,
                node: Btor2Node::Init(2, 5, 3),
                args: vec![],
            },
            Btor2Line {
                id: 7,
                sort_id: 2,
                node: Btor2Node::Add,
                args: vec![5, 4],
            },
            Btor2Line {
                id: 8,
                sort_id: 2,
                node: Btor2Node::Next(2, 5, 7),
                args: vec![],
            },
            Btor2Line {
                id: 9,
                sort_id: 2,
                node: Btor2Node::ConstD("10".to_string()),
                args: vec![],
            },
            Btor2Line {
                id: 10,
                sort_id: 1,
                node: Btor2Node::Eq,
                args: vec![5, 9],
            },
            Btor2Line {
                id: 11,
                sort_id: 0,
                node: Btor2Node::Bad(10),
                args: vec![],
            },
        ];

        let program = Btor2Program {
            lines,
            sorts,
            num_inputs: 0,
            num_states: 1,
            bad_properties: vec![11],
            constraints: vec![],
            fairness: vec![],
            justice: vec![],
        };

        let result = translate_to_chc(&program).unwrap();
        assert_eq!(result.state_vars.len(), 1);
        assert_eq!(result.state_vars[0].name, Some("count".to_string()));
        assert_eq!(result.problem.clauses().len(), 3);
    }

    #[test]
    fn test_negated_reference() {
        let mut sorts = HashMap::new();
        sorts.insert(1, Btor2Sort::BitVec(1));

        // Program: state x, bad -x (negated reference = NOT x)
        let lines = vec![
            Btor2Line {
                id: 1,
                sort_id: 0,
                node: Btor2Node::SortBitVec(1),
                args: vec![],
            },
            Btor2Line {
                id: 2,
                sort_id: 1,
                node: Btor2Node::Zero,
                args: vec![],
            },
            Btor2Line {
                id: 4,
                sort_id: 1,
                node: Btor2Node::State(1, Some("x".to_string())),
                args: vec![],
            },
            Btor2Line {
                id: 5,
                sort_id: 1,
                node: Btor2Node::Init(1, 4, 2),
                args: vec![],
            },
            Btor2Line {
                id: 6,
                sort_id: 1,
                node: Btor2Node::Next(1, 4, 2),
                args: vec![],
            },
            // bad -4 means NOT(state 4)
            Btor2Line {
                id: 7,
                sort_id: 0,
                node: Btor2Node::Bad(-4),
                args: vec![],
            },
        ];

        let program = Btor2Program {
            lines,
            sorts,
            num_inputs: 0,
            num_states: 1,
            bad_properties: vec![7],
            constraints: vec![],
            fairness: vec![],
            justice: vec![],
        };

        let result = translate_to_chc(&program).unwrap();
        assert_eq!(result.problem.clauses().len(), 3);
        // The bad expression should contain a NOT.
        let query = &result.problem.clauses()[2];
        assert!(query.is_query());
    }

    #[test]
    fn test_constraint_in_transition() {
        let mut sorts = HashMap::new();
        sorts.insert(1, Btor2Sort::BitVec(1));

        let lines = vec![
            Btor2Line {
                id: 1,
                sort_id: 0,
                node: Btor2Node::SortBitVec(1),
                args: vec![],
            },
            Btor2Line {
                id: 2,
                sort_id: 1,
                node: Btor2Node::Zero,
                args: vec![],
            },
            Btor2Line {
                id: 3,
                sort_id: 1,
                node: Btor2Node::Input(1, Some("inp".to_string())),
                args: vec![],
            },
            Btor2Line {
                id: 4,
                sort_id: 1,
                node: Btor2Node::State(1, Some("x".to_string())),
                args: vec![],
            },
            Btor2Line {
                id: 5,
                sort_id: 1,
                node: Btor2Node::Init(1, 4, 2),
                args: vec![],
            },
            Btor2Line {
                id: 6,
                sort_id: 1,
                node: Btor2Node::Next(1, 4, 3),
                args: vec![],
            },
            // Constraint: inp must be 0
            Btor2Line {
                id: 7,
                sort_id: 0,
                node: Btor2Node::Constraint(-3),
                args: vec![],
            },
            Btor2Line {
                id: 8,
                sort_id: 0,
                node: Btor2Node::Bad(4),
                args: vec![],
            },
        ];

        let program = Btor2Program {
            lines,
            sorts,
            num_inputs: 1,
            num_states: 1,
            bad_properties: vec![8],
            constraints: vec![7],
            fairness: vec![],
            justice: vec![],
        };

        let result = translate_to_chc(&program).unwrap();
        assert_eq!(result.state_vars.len(), 1);
        // 3 clauses: init, transition (with constraint), query.
        assert_eq!(result.problem.clauses().len(), 3);
        // Transition clause should have a constraint (from environment constraint).
        let trans = &result.problem.clauses()[1];
        assert!(trans.body.constraint.is_some());
    }

    #[test]
    fn test_array_state_translation() {
        // Program with an array state: mem : Array(BV8, BV32)
        // read mem[0], check if it equals 42, bad if so.
        let mut sorts = HashMap::new();
        sorts.insert(1, Btor2Sort::BitVec(1));
        sorts.insert(2, Btor2Sort::BitVec(8));
        sorts.insert(3, Btor2Sort::BitVec(32));
        sorts.insert(
            4,
            Btor2Sort::Array {
                index: Box::new(Btor2Sort::BitVec(8)),
                element: Box::new(Btor2Sort::BitVec(32)),
            },
        );

        let lines = vec![
            Btor2Line {
                id: 1,
                sort_id: 0,
                node: Btor2Node::SortBitVec(8),
                args: vec![],
            },
            Btor2Line {
                id: 2,
                sort_id: 0,
                node: Btor2Node::SortBitVec(32),
                args: vec![],
            },
            Btor2Line {
                id: 3,
                sort_id: 0,
                node: Btor2Node::SortBitVec(1),
                args: vec![],
            },
            Btor2Line {
                id: 4,
                sort_id: 0,
                node: Btor2Node::SortArray(1, 2),
                args: vec![],
            },
            // mem: state of array sort
            Btor2Line {
                id: 5,
                sort_id: 4,
                node: Btor2Node::State(4, Some("mem".to_string())),
                args: vec![],
            },
            // addr = 0 (BV8)
            Btor2Line {
                id: 6,
                sort_id: 2,
                node: Btor2Node::Zero,
                args: vec![],
            },
            // read mem[addr] -> BV32
            Btor2Line {
                id: 7,
                sort_id: 3,
                node: Btor2Node::Read,
                args: vec![5, 6],
            },
            // constd 42
            Btor2Line {
                id: 8,
                sort_id: 3,
                node: Btor2Node::ConstD("42".to_string()),
                args: vec![],
            },
            // eq: read == 42
            Btor2Line {
                id: 9,
                sort_id: 1,
                node: Btor2Node::Eq,
                args: vec![7, 8],
            },
            Btor2Line {
                id: 10,
                sort_id: 0,
                node: Btor2Node::Bad(9),
                args: vec![],
            },
        ];

        let program = Btor2Program {
            lines,
            sorts,
            num_inputs: 0,
            num_states: 1,
            bad_properties: vec![10],
            constraints: vec![],
            fairness: vec![],
            justice: vec![],
        };

        let result = translate_to_chc(&program).unwrap();
        assert_eq!(result.state_vars.len(), 1);
        assert_eq!(result.state_vars[0].name, Some("mem".to_string()));
        // State var sort should be Array.
        assert!(matches!(
            result.state_vars[0].var.sort,
            ChcSort::Array(_, _)
        ));
        // 3 clauses: init, transition, query.
        assert_eq!(result.problem.clauses().len(), 3);
    }

    #[test]
    fn test_array_init_with_constant() {
        // Program: init array state to constant 0 (const-array pattern).
        // This tests: init <array_sort> <state> <bv_const>
        let mut sorts = HashMap::new();
        sorts.insert(1, Btor2Sort::BitVec(8));
        sorts.insert(2, Btor2Sort::BitVec(32));
        sorts.insert(
            3,
            Btor2Sort::Array {
                index: Box::new(Btor2Sort::BitVec(8)),
                element: Box::new(Btor2Sort::BitVec(32)),
            },
        );
        sorts.insert(4, Btor2Sort::BitVec(1));

        let lines = vec![
            Btor2Line {
                id: 1,
                sort_id: 0,
                node: Btor2Node::SortBitVec(8),
                args: vec![],
            },
            Btor2Line {
                id: 2,
                sort_id: 0,
                node: Btor2Node::SortBitVec(32),
                args: vec![],
            },
            Btor2Line {
                id: 3,
                sort_id: 0,
                node: Btor2Node::SortArray(1, 2),
                args: vec![],
            },
            // BV32 zero constant
            Btor2Line {
                id: 4,
                sort_id: 2,
                node: Btor2Node::Zero,
                args: vec![],
            },
            // mem: array state
            Btor2Line {
                id: 5,
                sort_id: 3,
                node: Btor2Node::State(3, Some("mem".to_string())),
                args: vec![],
            },
            // init 3 5 4 — initialize array to constant 0
            Btor2Line {
                id: 6,
                sort_id: 3,
                node: Btor2Node::Init(3, 5, 4),
                args: vec![5, 4],
            },
            // read index
            Btor2Line {
                id: 7,
                sort_id: 1,
                node: Btor2Node::Zero,
                args: vec![],
            },
            // read mem[0]
            Btor2Line {
                id: 8,
                sort_id: 2,
                node: Btor2Node::Read,
                args: vec![5, 7],
            },
            // neq: read != 0
            Btor2Line {
                id: 9,
                sort_id: 4,
                node: Btor2Node::Neq,
                args: vec![8, 4],
            },
            Btor2Line {
                id: 10,
                sort_id: 0,
                node: Btor2Node::Bad(9),
                args: vec![],
            },
        ];

        let program = Btor2Program {
            lines,
            sorts,
            num_inputs: 0,
            num_states: 1,
            bad_properties: vec![10],
            constraints: vec![],
            fairness: vec![],
            justice: vec![],
        };

        // Should not panic — the init clause with a scalar constant for an
        // array state must be handled by lifting to ChcExpr::const_array.
        let result = translate_to_chc(&program).unwrap();
        assert_eq!(result.state_vars.len(), 1);
        assert_eq!(result.problem.clauses().len(), 3);
    }

    #[test]
    fn test_array_write_read_translation() {
        // Program: write mem[addr] = val, then read back and check.
        let mut sorts = HashMap::new();
        sorts.insert(1, Btor2Sort::BitVec(4));
        sorts.insert(2, Btor2Sort::BitVec(8));
        sorts.insert(
            3,
            Btor2Sort::Array {
                index: Box::new(Btor2Sort::BitVec(4)),
                element: Box::new(Btor2Sort::BitVec(8)),
            },
        );
        sorts.insert(4, Btor2Sort::BitVec(1));

        let lines = vec![
            Btor2Line {
                id: 1,
                sort_id: 0,
                node: Btor2Node::SortBitVec(4),
                args: vec![],
            },
            Btor2Line {
                id: 2,
                sort_id: 0,
                node: Btor2Node::SortBitVec(8),
                args: vec![],
            },
            Btor2Line {
                id: 3,
                sort_id: 0,
                node: Btor2Node::SortArray(1, 2),
                args: vec![],
            },
            // mem: array state (unconstrained init)
            Btor2Line {
                id: 5,
                sort_id: 3,
                node: Btor2Node::State(3, Some("mem".to_string())),
                args: vec![],
            },
            // addr: input BV4
            Btor2Line {
                id: 6,
                sort_id: 1,
                node: Btor2Node::Input(1, Some("addr".to_string())),
                args: vec![],
            },
            // val: constd 42 BV8
            Btor2Line {
                id: 7,
                sort_id: 2,
                node: Btor2Node::ConstD("42".to_string()),
                args: vec![],
            },
            // write mem[addr] = val -> new array
            Btor2Line {
                id: 8,
                sort_id: 3,
                node: Btor2Node::Write,
                args: vec![5, 6, 7],
            },
            // next mem = written array
            Btor2Line {
                id: 9,
                sort_id: 3,
                node: Btor2Node::Next(3, 5, 8),
                args: vec![],
            },
            // read mem[addr]
            Btor2Line {
                id: 10,
                sort_id: 2,
                node: Btor2Node::Read,
                args: vec![5, 6],
            },
            // neq: read != 42
            Btor2Line {
                id: 11,
                sort_id: 4,
                node: Btor2Node::Neq,
                args: vec![10, 7],
            },
            Btor2Line {
                id: 12,
                sort_id: 0,
                node: Btor2Node::Bad(11),
                args: vec![],
            },
        ];

        let program = Btor2Program {
            lines,
            sorts,
            num_inputs: 1,
            num_states: 1,
            bad_properties: vec![12],
            constraints: vec![],
            fairness: vec![],
            justice: vec![],
        };

        let result = translate_to_chc(&program).unwrap();
        assert_eq!(result.state_vars.len(), 1);
        assert_eq!(result.problem.clauses().len(), 3);
        // Transition clause should have next-state constraint (from write).
        let trans = &result.problem.clauses()[1];
        assert!(trans.body.constraint.is_some());
    }

    #[test]
    fn test_lift_scalar_to_array() {
        // Scalar target sort: no lifting.
        let bv_sort = ChcSort::BitVec(32);
        let expr = ChcExpr::BitVec(0, 32);
        let lifted = lift_scalar_to_array(&bv_sort, expr.clone());
        assert_eq!(lifted, expr);

        // Array target sort: lift scalar to const-array.
        let arr_sort = ChcSort::Array(Box::new(ChcSort::BitVec(8)), Box::new(ChcSort::BitVec(32)));
        let lifted = lift_scalar_to_array(&arr_sort, ChcExpr::BitVec(0, 32));
        assert!(
            matches!(&lifted, ChcExpr::ConstArray(_, _)),
            "expected ConstArray, got: {lifted:?}"
        );

        // Nested array: lift scalar through two levels.
        let nested_sort = ChcSort::Array(
            Box::new(ChcSort::BitVec(4)),
            Box::new(ChcSort::Array(
                Box::new(ChcSort::BitVec(8)),
                Box::new(ChcSort::BitVec(32)),
            )),
        );
        let lifted = lift_scalar_to_array(&nested_sort, ChcExpr::BitVec(0, 32));
        // Outer should be ConstArray.
        assert!(
            matches!(&lifted, ChcExpr::ConstArray(_, inner) if {
                matches!(inner.as_ref(), ChcExpr::ConstArray(_, _))
            }),
            "expected nested ConstArray, got: {lifted:?}"
        );
    }

    #[test]
    fn test_parse_and_translate_array_benchmark() {
        // Parse the pono constarrtest benchmark from text.
        let src = "\
1 sort bitvec 4
2 sort bitvec 8
3 sort array 1 2
4 const 2 00000000
5 state 3 mem
6 state 1 x
7 state 2 elem
8 init 3 5 4
9 read 2 5 6
10 inc 1 6
11 next 1 6 10
12 sort bitvec 1
13 neq 12 9 4
14 next 3 5 5
15 bad 13
";
        let program = crate::parser::parse(src).unwrap();
        let result = translate_to_chc(&program).unwrap();
        // 3 state vars: mem (array), x (BV4), elem (BV8).
        assert_eq!(result.state_vars.len(), 3);
        // 3 clauses: init, transition, query.
        assert_eq!(result.problem.clauses().len(), 3);
        // mem state should have Array sort.
        let mem_entry = result
            .state_vars
            .iter()
            .find(|e| e.name == Some("mem".to_string()))
            .expect("should have mem state");
        assert!(
            matches!(mem_entry.var.sort, ChcSort::Array(_, _)),
            "mem should have Array sort"
        );
    }

    /// Regression test for #3803: negated 1-bit references must use BvNot,
    /// not Bool NOT. The bakery.3.prop1 benchmark has `and 1 -state -cmp`
    /// where both args are negated 1-bit nodes. The old code used
    /// `ChcExpr::not` (Bool NOT) which produced ill-sorted expressions
    /// like `eq(Not(BV_var), 1bv1)` instead of `eq(BvNot(BV_var), 1bv1)`.
    #[test]
    fn test_negated_1bit_uses_bvnot() {
        // Program: two 1-bit states a and b, both init to 0.
        // bad = and(-a, -b) = NOT(a) AND NOT(b) as 1-bit BV.
        // Since a and b start at 0 and next=0, bad = AND(NOT(0), NOT(0)) = AND(1,1) = 1.
        // This SHOULD be sat (bad is reachable in initial state).
        let src = "\
1 sort bitvec 1
2 zero 1
3 state 1 a
4 init 1 3 2
5 next 1 3 2
6 state 1 b
7 init 1 6 2
8 next 1 6 2
9 and 1 -3 -6
10 bad 9
";
        let program = crate::parser::parse(src).unwrap();
        let result = translate_to_chc(&program).unwrap();

        // Verify structural properties.
        assert_eq!(result.state_vars.len(), 2);
        assert_eq!(result.problem.clauses().len(), 3);

        // The bad expression (from node 9: and(-3, -6)) should contain
        // BvNot, not Bool Not.
        let query_clause = &result.problem.clauses()[2];
        assert!(query_clause.is_query());

        // Check that the constraint in the query clause does not contain
        // any Bool Not applied to BV variables. Walk the expression tree.
        if let Some(constraint) = query_clause.body.constraint.as_ref() {
            fn check_no_bool_not_on_bv(expr: &ChcExpr, depth: usize) {
                if depth > 100 {
                    return;
                }
                if let ChcExpr::Op(ChcOp::Not, args) = expr {
                    // Bool NOT is OK if applied to a Bool expression
                    // (eq, and, or, not, etc.) but NOT OK if applied to
                    // a BV variable or BV op.
                    for arg in args {
                        if matches!(arg.as_ref(), ChcExpr::Var(v) if matches!(v.sort, ChcSort::BitVec(_)))
                        {
                            panic!("Found Bool NOT applied to BV variable: Not({:?})", arg);
                        }
                        if matches!(arg.as_ref(), ChcExpr::Op(op, _) if matches!(op,
                            ChcOp::BvNot | ChcOp::BvAnd | ChcOp::BvOr |
                            ChcOp::BvAdd | ChcOp::BvSub))
                        {
                            panic!("Found Bool NOT applied to BV op: Not({:?})", arg);
                        }
                    }
                }
                if let ChcExpr::Op(_, args) = expr {
                    for arg in args {
                        check_no_bool_not_on_bv(arg, depth + 1);
                    }
                }
            }
            check_no_bool_not_on_bv(constraint, 0);
        }
    }

    /// Regression test for #3803: the explicit BTOR2 `not` opcode on
    /// 1-bit values must also use BvNot, not Bool NOT.
    #[test]
    fn test_explicit_not_1bit_uses_bvnot() {
        let src = "\
1 sort bitvec 1
2 zero 1
3 state 1 x
4 init 1 3 2
5 next 1 3 2
6 not 1 3
7 bad 6
";
        let program = crate::parser::parse(src).unwrap();
        let result = translate_to_chc(&program).unwrap();

        // The bad expression comes from node 6 (not 1 3 = NOT(x)).
        // Verify it's BvNot, not Bool Not.
        let query_clause = &result.problem.clauses()[2];
        assert!(query_clause.is_query());

        if let Some(constraint) = query_clause.body.constraint.as_ref() {
            fn check_no_bool_not_on_bv(expr: &ChcExpr, depth: usize) {
                if depth > 100 {
                    return;
                }
                if let ChcExpr::Op(ChcOp::Not, args) = expr {
                    for arg in args {
                        if matches!(arg.as_ref(), ChcExpr::Var(v) if matches!(v.sort, ChcSort::BitVec(_)))
                        {
                            panic!("Found Bool NOT applied to BV variable: Not({:?})", arg);
                        }
                    }
                }
                if let ChcExpr::Op(_, args) = expr {
                    for arg in args {
                        check_no_bool_not_on_bv(arg, depth + 1);
                    }
                }
            }
            check_no_bool_not_on_bv(constraint, 0);
        }
    }
}
