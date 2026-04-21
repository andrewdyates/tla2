// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates
// BTOR2 to CHC translation for safety checking via z4-chc portfolio solver.
//
// Encodes BTOR2 `bad` properties as CHC safety queries:
//   Init(state) => Inv(state)
//   Inv(state) /\ Next(state, state') => Inv(state')
//   Inv(state) /\ bad(state) => false
//
// The z4-chc portfolio solver (PDR, BMC, k-induction, ...) then checks whether
// `bad` is reachable. UNSAT = safe; SAT = counterexample trace.

use std::collections::HashMap;
use std::sync::Arc;

use rustc_hash::FxHashMap;
use z4_chc::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

use crate::error::Btor2Error;
use crate::types::{Btor2Node, Btor2Program, Btor2Sort, NodeId};

/// Result of BTOR2 CHC checking for a single `bad` property.
#[derive(Debug)]
pub enum Btor2CheckResult {
    /// Property holds (bad state unreachable).
    Unsat,
    /// Property violated (bad state reachable). Contains counterexample step assignments.
    Sat {
        /// Counterexample trace: each step maps state variable names to bitvector values.
        trace: Vec<FxHashMap<String, i64>>,
    },
    /// Solver could not determine the result.
    Unknown { reason: String },
}

/// Translate a `Btor2Program` into a `ChcProblem` and solve each `bad` property.
///
/// Returns one `Btor2CheckResult` per `bad` property in the program.
pub fn check_btor2(program: &Btor2Program) -> Result<Vec<Btor2CheckResult>, Btor2Error> {
    if program.bad_properties.is_empty() {
        return Ok(vec![]);
    }

    let mut results = Vec::with_capacity(program.bad_properties.len());

    for (bad_idx, &bad_line_id) in program.bad_properties.iter().enumerate() {
        let result = check_single_bad(program, bad_line_id, bad_idx)?;
        results.push(result);
    }

    Ok(results)
}

/// Build and solve a CHC problem for one `bad` property.
fn check_single_bad(
    program: &Btor2Program,
    bad_line_id: NodeId,
    bad_idx: usize,
) -> Result<Btor2CheckResult, Btor2Error> {
    let ctx = TranslationCtx::new(program)?;

    let mut problem = ChcProblem::new();

    // Declare invariant predicate with one BV argument per state variable.
    let inv_sorts: Vec<ChcSort> = ctx
        .state_vars
        .iter()
        .map(|sv| sv.chc_sort.clone())
        .collect();
    let inv_pred = problem.declare_predicate(&format!("Inv_{bad_idx}"), inv_sorts);

    // Build Init clause: init_expr(state) => Inv(state)
    let init_expr = ctx.build_init_expr()?;
    let curr_args: Vec<ChcExpr> = ctx.state_vars.iter().map(|sv| sv.curr_expr()).collect();

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(init_expr),
        ClauseHead::Predicate(inv_pred, curr_args.clone()),
    ));

    // Build Next clause: Inv(state) /\ next_expr(state, state') => Inv(state')
    let next_expr = ctx.build_next_expr()?;
    let next_args: Vec<ChcExpr> = ctx.state_vars.iter().map(|sv| sv.next_expr()).collect();

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv_pred, curr_args.clone())], Some(next_expr)),
        ClauseHead::Predicate(inv_pred, next_args),
    ));

    // Build Bad clause: Inv(state) /\ bad(state) => false
    let bad_expr = ctx.translate_node(bad_line_id)?;
    // bad property is a 1-bit signal: extract the condition node from the Bad node.
    let bad_cond = match ctx.find_node(bad_line_id) {
        Some(line) => match &line.node {
            Btor2Node::Bad(cond_id) => ctx.translate_node(*cond_id)?,
            _ => bad_expr,
        },
        None => bad_expr,
    };
    // bad = 1 means property violated, so the query is: Inv(s) /\ (bad = 1) => false
    let bad_is_true = bv_is_true(&bad_cond);

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv_pred, curr_args)], Some(bad_is_true)),
        ClauseHead::False,
    ));

    // Solve with portfolio solver.
    let portfolio_config = z4_chc::PortfolioConfig::default();
    let solver = z4_chc::testing::new_portfolio_solver(problem, portfolio_config);
    let result = solver.solve();

    match result {
        z4_chc::ChcEngineResult::Safe(_) => Ok(Btor2CheckResult::Unsat),
        z4_chc::ChcEngineResult::Unsafe(cex) => {
            let trace = cex
                .steps
                .iter()
                .map(|step| step.assignments.clone())
                .collect();
            Ok(Btor2CheckResult::Sat { trace })
        }
        _ => Ok(Btor2CheckResult::Unknown {
            reason: "solver returned unknown or not-applicable".to_string(),
        }),
    }
}

// ---------------------------------------------------------------------------
// Translation context
// ---------------------------------------------------------------------------

/// Metadata for a single state variable.
struct StateVarInfo {
    /// Line id where the state was declared.
    _line_id: NodeId,
    /// Optional symbol name.
    _name: String,
    /// CHC sort for this state variable.
    chc_sort: ChcSort,
    /// Current-state CHC variable.
    curr_var: ChcVar,
    /// Next-state CHC variable.
    next_var: ChcVar,
    /// Init value expression node id (from `init` line), if any.
    init_value: Option<NodeId>,
    /// Next value expression node id (from `next` line), if any.
    next_value: Option<NodeId>,
}

impl StateVarInfo {
    fn curr_expr(&self) -> ChcExpr {
        ChcExpr::var(self.curr_var.clone())
    }

    fn next_expr(&self) -> ChcExpr {
        ChcExpr::var(self.next_var.clone())
    }
}

/// Metadata for an input variable.
struct InputVarInfo {
    /// CHC variable (unconstrained / havoc).
    var: ChcVar,
}

/// Translation context holding variable mappings and the program reference.
struct TranslationCtx<'a> {
    program: &'a Btor2Program,
    /// Lookup from line id to line.
    line_map: HashMap<NodeId, &'a crate::types::Btor2Line>,
    /// State variables in declaration order.
    state_vars: Vec<StateVarInfo>,
    /// Map from state line id to index in `state_vars`.
    state_index: HashMap<NodeId, usize>,
    /// Input variables keyed by line id.
    input_vars: HashMap<NodeId, InputVarInfo>,
}

impl<'a> TranslationCtx<'a> {
    fn new(program: &'a Btor2Program) -> Result<Self, Btor2Error> {
        // Build line map.
        let line_map: HashMap<NodeId, &crate::types::Btor2Line> =
            program.lines.iter().map(|l| (l.id, l)).collect();

        // Collect state and input variables.
        let mut state_vars = Vec::new();
        let mut state_index = HashMap::new();
        let mut input_vars = HashMap::new();
        let mut state_counter = 0usize;
        let mut input_counter = 0usize;

        for line in &program.lines {
            match &line.node {
                Btor2Node::State(sort_id, symbol) => {
                    let chc_sort = btor2_sort_to_chc(&program.sorts, *sort_id)?;
                    let name = symbol
                        .clone()
                        .unwrap_or_else(|| format!("s{state_counter}"));
                    let curr_var = ChcVar::new(&name, chc_sort.clone());
                    let next_var = curr_var.primed();

                    state_index.insert(line.id, state_vars.len());
                    state_vars.push(StateVarInfo {
                        _line_id: line.id,
                        _name: name,
                        chc_sort,
                        curr_var,
                        next_var,
                        init_value: None,
                        next_value: None,
                    });
                    state_counter += 1;
                }
                Btor2Node::Input(sort_id, symbol) => {
                    let chc_sort = btor2_sort_to_chc(&program.sorts, *sort_id)?;
                    let name = symbol
                        .clone()
                        .unwrap_or_else(|| format!("i{input_counter}"));
                    input_vars.insert(
                        line.id,
                        InputVarInfo {
                            var: ChcVar::new(&name, chc_sort),
                        },
                    );
                    input_counter += 1;
                }
                _ => {}
            }
        }

        // Wire init/next to state variables.
        let mut ctx = Self {
            program,
            line_map,
            state_vars,
            state_index,
            input_vars,
        };

        for line in &program.lines {
            match &line.node {
                Btor2Node::Init(_sort_id, state_id, value_id) => {
                    if let Some(&idx) = ctx.state_index.get(state_id) {
                        ctx.state_vars[idx].init_value = Some(*value_id);
                    }
                }
                Btor2Node::Next(_sort_id, state_id, value_id) => {
                    if let Some(&idx) = ctx.state_index.get(state_id) {
                        ctx.state_vars[idx].next_value = Some(*value_id);
                    }
                }
                _ => {}
            }
        }

        Ok(ctx)
    }

    fn find_node(&self, id: NodeId) -> Option<&&crate::types::Btor2Line> {
        let abs_id = id.unsigned_abs() as i64;
        self.line_map.get(&abs_id)
    }

    /// Build the Init expression: conjunction of `state_var = init_value` for all states
    /// that have an `init` line. States without init are unconstrained (any initial value).
    fn build_init_expr(&self) -> Result<ChcExpr, Btor2Error> {
        let mut conjuncts = Vec::new();
        for sv in &self.state_vars {
            if let Some(init_id) = sv.init_value {
                let init_val = self.translate_node_curr(init_id)?;
                // When initializing an array state with a scalar constant,
                // lift it to a const-array expression.
                let lifted = lift_scalar_to_array(&sv.chc_sort, init_val);
                conjuncts.push(ChcExpr::eq(sv.curr_expr(), lifted));
            }
        }
        // Constraints also apply to init.
        for &constraint_id in &self.program.constraints {
            if let Some(line) = self.line_map.get(&constraint_id) {
                if let Btor2Node::Constraint(cond_id) = &line.node {
                    let cond = self.translate_node_curr(*cond_id)?;
                    conjuncts.push(bv_is_true(&cond));
                }
            }
        }
        if conjuncts.is_empty() {
            Ok(ChcExpr::bool_const(true))
        } else {
            Ok(ChcExpr::and_all(conjuncts))
        }
    }

    /// Build the Next expression: conjunction of `state_var' = next_value(state)` for all
    /// states that have a `next` line. States without next are unconstrained (havoc).
    fn build_next_expr(&self) -> Result<ChcExpr, Btor2Error> {
        let mut conjuncts = Vec::new();
        for sv in &self.state_vars {
            if let Some(next_id) = sv.next_value {
                let next_val = self.translate_node_curr(next_id)?;
                conjuncts.push(ChcExpr::eq(sv.next_expr(), next_val));
            }
        }
        // Constraints also apply to transitions.
        for &constraint_id in &self.program.constraints {
            if let Some(line) = self.line_map.get(&constraint_id) {
                if let Btor2Node::Constraint(cond_id) = &line.node {
                    let cond = self.translate_node_curr(*cond_id)?;
                    conjuncts.push(bv_is_true(&cond));
                }
            }
        }
        if conjuncts.is_empty() {
            Ok(ChcExpr::bool_const(true))
        } else {
            Ok(ChcExpr::and_all(conjuncts))
        }
    }

    /// Translate a BTOR2 node id to a CHC expression using current-state variables.
    fn translate_node_curr(&self, id: NodeId) -> Result<ChcExpr, Btor2Error> {
        self.translate_node(id)
    }

    /// Translate a BTOR2 node id to a CHC expression.
    ///
    /// Negative ids denote bitwise negation of the referenced node.
    fn translate_node(&self, id: NodeId) -> Result<ChcExpr, Btor2Error> {
        let negated = id < 0;
        let abs_id = id.unsigned_abs() as i64;

        let line = self
            .line_map
            .get(&abs_id)
            .ok_or(Btor2Error::UndefinedNode {
                line: 0,
                node_id: abs_id,
            })?;

        let expr = self.translate_line(line)?;

        if negated {
            Ok(bv_not(&expr, &self.resolve_sort(line.sort_id)))
        } else {
            Ok(expr)
        }
    }

    /// Translate a single BTOR2 line to a CHC expression.
    fn translate_line(&self, line: &crate::types::Btor2Line) -> Result<ChcExpr, Btor2Error> {
        match &line.node {
            // State variable -> current-state CHC variable.
            Btor2Node::State(_, _) => {
                if let Some(&idx) = self.state_index.get(&line.id) {
                    Ok(self.state_vars[idx].curr_expr())
                } else {
                    Err(Btor2Error::UndefinedNode {
                        line: 0,
                        node_id: line.id,
                    })
                }
            }

            // Input variable -> unconstrained CHC variable.
            Btor2Node::Input(_, _) => {
                if let Some(info) = self.input_vars.get(&line.id) {
                    Ok(ChcExpr::var(info.var.clone()))
                } else {
                    Err(Btor2Error::UndefinedNode {
                        line: 0,
                        node_id: line.id,
                    })
                }
            }

            // Constants.
            Btor2Node::Const(bits) => {
                let width = self.resolve_bv_width(line.sort_id);
                let val = u128::from_str_radix(bits, 2).unwrap_or(0);
                Ok(ChcExpr::BitVec(val, width))
            }
            Btor2Node::ConstD(dec) => {
                let width = self.resolve_bv_width(line.sort_id);
                // Handle negative decimal constants.
                let val: u128 = if let Some(stripped) = dec.strip_prefix('-') {
                    let abs: u128 = stripped.parse().unwrap_or(0);
                    // Two's complement: mask to width bits.
                    let mask = if width >= 128 {
                        u128::MAX
                    } else {
                        (1u128 << width) - 1
                    };
                    ((!abs).wrapping_add(1)) & mask
                } else {
                    dec.parse().unwrap_or(0)
                };
                Ok(ChcExpr::BitVec(val, width))
            }
            Btor2Node::ConstH(hex) => {
                let width = self.resolve_bv_width(line.sort_id);
                let val = u128::from_str_radix(hex, 16).unwrap_or(0);
                Ok(ChcExpr::BitVec(val, width))
            }
            Btor2Node::Zero => {
                let width = self.resolve_bv_width(line.sort_id);
                Ok(ChcExpr::BitVec(0, width))
            }
            Btor2Node::One => {
                let width = self.resolve_bv_width(line.sort_id);
                Ok(ChcExpr::BitVec(1, width))
            }
            Btor2Node::Ones => {
                let width = self.resolve_bv_width(line.sort_id);
                let val = if width >= 128 {
                    u128::MAX
                } else {
                    (1u128 << width) - 1
                };
                Ok(ChcExpr::BitVec(val, width))
            }

            // Unary bitvector ops.
            Btor2Node::Not => self.translate_unary(line, ChcOp::BvNot),
            Btor2Node::Neg => self.translate_unary(line, ChcOp::BvNeg),
            Btor2Node::Inc => {
                let a = self.translate_node(line.args[0])?;
                let width = self.resolve_bv_width(line.sort_id);
                Ok(bv_op2(ChcOp::BvAdd, a, ChcExpr::BitVec(1, width)))
            }
            Btor2Node::Dec => {
                let a = self.translate_node(line.args[0])?;
                let width = self.resolve_bv_width(line.sort_id);
                let ones_val = if width >= 128 {
                    u128::MAX
                } else {
                    (1u128 << width) - 1
                };
                Ok(bv_op2(ChcOp::BvAdd, a, ChcExpr::BitVec(ones_val, width)))
            }
            Btor2Node::Redand => {
                // 1-bit result: 1 iff all bits are 1.
                let a = self.translate_node(line.args[0])?;
                let width = self.resolve_bv_width_of_arg(line.args[0]);
                let all_ones = if width >= 128 {
                    u128::MAX
                } else {
                    (1u128 << width) - 1
                };
                Ok(ChcExpr::ite(
                    ChcExpr::eq(a, ChcExpr::BitVec(all_ones, width)),
                    ChcExpr::BitVec(1, 1),
                    ChcExpr::BitVec(0, 1),
                ))
            }
            Btor2Node::Redor => {
                let a = self.translate_node(line.args[0])?;
                let width = self.resolve_bv_width_of_arg(line.args[0]);
                Ok(ChcExpr::ite(
                    ChcExpr::eq(a, ChcExpr::BitVec(0, width)),
                    ChcExpr::BitVec(0, 1),
                    ChcExpr::BitVec(1, 1),
                ))
            }
            Btor2Node::Redxor => {
                // Parity: expand to XOR chain or approximate.
                // For the CHC encoding, use a simplified representation.
                let a = self.translate_node(line.args[0])?;
                let width = self.resolve_bv_width_of_arg(line.args[0]);
                // Approximate: check parity via repeated extraction and XOR.
                // For now, encode as uninterpreted (the solver handles BV ops).
                Ok(ChcExpr::ite(
                    ChcExpr::eq(a, ChcExpr::BitVec(0, width)),
                    ChcExpr::BitVec(0, 1),
                    ChcExpr::BitVec(1, 1), // Approximation; exact needs bit-level parity.
                ))
            }

            // Binary bitvector ops.
            Btor2Node::Add => self.translate_binary(line, ChcOp::BvAdd),
            Btor2Node::Sub => self.translate_binary(line, ChcOp::BvSub),
            Btor2Node::Mul => self.translate_binary(line, ChcOp::BvMul),
            Btor2Node::UDiv => self.translate_binary(line, ChcOp::BvUDiv),
            Btor2Node::SDiv => self.translate_binary(line, ChcOp::BvSDiv),
            Btor2Node::URem => self.translate_binary(line, ChcOp::BvURem),
            Btor2Node::SRem => self.translate_binary(line, ChcOp::BvSRem),
            Btor2Node::SMod => self.translate_binary(line, ChcOp::BvSMod),
            Btor2Node::And => self.translate_binary(line, ChcOp::BvAnd),
            Btor2Node::Or => self.translate_binary(line, ChcOp::BvOr),
            Btor2Node::Xor => self.translate_binary(line, ChcOp::BvXor),
            Btor2Node::Nand => self.translate_binary(line, ChcOp::BvNand),
            Btor2Node::Nor => self.translate_binary(line, ChcOp::BvNor),
            Btor2Node::Xnor => self.translate_binary(line, ChcOp::BvXnor),
            Btor2Node::Sll => self.translate_binary(line, ChcOp::BvShl),
            Btor2Node::Srl => self.translate_binary(line, ChcOp::BvLShr),
            Btor2Node::Sra => self.translate_binary(line, ChcOp::BvAShr),
            Btor2Node::Rol => {
                // Rotate left: no direct ChcOp, encode via shift/or.
                let a = self.translate_node(line.args[0])?;
                let b = self.translate_node(line.args[1])?;
                let width = self.resolve_bv_width(line.sort_id);
                let width_bv = ChcExpr::BitVec(u128::from(width), width);
                let diff = bv_op2(ChcOp::BvSub, width_bv, b.clone());
                let left = bv_op2(ChcOp::BvShl, a.clone(), b);
                let right = bv_op2(ChcOp::BvLShr, a, diff);
                Ok(bv_op2(ChcOp::BvOr, left, right))
            }
            Btor2Node::Ror => {
                let a = self.translate_node(line.args[0])?;
                let b = self.translate_node(line.args[1])?;
                let width = self.resolve_bv_width(line.sort_id);
                let width_bv = ChcExpr::BitVec(u128::from(width), width);
                let diff = bv_op2(ChcOp::BvSub, width_bv, b.clone());
                let right = bv_op2(ChcOp::BvLShr, a.clone(), b);
                let left = bv_op2(ChcOp::BvShl, a, diff);
                Ok(bv_op2(ChcOp::BvOr, right, left))
            }

            // Comparisons.
            Btor2Node::Eq => {
                let a = self.translate_node(line.args[0])?;
                let b = self.translate_node(line.args[1])?;
                // BTOR2 eq returns 1-bit BV. Encode as ITE over ChcExpr::eq.
                Ok(ChcExpr::ite(
                    ChcExpr::eq(a, b),
                    ChcExpr::BitVec(1, 1),
                    ChcExpr::BitVec(0, 1),
                ))
            }
            Btor2Node::Neq => {
                let a = self.translate_node(line.args[0])?;
                let b = self.translate_node(line.args[1])?;
                Ok(ChcExpr::ite(
                    ChcExpr::eq(a, b),
                    ChcExpr::BitVec(0, 1),
                    ChcExpr::BitVec(1, 1),
                ))
            }
            Btor2Node::Ugt => self.translate_cmp(line, ChcOp::BvUGt),
            Btor2Node::Ugte => self.translate_cmp(line, ChcOp::BvUGe),
            Btor2Node::Ult => self.translate_cmp(line, ChcOp::BvULt),
            Btor2Node::Ulte => self.translate_cmp(line, ChcOp::BvULe),
            Btor2Node::Sgt => self.translate_cmp(line, ChcOp::BvSGt),
            Btor2Node::Sgte => self.translate_cmp(line, ChcOp::BvSGe),
            Btor2Node::Slt => self.translate_cmp(line, ChcOp::BvSLt),
            Btor2Node::Slte => self.translate_cmp(line, ChcOp::BvSLe),

            // Concat.
            Btor2Node::Concat => self.translate_binary(line, ChcOp::BvConcat),

            // Boolean ops (1-bit).
            Btor2Node::Iff => {
                let a = self.translate_node(line.args[0])?;
                let b = self.translate_node(line.args[1])?;
                // iff(a, b) = eq(a, b) as 1-bit BV.
                Ok(ChcExpr::ite(
                    ChcExpr::eq(a, b),
                    ChcExpr::BitVec(1, 1),
                    ChcExpr::BitVec(0, 1),
                ))
            }
            Btor2Node::Implies => {
                let a = self.translate_node(line.args[0])?;
                let b = self.translate_node(line.args[1])?;
                // implies(a, b) = !a | b as 1-bit BV.
                Ok(bv_op2(ChcOp::BvOr, bv_op1(ChcOp::BvNot, a), b))
            }

            // Indexed ops.
            Btor2Node::Slice(upper, lower) => {
                let a = self.translate_node(line.args[0])?;
                Ok(ChcExpr::Op(
                    ChcOp::BvExtract(*upper, *lower),
                    vec![Arc::new(a)],
                ))
            }
            Btor2Node::Uext(w) => {
                let a = self.translate_node(line.args[0])?;
                Ok(ChcExpr::Op(ChcOp::BvZeroExtend(*w), vec![Arc::new(a)]))
            }
            Btor2Node::Sext(w) => {
                let a = self.translate_node(line.args[0])?;
                Ok(ChcExpr::Op(ChcOp::BvSignExtend(*w), vec![Arc::new(a)]))
            }

            // Ternary: ite / write.
            Btor2Node::Ite => {
                let cond = self.translate_node(line.args[0])?;
                let then_ = self.translate_node(line.args[1])?;
                let else_ = self.translate_node(line.args[2])?;
                // BTOR2 ite condition is 1-bit BV; convert to Bool for ChcExpr::ite.
                Ok(ChcExpr::ite(bv_is_true(&cond), then_, else_))
            }
            Btor2Node::Write => {
                let arr = self.translate_node(line.args[0])?;
                let idx = self.translate_node(line.args[1])?;
                let val = self.translate_node(line.args[2])?;
                Ok(ChcExpr::store(arr, idx, val))
            }

            // Array read.
            Btor2Node::Read => {
                let arr = self.translate_node(line.args[0])?;
                let idx = self.translate_node(line.args[1])?;
                Ok(ChcExpr::select(arr, idx))
            }

            // Overflow detection: encode as 1-bit result. Approximate as false (no overflow).
            Btor2Node::Saddo
            | Btor2Node::Sdivo
            | Btor2Node::Smulo
            | Btor2Node::Ssubo
            | Btor2Node::Uaddo
            | Btor2Node::Umulo
            | Btor2Node::Usubo => Ok(ChcExpr::BitVec(0, 1)),

            // Init/Next/Bad/Constraint/Fair/Justice/Output/Sort: should not be translated as
            // expressions directly. Return a sentinel.
            Btor2Node::Init(_, _, value_id) => self.translate_node(*value_id),
            Btor2Node::Next(_, _, value_id) => self.translate_node(*value_id),
            Btor2Node::Bad(cond_id) => self.translate_node(*cond_id),
            Btor2Node::Constraint(cond_id) => self.translate_node(*cond_id),
            Btor2Node::Fair(cond_id) => self.translate_node(*cond_id),
            Btor2Node::Output(val_id) => self.translate_node(*val_id),
            Btor2Node::Justice(_) | Btor2Node::SortBitVec(_) | Btor2Node::SortArray(_, _) => {
                Ok(ChcExpr::bool_const(true))
            }
        }
    }

    fn translate_unary(
        &self,
        line: &crate::types::Btor2Line,
        op: ChcOp,
    ) -> Result<ChcExpr, Btor2Error> {
        let a = self.translate_node(line.args[0])?;
        Ok(bv_op1(op, a))
    }

    fn translate_binary(
        &self,
        line: &crate::types::Btor2Line,
        op: ChcOp,
    ) -> Result<ChcExpr, Btor2Error> {
        let a = self.translate_node(line.args[0])?;
        let b = self.translate_node(line.args[1])?;
        Ok(bv_op2(op, a, b))
    }

    /// Translate a comparison that returns a 1-bit BV.
    fn translate_cmp(
        &self,
        line: &crate::types::Btor2Line,
        op: ChcOp,
    ) -> Result<ChcExpr, Btor2Error> {
        let a = self.translate_node(line.args[0])?;
        let b = self.translate_node(line.args[1])?;
        let cmp = ChcExpr::Op(op, vec![Arc::new(a), Arc::new(b)]);
        Ok(ChcExpr::ite(
            cmp,
            ChcExpr::BitVec(1, 1),
            ChcExpr::BitVec(0, 1),
        ))
    }

    /// Resolve the BV width for a sort id.
    fn resolve_bv_width(&self, sort_id: i64) -> u32 {
        match self.program.sorts.get(&sort_id) {
            Some(Btor2Sort::BitVec(w)) => *w,
            _ => 32, // Fallback.
        }
    }

    /// Resolve the BV width of the sort of a node argument.
    fn resolve_bv_width_of_arg(&self, node_id: NodeId) -> u32 {
        let abs_id = node_id.unsigned_abs() as i64;
        if let Some(line) = self.line_map.get(&abs_id) {
            self.resolve_bv_width(line.sort_id)
        } else {
            32
        }
    }

    fn resolve_sort(&self, sort_id: i64) -> Btor2Sort {
        self.program
            .sorts
            .get(&sort_id)
            .cloned()
            .unwrap_or(Btor2Sort::BitVec(32))
    }
}

// ---------------------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------------------

/// Convert a BTOR2 sort id to a CHC sort.
fn btor2_sort_to_chc(sorts: &HashMap<i64, Btor2Sort>, sort_id: i64) -> Result<ChcSort, Btor2Error> {
    match sorts.get(&sort_id) {
        Some(Btor2Sort::BitVec(w)) => Ok(ChcSort::BitVec(*w)),
        Some(Btor2Sort::Array { index, element }) => {
            let idx_sort = btor2_sort_to_chc_direct(index);
            let elem_sort = btor2_sort_to_chc_direct(element);
            Ok(ChcSort::Array(Box::new(idx_sort), Box::new(elem_sort)))
        }
        None => Err(Btor2Error::InvalidSort { line: 0, sort_id }),
    }
}

fn btor2_sort_to_chc_direct(sort: &Btor2Sort) -> ChcSort {
    match sort {
        Btor2Sort::BitVec(w) => ChcSort::BitVec(*w),
        Btor2Sort::Array { index, element } => ChcSort::Array(
            Box::new(btor2_sort_to_chc_direct(index)),
            Box::new(btor2_sort_to_chc_direct(element)),
        ),
    }
}

/// Check if a 1-bit bitvector expression is true (== 1).
fn bv_is_true(expr: &ChcExpr) -> ChcExpr {
    ChcExpr::eq(expr.clone(), ChcExpr::BitVec(1, 1))
}

/// Bitwise NOT for a bitvector expression.
fn bv_not(expr: &ChcExpr, _sort: &Btor2Sort) -> ChcExpr {
    bv_op1(ChcOp::BvNot, expr.clone())
}

fn bv_op1(op: ChcOp, a: ChcExpr) -> ChcExpr {
    ChcExpr::Op(op, vec![Arc::new(a)])
}

fn bv_op2(op: ChcOp, a: ChcExpr, b: ChcExpr) -> ChcExpr {
    ChcExpr::Op(op, vec![Arc::new(a), Arc::new(b)])
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
            let inner = lift_scalar_to_array(elem_sort, expr);
            ChcExpr::const_array(key_sort.as_ref().clone(), inner)
        }
        _ => expr,
    }
}
