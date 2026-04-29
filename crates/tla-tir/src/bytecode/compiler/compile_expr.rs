// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `compile_expr` dispatch table — the main TIR expression→opcode translation.
//!
//! Support-heavy lowering (name resolution, EXCEPT, records, Prime, UNCHANGED)
//! lives in `compile_expr_support.rs`.

use super::super::opcode::{Opcode, Register};
use super::{CompileError, FnCompileState};
use crate::nodes::{TirArithOp, TirCmpOp, TirExpr, TirSetOp};
use tla_core::Spanned;

impl<'a> FnCompileState<'a> {
    /// Compile a TIR expression, returning the register holding the result.
    pub(super) fn compile_expr(
        &mut self,
        expr: &Spanned<TirExpr>,
    ) -> Result<Register, CompileError> {
        match &expr.node {
            // === Constants ===
            TirExpr::Const { value, .. } => self.compile_const(value),

            // === Variables (support module) ===
            TirExpr::Name(name_ref) => self.compile_name_expr(name_ref),

            // === Arithmetic ===
            TirExpr::ArithBinOp { left, op, right } => {
                let r1 = self.compile_expr(left)?;
                let r2 = self.compile_expr(right)?;
                let rd = self.alloc_reg()?;
                let opcode = match op {
                    TirArithOp::Add => Opcode::AddInt { rd, r1, r2 },
                    TirArithOp::Sub => Opcode::SubInt { rd, r1, r2 },
                    TirArithOp::Mul => Opcode::MulInt { rd, r1, r2 },
                    TirArithOp::Div => Opcode::DivInt { rd, r1, r2 },
                    TirArithOp::IntDiv => Opcode::IntDiv { rd, r1, r2 },
                    TirArithOp::Mod => Opcode::ModInt { rd, r1, r2 },
                    TirArithOp::Pow => Opcode::PowInt { rd, r1, r2 },
                };
                self.func.emit(opcode);
                Ok(rd)
            }

            TirExpr::ArithNeg(inner) => {
                let rs = self.compile_expr(inner)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::NegInt { rd, rs });
                Ok(rd)
            }

            // === Boolean ===
            TirExpr::BoolBinOp { left, op, right } => self.compile_bool_binop(left, *op, right),

            TirExpr::BoolNot(inner) => {
                let rs = self.compile_expr(inner)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::Not { rd, rs });
                Ok(rd)
            }

            // === Comparison ===
            TirExpr::Cmp { left, op, right } => {
                let r1 = self.compile_expr(left)?;
                let r2 = self.compile_expr(right)?;
                let rd = self.alloc_reg()?;
                let opcode = match op {
                    TirCmpOp::Eq => Opcode::Eq { rd, r1, r2 },
                    TirCmpOp::Neq => Opcode::Neq { rd, r1, r2 },
                    TirCmpOp::Lt => Opcode::LtInt { rd, r1, r2 },
                    TirCmpOp::Leq => Opcode::LeInt { rd, r1, r2 },
                    TirCmpOp::Gt => Opcode::GtInt { rd, r1, r2 },
                    TirCmpOp::Geq => Opcode::GeInt { rd, r1, r2 },
                };
                self.func.emit(opcode);
                Ok(rd)
            }

            // === Set Membership ===
            TirExpr::In { elem, set } => {
                let r_elem = self.compile_expr(elem)?;
                let r_set = self.compile_expr(set)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::SetIn {
                    rd,
                    elem: r_elem,
                    set: r_set,
                });
                Ok(rd)
            }

            TirExpr::Subseteq { left, right } => {
                let r1 = self.compile_expr(left)?;
                let r2 = self.compile_expr(right)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::Subseteq { rd, r1, r2 });
                Ok(rd)
            }

            // === If-Then-Else ===
            TirExpr::If { cond, then_, else_ } => self.compile_if(cond, then_, else_),

            // === Set Operations ===
            TirExpr::SetEnum(elements) => {
                if elements.is_empty() {
                    let rd = self.alloc_reg()?;
                    self.func.emit(Opcode::SetEnum {
                        rd,
                        start: 0,
                        count: 0,
                    });
                    return Ok(rd);
                }

                let start = self.compile_exprs_into_consecutive(elements.iter())?;
                let count = elements.len().min(255) as u8;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::SetEnum { rd, start, count });
                Ok(rd)
            }

            TirExpr::SetBinOp { left, op, right } => {
                let r1 = self.compile_expr(left)?;
                let r2 = self.compile_expr(right)?;
                let rd = self.alloc_reg()?;
                let opcode = match op {
                    TirSetOp::Union => Opcode::SetUnion { rd, r1, r2 },
                    TirSetOp::Intersect => Opcode::SetIntersect { rd, r1, r2 },
                    TirSetOp::Minus => Opcode::SetDiff { rd, r1, r2 },
                };
                self.func.emit(opcode);
                Ok(rd)
            }

            TirExpr::Powerset(inner) => {
                let rs = self.compile_expr(inner)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::Powerset { rd, rs });
                Ok(rd)
            }

            TirExpr::BigUnion(inner) => {
                let rs = self.compile_expr(inner)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::BigUnion { rd, rs });
                Ok(rd)
            }

            TirExpr::KSubset { base, k } => {
                let r_base = self.compile_expr(base)?;
                let r_k = self.compile_expr(k)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::KSubset {
                    rd,
                    base: r_base,
                    k: r_k,
                });
                Ok(rd)
            }

            TirExpr::Range { lo, hi } => {
                let r_lo = self.compile_expr(lo)?;
                let r_hi = self.compile_expr(hi)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::Range {
                    rd,
                    lo: r_lo,
                    hi: r_hi,
                });
                Ok(rd)
            }

            // === Quantifiers ===
            TirExpr::Forall { vars, body } => self.compile_forall(vars, body),
            TirExpr::Exists { vars, body } => self.compile_exists(vars, body),
            TirExpr::Choose { var, body } => self.compile_choose(var, body),

            // === Set Comprehensions ===
            TirExpr::SetFilter { var, body } => self.compile_set_filter(var, body),
            TirExpr::SetBuilder { body, vars } => self.compile_set_builder(body, vars),

            // === Functions ===
            TirExpr::FuncDef { vars, body } => self.compile_func_def(vars, body),

            TirExpr::FuncApply { func, arg } => {
                let r_func = self.compile_expr(func)?;
                let r_arg = self.compile_expr(arg)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::FuncApply {
                    rd,
                    func: r_func,
                    arg: r_arg,
                });
                Ok(rd)
            }

            TirExpr::FuncSet { domain, range } => {
                let r_domain = self.compile_expr(domain)?;
                let r_range = self.compile_expr(range)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::FuncSet {
                    rd,
                    domain: r_domain,
                    range: r_range,
                });
                Ok(rd)
            }

            TirExpr::Domain(inner) => {
                let rs = self.compile_expr(inner)?;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::Domain { rd, rs });
                Ok(rd)
            }

            // === EXCEPT (support module) ===
            TirExpr::Except { base, specs } => self.compile_except_expr(base, specs),

            // === Records (support module) ===
            TirExpr::Record(fields) => self.compile_record_expr(fields),
            TirExpr::RecordAccess { record, field } => {
                self.compile_record_access_expr(record, field)
            }
            TirExpr::RecordSet(fields) => self.compile_record_set_expr(fields),

            // === Tuples ===
            TirExpr::Tuple(elements) => {
                let start = self.compile_exprs_into_consecutive(elements.iter())?;
                let count = elements.len().min(255) as u8;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::TupleNew { rd, start, count });
                Ok(rd)
            }

            TirExpr::Times(components) => {
                let start = self.compile_exprs_into_consecutive(components.iter())?;
                let count = components.len().min(255) as u8;
                let rd = self.alloc_reg()?;
                self.func.emit(Opcode::Times { rd, start, count });
                Ok(rd)
            }

            // === Priming (support module) ===
            TirExpr::Prime(inner) => self.compile_prime_expr(inner),
            TirExpr::Unchanged(inner) => self.compile_unchanged_expr(inner),

            // === LET/IN ===
            TirExpr::Let { defs, body } => self.compile_let(defs, body),

            // === CASE ===
            TirExpr::Case { arms, other } => self.compile_case(arms, other.as_deref()),

            // === Labels (transparent) ===
            TirExpr::Label { body, .. } => self.compile_expr(body),

            // === ExceptAt (@) ===
            TirExpr::ExceptAt => {
                if let Some(at_reg) = self.except_at_register {
                    // @ resolves to the pre-computed base[key] value.
                    Ok(at_reg)
                } else {
                    Err(CompileError::Unsupported("standalone ExceptAt".to_string()))
                }
            }

            // === Operator References / Apply ===
            TirExpr::OperatorRef(op_ref) => self.compile_operator_ref(op_ref),
            TirExpr::Apply { op, args } => self.compile_apply(op, args),
            TirExpr::Lambda {
                params,
                body,
                ast_body,
            } => self.compile_lambda_expr(params, body, ast_body),
            TirExpr::OpRef(op) => self.compile_op_ref_expr(op, expr.span),
            TirExpr::ActionSubscript { .. } => {
                Err(CompileError::Unsupported("ActionSubscript".to_string()))
            }

            // Temporal operators — never evaluated at the value level.
            TirExpr::Always(_)
            | TirExpr::Eventually(_)
            | TirExpr::LeadsTo { .. }
            | TirExpr::WeakFair { .. }
            | TirExpr::StrongFair { .. }
            | TirExpr::Enabled(_) => {
                Err(CompileError::Unsupported("temporal operator".to_string()))
            }
        }
    }
}
