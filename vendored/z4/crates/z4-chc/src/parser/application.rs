// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Operator/application decoding for the CHC parser.
//!
//! Owns the big dispatch table mapping SMT-LIB function names to `ChcExpr`
//! constructors. Handles arithmetic, bitvector, array, boolean, and user-
//! defined function applications.

use super::bitvector::infer_bv_width_from_expr;
use super::ChcParser;
use crate::{ChcError, ChcExpr, ChcOp, ChcResult};
use std::sync::Arc;

impl ChcParser {
    /// Parse a chainable SMT-LIB operator (=, <, <=, >, >=).
    ///
    /// `(op a b c)` desugars to `(and (op a b) (op b c))`.
    pub(super) fn parse_chainable(
        op: &str,
        args: Vec<ChcExpr>,
        bin: fn(ChcExpr, ChcExpr) -> ChcExpr,
    ) -> ChcResult<ChcExpr> {
        if args.len() < 2 {
            return Err(ChcError::Parse(format!(
                "'{op}' requires at least 2 arguments"
            )));
        }
        if args.len() == 2 {
            let mut iter = args.into_iter();
            let a = Self::next_checked(&mut iter, op)?;
            let b = Self::next_checked(&mut iter, op)?;
            Ok(bin(a, b))
        } else {
            let chain: Vec<ChcExpr> = args
                .windows(2)
                .map(|w| bin(w[0].clone(), w[1].clone()))
                .collect();
            Ok(ChcExpr::and_all(chain))
        }
    }

    pub(super) fn next_checked<I>(iter: &mut I, op: &str) -> ChcResult<ChcExpr>
    where
        I: Iterator<Item = ChcExpr>,
    {
        iter.next().ok_or_else(|| {
            ChcError::Parse(format!(
                "Internal parser error: '{op}' arity check mismatch"
            ))
        })
    }

    /// Parse function application
    pub(super) fn parse_application(&mut self, func: &str) -> ChcResult<ChcExpr> {
        let mut args = Vec::new();

        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some(')') {
                break;
            }
            args.push(self.parse_expr()?);
        }
        self.expect_char(')')?;

        // Map function names to operations
        match func {
            "not" => {
                if args.len() != 1 {
                    return Err(ChcError::Parse("'not' requires exactly 1 argument".into()));
                }
                let mut iter = args.into_iter();
                Ok(ChcExpr::not(Self::next_checked(&mut iter, "not")?))
            }
            "and" => Ok(ChcExpr::and_all(args)),
            "or" => Ok(ChcExpr::or_all(args)),
            "=>" | "implies" => {
                if args.len() != 2 {
                    return Err(ChcError::Parse("'=>' requires exactly 2 arguments".into()));
                }
                let mut iter = args.into_iter();
                let a = Self::next_checked(&mut iter, "=>")?;
                let b = Self::next_checked(&mut iter, "=>")?;
                Ok(ChcExpr::implies(a, b))
            }
            // SMT-LIB 2.6 chainable operators: (op a b c) → (and (op a b) (op b c))
            "=" => Self::parse_chainable("=", args, ChcExpr::eq),
            "<" => Self::parse_chainable("<", args, ChcExpr::lt),
            "<=" => Self::parse_chainable("<=", args, ChcExpr::le),
            ">" => Self::parse_chainable(">", args, ChcExpr::gt),
            ">=" => Self::parse_chainable(">=", args, ChcExpr::ge),
            "distinct" => {
                // Pairwise: (distinct a b c) → (and (!= a b) (!= a c) (!= b c))
                if args.len() < 2 {
                    return Err(ChcError::Parse(
                        "'distinct' requires at least 2 arguments".into(),
                    ));
                }
                if args.len() == 2 {
                    let mut iter = args.into_iter();
                    let a = Self::next_checked(&mut iter, "distinct")?;
                    let b = Self::next_checked(&mut iter, "distinct")?;
                    Ok(ChcExpr::ne(a, b))
                } else {
                    let mut pairs = Vec::new();
                    for i in 0..args.len() {
                        for j in (i + 1)..args.len() {
                            pairs.push(ChcExpr::ne(args[i].clone(), args[j].clone()));
                        }
                    }
                    Ok(ChcExpr::and_all(pairs))
                }
            }
            "+" => {
                if args.is_empty() {
                    Ok(ChcExpr::int(0))
                } else {
                    let mut iter = args.into_iter();
                    let first = Self::next_checked(&mut iter, "+")?;
                    Ok(iter.fold(first, ChcExpr::add))
                }
            }
            "-" => {
                if args.is_empty() {
                    return Err(ChcError::Parse("'-' requires at least 1 argument".into()));
                }
                if args.len() == 1 {
                    let mut iter = args.into_iter();
                    Ok(ChcExpr::neg(Self::next_checked(&mut iter, "-")?))
                } else {
                    let mut iter = args.into_iter();
                    let first = Self::next_checked(&mut iter, "-")?;
                    Ok(iter.fold(first, ChcExpr::sub))
                }
            }
            "*" => {
                if args.is_empty() {
                    Ok(ChcExpr::int(1))
                } else {
                    let mut iter = args.into_iter();
                    let first = Self::next_checked(&mut iter, "*")?;
                    Ok(iter.fold(first, ChcExpr::mul))
                }
            }
            "div" => {
                if args.len() != 2 {
                    return Err(ChcError::Parse("'div' requires exactly 2 arguments".into()));
                }
                let mut iter = args.into_iter();
                let a = Self::next_checked(&mut iter, "div")?;
                let b = Self::next_checked(&mut iter, "div")?;
                Ok(ChcExpr::Op(ChcOp::Div, vec![Arc::new(a), Arc::new(b)]))
            }
            "mod" => {
                if args.len() != 2 {
                    return Err(ChcError::Parse("'mod' requires exactly 2 arguments".into()));
                }
                let mut iter = args.into_iter();
                let a = Self::next_checked(&mut iter, "mod")?;
                let b = Self::next_checked(&mut iter, "mod")?;
                Ok(ChcExpr::Op(ChcOp::Mod, vec![Arc::new(a), Arc::new(b)]))
            }
            "ite" => {
                if args.len() != 3 {
                    return Err(ChcError::Parse("'ite' requires exactly 3 arguments".into()));
                }
                let mut iter = args.into_iter();
                let cond = Self::next_checked(&mut iter, "ite")?;
                let then_val = Self::next_checked(&mut iter, "ite")?;
                let else_val = Self::next_checked(&mut iter, "ite")?;
                Ok(ChcExpr::ite(cond, then_val, else_val))
            }
            "select" => {
                if args.len() != 2 {
                    return Err(ChcError::Parse(
                        "'select' requires exactly 2 arguments".into(),
                    ));
                }
                let mut iter = args.into_iter();
                let arr = Self::next_checked(&mut iter, "select")?;
                let idx = Self::next_checked(&mut iter, "select")?;
                Ok(ChcExpr::select(arr, idx))
            }
            "store" => {
                if args.len() != 3 {
                    return Err(ChcError::Parse(
                        "'store' requires exactly 3 arguments".into(),
                    ));
                }
                let mut iter = args.into_iter();
                let arr = Self::next_checked(&mut iter, "store")?;
                let idx = Self::next_checked(&mut iter, "store")?;
                let val = Self::next_checked(&mut iter, "store")?;
                Ok(ChcExpr::store(arr, idx, val))
            }
            "true" => Ok(ChcExpr::Bool(true)),
            "false" => Ok(ChcExpr::Bool(false)),
            // Bitvector binary arithmetic/bitwise/shift operations
            // bvadd/bvmul/bvand/bvor/bvxor are left-associative per SMT-LIB (#5445)
            "bvadd" | "bvsub" | "bvmul" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod"
            | "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor" | "bvxnor" | "bvshl" | "bvlshr"
            | "bvashr" => {
                let left_assoc = matches!(func, "bvadd" | "bvmul" | "bvand" | "bvor" | "bvxor");
                if args.len() < 2 || (!left_assoc && args.len() != 2) {
                    let msg = if left_assoc {
                        "at least 2"
                    } else {
                        "exactly 2"
                    };
                    return Err(ChcError::Parse(format!(
                        "'{func}' requires {msg} arguments"
                    )));
                }
                let op = match func {
                    "bvadd" => ChcOp::BvAdd,
                    "bvsub" => ChcOp::BvSub,
                    "bvmul" => ChcOp::BvMul,
                    "bvudiv" => ChcOp::BvUDiv,
                    "bvurem" => ChcOp::BvURem,
                    "bvsdiv" => ChcOp::BvSDiv,
                    "bvsrem" => ChcOp::BvSRem,
                    "bvsmod" => ChcOp::BvSMod,
                    "bvand" => ChcOp::BvAnd,
                    "bvor" => ChcOp::BvOr,
                    "bvxor" => ChcOp::BvXor,
                    "bvnand" => ChcOp::BvNand,
                    "bvnor" => ChcOp::BvNor,
                    "bvxnor" => ChcOp::BvXnor,
                    "bvshl" => ChcOp::BvShl,
                    "bvlshr" => ChcOp::BvLShr,
                    "bvashr" => ChcOp::BvAShr,
                    _ => {
                        return Err(ChcError::Parse(format!("Unexpected BV operator: {func}")));
                    }
                };
                // Left-associative fold: (op a b c) => (op (op a b) c)
                let mut result = ChcExpr::Op(
                    op.clone(),
                    vec![Arc::new(args[0].clone()), Arc::new(args[1].clone())],
                );
                for arg in &args[2..] {
                    result = ChcExpr::Op(op.clone(), vec![Arc::new(result), Arc::new(arg.clone())]);
                }
                Ok(result)
            }
            // Bitvector unary operations
            "bvnot" | "bvneg" | "bv2nat" | "bv2int" => {
                if args.len() != 1 {
                    return Err(ChcError::Parse(format!(
                        "'{func}' requires exactly 1 argument"
                    )));
                }
                let op = match func {
                    "bvnot" => ChcOp::BvNot,
                    "bvneg" => ChcOp::BvNeg,
                    "bv2nat" | "bv2int" => ChcOp::Bv2Nat,
                    _ => {
                        return Err(ChcError::Parse(format!(
                            "Unexpected unary BV operator: {func}"
                        )));
                    }
                };
                let args_arc: Vec<Arc<ChcExpr>> = args.into_iter().map(Arc::new).collect();
                Ok(ChcExpr::Op(op, args_arc))
            }
            // Bitvector comparison operations (return Bool)
            "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
                if args.len() != 2 {
                    return Err(ChcError::Parse(format!(
                        "'{func}' requires exactly 2 arguments"
                    )));
                }
                let op = match func {
                    "bvult" => ChcOp::BvULt,
                    "bvule" => ChcOp::BvULe,
                    "bvugt" => ChcOp::BvUGt,
                    "bvuge" => ChcOp::BvUGe,
                    "bvslt" => ChcOp::BvSLt,
                    "bvsle" => ChcOp::BvSLe,
                    "bvsgt" => ChcOp::BvSGt,
                    "bvsge" => ChcOp::BvSGe,
                    _ => {
                        return Err(ChcError::Parse(format!(
                            "Unexpected BV comparison operator: {func}"
                        )));
                    }
                };
                let args_arc: Vec<Arc<ChcExpr>> = args.into_iter().map(Arc::new).collect();
                Ok(ChcExpr::Op(op, args_arc))
            }
            // bvcomp: bitwise comparison, returns BitVec(1)
            "bvcomp" => {
                if args.len() != 2 {
                    return Err(ChcError::Parse(
                        "'bvcomp' requires exactly 2 arguments".into(),
                    ));
                }
                let args_arc: Vec<Arc<ChcExpr>> = args.into_iter().map(Arc::new).collect();
                Ok(ChcExpr::Op(ChcOp::BvComp, args_arc))
            }
            // Z3-specific "safe division" BV operators that handle division-by-zero.
            // bvsrem_i(a,b) = ite(b=0, a, bvsrem(a,b))
            // bvurem_i(a,b) = ite(b=0, a, bvurem(a,b))
            // bvsmod_i(a,b) = ite(b=0, a, bvsmod(a,b))
            // bvsdiv_i(a,b) = ite(b=0, ite(bvslt(a,0), 1, -1), bvsdiv(a,b))
            // bvudiv_i(a,b) = ite(b=0, -1, bvudiv(a,b)) where -1 = all-ones BV
            "bvsrem_i" | "bvurem_i" | "bvsdiv_i" | "bvudiv_i" | "bvsmod_i" => {
                if args.len() != 2 {
                    return Err(ChcError::Parse(format!(
                        "'{func}' requires exactly 2 arguments"
                    )));
                }
                let a = args[0].clone();
                let b = args[1].clone();
                // Infer width from operands for zero literal construction.
                let width = infer_bv_width_from_expr(&a)
                    .or_else(|| infer_bv_width_from_expr(&b))
                    .ok_or_else(|| {
                        ChcError::Parse(format!(
                            "'{func}' requires bitvector operands with known width"
                        ))
                    })?;
                let zero = ChcExpr::BitVec(0, width);
                let b_is_zero = ChcExpr::eq(b.clone(), zero);
                let (default_val, core_op) = match func {
                    "bvsrem_i" => (a.clone(), ChcOp::BvSRem),
                    "bvurem_i" => (a.clone(), ChcOp::BvURem),
                    "bvsmod_i" => (a.clone(), ChcOp::BvSMod),
                    "bvudiv_i" => {
                        // -1 as all-ones bitvector
                        (Self::make_all_ones_bv(width), ChcOp::BvUDiv)
                    }
                    "bvsdiv_i" => {
                        // ite(bvslt(a, 0), 1, -1) — simplified to 0 for CHC contexts
                        // where division-by-zero is typically unreachable.
                        let one = ChcExpr::BitVec(1, width);
                        let neg_one = Self::make_all_ones_bv(width);
                        let a_neg = ChcExpr::Op(
                            ChcOp::BvSLt,
                            vec![Arc::new(a.clone()), Arc::new(ChcExpr::BitVec(0, width))],
                        );
                        (ChcExpr::ite(a_neg, one, neg_one), ChcOp::BvSDiv)
                    }
                    _ => unreachable!(),
                };
                let core_result = ChcExpr::Op(core_op, vec![Arc::new(a), Arc::new(b)]);
                Ok(ChcExpr::ite(b_is_zero, default_val, core_result))
            }
            // concat: variadic bitvector concatenation
            "concat" => {
                if args.len() < 2 {
                    return Err(ChcError::Parse(
                        "'concat' requires at least 2 arguments".into(),
                    ));
                }
                let args_arc: Vec<Arc<ChcExpr>> = args.into_iter().map(Arc::new).collect();
                Ok(ChcExpr::Op(ChcOp::BvConcat, args_arc))
            }
            _ => {
                // Check if it's a predicate application
                if let Some((pred_id, _sorts)) = self.predicates.get(func).cloned() {
                    // It's a predicate application - create PredicateApp expression
                    Ok(ChcExpr::predicate_app(func, pred_id, args))
                } else if let Some((ret_sort, arg_sorts)) = self
                    .resolve_function_signature(
                        func,
                        &args.iter().map(ChcExpr::sort).collect::<Vec<_>>(),
                    )?
                    .or_else(|| self.functions.get(func).cloned())
                {
                    // It's a declared function (constructor, selector, or tester)
                    // Validate argument count
                    if args.len() != arg_sorts.len() {
                        return Err(ChcError::Parse(format!(
                            "Function '{}' expects {} arguments, got {}",
                            func,
                            arg_sorts.len(),
                            args.len()
                        )));
                    }
                    let args_arc: Vec<Arc<ChcExpr>> = args.into_iter().map(Arc::new).collect();
                    Ok(ChcExpr::FuncApp(func.to_string(), ret_sort, args_arc))
                } else {
                    // Unknown function - fail with error (fixes #352)
                    Err(ChcError::Parse(format!(
                        "Unknown function application: '{func}'. Only built-in ops and declared predicates are supported in z4-chc."
                    )))
                }
            }
        }
    }
}
