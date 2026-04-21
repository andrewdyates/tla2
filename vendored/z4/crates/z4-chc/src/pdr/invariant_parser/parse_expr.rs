// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression parsing for the invariant parser.
//!
//! Recursive-descent parser for SMT-LIB expressions: boolean connectives,
//! arithmetic operators, array operations, let-bindings, and literals.

use super::InvariantParser;
use crate::error::ChcError;
use crate::expr::maybe_grow_expr_stack;
use crate::{ChcExpr, ChcOp, ChcResult, ChcSort, ChcVar};
use std::sync::Arc;

impl<'a> InvariantParser<'a> {
    pub(super) fn parse_expr(&mut self, vars: &[ChcVar]) -> ChcResult<ChcExpr> {
        // Stacker protection: invariant expressions from PDR can be deeply nested
        // when CHC problems have many predicates with many args (#6847).
        maybe_grow_expr_stack(|| self.parse_expr_inner(vars))
    }

    fn parse_expr_inner(&mut self, vars: &[ChcVar]) -> ChcResult<ChcExpr> {
        self.skip_whitespace_and_comments();

        match self.peek_char() {
            Some('(') => {
                self.pos += 1;
                self.skip_whitespace_and_comments();

                // Higher-order application like ((as const (Array Int Int)) value)
                if self.peek_char() == Some('(') {
                    let head = self.parse_expr(vars)?;
                    self.skip_whitespace_and_comments();

                    let args = self.parse_expr_list(vars)?;
                    self.expect_char(')')?;

                    return match head {
                        ChcExpr::ConstArrayMarker(key_sort) => {
                            if args.len() != 1 {
                                Err(ChcError::Parse(
                                    "(as const ...) requires exactly 1 argument".into(),
                                ))
                            } else {
                                Ok(ChcExpr::const_array(
                                    key_sort,
                                    args.into_iter().next().ok_or_else(|| {
                                        ChcError::Parse("(as const ...) missing argument".into())
                                    })?,
                                ))
                            }
                        }
                        _ => Err(ChcError::Parse(
                            "Unsupported higher-order application".into(),
                        )),
                    };
                }

                let op = self.parse_symbol()?;
                self.skip_whitespace_and_comments();

                match op.as_str() {
                    "as" => {
                        let name = self.parse_symbol()?;
                        self.skip_whitespace_and_comments();

                        match name.as_str() {
                            "const" => {
                                let sort = self.parse_sort()?;
                                let key_sort = match &sort {
                                    ChcSort::Array(ks, _) => ks.as_ref().clone(),
                                    _ => {
                                        return Err(ChcError::Parse(format!(
                                            "Expected array sort in (as const ...), got: {sort:?}"
                                        )));
                                    }
                                };
                                self.skip_whitespace_and_comments();
                                self.expect_char(')')?;
                                Ok(ChcExpr::ConstArrayMarker(key_sort))
                            }
                            _ => Err(ChcError::Parse(format!(
                                "Unknown 'as' form: (as {name} ...)"
                            ))),
                        }
                    }
                    "let" => {
                        // Parse: (let ((var expr) ...) body)
                        self.expect_char('(')?;
                        let mut let_bindings: Vec<(ChcVar, ChcExpr)> = Vec::new();
                        loop {
                            self.skip_whitespace_and_comments();
                            if self.peek_char() == Some(')') {
                                break;
                            }
                            self.expect_char('(')?;
                            self.skip_whitespace_and_comments();
                            let binding_name = self.parse_symbol()?;
                            self.skip_whitespace_and_comments();
                            let binding_expr = self.parse_expr(vars)?;
                            self.skip_whitespace_and_comments();
                            self.expect_char(')')?;
                            let_bindings.push((
                                ChcVar::new(binding_name, binding_expr.sort()),
                                binding_expr,
                            ));
                        }
                        self.expect_char(')')?; // close binding list
                        self.skip_whitespace_and_comments();

                        // Let bindings shadow outer variables of the same name.
                        let mut extended_vars: Vec<ChcVar> =
                            let_bindings.iter().map(|(v, _)| v.clone()).collect();
                        extended_vars.extend_from_slice(vars);

                        let body = self.parse_expr(&extended_vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;

                        // Let bindings are simultaneous (SMT-LIB): substitute all at once.
                        Ok(body.substitute(&let_bindings))
                    }
                    "not" => {
                        let arg = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcExpr::not(arg))
                    }
                    "and" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        Ok(ChcExpr::and_all(args))
                    }
                    "or" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        Ok(ChcExpr::or_all(args))
                    }
                    "=>" => {
                        let a = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let b = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcExpr::implies(a, b))
                    }
                    "=" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        match args.len() {
                            0 | 1 => Ok(ChcExpr::Bool(true)),
                            2 => Ok(ChcExpr::eq(args[0].clone(), args[1].clone())),
                            _ => {
                                let mut conj: Option<ChcExpr> = None;
                                for w in args.windows(2) {
                                    let eq = ChcExpr::eq(w[0].clone(), w[1].clone());
                                    conj = Some(match conj {
                                        Some(prev) => ChcExpr::and(prev, eq),
                                        None => eq,
                                    });
                                }
                                Ok(conj.unwrap_or(ChcExpr::Bool(true)))
                            }
                        }
                    }
                    "distinct" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        match args.len() {
                            0 | 1 => Ok(ChcExpr::Bool(true)),
                            2 => Ok(ChcExpr::ne(args[0].clone(), args[1].clone())),
                            _ => {
                                let mut conj: Option<ChcExpr> = None;
                                for i in 0..args.len() {
                                    for j in (i + 1)..args.len() {
                                        let ne = ChcExpr::ne(args[i].clone(), args[j].clone());
                                        conj = Some(match conj {
                                            Some(prev) => ChcExpr::and(prev, ne),
                                            None => ne,
                                        });
                                    }
                                }
                                Ok(conj.unwrap_or(ChcExpr::Bool(true)))
                            }
                        }
                    }
                    "<" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        match args.len() {
                            0 | 1 => Ok(ChcExpr::Bool(true)),
                            _ => {
                                let mut conj: Option<ChcExpr> = None;
                                for w in args.windows(2) {
                                    let lt = ChcExpr::lt(w[0].clone(), w[1].clone());
                                    conj = Some(match conj {
                                        Some(prev) => ChcExpr::and(prev, lt),
                                        None => lt,
                                    });
                                }
                                Ok(conj.unwrap_or(ChcExpr::Bool(true)))
                            }
                        }
                    }
                    "<=" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        match args.len() {
                            0 | 1 => Ok(ChcExpr::Bool(true)),
                            _ => {
                                let mut conj: Option<ChcExpr> = None;
                                for w in args.windows(2) {
                                    let le = ChcExpr::le(w[0].clone(), w[1].clone());
                                    conj = Some(match conj {
                                        Some(prev) => ChcExpr::and(prev, le),
                                        None => le,
                                    });
                                }
                                Ok(conj.unwrap_or(ChcExpr::Bool(true)))
                            }
                        }
                    }
                    ">" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        match args.len() {
                            0 | 1 => Ok(ChcExpr::Bool(true)),
                            _ => {
                                let mut conj: Option<ChcExpr> = None;
                                for w in args.windows(2) {
                                    let gt = ChcExpr::gt(w[0].clone(), w[1].clone());
                                    conj = Some(match conj {
                                        Some(prev) => ChcExpr::and(prev, gt),
                                        None => gt,
                                    });
                                }
                                Ok(conj.unwrap_or(ChcExpr::Bool(true)))
                            }
                        }
                    }
                    ">=" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        match args.len() {
                            0 | 1 => Ok(ChcExpr::Bool(true)),
                            _ => {
                                let mut conj: Option<ChcExpr> = None;
                                for w in args.windows(2) {
                                    let ge = ChcExpr::ge(w[0].clone(), w[1].clone());
                                    conj = Some(match conj {
                                        Some(prev) => ChcExpr::and(prev, ge),
                                        None => ge,
                                    });
                                }
                                Ok(conj.unwrap_or(ChcExpr::Bool(true)))
                            }
                        }
                    }
                    "+" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        if args.is_empty() {
                            Ok(ChcExpr::int(0))
                        } else {
                            args.into_iter().reduce(ChcExpr::add).ok_or_else(|| {
                                ChcError::Parse("'+' requires at least 1 argument".into())
                            })
                        }
                    }
                    "-" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        match args.len() {
                            0 => Err(ChcError::Parse("'-' expects at least 1 argument".into())),
                            1 => Ok(ChcExpr::neg(args.into_iter().next().ok_or_else(|| {
                                ChcError::Parse("'-' missing argument".into())
                            })?)),
                            _ => {
                                let mut it = args.into_iter();
                                let mut acc = it.next().ok_or_else(|| {
                                    ChcError::Parse("'-' missing first argument".into())
                                })?;
                                for a in it {
                                    acc = ChcExpr::sub(acc, a);
                                }
                                Ok(acc)
                            }
                        }
                    }
                    "*" => {
                        let args = self.parse_expr_list(vars)?;
                        self.expect_char(')')?;
                        if args.is_empty() {
                            Ok(ChcExpr::int(1))
                        } else {
                            args.into_iter().reduce(ChcExpr::mul).ok_or_else(|| {
                                ChcError::Parse("'*' requires at least 1 argument".into())
                            })
                        }
                    }
                    "div" => {
                        let a = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let b = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcExpr::Op(ChcOp::Div, vec![Arc::new(a), Arc::new(b)]))
                    }
                    "mod" => {
                        let a = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let b = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcExpr::Op(ChcOp::Mod, vec![Arc::new(a), Arc::new(b)]))
                    }
                    "ite" => {
                        let cond = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let then_ = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let else_ = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcExpr::ite(cond, then_, else_))
                    }
                    "select" => {
                        let arr = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let idx = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcExpr::select(arr, idx))
                    }
                    "store" => {
                        let arr = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let idx = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let val = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcExpr::store(arr, idx, val))
                    }
                    "/" => {
                        // Real division: (/ num denom)
                        let num = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        let denom = self.parse_expr(vars)?;
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        // If both are integers (possibly with explicit unary negation), create Real
                        if let (ChcExpr::Int(n), ChcExpr::Int(d)) = (&num, &denom) {
                            return Ok(ChcExpr::Real(*n, *d));
                        }
                        if let (ChcExpr::Op(ChcOp::Neg, args), ChcExpr::Int(d)) = (&num, &denom) {
                            if args.len() == 1 {
                                if let ChcExpr::Int(n) = args[0].as_ref() {
                                    return Ok(ChcExpr::Real(-*n, *d));
                                }
                            }
                        }
                        Ok(ChcExpr::Op(
                            ChcOp::Div,
                            vec![Arc::new(num), Arc::new(denom)],
                        ))
                    }
                    _ => Err(ChcError::Parse(format!("Unknown operator: {op}"))),
                }
            }
            Some(c) if c.is_ascii_digit() => {
                let num = self.parse_numeral()?;
                Ok(ChcExpr::int(num))
            }
            Some('-') => {
                // Negative number
                self.pos += 1;
                let num = self.parse_numeral()?;
                Ok(ChcExpr::int(-num))
            }
            Some(_) => {
                let name = self.parse_symbol()?;
                match name.as_str() {
                    "true" => Ok(ChcExpr::Bool(true)),
                    "false" => Ok(ChcExpr::Bool(false)),
                    _ => {
                        // Look up in vars
                        for var in vars {
                            if var.name == name {
                                return Ok(ChcExpr::var(var.clone()));
                            }
                        }
                        // Unknown variable - create with Int sort as default
                        Ok(ChcExpr::var(ChcVar::new(name, ChcSort::Int)))
                    }
                }
            }
            None => Err(ChcError::Parse("Unexpected end of input".into())),
        }
    }
}
