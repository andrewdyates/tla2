// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{dispatch_translate_bool, dispatch_translate_int, TranslateExpr};
use crate::ast::Expr;
use crate::name_intern::NameId;
use crate::span::Spanned;
use num_bigint::BigInt;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
enum TestError {
    Message(String),
}

impl From<String> for TestError {
    fn from(value: String) -> Self {
        Self::Message(value)
    }
}

#[derive(Default)]
struct TestTranslator {
    bool_vars: HashMap<String, bool>,
    int_vars: HashMap<String, i64>,
    allow_prime: bool,
}

impl TranslateExpr for TestTranslator {
    type Bool = bool;
    type Int = i64;
    type Error = TestError;

    fn bool_const(&mut self, val: bool) -> Self::Bool {
        val
    }

    fn int_const(&mut self, val: i64) -> Result<Self::Int, Self::Error> {
        Ok(val)
    }

    fn lookup_bool_var(&mut self, name: &str) -> Result<Self::Bool, Self::Error> {
        self.bool_vars
            .get(name)
            .copied()
            .ok_or_else(|| format!("unknown bool variable: {name}").into())
    }

    fn lookup_int_var(&mut self, name: &str) -> Result<Self::Int, Self::Error> {
        self.int_vars
            .get(name)
            .copied()
            .ok_or_else(|| format!("unknown int variable: {name}").into())
    }

    fn and(&mut self, lhs: Self::Bool, rhs: Self::Bool) -> Self::Bool {
        lhs && rhs
    }

    fn or(&mut self, lhs: Self::Bool, rhs: Self::Bool) -> Self::Bool {
        lhs || rhs
    }

    fn not(&mut self, expr: Self::Bool) -> Self::Bool {
        !expr
    }

    fn implies(&mut self, lhs: Self::Bool, rhs: Self::Bool) -> Self::Bool {
        !lhs || rhs
    }

    // iff() uses default from TranslateExpr

    fn lt(&mut self, lhs: Self::Int, rhs: Self::Int) -> Self::Bool {
        lhs < rhs
    }

    fn le(&mut self, lhs: Self::Int, rhs: Self::Int) -> Self::Bool {
        lhs <= rhs
    }

    fn gt(&mut self, lhs: Self::Int, rhs: Self::Int) -> Self::Bool {
        lhs > rhs
    }

    fn ge(&mut self, lhs: Self::Int, rhs: Self::Int) -> Self::Bool {
        lhs >= rhs
    }

    fn add(&mut self, lhs: Self::Int, rhs: Self::Int) -> Self::Int {
        lhs + rhs
    }

    fn sub(&mut self, lhs: Self::Int, rhs: Self::Int) -> Self::Int {
        lhs - rhs
    }

    fn mul(&mut self, lhs: Self::Int, rhs: Self::Int) -> Result<Self::Int, Self::Error> {
        Ok(lhs * rhs)
    }

    fn neg(&mut self, expr: Self::Int) -> Self::Int {
        -expr
    }

    fn div(&mut self, lhs: Self::Int, rhs: Self::Int) -> Result<Self::Int, Self::Error> {
        if rhs == 0 {
            return Err("division by zero".to_string().into());
        }
        Ok(lhs / rhs)
    }

    fn modulo(&mut self, lhs: Self::Int, rhs: Self::Int) -> Result<Self::Int, Self::Error> {
        if rhs == 0 {
            return Err("modulo by zero".to_string().into());
        }
        Ok(lhs % rhs)
    }

    fn ite_bool(&mut self, cond: Self::Bool, then_b: Self::Bool, else_b: Self::Bool) -> Self::Bool {
        if cond {
            then_b
        } else {
            else_b
        }
    }

    fn ite_int(&mut self, cond: Self::Bool, then_i: Self::Int, else_i: Self::Int) -> Self::Int {
        if cond {
            then_i
        } else {
            else_i
        }
    }

    fn translate_eq(
        &mut self,
        left: &Spanned<Expr>,
        right: &Spanned<Expr>,
    ) -> Result<Self::Bool, Self::Error> {
        if let Ok(lhs) = dispatch_translate_int(self, left) {
            if let Ok(rhs) = dispatch_translate_int(self, right) {
                return Ok(lhs == rhs);
            }
        }

        if let Ok(lhs) = dispatch_translate_bool(self, left) {
            if let Ok(rhs) = dispatch_translate_bool(self, right) {
                return Ok(lhs == rhs);
            }
        }

        Err("unable to compare values for equality".to_string().into())
    }

    fn translate_bool_extended(
        &mut self,
        expr: &Spanned<Expr>,
    ) -> Option<Result<Self::Bool, Self::Error>> {
        if !self.allow_prime {
            return None;
        }
        match &expr.node {
            Expr::Prime(inner) => Some(dispatch_translate_bool(self, inner)),
            _ => None,
        }
    }
}

fn expr(node: Expr) -> Spanned<Expr> {
    Spanned::dummy(node)
}

fn int_expr(value: i64) -> Spanned<Expr> {
    expr(Expr::Int(BigInt::from(value)))
}

fn boxed(node: Expr) -> Box<Spanned<Expr>> {
    Box::new(expr(node))
}

#[test]
fn dispatch_translate_bool_handles_shared_ops() {
    let mut translator = TestTranslator::default();
    translator.bool_vars.insert("p".to_string(), true);
    translator.bool_vars.insert("q".to_string(), false);

    let formula = expr(Expr::Or(
        Box::new(expr(Expr::And(
            Box::new(expr(Expr::Ident("p".to_string(), NameId::INVALID))),
            Box::new(expr(Expr::Not(Box::new(expr(Expr::Ident(
                "q".to_string(),
                NameId::INVALID,
            )))))),
        ))),
        boxed(Expr::Eq(Box::new(int_expr(2)), Box::new(int_expr(2)))),
    ));

    let result = dispatch_translate_bool(&mut translator, &formula).unwrap();
    assert!(result);
}

#[test]
fn dispatch_translate_int_handles_arithmetic_and_ite() {
    let mut translator = TestTranslator::default();
    translator.bool_vars.insert("cond".to_string(), true);
    translator.int_vars.insert("x".to_string(), 7);

    let arithmetic = expr(Expr::Add(
        Box::new(expr(Expr::Ident("x".to_string(), NameId::INVALID))),
        Box::new(expr(Expr::Mul(
            Box::new(int_expr(2)),
            Box::new(int_expr(3)),
        ))),
    ));
    assert_eq!(
        dispatch_translate_int(&mut translator, &arithmetic).unwrap(),
        13
    );

    let ite = expr(Expr::If(
        Box::new(expr(Expr::Ident("cond".to_string(), NameId::INVALID))),
        Box::new(int_expr(10)),
        Box::new(int_expr(1)),
    ));
    assert_eq!(dispatch_translate_int(&mut translator, &ite).unwrap(), 10);
}

#[test]
fn dispatch_translate_bool_uses_extension_hook() {
    let mut without_hook = TestTranslator::default();
    let primed_true = expr(Expr::Prime(Box::new(expr(Expr::Bool(true)))));
    let err = dispatch_translate_bool(&mut without_hook, &primed_true).unwrap_err();
    assert!(matches!(err, TestError::Message(msg) if msg.contains("unsupported bool expr")));

    let mut with_hook = TestTranslator {
        allow_prime: true,
        ..Default::default()
    };
    assert!(dispatch_translate_bool(&mut with_hook, &primed_true).unwrap());
}

#[test]
fn dispatch_translate_int_reports_integer_overflow() {
    let mut translator = TestTranslator::default();
    let overflow = expr(Expr::Int(BigInt::from(i64::MAX) + BigInt::from(1)));
    let err = dispatch_translate_int(&mut translator, &overflow).unwrap_err();
    assert!(matches!(err, TestError::Message(msg) if msg.contains("too large for i64")));
}
