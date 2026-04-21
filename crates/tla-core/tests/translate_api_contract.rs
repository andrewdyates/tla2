// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;
use tla_core::ast::Expr;
use tla_core::{dispatch_translate_bool, dispatch_translate_int, NameId, Spanned, TranslateExpr};

#[derive(Default)]
struct ContractTranslator {
    bool_vars: HashMap<String, bool>,
    int_vars: HashMap<String, i64>,
    eq_override: Option<bool>,
}

impl TranslateExpr for ContractTranslator {
    type Bool = bool;
    type Int = i64;
    type Error = String;

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
            .ok_or_else(|| format!("unknown bool variable: {name}"))
    }

    fn lookup_int_var(&mut self, name: &str) -> Result<Self::Int, Self::Error> {
        self.int_vars
            .get(name)
            .copied()
            .ok_or_else(|| format!("unknown int variable: {name}"))
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
            return Err("division by zero".to_string());
        }
        Ok(lhs / rhs)
    }

    fn modulo(&mut self, lhs: Self::Int, rhs: Self::Int) -> Result<Self::Int, Self::Error> {
        if rhs == 0 {
            return Err("modulo by zero".to_string());
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

        Err("unable to compare values for equality".to_string())
    }

    fn translate_bool_extended(
        &mut self,
        expr: &Spanned<Expr>,
    ) -> Option<Result<Self::Bool, Self::Error>> {
        match (&expr.node, self.eq_override) {
            (Expr::Eq(_, _), Some(value)) => Some(Ok(value)),
            _ => None,
        }
    }
}

fn expr(node: Expr) -> Spanned<Expr> {
    Spanned::dummy(node)
}

fn ident(name: &str) -> Spanned<Expr> {
    expr(Expr::Ident(name.to_string(), NameId::INVALID))
}

fn int_expr(value: i64) -> Spanned<Expr> {
    expr(Expr::Int(value.into()))
}

// Keep these tests under a named module so `cargo test ... translate_api_contract`
// matches the intended public-contract canary.
mod translate_api_contract {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn root_translate_surface_compiles_and_dispatches() {
        let mut translator = ContractTranslator::default();
        translator.bool_vars.insert("flag".to_string(), true);
        translator.int_vars.insert("x".to_string(), 3);

        let arithmetic = expr(Expr::Add(Box::new(ident("x")), Box::new(int_expr(2))));
        assert_eq!(
            dispatch_translate_int(&mut translator, &arithmetic).unwrap(),
            5
        );

        let formula = expr(Expr::And(
            Box::new(ident("flag")),
            Box::new(expr(Expr::Eq(Box::new(arithmetic), Box::new(int_expr(5))))),
        ));
        assert!(dispatch_translate_bool(&mut translator, &formula).unwrap());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn hook_first_contract_allows_shared_arm_override() {
        let expr = expr(Expr::Eq(Box::new(int_expr(2)), Box::new(int_expr(2))));

        let mut without_override = ContractTranslator::default();
        assert!(dispatch_translate_bool(&mut without_override, &expr).unwrap());

        let mut with_override = ContractTranslator {
            eq_override: Some(false),
            ..Default::default()
        };
        assert!(!dispatch_translate_bool(&mut with_override, &expr).unwrap());
    }
}
