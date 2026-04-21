// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use tla_core::ast::Expr;

pub(super) fn expr_kind(expr: &Expr) -> &'static str {
    literal_expr_kind(expr)
        .or_else(|| name_expr_kind(expr))
        .or_else(|| operator_expr_kind(expr))
        .or_else(|| logic_expr_kind(expr))
        .or_else(|| collection_expr_kind(expr))
        .or_else(|| arithmetic_expr_kind(expr))
        .expect("expr_kind must cover every Expr variant")
}

fn literal_expr_kind(expr: &Expr) -> Option<&'static str> {
    match expr {
        Expr::Bool(_) => Some("Bool"),
        Expr::Int(_) => Some("Int"),
        Expr::String(_) => Some("String"),
        _ => None,
    }
}

fn name_expr_kind(expr: &Expr) -> Option<&'static str> {
    match expr {
        Expr::Ident(_, _) => Some("Ident"),
        Expr::StateVar(_, _, _) => Some("StateVar"),
        Expr::OpRef(_) => Some("OpRef"),
        _ => None,
    }
}

fn operator_expr_kind(expr: &Expr) -> Option<&'static str> {
    match expr {
        Expr::Apply(_, _) => Some("Apply"),
        Expr::Lambda(_, _) => Some("Lambda"),
        Expr::Label(_) => Some("Label"),
        Expr::ModuleRef(_, _, _) => Some("ModuleRef"),
        Expr::InstanceExpr(_, _) => Some("InstanceExpr"),
        Expr::SubstIn(_, _) => Some("SubstIn"),
        Expr::Enabled(_) => Some("Enabled"),
        _ => None,
    }
}

fn logic_expr_kind(expr: &Expr) -> Option<&'static str> {
    match expr {
        Expr::And(_, _) => Some("And"),
        Expr::Or(_, _) => Some("Or"),
        Expr::Not(_) => Some("Not"),
        Expr::Implies(_, _) => Some("Implies"),
        Expr::Equiv(_, _) => Some("Equiv"),
        Expr::Forall(_, _) => Some("Forall"),
        Expr::Exists(_, _) => Some("Exists"),
        Expr::Choose(_, _) => Some("Choose"),
        Expr::Eq(_, _) => Some("Eq"),
        Expr::Neq(_, _) => Some("Neq"),
        Expr::Lt(_, _) => Some("Lt"),
        Expr::Leq(_, _) => Some("Leq"),
        Expr::Gt(_, _) => Some("Gt"),
        Expr::Geq(_, _) => Some("Geq"),
        Expr::If(_, _, _) => Some("If"),
        Expr::Case(_, _) => Some("Case"),
        Expr::Let(_, _) => Some("Let"),
        Expr::Always(_) => Some("Always"),
        Expr::Eventually(_) => Some("Eventually"),
        Expr::LeadsTo(_, _) => Some("LeadsTo"),
        Expr::WeakFair(_, _) => Some("WeakFair"),
        Expr::StrongFair(_, _) => Some("StrongFair"),
        _ => None,
    }
}

fn collection_expr_kind(expr: &Expr) -> Option<&'static str> {
    match expr {
        Expr::SetEnum(_) => Some("SetEnum"),
        Expr::SetBuilder(_, _) => Some("SetBuilder"),
        Expr::SetFilter(_, _) => Some("SetFilter"),
        Expr::In(_, _) => Some("In"),
        Expr::NotIn(_, _) => Some("NotIn"),
        Expr::Subseteq(_, _) => Some("Subseteq"),
        Expr::Union(_, _) => Some("Union"),
        Expr::Intersect(_, _) => Some("Intersect"),
        Expr::SetMinus(_, _) => Some("SetMinus"),
        Expr::Powerset(_) => Some("Powerset"),
        Expr::BigUnion(_) => Some("BigUnion"),
        Expr::FuncDef(_, _) => Some("FuncDef"),
        Expr::FuncApply(_, _) => Some("FuncApply"),
        Expr::Domain(_) => Some("Domain"),
        Expr::Except(_, _) => Some("Except"),
        Expr::FuncSet(_, _) => Some("FuncSet"),
        Expr::Record(_) => Some("Record"),
        Expr::RecordAccess(_, _) => Some("RecordAccess"),
        Expr::RecordSet(_) => Some("RecordSet"),
        Expr::Tuple(_) => Some("Tuple"),
        Expr::Times(_) => Some("Times"),
        Expr::Range(_, _) => Some("Range"),
        Expr::Prime(_) => Some("Prime"),
        Expr::Unchanged(_) => Some("Unchanged"),
        _ => None,
    }
}

fn arithmetic_expr_kind(expr: &Expr) -> Option<&'static str> {
    match expr {
        Expr::Neg(_) => Some("Neg"),
        Expr::Add(_, _) => Some("Add"),
        Expr::Sub(_, _) => Some("Sub"),
        Expr::Mul(_, _) => Some("Mul"),
        Expr::Div(_, _) => Some("Div"),
        Expr::IntDiv(_, _) => Some("IntDiv"),
        Expr::Mod(_, _) => Some("Mod"),
        Expr::Pow(_, _) => Some("Pow"),
        _ => None,
    }
}
