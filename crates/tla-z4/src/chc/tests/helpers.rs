// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;
use tla_core::ast::{BoundVar, ExceptPathElement, ExceptSpec, Expr};
use tla_core::name_intern::NameId;
use tla_core::Spanned;
use z4_chc::PdrConfig;

/// Helper to create a TLA+ Int literal expression
pub(super) fn int_expr(n: i64) -> Spanned<Expr> {
    Spanned::dummy(Expr::Int(BigInt::from(n)))
}

/// Helper to create a state variable reference
pub(super) fn var_expr(name: &str) -> Spanned<Expr> {
    Spanned::dummy(Expr::StateVar(name.to_string(), 0, NameId::INVALID))
}

/// Helper to create a primed variable reference
pub(super) fn prime_expr(name: &str) -> Spanned<Expr> {
    Spanned::dummy(Expr::Prime(Box::new(var_expr(name))))
}

/// Helper to create an equality expression
pub(super) fn eq_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Eq(Box::new(a), Box::new(b)))
}

/// Helper to create a less-than expression
pub(super) fn lt_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Lt(Box::new(a), Box::new(b)))
}

/// Helper to create a less-than-or-equal expression
pub(super) fn le_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Leq(Box::new(a), Box::new(b)))
}

/// Helper to create an addition expression
pub(super) fn add_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Add(Box::new(a), Box::new(b)))
}

/// Helper to create an AND expression
pub(super) fn and_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::And(Box::new(a), Box::new(b)))
}

/// Helper to create an OR expression
pub(super) fn or_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Or(Box::new(a), Box::new(b)))
}

pub(super) fn pdr_config(max_frames: usize, max_iterations: usize) -> PdrConfig {
    PdrConfig::default()
        .with_max_frames(max_frames)
        .with_max_iterations(max_iterations)
}

pub(super) const PDR_TEST_LIMITS: (usize, usize) = (10, 100);
pub(super) const PDR_TEST_SLOW_LIMITS: (usize, usize) = (15, 150);

pub(super) fn pdr_test_config() -> PdrConfig {
    pdr_config(PDR_TEST_LIMITS.0, PDR_TEST_LIMITS.1)
}

pub(super) fn pdr_test_config_slow() -> PdrConfig {
    pdr_config(PDR_TEST_SLOW_LIMITS.0, PDR_TEST_SLOW_LIMITS.1)
}

// Extended helpers from #643 operator coverage
pub(super) fn sub_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Sub(Box::new(a), Box::new(b)))
}
pub(super) fn mul_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Mul(Box::new(a), Box::new(b)))
}
pub(super) fn neg_expr(a: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Neg(Box::new(a)))
}
pub(super) fn div_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::IntDiv(Box::new(a), Box::new(b)))
}
pub(super) fn mod_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Mod(Box::new(a), Box::new(b)))
}
pub(super) fn not_expr(a: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Not(Box::new(a)))
}
pub(super) fn implies_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Implies(Box::new(a), Box::new(b)))
}
pub(super) fn equiv_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Equiv(Box::new(a), Box::new(b)))
}
pub(super) fn ite_expr(
    cond: Spanned<Expr>,
    then_br: Spanned<Expr>,
    else_br: Spanned<Expr>,
) -> Spanned<Expr> {
    Spanned::dummy(Expr::If(
        Box::new(cond),
        Box::new(then_br),
        Box::new(else_br),
    ))
}
pub(super) fn bool_expr(b: bool) -> Spanned<Expr> {
    Spanned::dummy(Expr::Bool(b))
}

pub(super) fn string_expr(s: &str) -> Spanned<Expr> {
    Spanned::dummy(Expr::String(s.to_string()))
}

pub(super) fn ident_expr(name: &str) -> Spanned<Expr> {
    Spanned::dummy(Expr::Ident(name.to_string(), NameId::INVALID))
}

pub(super) fn set_enum_expr(items: Vec<Spanned<Expr>>) -> Spanned<Expr> {
    Spanned::dummy(Expr::SetEnum(items))
}

pub(super) fn in_expr(elem: Spanned<Expr>, set: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::In(Box::new(elem), Box::new(set)))
}

pub(super) fn func_apply_expr(func: Spanned<Expr>, arg: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::FuncApply(Box::new(func), Box::new(arg)))
}

pub(super) fn record_expr(fields: Vec<(&str, Spanned<Expr>)>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Record(
        fields
            .into_iter()
            .map(|(name, value)| (Spanned::dummy(name.to_string()), value))
            .collect(),
    ))
}

pub(super) fn record_set_expr(fields: Vec<(&str, Spanned<Expr>)>) -> Spanned<Expr> {
    Spanned::dummy(Expr::RecordSet(
        fields
            .into_iter()
            .map(|(name, value)| (Spanned::dummy(name.to_string()), value))
            .collect(),
    ))
}

pub(super) fn record_access_expr(record: Spanned<Expr>, field: &str) -> Spanned<Expr> {
    Spanned::dummy(Expr::RecordAccess(
        Box::new(record),
        tla_core::ast::RecordFieldName::from(Spanned::dummy(field.to_string())),
    ))
}

pub(super) fn bound_var(name: &str, domain: Spanned<Expr>) -> BoundVar {
    BoundVar {
        name: Spanned::dummy(name.to_string()),
        domain: Some(Box::new(domain)),
        pattern: None,
    }
}

pub(super) fn forall_expr(bounds: Vec<BoundVar>, body: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Forall(bounds, Box::new(body)))
}

pub(super) fn exists_expr(bounds: Vec<BoundVar>, body: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Exists(bounds, Box::new(body)))
}

pub(super) fn func_def_expr(bounds: Vec<BoundVar>, body: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::FuncDef(bounds, Box::new(body)))
}

pub(super) fn except_expr(
    base: Spanned<Expr>,
    index: Spanned<Expr>,
    value: Spanned<Expr>,
) -> Spanned<Expr> {
    Spanned::dummy(Expr::Except(
        Box::new(base),
        vec![ExceptSpec {
            path: vec![ExceptPathElement::Index(index)],
            value,
        }],
    ))
}

pub(super) fn record_except_expr(
    base: Spanned<Expr>,
    field: &str,
    value: Spanned<Expr>,
) -> Spanned<Expr> {
    Spanned::dummy(Expr::Except(
        Box::new(base),
        vec![ExceptSpec {
            path: vec![ExceptPathElement::Field(
                Spanned::dummy(field.to_string()).into(),
            )],
            value,
        }],
    ))
}

pub(super) fn ge_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Geq(Box::new(a), Box::new(b)))
}
pub(super) fn gt_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Gt(Box::new(a), Box::new(b)))
}
pub(super) fn ne_expr(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Neq(Box::new(a), Box::new(b)))
}

pub(super) fn range_expr(lo: Spanned<Expr>, hi: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::Range(Box::new(lo), Box::new(hi)))
}

pub(super) fn notin_expr(elem: Spanned<Expr>, set: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::dummy(Expr::NotIn(Box::new(elem), Box::new(set)))
}

pub(super) fn let_expr(defs: Vec<(&str, Spanned<Expr>)>, body: Spanned<Expr>) -> Spanned<Expr> {
    use tla_core::ast::OperatorDef;
    let op_defs = defs
        .into_iter()
        .map(|(name, def_body)| OperatorDef {
            name: Spanned::dummy(name.to_string()),
            params: vec![],
            body: def_body,
            local: true,
            contains_prime: false,
            guards_depend_on_prime: false,
            has_primed_param: false,
            is_recursive: false,
            self_call_count: 0,
        })
        .collect();
    Spanned::dummy(Expr::Let(op_defs, Box::new(body)))
}
