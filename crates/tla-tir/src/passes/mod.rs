// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(test)]
mod tests;

use crate::nodes::{
    TirArithOp, TirBoundVar, TirCaseArm, TirCmpOp, TirExceptPathElement, TirExceptSpec, TirExpr,
    TirLetDef, TirModuleRefSegment, TirOperatorRef,
};
use crate::types::TirType;
use tla_core::Spanned;
use tla_value::Value;

pub trait TirPass {
    #[must_use]
    fn name(&self) -> &'static str;

    #[must_use]
    fn run(&self, expr: Spanned<TirExpr>) -> Spanned<TirExpr>;
}

pub struct PassPipeline {
    passes: Vec<Box<dyn TirPass>>,
}

impl Default for PassPipeline {
    fn default() -> Self {
        Self::new()
    }
}

impl PassPipeline {
    #[must_use]
    pub fn new() -> Self {
        Self { passes: Vec::new() }
    }

    #[must_use]
    pub fn add<P: TirPass + 'static>(&mut self, pass: P) -> &mut Self {
        self.passes.push(Box::new(pass));
        self
    }

    #[must_use]
    pub fn default_pipeline() -> Self {
        let mut pipeline = Self::new();
        let _ = pipeline
            .add(NnfPass)
            .add(ConstantFoldPass)
            .add(SkolemizationPass)
            .add(DeadBranchPass);
        pipeline
    }

    #[must_use]
    pub fn run(&self, expr: Spanned<TirExpr>) -> Spanned<TirExpr> {
        self.passes.iter().fold(expr, |expr, pass| pass.run(expr))
    }
}

pub struct NnfPass;

impl TirPass for NnfPass {
    fn name(&self) -> &'static str {
        "nnf"
    }

    fn run(&self, expr: Spanned<TirExpr>) -> Spanned<TirExpr> {
        crate::preprocess::nnf_transform(expr)
    }
}

pub struct ConstantFoldPass;

impl TirPass for ConstantFoldPass {
    fn name(&self) -> &'static str {
        "constant_fold"
    }

    fn run(&self, expr: Spanned<TirExpr>) -> Spanned<TirExpr> {
        arith_constant_fold(crate::preprocess::constant_fold(expr))
    }
}

pub struct SkolemizationPass;

impl TirPass for SkolemizationPass {
    fn name(&self) -> &'static str {
        "skolemization"
    }

    fn run(&self, expr: Spanned<TirExpr>) -> Spanned<TirExpr> {
        skolemize_bounded_exists(expr)
    }
}

pub struct DeadBranchPass;

impl TirPass for DeadBranchPass {
    fn name(&self) -> &'static str {
        "dead_branch"
    }

    fn run(&self, expr: Spanned<TirExpr>) -> Spanned<TirExpr> {
        dead_branch_eliminate(expr)
    }
}

type ExprTransform = fn(Spanned<TirExpr>) -> Spanned<TirExpr>;

#[must_use]
pub(crate) fn arith_constant_fold(expr: Spanned<TirExpr>) -> Spanned<TirExpr> {
    let expr = map_children(expr, arith_constant_fold);
    let span = expr.span;

    match expr.node {
        TirExpr::ArithBinOp { left, op, right } => {
            if let (Some(lhs), Some(rhs)) = (as_i64_const(&left), as_i64_const(&right)) {
                if let Some(value) = fold_arith_bin_op(lhs, op, rhs) {
                    return int_const_with_span(value, span);
                }
            }

            Spanned {
                node: TirExpr::ArithBinOp { left, op, right },
                span,
            }
        }
        TirExpr::ArithNeg(inner) => {
            if let Some(value) = as_i64_const(&inner) {
                if let Some(negated) = value.checked_neg() {
                    return int_const_with_span(negated, span);
                }
            }

            Spanned {
                node: TirExpr::ArithNeg(inner),
                span,
            }
        }
        TirExpr::Cmp { left, op, right } => {
            if let (Some(lhs), Some(rhs)) = (as_i64_const(&left), as_i64_const(&right)) {
                return bool_const_with_span(fold_cmp_op(lhs, op, rhs), span);
            }

            Spanned {
                node: TirExpr::Cmp { left, op, right },
                span,
            }
        }
        node => Spanned { node, span },
    }
}

#[must_use]
fn skolemize_bounded_exists(expr: Spanned<TirExpr>) -> Spanned<TirExpr> {
    let expr = map_children(expr, skolemize_bounded_exists);
    let span = expr.span;

    match expr.node {
        TirExpr::Exists { vars, body } => {
            if vars.iter().all(|var| var.domain.is_some()) {
                let body = Spanned {
                    node: TirExpr::Exists { vars, body },
                    span,
                };
                Spanned {
                    node: TirExpr::Label {
                        name: "__skolem__".to_string(),
                        body: Box::new(body),
                    },
                    span,
                }
            } else {
                Spanned {
                    node: TirExpr::Exists { vars, body },
                    span,
                }
            }
        }
        node => Spanned { node, span },
    }
}

#[must_use]
fn dead_branch_eliminate(expr: Spanned<TirExpr>) -> Spanned<TirExpr> {
    let expr = map_children(expr, dead_branch_eliminate);
    let span = expr.span;

    match expr.node {
        TirExpr::If { cond, then_, else_ } => match as_bool_const(&cond) {
            Some(true) => *then_,
            Some(false) => *else_,
            None => Spanned {
                node: TirExpr::If { cond, then_, else_ },
                span,
            },
        },
        TirExpr::Case { arms, other } => {
            let mut all_false = true;
            let mut rebuilt_arms = Vec::with_capacity(arms.len());

            for arm in arms {
                match as_bool_const(&arm.guard) {
                    Some(true) => return arm.body,
                    Some(false) => {
                        continue;
                    }
                    None => {
                        all_false = false;
                    }
                }

                rebuilt_arms.push(arm);
            }

            if all_false {
                if let Some(other) = other {
                    return *other;
                }
            }

            Spanned {
                node: TirExpr::Case {
                    arms: rebuilt_arms,
                    other,
                },
                span,
            }
        }
        TirExpr::Forall { vars, body } => match as_bool_const(&body) {
            Some(true) => bool_const_with_span(true, span),
            _ => Spanned {
                node: TirExpr::Forall { vars, body },
                span,
            },
        },
        TirExpr::Exists { vars, body } => match as_bool_const(&body) {
            Some(false) => bool_const_with_span(false, span),
            _ => Spanned {
                node: TirExpr::Exists { vars, body },
                span,
            },
        },
        TirExpr::Let { defs, body } => {
            if matches!(body.node, TirExpr::Const { .. }) {
                *body
            } else {
                Spanned {
                    node: TirExpr::Let { defs, body },
                    span,
                }
            }
        }
        node => Spanned { node, span },
    }
}

#[must_use]
fn map_children(expr: Spanned<TirExpr>, transform: ExprTransform) -> Spanned<TirExpr> {
    let span = expr.span;
    let node = match expr.node {
        TirExpr::Const { value, ty } => TirExpr::Const { value, ty },
        TirExpr::Name(name) => TirExpr::Name(name),
        TirExpr::OperatorRef(op_ref) => {
            TirExpr::OperatorRef(transform_operator_ref(op_ref, transform))
        }
        TirExpr::ArithBinOp { left, op, right } => TirExpr::ArithBinOp {
            left: Box::new(transform(*left)),
            op,
            right: Box::new(transform(*right)),
        },
        TirExpr::ArithNeg(inner) => TirExpr::ArithNeg(Box::new(transform(*inner))),
        TirExpr::BoolBinOp { left, op, right } => TirExpr::BoolBinOp {
            left: Box::new(transform(*left)),
            op,
            right: Box::new(transform(*right)),
        },
        TirExpr::BoolNot(inner) => TirExpr::BoolNot(Box::new(transform(*inner))),
        TirExpr::Cmp { left, op, right } => TirExpr::Cmp {
            left: Box::new(transform(*left)),
            op,
            right: Box::new(transform(*right)),
        },
        TirExpr::In { elem, set } => TirExpr::In {
            elem: Box::new(transform(*elem)),
            set: Box::new(transform(*set)),
        },
        TirExpr::Subseteq { left, right } => TirExpr::Subseteq {
            left: Box::new(transform(*left)),
            right: Box::new(transform(*right)),
        },
        TirExpr::Unchanged(inner) => TirExpr::Unchanged(Box::new(transform(*inner))),
        TirExpr::ActionSubscript {
            kind,
            action,
            subscript,
        } => TirExpr::ActionSubscript {
            kind,
            action: Box::new(transform(*action)),
            subscript: Box::new(transform(*subscript)),
        },
        TirExpr::Always(inner) => TirExpr::Always(Box::new(transform(*inner))),
        TirExpr::Eventually(inner) => TirExpr::Eventually(Box::new(transform(*inner))),
        TirExpr::RecordAccess { record, field } => TirExpr::RecordAccess {
            record: Box::new(transform(*record)),
            field,
        },
        TirExpr::Except { base, specs } => TirExpr::Except {
            base: Box::new(transform(*base)),
            specs: specs
                .into_iter()
                .map(|spec| transform_except_spec(spec, transform))
                .collect(),
        },
        TirExpr::ExceptAt => TirExpr::ExceptAt,
        TirExpr::Range { lo, hi } => TirExpr::Range {
            lo: Box::new(transform(*lo)),
            hi: Box::new(transform(*hi)),
        },
        TirExpr::If { cond, then_, else_ } => TirExpr::If {
            cond: Box::new(transform(*cond)),
            then_: Box::new(transform(*then_)),
            else_: Box::new(transform(*else_)),
        },
        TirExpr::Forall { vars, body } => TirExpr::Forall {
            vars: vars
                .into_iter()
                .map(|var| transform_bound_var(var, transform))
                .collect(),
            body: Box::new(transform(*body)),
        },
        TirExpr::Exists { vars, body } => TirExpr::Exists {
            vars: vars
                .into_iter()
                .map(|var| transform_bound_var(var, transform))
                .collect(),
            body: Box::new(transform(*body)),
        },
        TirExpr::Choose { var, body } => TirExpr::Choose {
            var: transform_bound_var(var, transform),
            body: Box::new(transform(*body)),
        },
        TirExpr::SetEnum(elems) => TirExpr::SetEnum(transform_exprs(elems, transform)),
        TirExpr::SetFilter { var, body } => TirExpr::SetFilter {
            var: transform_bound_var(var, transform),
            body: Box::new(transform(*body)),
        },
        TirExpr::SetBuilder { body, vars } => TirExpr::SetBuilder {
            body: Box::new(transform(*body)),
            vars: vars
                .into_iter()
                .map(|var| transform_bound_var(var, transform))
                .collect(),
        },
        TirExpr::SetBinOp { left, op, right } => TirExpr::SetBinOp {
            left: Box::new(transform(*left)),
            op,
            right: Box::new(transform(*right)),
        },
        TirExpr::Powerset(inner) => TirExpr::Powerset(Box::new(transform(*inner))),
        TirExpr::BigUnion(inner) => TirExpr::BigUnion(Box::new(transform(*inner))),
        TirExpr::KSubset { base, k } => TirExpr::KSubset {
            base: Box::new(transform(*base)),
            k: Box::new(transform(*k)),
        },
        TirExpr::FuncDef { vars, body } => TirExpr::FuncDef {
            vars: vars
                .into_iter()
                .map(|var| transform_bound_var(var, transform))
                .collect(),
            body: Box::new(transform(*body)),
        },
        TirExpr::FuncApply { func, arg } => TirExpr::FuncApply {
            func: Box::new(transform(*func)),
            arg: Box::new(transform(*arg)),
        },
        TirExpr::FuncSet { domain, range } => TirExpr::FuncSet {
            domain: Box::new(transform(*domain)),
            range: Box::new(transform(*range)),
        },
        TirExpr::Domain(inner) => TirExpr::Domain(Box::new(transform(*inner))),
        TirExpr::Record(fields) => TirExpr::Record(
            fields
                .into_iter()
                .map(|(field, expr)| (field, transform(expr)))
                .collect(),
        ),
        TirExpr::RecordSet(fields) => TirExpr::RecordSet(
            fields
                .into_iter()
                .map(|(field, expr)| (field, transform(expr)))
                .collect(),
        ),
        TirExpr::Tuple(elems) => TirExpr::Tuple(transform_exprs(elems, transform)),
        TirExpr::Times(elems) => TirExpr::Times(transform_exprs(elems, transform)),
        TirExpr::Let { defs, body } => TirExpr::Let {
            defs: defs
                .into_iter()
                .map(|def| transform_let_def(def, transform))
                .collect(),
            body: Box::new(transform(*body)),
        },
        TirExpr::Case { arms, other } => TirExpr::Case {
            arms: arms
                .into_iter()
                .map(|arm| transform_case_arm(arm, transform))
                .collect(),
            other: other.map(|other| Box::new(transform(*other))),
        },
        TirExpr::Prime(inner) => TirExpr::Prime(Box::new(transform(*inner))),
        TirExpr::Apply { op, args } => TirExpr::Apply {
            op: Box::new(transform(*op)),
            args: transform_exprs(args, transform),
        },
        TirExpr::Lambda {
            params,
            body,
            ast_body,
        } => TirExpr::Lambda {
            params,
            body: Box::new(transform(*body)),
            ast_body,
        },
        TirExpr::OpRef(name) => TirExpr::OpRef(name),
        TirExpr::Label { name, body } => TirExpr::Label {
            name,
            body: Box::new(transform(*body)),
        },
        TirExpr::LeadsTo { left, right } => TirExpr::LeadsTo {
            left: Box::new(transform(*left)),
            right: Box::new(transform(*right)),
        },
        TirExpr::WeakFair { vars, action } => TirExpr::WeakFair {
            vars: Box::new(transform(*vars)),
            action: Box::new(transform(*action)),
        },
        TirExpr::StrongFair { vars, action } => TirExpr::StrongFair {
            vars: Box::new(transform(*vars)),
            action: Box::new(transform(*action)),
        },
        TirExpr::Enabled(inner) => TirExpr::Enabled(Box::new(transform(*inner))),
    };

    Spanned { node, span }
}

fn transform_bound_var(var: TirBoundVar, transform: ExprTransform) -> TirBoundVar {
    TirBoundVar {
        name: var.name,
        name_id: var.name_id,
        domain: var.domain.map(|domain| Box::new(transform(*domain))),
        pattern: var.pattern,
    }
}

fn transform_case_arm(arm: TirCaseArm, transform: ExprTransform) -> TirCaseArm {
    TirCaseArm {
        guard: transform(arm.guard),
        body: transform(arm.body),
    }
}

fn transform_let_def(def: TirLetDef, transform: ExprTransform) -> TirLetDef {
    TirLetDef {
        name: def.name,
        name_id: def.name_id,
        params: def.params,
        body: transform(def.body),
    }
}

fn transform_except_spec(spec: TirExceptSpec, transform: ExprTransform) -> TirExceptSpec {
    TirExceptSpec {
        path: spec
            .path
            .into_iter()
            .map(|element| match element {
                TirExceptPathElement::Index(index) => {
                    TirExceptPathElement::Index(Box::new(transform(*index)))
                }
                TirExceptPathElement::Field(field) => TirExceptPathElement::Field(field),
            })
            .collect(),
        value: transform(spec.value),
    }
}

fn transform_operator_ref(op_ref: TirOperatorRef, transform: ExprTransform) -> TirOperatorRef {
    TirOperatorRef {
        path: op_ref
            .path
            .into_iter()
            .map(|segment| transform_module_ref_segment(segment, transform))
            .collect(),
        operator: op_ref.operator,
        operator_id: op_ref.operator_id,
        args: transform_exprs(op_ref.args, transform),
    }
}

fn transform_module_ref_segment(
    segment: TirModuleRefSegment,
    transform: ExprTransform,
) -> TirModuleRefSegment {
    TirModuleRefSegment {
        name: segment.name,
        name_id: segment.name_id,
        args: transform_exprs(segment.args, transform),
    }
}

fn transform_exprs(
    exprs: Vec<Spanned<TirExpr>>,
    transform: ExprTransform,
) -> Vec<Spanned<TirExpr>> {
    exprs.into_iter().map(transform).collect()
}

fn as_bool_const(expr: &Spanned<TirExpr>) -> Option<bool> {
    match &expr.node {
        TirExpr::Const {
            value: Value::Bool(value),
            ..
        } => Some(*value),
        _ => None,
    }
}

fn as_i64_const(expr: &Spanned<TirExpr>) -> Option<i64> {
    match &expr.node {
        TirExpr::Const { value, .. } => value.as_i64(),
        _ => None,
    }
}

fn fold_arith_bin_op(lhs: i64, op: TirArithOp, rhs: i64) -> Option<i64> {
    match op {
        TirArithOp::Add => lhs.checked_add(rhs),
        TirArithOp::Sub => lhs.checked_sub(rhs),
        TirArithOp::Mul => lhs.checked_mul(rhs),
        TirArithOp::IntDiv => {
            if rhs == 0 {
                return None;
            }
            let q = lhs.checked_div(rhs)?;
            Some(if (lhs ^ rhs) < 0 && lhs % rhs != 0 {
                q - 1
            } else {
                q
            })
        }
        TirArithOp::Mod => {
            if rhs == 0 {
                return None;
            }
            let r = lhs.checked_rem(rhs)?;
            Some(if r < 0 { r + rhs.abs() } else { r })
        }
        TirArithOp::Div | TirArithOp::Pow => None,
    }
}

fn fold_cmp_op(lhs: i64, op: TirCmpOp, rhs: i64) -> bool {
    match op {
        TirCmpOp::Eq => lhs == rhs,
        TirCmpOp::Neq => lhs != rhs,
        TirCmpOp::Lt => lhs < rhs,
        TirCmpOp::Leq => lhs <= rhs,
        TirCmpOp::Gt => lhs > rhs,
        TirCmpOp::Geq => lhs >= rhs,
    }
}

fn bool_const_with_span(value: bool, span: tla_core::span::Span) -> Spanned<TirExpr> {
    Spanned {
        node: TirExpr::Const {
            value: Value::Bool(value),
            ty: TirType::Bool,
        },
        span,
    }
}

fn int_const_with_span(value: i64, span: tla_core::span::Span) -> Spanned<TirExpr> {
    Spanned {
        node: TirExpr::Const {
            value: Value::int(value),
            ty: TirType::Int,
        },
        span,
    }
}
