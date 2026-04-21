// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Helper methods for the TIR lowerer: binary operators, bound variables,
// action subscripts, record access, and EXCEPT lowering.

use super::lowerer::Lowerer;
use super::scope::LoweringScope;
use crate::error::TirLowerError;
use crate::nodes::{
    TirActionSubscriptKind, TirArithOp, TirBoolOp, TirBoundPattern, TirBoundVar, TirCmpOp,
    TirExceptPathElement, TirExceptSpec, TirExpr, TirFieldName, TirSetOp,
};
use tla_core::ast::{BoundPattern, BoundVar, ExceptPathElement, Expr};
use tla_core::{intern_name, Spanned};

impl<'a> Lowerer<'a> {
    pub(super) fn lower_bound_var(
        &self,
        scope: &LoweringScope<'a>,
        var: &BoundVar,
    ) -> Result<TirBoundVar, TirLowerError> {
        let domain = var
            .domain
            .as_ref()
            .map(|d| self.lower_expr(scope, d))
            .transpose()?
            .map(Box::new);
        let pattern = var.pattern.as_ref().map(|p| match p {
            BoundPattern::Var(name) => {
                TirBoundPattern::Var(name.node.clone(), intern_name(&name.node))
            }
            BoundPattern::Tuple(names) => TirBoundPattern::Tuple(
                names
                    .iter()
                    .map(|n| (n.node.clone(), intern_name(&n.node)))
                    .collect(),
            ),
        });
        Ok(TirBoundVar {
            name: var.name.node.clone(),
            name_id: intern_name(&var.name.node),
            domain,
            pattern,
        })
    }

    pub(super) fn lower_bound_vars(
        &self,
        scope: &LoweringScope<'a>,
        vars: &[BoundVar],
    ) -> Result<Vec<TirBoundVar>, TirLowerError> {
        vars.iter()
            .map(|v| self.lower_bound_var(scope, v))
            .collect()
    }

    pub(super) fn lower_bool_bin(
        &self,
        scope: &LoweringScope<'a>,
        left: &Spanned<Expr>,
        op: TirBoolOp,
        right: &Spanned<Expr>,
    ) -> Result<TirExpr, TirLowerError> {
        Ok(TirExpr::BoolBinOp {
            left: Box::new(self.lower_expr(scope, left)?),
            op,
            right: Box::new(self.lower_expr(scope, right)?),
        })
    }

    pub(super) fn lower_cmp(
        &self,
        scope: &LoweringScope<'a>,
        left: &Spanned<Expr>,
        op: TirCmpOp,
        right: &Spanned<Expr>,
    ) -> Result<TirExpr, TirLowerError> {
        Ok(TirExpr::Cmp {
            left: Box::new(self.lower_expr(scope, left)?),
            op,
            right: Box::new(self.lower_expr(scope, right)?),
        })
    }

    pub(super) fn lower_in(
        &self,
        scope: &LoweringScope<'a>,
        elem: &Spanned<Expr>,
        set: &Spanned<Expr>,
    ) -> Result<TirExpr, TirLowerError> {
        Ok(TirExpr::In {
            elem: Box::new(self.lower_expr(scope, elem)?),
            set: Box::new(self.lower_expr(scope, set)?),
        })
    }

    pub(super) fn lower_arith_bin(
        &self,
        scope: &LoweringScope<'a>,
        left: &Spanned<Expr>,
        op: TirArithOp,
        right: &Spanned<Expr>,
    ) -> Result<TirExpr, TirLowerError> {
        Ok(TirExpr::ArithBinOp {
            left: Box::new(self.lower_expr(scope, left)?),
            op,
            right: Box::new(self.lower_expr(scope, right)?),
        })
    }

    pub(super) fn lower_set_bin(
        &self,
        scope: &LoweringScope<'a>,
        left: &Spanned<Expr>,
        op: TirSetOp,
        right: &Spanned<Expr>,
    ) -> Result<TirExpr, TirLowerError> {
        Ok(TirExpr::SetBinOp {
            left: Box::new(self.lower_expr(scope, left)?),
            op,
            right: Box::new(self.lower_expr(scope, right)?),
        })
    }

    pub(super) fn lower_action_subscript(
        &self,
        scope: &LoweringScope<'a>,
        expr: &Spanned<Expr>,
    ) -> Result<Spanned<TirExpr>, TirLowerError> {
        let (kind, action, subscript) = match &expr.node {
            Expr::Or(action, unchanged) => match &unchanged.node {
                Expr::Unchanged(subscript) => (
                    TirActionSubscriptKind::Box,
                    action.as_ref(),
                    subscript.as_ref(),
                ),
                _ => return Err(TirLowerError::InvalidActionSubscriptBridge { span: expr.span }),
            },
            Expr::And(action, not_unchanged) => match &not_unchanged.node {
                Expr::Not(inner) => match &inner.node {
                    Expr::Unchanged(subscript) => (
                        TirActionSubscriptKind::Angle,
                        action.as_ref(),
                        subscript.as_ref(),
                    ),
                    _ => {
                        return Err(TirLowerError::InvalidActionSubscriptBridge {
                            span: expr.span,
                        });
                    }
                },
                _ => return Err(TirLowerError::InvalidActionSubscriptBridge { span: expr.span }),
            },
            _ => return Err(TirLowerError::InvalidActionSubscriptBridge { span: expr.span }),
        };

        Ok(Spanned::new(
            TirExpr::ActionSubscript {
                kind,
                action: Box::new(self.lower_expr(scope, action)?),
                subscript: Box::new(self.lower_expr(scope, subscript)?),
            },
            expr.span,
        ))
    }

    pub(super) fn lower_record_access(
        &self,
        scope: &LoweringScope<'a>,
        base: &Spanned<Expr>,
        field: &tla_core::ast::RecordFieldName,
    ) -> Result<TirExpr, TirLowerError> {
        Ok(TirExpr::RecordAccess {
            record: Box::new(self.lower_expr(scope, base)?),
            field: TirFieldName {
                name: field.name.node.clone(),
                field_id: field.field_id,
            },
        })
    }

    pub(super) fn lower_except(
        &self,
        scope: &LoweringScope<'a>,
        base: &Spanned<Expr>,
        specs: &[tla_core::ast::ExceptSpec],
    ) -> Result<TirExpr, TirLowerError> {
        let tir_base = self.lower_expr(scope, base)?;
        let tir_specs = specs
            .iter()
            .map(|spec| {
                let path = spec
                    .path
                    .iter()
                    .map(|elem| match elem {
                        ExceptPathElement::Index(idx) => Ok(TirExceptPathElement::Index(Box::new(
                            self.lower_expr(scope, idx)?,
                        ))),
                        ExceptPathElement::Field(field) => {
                            Ok(TirExceptPathElement::Field(TirFieldName {
                                name: field.name.node.clone(),
                                field_id: field.field_id,
                            }))
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let prev = self.in_except_value.get();
                self.in_except_value.set(true);
                let value = self.lower_expr(scope, &spec.value);
                self.in_except_value.set(prev);

                Ok(TirExceptSpec {
                    path,
                    value: value?,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok(TirExpr::Except {
            base: Box::new(tir_base),
            specs: tir_specs,
        })
    }
}
