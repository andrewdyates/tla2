// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared bound-variable operations for AST and TIR quantifier helpers.

use super::quantifiers::{
    push_bound_var_mut_preinterned, push_bound_var_owned_preinterned, PreInternedBound,
};
use crate::tir::eval_tir;
use crate::{eval, EvalCtx, EvalError, EvalResult};
use tla_core::ast::{BoundPattern, BoundVar};
use tla_core::Span;
use tla_tir::nodes::{TirBoundPattern, TirBoundVar};
use tla_value::Value;

/// Shared bound-variable operations used by AST and TIR quantifier wrappers.
pub(crate) trait BoundVarOps {
    fn is_simple(&self) -> bool;
    fn domain_span(&self) -> Option<Span>;
    fn eval_domain(&self, ctx: &EvalCtx, kind: &str, span: Option<Span>) -> EvalResult<Value>;
    fn push_binding(&self, ctx: &mut EvalCtx, elem: &Value, span: Option<Span>) -> EvalResult<()>;
    fn push_binding_owned(
        &self,
        ctx: &mut EvalCtx,
        elem: Value,
        span: Option<Span>,
    ) -> EvalResult<()>;
}

/// AST bound variable with pre-interned names, ready for quantifier loops.
pub(crate) struct PreparedBound<'a> {
    bound: &'a BoundVar,
    pre: PreInternedBound,
}

impl<'a> PreparedBound<'a> {
    pub(crate) fn new(bound: &'a BoundVar) -> Self {
        Self {
            bound,
            pre: PreInternedBound::from_bound(bound),
        }
    }

    pub(crate) fn pre(&self) -> &PreInternedBound {
        &self.pre
    }
}

impl BoundVarOps for PreparedBound<'_> {
    fn is_simple(&self) -> bool {
        !matches!(&self.bound.pattern, Some(BoundPattern::Tuple(_)))
    }

    fn domain_span(&self) -> Option<Span> {
        self.bound.domain.as_ref().map(|domain| domain.span)
    }

    fn eval_domain(&self, ctx: &EvalCtx, kind: &str, span: Option<Span>) -> EvalResult<Value> {
        let domain = self
            .bound
            .domain
            .as_ref()
            .ok_or_else(|| EvalError::Internal {
                message: format!("{kind} requires bounded quantification"),
                span,
            })?;
        eval(ctx, domain)
    }

    fn push_binding(&self, ctx: &mut EvalCtx, elem: &Value, span: Option<Span>) -> EvalResult<()> {
        push_bound_var_mut_preinterned(ctx, self.bound, elem, span, Some(&self.pre))
    }

    fn push_binding_owned(
        &self,
        ctx: &mut EvalCtx,
        elem: Value,
        span: Option<Span>,
    ) -> EvalResult<()> {
        push_bound_var_owned_preinterned(ctx, self.bound, elem, span, Some(&self.pre))
    }
}

/// Push a TIR bound variable binding onto the context.
/// TIR bound vars carry pre-interned `NameId`, avoiding runtime intern lookups.
pub(crate) fn push_tir_bound_var(
    ctx: &mut EvalCtx,
    var: &TirBoundVar,
    elem: &Value,
    span: Option<Span>,
) -> EvalResult<()> {
    match &var.pattern {
        Some(TirBoundPattern::Tuple(vars)) => {
            let tuple = elem
                .to_tuple_like_elements()
                .ok_or_else(|| EvalError::type_error("Tuple", elem, span))?;
            if tuple.len() != vars.len() {
                return Err(EvalError::Internal {
                    message: format!(
                        "Tuple pattern has {} variables but element has {} components",
                        vars.len(),
                        tuple.len()
                    ),
                    span,
                });
            }
            for ((_name, name_id), val) in vars.iter().zip(tuple.iter()) {
                ctx.push_binding_by_id(*name_id, val.clone());
            }
            Ok(())
        }
        Some(TirBoundPattern::Var(_name, name_id)) => {
            ctx.push_binding_by_id(*name_id, elem.clone());
            Ok(())
        }
        None => {
            ctx.push_binding_by_id(var.name_id, elem.clone());
            Ok(())
        }
    }
}

pub(crate) fn is_simple_tir_bound(var: &TirBoundVar) -> bool {
    !matches!(&var.pattern, Some(TirBoundPattern::Tuple(_)))
}

impl BoundVarOps for TirBoundVar {
    fn is_simple(&self) -> bool {
        is_simple_tir_bound(self)
    }

    fn domain_span(&self) -> Option<Span> {
        self.domain.as_ref().map(|domain| domain.span)
    }

    fn eval_domain(&self, ctx: &EvalCtx, kind: &str, span: Option<Span>) -> EvalResult<Value> {
        let domain = self.domain.as_ref().ok_or_else(|| EvalError::Internal {
            message: format!("{kind} requires bounded quantification"),
            span,
        })?;
        eval_tir(ctx, domain)
    }

    fn push_binding(&self, ctx: &mut EvalCtx, elem: &Value, span: Option<Span>) -> EvalResult<()> {
        push_tir_bound_var(ctx, self, elem, span)
    }

    fn push_binding_owned(
        &self,
        ctx: &mut EvalCtx,
        elem: Value,
        span: Option<Span>,
    ) -> EvalResult<()> {
        match &self.pattern {
            Some(TirBoundPattern::Tuple(_)) => push_tir_bound_var(ctx, self, &elem, span),
            Some(TirBoundPattern::Var(_name, name_id)) => {
                ctx.push_binding_by_id(*name_id, elem);
                Ok(())
            }
            None => {
                ctx.push_binding_by_id(self.name_id, elem);
                Ok(())
            }
        }
    }
}
