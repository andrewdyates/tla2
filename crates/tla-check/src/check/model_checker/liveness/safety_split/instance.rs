// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Instance-specific classification logic for safety/liveness splitting.
//!
//! Handles INSTANCE module references: qualifying identifiers into instance
//! scope, splitting instance operator bodies, and classifying each conjunct.

use super::super::super::{Expr, ModelChecker, ModuleTarget, Spanned};
use super::TermBucket;
use crate::eval::apply_substitutions;

/// Qualify an identifier into a module reference: `name` -> `instance!name`.
fn qualify_ident(
    instance_target: &ModuleTarget,
    name: &str,
    span: tla_core::span::Span,
) -> Spanned<Expr> {
    Spanned {
        node: Expr::ModuleRef(instance_target.clone(), name.to_string(), Vec::new()),
        span,
    }
}

/// If `expr` is an `Ident`, qualify it into the given instance scope; otherwise clone as-is.
fn qualify_if_ident(instance_target: &ModuleTarget, expr: &Spanned<Expr>) -> Spanned<Expr> {
    match &expr.node {
        Expr::Ident(name, _) => qualify_ident(instance_target, name, expr.span),
        _ => expr.clone(),
    }
}

/// Classify an `Always(inner)` part from an instance body.
///
/// For `[][Next]_vars`, the lowered form is `[](Next \/ UNCHANGED vars)`.
/// Qualifies identifiers into the instance scope so the extracted safety
/// term is evaluable in the outer module.
fn classify_instance_always(
    ctx: &crate::eval::EvalCtx,
    part: &Spanned<Expr>,
    source_part: &Spanned<Expr>,
    inner: &Spanned<Expr>,
    target: &ModuleTarget,
) -> (TermBucket, bool) {
    let source_has_span = matches!(
        &source_part.node,
        Expr::Always(source_inner) if ctx.is_action_subscript_span(source_inner.span)
    );
    let has_span = ctx.is_action_subscript_span(inner.span) || source_has_span;

    // Part of #3187: Span provenance is the sole discriminator. INSTANCE module
    // spans ARE registered via register_action_subscript_spans in
    // load_instance_module_with_extends (eval_module_load.rs:259). The prior
    // structural Or(_, Unchanged(_)) fallback was removed because it can't
    // distinguish real [A]_v subscripts from hand-written [](A \/ UNCHANGED v).
    if !has_span {
        return (TermBucket::Liveness(part.clone()), false);
    }

    let extracted = match &inner.node {
        Expr::Or(left, right) => extract_or_unchanged_action(inner, left, right, target),
        Expr::Ident(name, _) => Some(qualify_ident(target, name, inner.span)),
        _ => None,
    };
    if let Some(action) = extracted {
        return (TermBucket::Always(action), true);
    }

    if source_has_span {
        let converter = crate::liveness::AstToLive::new();
        let level = converter.get_level_with_ctx(ctx, &inner.node);
        let has_nested_temporal = ModelChecker::has_nested_temporal_for_safety_split(&part.node);
        let has_enabled = ModelChecker::contains_enabled(&inner.node);

        if !has_nested_temporal
            && !has_enabled
            && matches!(level, crate::liveness::ExprLevel::Action)
        {
            let qualified_inner = qualify_if_ident(target, inner);
            return (TermBucket::Always(qualified_inner), true);
        }
    }

    (TermBucket::Liveness(part.clone()), false)
}

/// Classify a single-arg `Apply` (potential `WF_`/`SF_` call) from an instance.
fn classify_instance_apply(
    part: &Spanned<Expr>,
    op: &Spanned<Expr>,
    args: &[Spanned<Expr>],
    target: &ModuleTarget,
) -> (TermBucket, bool) {
    if let Expr::Ident(fname, _) = &op.node {
        if fname.starts_with("WF_") || fname.starts_with("SF_") {
            let new_arg = qualify_if_ident(target, &args[0]);
            return (
                TermBucket::Liveness(Spanned {
                    node: Expr::Apply(Box::new(op.clone()), vec![new_arg]),
                    span: part.span,
                }),
                true,
            );
        }
    }
    (TermBucket::Liveness(part.clone()), false)
}

/// Extract and qualify an `Action \/ UNCHANGED vars` pattern from an Always body.
fn extract_or_unchanged_action(
    inner: &Spanned<Expr>,
    left: &Spanned<Expr>,
    right: &Spanned<Expr>,
    target: &ModuleTarget,
) -> Option<Spanned<Expr>> {
    let (action, unchanged, action_on_left) = match (&left.node, &right.node) {
        (Expr::Unchanged(_), _) => (right, left, false),
        (_, Expr::Unchanged(_)) => (left, right, true),
        _ => (inner, inner, true),
    };

    let Expr::Unchanged(unch_inner) = &unchanged.node else {
        return None;
    };

    let qualified_action = qualify_if_ident(target, action);
    let qualified_unch = qualify_if_ident(target, unch_inner.as_ref());
    let qualified_unchanged = Spanned {
        node: Expr::Unchanged(Box::new(qualified_unch)),
        span: unchanged.span,
    };

    let (new_left, new_right) = if action_on_left {
        (qualified_action, qualified_unchanged)
    } else {
        (qualified_unchanged, qualified_action)
    };

    Some(Spanned {
        node: Expr::Or(Box::new(new_left), Box::new(new_right)),
        span: inner.span,
    })
}

impl ModelChecker<'_> {
    /// Try to split a zero-arg named-instance module ref into safety/liveness parts.
    pub(super) fn try_split_module_ref(
        &self,
        term: &Spanned<Expr>,
        target: &ModuleTarget,
        op_name: &str,
        args: &[Spanned<Expr>],
    ) -> Option<Vec<TermBucket>> {
        if !args.is_empty() {
            return None;
        }
        let ModuleTarget::Named(instance_name) = target else {
            return None;
        };
        let info = self.ctx.get_instance(instance_name)?;
        let op_def = self.ctx.get_instance_op(&info.module_name, op_name)?;
        if !op_def.params.is_empty() {
            return None;
        }

        let mut source_parts = Vec::new();
        Self::flatten_and_terms(&op_def.body, &mut source_parts);

        let mut buckets = Vec::new();
        let mut extracted_any = false;
        for source_part in &source_parts {
            let substituted_part = apply_substitutions(source_part, &info.substitutions);
            let mut parts = Vec::new();
            Self::flatten_and_terms(&substituted_part, &mut parts);

            for part in &parts {
                let (bucket, did) = self.classify_instance_part(
                    part,
                    source_part,
                    term,
                    target,
                    op_name,
                    &info.module_name,
                );
                buckets.push(bucket);
                extracted_any |= did;
            }
        }
        if extracted_any {
            Some(buckets)
        } else {
            None
        }
    }

    /// Classify one conjunct from an expanded instance operator body.
    fn classify_instance_part(
        &self,
        part: &Spanned<Expr>,
        source_part: &Spanned<Expr>,
        original: &Spanned<Expr>,
        target: &ModuleTarget,
        op_name: &str,
        module_name: &str,
    ) -> (TermBucket, bool) {
        match &part.node {
            Expr::Ident(name, _) => {
                let is_temporal = self
                    .ctx
                    .get_instance_op(module_name, name)
                    .is_some_and(|d| Self::contains_temporal_helper(&d.body.node));
                let mr = qualify_ident(target, name, part.span);
                if is_temporal {
                    (TermBucket::Liveness(mr), true)
                } else {
                    (TermBucket::Init(mr), true)
                }
            }
            Expr::Always(inner) => {
                classify_instance_always(&self.ctx, part, source_part, inner, target)
            }
            Expr::Apply(op, a) if a.len() == 1 => classify_instance_apply(part, op, a, target),
            Expr::WeakFair(sub, action) | Expr::StrongFair(sub, action) => {
                let new_sub = qualify_if_ident(target, sub);
                let new_action = qualify_if_ident(target, action);
                let node = if matches!(&part.node, Expr::WeakFair(_, _)) {
                    Expr::WeakFair(Box::new(new_sub), Box::new(new_action))
                } else {
                    Expr::StrongFair(Box::new(new_sub), Box::new(new_action))
                };
                (
                    TermBucket::Liveness(Spanned {
                        node,
                        span: part.span,
                    }),
                    true,
                )
            }
            Expr::ModuleRef(..) => {
                let mr = qualify_ident(target, op_name, original.span);
                (TermBucket::Liveness(mr), true)
            }
            _ => {
                if Self::contains_temporal_helper(&part.node) || Self::contains_enabled(&part.node)
                {
                    (TermBucket::Liveness(part.clone()), false)
                } else {
                    (TermBucket::Init(part.clone()), true)
                }
            }
        }
    }
}
