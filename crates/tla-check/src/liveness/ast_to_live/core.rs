// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::live_expr::{ExprLevel, LiveExpr};
use super::errors::ConvertError;
use crate::eval::{eval_entry, EvalCtx, EvalError};
use crate::Value;
use std::cell::{Cell, RefCell};
use std::sync::Arc;
use tla_core::ast::{Expr, ModuleTarget};
use tla_core::Spanned;

// debug_flag! macro defined in crate::debug_env (via #[macro_use])

debug_flag!(pub(super) debug_resolve, "TLA2_DEBUG_RESOLVE");
debug_flag!(pub(super) debug_let, "TLA2_DEBUG_LET");
debug_flag!(pub(super) debug_instance_resolve, "TLA2_DEBUG_INSTANCE_RESOLVE");
debug_flag!(pub(super) debug_subst, "TLA2_DEBUG_SUBST");

/// Returns true if the eval error indicates an unbound variable or operator,
/// meaning the expression's level was likely misclassified as constant when it
/// is actually state-level. These errors should fall back to state predicate
/// treatment. All other eval errors (DivisionByZero, TypeError, etc.) are
/// genuine failures that should be propagated.
pub(super) fn is_binding_error(e: &EvalError) -> bool {
    matches!(
        e,
        EvalError::UndefinedVar { .. } | EvalError::UndefinedOp { .. }
    )
}

/// Returns true if the eval error indicates a non-enumerable domain (e.g.,
/// `Seq({1})` or `Nat`), meaning the constant-level expression involves a set
/// that is too large to enumerate. These expressions should fall back to state
/// predicate treatment rather than failing liveness conversion. TLC handles
/// these by leaving them as unevaluated predicates.
///
/// Part of #4067.
pub(super) fn is_non_enumerable_error(e: &EvalError) -> bool {
    matches!(e, EvalError::SetTooLarge { .. })
}

/// Part of #3100: Structured action predicate hint for provenance matching.
///
/// Records the operator name and any const-level actual-arg bindings captured
/// at fairness conversion time. This allows the inline fairness cache to
/// distinguish `WF_vars(Op(1))` from `WF_vars(Op(2))` without re-parsing.
#[derive(Debug, Clone)]
pub struct ActionPredHint {
    pub tag: u32,
    pub name: Arc<str>,
    /// Whether this hint is safe to use for split-action fast-path prepopulation.
    ///
    /// INSTANCE-qualified `ModuleRef` hints still participate in diagnostics and
    /// metadata tests, but their split-action provenance is currently too coarse
    /// to bypass evaluator-based action checks without false positives (#3161).
    pub split_action_fast_path_safe: bool,
    /// Const-level actual-arg bindings: `(formal_param_name, value)`.
    /// Empty for bare identifiers like `WF_vars(Next)`.
    pub actual_arg_bindings: Vec<(Arc<str>, Value)>,
}

/// Converter from AST to LiveExpr
///
/// Maintains state during conversion, including tag allocation for predicates.
pub struct AstToLive {
    /// Next tag to assign to predicates
    next_tag: Cell<u32>,
    /// Default module name used when rendering TLC-shaped location strings.
    ///
    /// TLC's EC.TLC_LIVE_CANNOT_HANDLE_FORMULA prints a location string by default. We don't
    /// currently compute line/col here, but we still want a stable "bytes ... of module ..."
    /// shape for output parity.
    location_module_name: Option<Arc<str>>,
    /// Stack of module reference targets currently being inlined.
    ///
    /// When converting `M!Op` by inlining `Op`'s body, predicates inside that body
    /// may reference module-local operators (e.g., `Next`, `Init`). Those must be
    /// qualified so they can be evaluated later without module-local operator scope.
    target_stack: RefCell<Vec<Arc<ModuleTarget>>>,
    /// Stack of LET definitions currently in scope.
    ///
    /// When converting predicates inside `LET defs IN body`, the predicate expressions
    /// need to be wrapped in the LET so they can be evaluated later with the definitions
    /// in scope.
    let_defs_stack: RefCell<Vec<Vec<tla_core::ast::OperatorDef>>>,
    /// Stack of bound-variable bindings for liveness bounded quantifiers.
    ///
    /// This mirrors TLC's `Context` chain: when we expand bounded quantifiers
    /// in temporal formulas, we enumerate binding environments and attach them
    /// to leaf predicates (no Value→Expr substitution).
    quantifier_bindings_stack: RefCell<Vec<Option<crate::eval::BindingChain>>>,
    /// Part of #3100: Action predicate hints mapping tag → action identity.
    ///
    /// Recorded during WF/SF conversion so the inline liveness recorder can match
    /// ActionPred tags to split_action indices without re-parsing expressions.
    /// Extended with actual-arg bindings to distinguish `WF_vars(Op(1))` from
    /// `WF_vars(Op(2))`.
    action_pred_hints: RefCell<Vec<ActionPredHint>>,
}

pub(super) struct TargetGuard<'a> {
    stack: &'a RefCell<Vec<Arc<ModuleTarget>>>,
}

impl Drop for TargetGuard<'_> {
    fn drop(&mut self) {
        self.stack.borrow_mut().pop();
    }
}

pub(super) struct LetGuard<'a> {
    stack: &'a RefCell<Vec<Vec<tla_core::ast::OperatorDef>>>,
}

impl Drop for LetGuard<'_> {
    fn drop(&mut self) {
        self.stack.borrow_mut().pop();
    }
}

pub(super) struct QuantifierBindingsGuard<'a> {
    stack: &'a RefCell<Vec<Option<crate::eval::BindingChain>>>,
}

impl Drop for QuantifierBindingsGuard<'_> {
    fn drop(&mut self) {
        self.stack.borrow_mut().pop();
    }
}

impl AstToLive {
    /// Create a new converter
    pub fn new() -> Self {
        Self {
            next_tag: Cell::new(1),
            location_module_name: None,
            target_stack: RefCell::new(Vec::new()),
            let_defs_stack: RefCell::new(Vec::new()),
            quantifier_bindings_stack: RefCell::new(Vec::new()),
            action_pred_hints: RefCell::new(Vec::new()),
        }
    }

    /// Part of #3065: Return the current tag counter value.
    /// Used to determine the max fairness tag after fairness conversion.
    pub fn next_tag(&self) -> u32 {
        self.next_tag.get()
    }

    /// Set the default module name used for TLC-shaped location strings.
    pub fn with_location_module_name(mut self, module_name: impl Into<Arc<str>>) -> Self {
        self.location_module_name = Some(module_name.into());
        self
    }

    pub(super) fn location_module_name_for_error(&self) -> Option<Arc<str>> {
        self.location_module_name.clone()
    }

    /// Push LET definitions onto the stack
    pub(super) fn push_let_defs(&self, defs: Vec<tla_core::ast::OperatorDef>) -> LetGuard<'_> {
        self.let_defs_stack.borrow_mut().push(defs);
        LetGuard {
            stack: &self.let_defs_stack,
        }
    }

    /// Wrap an expression in any LET definitions currently in scope
    pub(super) fn wrap_in_let_defs(&self, expr: Spanned<Expr>) -> Spanned<Expr> {
        let stack = self.let_defs_stack.borrow();
        if stack.is_empty() {
            return expr;
        }
        // Flatten all LET definitions and wrap the expression
        let all_defs: Vec<_> = stack.iter().flatten().cloned().collect();
        if all_defs.is_empty() {
            return expr;
        }
        Spanned {
            span: expr.span,
            node: Expr::Let(all_defs, Box::new(expr)),
        }
    }

    /// Allocate a new unique tag for a predicate
    pub fn alloc_tag(&self) -> u32 {
        let tag = self.next_tag.get();
        self.next_tag.set(tag + 1);
        tag
    }

    /// Part of #3100: Record a structured action predicate hint.
    pub fn record_action_hint(&self, hint: ActionPredHint) {
        self.action_pred_hints.borrow_mut().push(hint);
    }

    /// Part of #3100: Consume the accumulated action predicate hints.
    pub fn take_action_pred_hints(&self) -> Vec<ActionPredHint> {
        std::mem::take(&mut *self.action_pred_hints.borrow_mut())
    }

    pub(super) fn current_quantifier_bindings(&self) -> Option<crate::eval::BindingChain> {
        self.quantifier_bindings_stack
            .borrow()
            .last()
            .cloned()
            .flatten()
    }

    pub(super) fn push_quantifier_bindings(
        &self,
        bindings: Option<crate::eval::BindingChain>,
    ) -> QuantifierBindingsGuard<'_> {
        self.quantifier_bindings_stack.borrow_mut().push(bindings);
        QuantifierBindingsGuard {
            stack: &self.quantifier_bindings_stack,
        }
    }

    pub(super) fn current_target(&self) -> Option<Arc<ModuleTarget>> {
        self.target_stack.borrow().last().cloned()
    }

    pub(super) fn push_target(&self, target: Arc<ModuleTarget>) -> TargetGuard<'_> {
        self.target_stack.borrow_mut().push(target);
        TargetGuard {
            stack: &self.target_stack,
        }
    }

    /// Convert an AST expression to a LiveExpr
    ///
    /// The context is used to evaluate constant subexpressions.
    pub fn convert(&self, ctx: &EvalCtx, expr: &Spanned<Expr>) -> Result<LiveExpr, ConvertError> {
        self.convert_expr(ctx, &expr.node, Arc::new(expr.clone()))
    }

    /// Internal conversion with the original expression for predicates
    fn convert_expr(
        &self,
        ctx: &EvalCtx,
        expr: &Expr,
        original: Arc<Spanned<Expr>>,
    ) -> Result<LiveExpr, ConvertError> {
        // IMPORTANT: Handle ENABLED specially before level-based dispatch.
        // ENABLED is state-level but cannot be evaluated by `eval()` - it must
        // be converted to LiveExpr::Enabled and handled by eval_live_expr.
        // This also applies to expressions containing ENABLED (like ~ENABLED A).
        match expr {
            // ENABLED A -> LiveExpr::Enabled
            Expr::Enabled(inner) => {
                // Resolve operator references (and LET expansions) so ENABLED can be evaluated
                // later without relying on the conversion-time context.
                let resolved_action = self.resolve_action_expr(ctx, inner);
                let wrapped = self.wrap_in_let_defs(resolved_action);
                return Ok(LiveExpr::enabled(Arc::new(wrapped), self.alloc_tag()));
            }
            // NOT containing ENABLED -> LiveExpr::Not(convert inner)
            Expr::Not(inner) if Self::contains_enabled(&inner.node) => {
                let inner_live = self.convert(ctx, inner)?;
                return Ok(LiveExpr::not(inner_live));
            }
            // AND/OR containing ENABLED -> convert recursively
            Expr::And(a, b)
                if Self::contains_enabled(&a.node) || Self::contains_enabled(&b.node) =>
            {
                let left_live = self.convert(ctx, a)?;
                let right_live = self.convert(ctx, b)?;
                return Ok(LiveExpr::and(vec![left_live, right_live]));
            }
            Expr::Or(a, b)
                if Self::contains_enabled(&a.node) || Self::contains_enabled(&b.node) =>
            {
                let left_live = self.convert(ctx, a)?;
                let right_live = self.convert(ctx, b)?;
                return Ok(LiveExpr::or(vec![left_live, right_live]));
            }
            Expr::Implies(a, b)
                if Self::contains_enabled(&a.node) || Self::contains_enabled(&b.node) =>
            {
                let left_live = self.convert(ctx, a)?;
                let right_live = self.convert(ctx, b)?;
                return Ok(LiveExpr::or(vec![LiveExpr::not(left_live), right_live]));
            }
            // EQUIV containing ENABLED: A <=> B is equivalent to (A /\ B) \/ (~A /\ ~B)
            Expr::Equiv(a, b)
                if Self::contains_enabled(&a.node) || Self::contains_enabled(&b.node) =>
            {
                let left_live = self.convert(ctx, a)?;
                let right_live = self.convert(ctx, b)?;
                // (A /\ B) \/ (~A /\ ~B)
                let both_true = LiveExpr::and(vec![left_live.clone(), right_live.clone()]);
                let both_false =
                    LiveExpr::and(vec![LiveExpr::not(left_live), LiveExpr::not(right_live)]);
                return Ok(LiveExpr::or(vec![both_true, both_false]));
            }
            _ => {}
        }

        // Determine expression level first - use context to resolve operator definitions
        let level = self.get_level_with_ctx(ctx, expr);

        match level {
            ExprLevel::Constant => {
                // Try to evaluate constant expressions
                match eval_entry(ctx, &original) {
                    Ok(Value::Bool(b)) => Ok(LiveExpr::Bool(b)),
                    Ok(_) => Err(ConvertError::NonBooleanConstant(original)),
                    Err(e) if is_binding_error(&e) || is_non_enumerable_error(&e) => {
                        // Unbound variable/operator or non-enumerable domain
                        // (e.g., Seq({1})): level was misclassified as constant
                        // or the expression involves a set too large to enumerate.
                        // Fall back to state predicate. Part of #4067.
                        // Part of #3227: Always use qualify_predicate_expr (see
                        // State handler comment for rationale).
                        let qualified = self.qualify_predicate_expr(ctx, original.as_ref());
                        let wrapped = self.wrap_in_let_defs(qualified);
                        Ok(LiveExpr::state_pred_with_bindings(
                            Arc::new(wrapped),
                            self.alloc_tag(),
                            self.current_quantifier_bindings(),
                        ))
                    }
                    Err(e) => Err(ConvertError::EvalFailed {
                        original,
                        source: e,
                    }),
                }
            }
            ExprLevel::State => {
                // State-level predicate. No speculative eval needed here — binding-aware
                // level analysis in get_level_with_ctx now correctly classifies
                // quantifier-pure expressions (e.g., `oi # oj` where both are bound
                // quantifier variables) as Constant, routing them through the Constant
                // handler above. Mixed expressions like `r \in unsat[c]` (bound `r`,`c`
                // but state var `unsat`) remain State and become StatePred nodes.
                // Part of #3208: the removed speculative eval block was unsound because
                // it could constant-fold state-dependent expressions when quantifier
                // bindings accidentally resolved state variables from the EvalCtx.
                //
                // Part of #3227: Always use qualify_predicate_expr for state predicates.
                // The previous code used reify_current_target_leaf_expr when
                // current_target was Some, which calls resolve_action_expr_node to
                // inline operator bodies and constant-fold. This is correct for
                // action-level predicates (which need full resolution for primed
                // variables) but unnecessary and potentially expensive for state
                // predicates — the evaluator resolves operators at runtime. For
                // EWD998ChanID, this caused a combinatorial explosion: resolving
                // terminationDetected inlined CHOOSE n \in Node : TRUE with
                // Node = {n1,...,n5}, triggering 300K+ eval calls during conversion.
                let qualified = self.qualify_predicate_expr(ctx, original.as_ref());
                let wrapped = self.wrap_in_let_defs(qualified);
                Ok(LiveExpr::state_pred_with_bindings(
                    Arc::new(wrapped),
                    self.alloc_tag(),
                    self.current_quantifier_bindings(),
                ))
            }
            ExprLevel::Action => {
                // Action-level predicate (contains primed variables)
                // Use resolve_action_expr to inline operators and expand LET bindings.
                // This is critical for fixing #233 - LET bindings must be expanded
                // at conversion time because the evaluation context during SCC checking
                // doesn't preserve LET definitions.
                let resolved = self.resolve_action_expr(ctx, original.as_ref());
                let wrapped = self.wrap_in_let_defs(resolved);
                Ok(LiveExpr::action_pred_with_bindings(
                    Arc::new(wrapped),
                    self.alloc_tag(),
                    self.current_quantifier_bindings(),
                ))
            }
            ExprLevel::Temporal => {
                // Contains temporal operators - need to recurse
                self.convert_temporal(ctx, expr, original)
            }
        }
    }

    /// Check if an expression contains ENABLED (at any nesting level).
    /// Delegates to the generic ExprVisitor infrastructure for exhaustive traversal.
    fn contains_enabled(expr: &Expr) -> bool {
        crate::expr_visitor::expr_contains_enabled_v(expr)
    }
}
