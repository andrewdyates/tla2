// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::expr_kind::expr_kind;
use super::scope::{BoundExpr, LoweringScope};
use super::{is_instance_expr, TirLoweringEnv};
use crate::error::TirLowerError;
use crate::nodes::{
    TirArithOp, TirBoolOp, TirCaseArm, TirCmpOp, TirExpr, TirFieldName, TirLetDef, TirNameKind,
    TirNameRef, TirSetOp,
};
use crate::types::TirType;
use std::cell::{Cell, RefCell};
use std::sync::Arc;
use tla_core::ast::{BoundPattern, BoundVar, Expr};
use tla_core::{intern_name, Spanned};
use tla_value::{intern_string, val_false, val_int, val_true, Value};

pub(super) struct Lowerer<'a> {
    pub(super) env: &'a TirLoweringEnv<'a>,
    pub(super) resolution_stack: RefCell<Vec<(String, String)>>,
    pub(super) in_except_value: Cell<bool>,
    /// When true, parameterized builtins (Append, Len, Cardinality, etc.) are
    /// lowered as generic `TirExpr::Apply` instead of being rejected. This is
    /// used by the codegen path which translates these calls directly to Rust
    /// stdlib methods, bypassing the TIR evaluator. Part of #3729.
    pub(super) allow_unsupported_builtins: bool,
}

pub(super) struct ResolutionGuard<'a, 'b> {
    pub(super) lowerer: &'b Lowerer<'a>,
}

impl Drop for ResolutionGuard<'_, '_> {
    fn drop(&mut self) {
        self.lowerer
            .resolution_stack
            .borrow_mut()
            .pop()
            .expect("resolution stack underflow");
    }
}

impl<'a> Lowerer<'a> {
    pub(super) fn new(env: &'a TirLoweringEnv<'a>) -> Self {
        Self {
            env,
            resolution_stack: RefCell::new(Vec::new()),
            in_except_value: Cell::new(false),
            allow_unsupported_builtins: false,
        }
    }

    pub(super) fn new_permissive(env: &'a TirLoweringEnv<'a>) -> Self {
        Self {
            env,
            resolution_stack: RefCell::new(Vec::new()),
            in_except_value: Cell::new(false),
            allow_unsupported_builtins: true,
        }
    }

    pub(super) fn lower_expr(
        &self,
        scope: &LoweringScope<'a>,
        expr: &Spanned<Expr>,
    ) -> Result<Spanned<TirExpr>, TirLowerError> {
        if scope.module().action_subscript_spans.contains(&expr.span)
            && has_action_subscript_shape(&expr.node)
        {
            return self.lower_action_subscript(scope, expr);
        }

        let tir = self.lower_non_action_expr(scope, expr)?;
        Ok(Spanned::new(tir, expr.span))
    }

    fn lower_non_action_expr(
        &self,
        scope: &LoweringScope<'a>,
        expr: &Spanned<Expr>,
    ) -> Result<TirExpr, TirLowerError> {
        if let Some(tir) = lower_literal_expr(&expr.node) {
            return Ok(tir);
        }

        // Recognize @ (EXCEPT-AT) before general name/binding handling.
        if is_except_at_ident(&expr.node) {
            return if self.in_except_value.get() {
                Ok(TirExpr::ExceptAt)
            } else {
                Err(TirLowerError::InvalidExceptAt { span: expr.span })
            };
        }

        if let Some(bound) = bound_name_expr(scope, &expr.node) {
            return self
                .lower_expr(&bound.scope, &bound.expr)
                .map(|expr| expr.node);
        }

        if let Some(tir) = lower_name_expr(&expr.node) {
            return Ok(tir);
        }

        match &expr.node {
            // === Module/Instance resolution ===
            Expr::ModuleRef(target, operator, args) => {
                let resolved_scope = self.resolve_target(scope, target, expr.span)?;
                let resolved =
                    self.resolve_operator_expr(scope, &resolved_scope, operator, args, expr.span)?;
                self.lower_expr(&resolved.scope, &resolved.expr)
                    .map(|expr| expr.node)
            }
            Expr::SubstIn(substitutions, body) => {
                let inner_scope = scope.with_same_module_substitutions(substitutions);
                self.lower_expr(&inner_scope, body).map(|expr| expr.node)
            }

            // === Boolean connectives ===
            Expr::And(left, right) => self.lower_bool_bin(scope, left, TirBoolOp::And, right),
            Expr::Or(left, right) => self.lower_bool_bin(scope, left, TirBoolOp::Or, right),
            Expr::Implies(left, right) => {
                self.lower_bool_bin(scope, left, TirBoolOp::Implies, right)
            }
            Expr::Equiv(left, right) => self.lower_bool_bin(scope, left, TirBoolOp::Equiv, right),
            Expr::Not(inner) => Ok(TirExpr::BoolNot(Box::new(self.lower_expr(scope, inner)?))),

            // === Comparisons ===
            Expr::Eq(left, right) => self.lower_cmp(scope, left, TirCmpOp::Eq, right),
            Expr::Neq(left, right) => self.lower_cmp(scope, left, TirCmpOp::Neq, right),
            Expr::Lt(left, right) => self.lower_cmp(scope, left, TirCmpOp::Lt, right),
            Expr::Leq(left, right) => self.lower_cmp(scope, left, TirCmpOp::Leq, right),
            Expr::Gt(left, right) => self.lower_cmp(scope, left, TirCmpOp::Gt, right),
            Expr::Geq(left, right) => self.lower_cmp(scope, left, TirCmpOp::Geq, right),

            // === Membership ===
            Expr::In(elem, set) => self.lower_in(scope, elem, set),
            Expr::NotIn(elem, set) => Ok(TirExpr::BoolNot(Box::new(Spanned::new(
                self.lower_in(scope, elem, set)?,
                expr.span,
            )))),
            Expr::Subseteq(left, right) => Ok(TirExpr::Subseteq {
                left: Box::new(self.lower_expr(scope, left)?),
                right: Box::new(self.lower_expr(scope, right)?),
            }),

            // === Arithmetic ===
            Expr::Add(left, right) => self.lower_arith_bin(scope, left, TirArithOp::Add, right),
            Expr::Sub(left, right) => self.lower_arith_bin(scope, left, TirArithOp::Sub, right),
            Expr::Mul(left, right) => self.lower_arith_bin(scope, left, TirArithOp::Mul, right),
            Expr::Div(left, right) => self.lower_arith_bin(scope, left, TirArithOp::Div, right),
            Expr::IntDiv(left, right) => {
                self.lower_arith_bin(scope, left, TirArithOp::IntDiv, right)
            }
            Expr::Mod(left, right) => self.lower_arith_bin(scope, left, TirArithOp::Mod, right),
            Expr::Pow(left, right) => self.lower_arith_bin(scope, left, TirArithOp::Pow, right),
            Expr::Neg(inner) => Ok(TirExpr::ArithNeg(Box::new(self.lower_expr(scope, inner)?))),
            Expr::Range(lo, hi) => Ok(TirExpr::Range {
                lo: Box::new(self.lower_expr(scope, lo)?),
                hi: Box::new(self.lower_expr(scope, hi)?),
            }),

            // === Actions ===
            Expr::Unchanged(inner) => {
                Ok(TirExpr::Unchanged(Box::new(self.lower_expr(scope, inner)?)))
            }
            Expr::Prime(inner) => Ok(TirExpr::Prime(Box::new(self.lower_expr(scope, inner)?))),

            // === Temporal ===
            Expr::Always(inner) => Ok(TirExpr::Always(Box::new(self.lower_expr(scope, inner)?))),
            Expr::Eventually(inner) => Ok(TirExpr::Eventually(Box::new(
                self.lower_expr(scope, inner)?,
            ))),
            Expr::LeadsTo(left, right) => Ok(TirExpr::LeadsTo {
                left: Box::new(self.lower_expr(scope, left)?),
                right: Box::new(self.lower_expr(scope, right)?),
            }),
            Expr::WeakFair(vars, action) => Ok(TirExpr::WeakFair {
                vars: Box::new(self.lower_expr(scope, vars)?),
                action: Box::new(self.lower_expr(scope, action)?),
            }),
            Expr::StrongFair(vars, action) => Ok(TirExpr::StrongFair {
                vars: Box::new(self.lower_expr(scope, vars)?),
                action: Box::new(self.lower_expr(scope, action)?),
            }),
            Expr::Enabled(inner) => Ok(TirExpr::Enabled(Box::new(self.lower_expr(scope, inner)?))),

            // === Control ===
            Expr::If(cond, then_, else_) => Ok(TirExpr::If {
                cond: Box::new(self.lower_expr(scope, cond)?),
                then_: Box::new(self.lower_expr(scope, then_)?),
                else_: Box::new(self.lower_expr(scope, else_)?),
            }),
            Expr::Case(arms, other) => {
                let tir_arms = arms
                    .iter()
                    .map(|arm| {
                        Ok(TirCaseArm {
                            guard: self.lower_expr(scope, &arm.guard)?,
                            body: self.lower_expr(scope, &arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let tir_other = other
                    .as_ref()
                    .map(|e| self.lower_expr(scope, e))
                    .transpose()?
                    .map(Box::new);
                Ok(TirExpr::Case {
                    arms: tir_arms,
                    other: tir_other,
                })
            }
            Expr::Let(defs, body) => {
                let let_scope = scope.with_operator_defs(defs);
                let tir_defs = defs
                    .iter()
                    .filter(|def| !is_instance_expr(&def.body))
                    .map(|def| {
                        let lowered_body = self.lower_expr(&let_scope, &def.body)?;
                        let params: Vec<String> =
                            def.params.iter().map(|p| p.name.node.clone()).collect();
                        // Part of #3262: Lower parameterized LET defs to LAMBDA + binding.
                        // `LET Op(x) == body IN expr` becomes `LET Op == LAMBDA x: body IN expr`
                        // so the evaluator eagerly binds Op to a closure value.
                        if params.is_empty() {
                            Ok(TirLetDef {
                                name: def.name.node.clone(),
                                name_id: intern_name(&def.name.node),
                                params: vec![],
                                body: lowered_body,
                            })
                        } else {
                            use crate::nodes::PreservedAstBody;
                            let lambda_body = Spanned {
                                node: TirExpr::Lambda {
                                    params,
                                    body: Box::new(lowered_body),
                                    ast_body: PreservedAstBody(Arc::new(def.body.clone())),
                                },
                                span: def.body.span,
                            };
                            Ok(TirLetDef {
                                name: def.name.node.clone(),
                                name_id: intern_name(&def.name.node),
                                params: vec![],
                                body: lambda_body,
                            })
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(TirExpr::Let {
                    defs: tir_defs,
                    body: Box::new(self.lower_expr(&let_scope, body)?),
                })
            }

            // === Quantifiers ===
            Expr::Forall(vars, body) => self.lower_nested_forall(scope, vars, body),
            Expr::Exists(vars, body) => self.lower_nested_exists(scope, vars, body),
            Expr::Choose(var, body) => Ok(TirExpr::Choose {
                var: self.lower_bound_var(scope, var)?,
                body: Box::new(self.lower_expr(scope, body)?),
            }),

            // === Sets ===
            Expr::SetEnum(elems) => {
                let tir_elems = elems
                    .iter()
                    .map(|e| self.lower_expr(scope, e))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(TirExpr::SetEnum(tir_elems))
            }
            Expr::SetFilter(var, body) => {
                // K-subset optimization: detect {x \in SUBSET(S) : Cardinality(x) = k}
                // and lower to TirExpr::KSubset instead. This avoids the Cardinality
                // unsupported-builtin rejection and enables direct C(n,k) generation.
                // Part of #3907.
                if let Some(ksubset) = self.try_lower_ksubset_pattern(scope, var, body) {
                    return ksubset;
                }
                Ok(TirExpr::SetFilter {
                    var: self.lower_bound_var(scope, var)?,
                    body: Box::new(self.lower_expr(scope, body)?),
                })
            }
            Expr::SetBuilder(body, vars) => Ok(TirExpr::SetBuilder {
                body: Box::new(self.lower_expr(scope, body)?),
                vars: self.lower_bound_vars(scope, vars)?,
            }),
            Expr::Union(left, right) => self.lower_set_bin(scope, left, TirSetOp::Union, right),
            Expr::Intersect(left, right) => {
                self.lower_set_bin(scope, left, TirSetOp::Intersect, right)
            }
            Expr::SetMinus(left, right) => self.lower_set_bin(scope, left, TirSetOp::Minus, right),
            Expr::Powerset(inner) => {
                Ok(TirExpr::Powerset(Box::new(self.lower_expr(scope, inner)?)))
            }
            Expr::BigUnion(inner) => {
                Ok(TirExpr::BigUnion(Box::new(self.lower_expr(scope, inner)?)))
            }

            // === Functions ===
            Expr::FuncDef(vars, body) => Ok(TirExpr::FuncDef {
                vars: self.lower_bound_vars(scope, vars)?,
                body: Box::new(self.lower_expr(scope, body)?),
            }),
            Expr::FuncApply(func, arg) => Ok(TirExpr::FuncApply {
                func: Box::new(self.lower_expr(scope, func)?),
                arg: Box::new(self.lower_expr(scope, arg)?),
            }),
            Expr::FuncSet(domain, range) => Ok(TirExpr::FuncSet {
                domain: Box::new(self.lower_expr(scope, domain)?),
                range: Box::new(self.lower_expr(scope, range)?),
            }),
            Expr::Domain(inner) => Ok(TirExpr::Domain(Box::new(self.lower_expr(scope, inner)?))),

            // === Records/Tuples ===
            Expr::Record(fields) => {
                let tir_fields = fields
                    .iter()
                    .map(|(name, val)| {
                        Ok((
                            TirFieldName {
                                name: name.node.clone(),
                                field_id: intern_name(&name.node),
                            },
                            self.lower_expr(scope, val)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(TirExpr::Record(tir_fields))
            }
            Expr::RecordSet(fields) => {
                let tir_fields = fields
                    .iter()
                    .map(|(name, val)| {
                        Ok((
                            TirFieldName {
                                name: name.node.clone(),
                                field_id: intern_name(&name.node),
                            },
                            self.lower_expr(scope, val)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(TirExpr::RecordSet(tir_fields))
            }
            Expr::RecordAccess(base, field) => self.lower_record_access(scope, base, field),
            Expr::Tuple(elems) => {
                let tir_elems = elems
                    .iter()
                    .map(|e| self.lower_expr(scope, e))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(TirExpr::Tuple(tir_elems))
            }
            Expr::Times(factors) => {
                let tir_factors = factors
                    .iter()
                    .map(|e| self.lower_expr(scope, e))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(TirExpr::Times(tir_factors))
            }

            // === EXCEPT ===
            Expr::Except(base, specs) => self.lower_except(scope, base, specs),

            // === Generic operator application ===
            Expr::Apply(op, args) => {
                // Reject unresolved parameterized builtin calls that the TIR
                // evaluator cannot execute. These must fall back to AST until
                // real TIR builtin dispatch exists.
                //
                // Keep same-name user/local/imported operators on the TIR path:
                // `Cardinality(x) == ...` in the spec should still lower as a
                // normal user operator application even though the builtin
                // `Cardinality(...)` must fall back.
                if self.is_unsupported_parameterized_builtin(scope, op) {
                    return Err(TirLowerError::UnsupportedExpr {
                        kind: expr_kind(&expr.node),
                        span: expr.span,
                    });
                }
                let tir_op = self.lower_expr(scope, op)?;
                let tir_args = args
                    .iter()
                    .map(|a| self.lower_expr(scope, a))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(TirExpr::Apply {
                    op: Box::new(tir_op),
                    args: tir_args,
                })
            }

            // === Lambda / higher-order ===
            Expr::Lambda(params, body) => {
                use crate::nodes::PreservedAstBody;
                Ok(TirExpr::Lambda {
                    params: params.iter().map(|p| p.node.clone()).collect(),
                    body: Box::new(self.lower_expr(scope, body)?),
                    ast_body: PreservedAstBody(Arc::new((**body).clone())),
                })
            }
            Expr::OpRef(name) => Ok(TirExpr::OpRef(name.clone())),
            Expr::Label(label) => Ok(TirExpr::Label {
                name: label.name.node.clone(),
                body: Box::new(self.lower_expr(scope, &label.body)?),
            }),

            _ => Err(TirLowerError::UnsupportedExpr {
                kind: expr_kind(&expr.node),
                span: expr.span,
            }),
        }
    }

    fn is_unsupported_parameterized_builtin(
        &self,
        scope: &LoweringScope<'a>,
        op: &Spanned<Expr>,
    ) -> bool {
        // In permissive mode (codegen), allow all builtins through as generic
        // Apply nodes. The codegen backend translates them to Rust stdlib calls.
        if self.allow_unsupported_builtins {
            return false;
        }

        let Expr::Ident(name, _) = &op.node else {
            return false;
        };

        // Part of #3460: use has_local_operator_definition instead of
        // has_operator_definition. The latter includes imported modules
        // (EXTENDS/INSTANCE), which means `Append` from `EXTENDS Sequences`
        // is treated as a "known operator" and bypasses the builtin gate.
        // Only skip the gate for operators defined in the spec itself.
        !self.has_local_operator_definition(scope, name)
            && is_unsupported_parameterized_builtin_name(name)
    }

    fn lower_nested_forall(
        &self,
        scope: &LoweringScope<'a>,
        vars: &[BoundVar],
        body: &Spanned<Expr>,
    ) -> Result<TirExpr, TirLowerError> {
        let Some((first, rest)) = vars.split_first() else {
            return self.lower_expr(scope, body).map(|expr| expr.node);
        };

        let tir_var = self.lower_bound_var(scope, first)?;
        let shadow_scope = scope.with_shadowed_bindings(bound_var_shadow_names(first));
        let tir_body = if rest.is_empty() {
            self.lower_expr(&shadow_scope, body)?
        } else {
            Spanned::new(
                self.lower_nested_forall(&shadow_scope, rest, body)?,
                body.span,
            )
        };

        Ok(TirExpr::Forall {
            vars: vec![tir_var],
            body: Box::new(tir_body),
        })
    }

    fn lower_nested_exists(
        &self,
        scope: &LoweringScope<'a>,
        vars: &[BoundVar],
        body: &Spanned<Expr>,
    ) -> Result<TirExpr, TirLowerError> {
        let Some((first, rest)) = vars.split_first() else {
            return self.lower_expr(scope, body).map(|expr| expr.node);
        };

        let tir_var = self.lower_bound_var(scope, first)?;
        let shadow_scope = scope.with_shadowed_bindings(bound_var_shadow_names(first));
        let tir_body = if rest.is_empty() {
            self.lower_expr(&shadow_scope, body)?
        } else {
            Spanned::new(
                self.lower_nested_exists(&shadow_scope, rest, body)?,
                body.span,
            )
        };

        Ok(TirExpr::Exists {
            vars: vec![tir_var],
            body: Box::new(tir_body),
        })
    }

    /// Detect `{x \in SUBSET(S) : Cardinality(x) = k}` and lower to
    /// `TirExpr::KSubset { base, k }` directly.
    ///
    /// This bypasses the `Cardinality` unsupported-builtin rejection and
    /// replaces 2^n powerset+filter with direct C(n,k) k-subset generation.
    /// Part of #3907.
    fn try_lower_ksubset_pattern(
        &self,
        scope: &LoweringScope<'a>,
        var: &BoundVar,
        body: &Spanned<Expr>,
    ) -> Option<Result<TirExpr, TirLowerError>> {
        // Domain must be SUBSET(S).
        let domain = var.domain.as_ref()?;
        let Expr::Powerset(base_expr) = &domain.node else {
            return None;
        };

        // Body must be Eq(lhs, rhs).
        let Expr::Eq(lhs, rhs) = &body.node else {
            return None;
        };

        let bound_name = &var.name.node;

        // Try both orientations: Cardinality(x) = k  and  k = Cardinality(x)
        let k_expr = try_match_ast_cardinality_eq(bound_name, lhs, rhs)
            .or_else(|| try_match_ast_cardinality_eq(bound_name, rhs, lhs))?;

        // Verify k_expr does not reference the bound variable.
        if ast_expr_references_name(&k_expr.node, bound_name) {
            return None;
        }

        // Lower base and k expressions.
        let tir_base = match self.lower_expr(scope, base_expr) {
            Ok(b) => b,
            Err(e) => return Some(Err(e)),
        };
        let tir_k = match self.lower_expr(scope, k_expr) {
            Ok(k) => k,
            Err(e) => return Some(Err(e)),
        };

        Some(Ok(TirExpr::KSubset {
            base: Box::new(tir_base),
            k: Box::new(tir_k),
        }))
    }
}

fn bound_var_shadow_names(var: &BoundVar) -> Vec<String> {
    let mut names = vec![var.name.node.clone()];
    if let Some(BoundPattern::Tuple(pattern_vars)) = &var.pattern {
        names.extend(pattern_vars.iter().map(|name| name.node.clone()));
    }
    names
}

fn lower_literal_expr(expr: &Expr) -> Option<TirExpr> {
    match expr {
        Expr::Bool(value) => Some(TirExpr::Const {
            value: if *value { val_true() } else { val_false() },
            ty: TirType::Bool,
        }),
        Expr::Int(value) => Some(TirExpr::Const {
            value: val_int(value),
            ty: TirType::Int,
        }),
        Expr::String(value) => Some(TirExpr::Const {
            value: Value::String(intern_string(value)),
            ty: TirType::Str,
        }),
        _ => None,
    }
}

/// Returns true for bare identifier operator names whose builtin meaning is not
/// yet supported by the TIR evaluator's generic `Apply` path.
///
/// The sequence family (`Append`, `Head`, `Tail`, `SubSeq`, `SelectSeq`, `Len`,
/// `Seq`) and `FiniteSets!Cardinality` have no TIR evaluator dispatch. If
/// lowered as generic `TirExpr::Apply`, evaluation treats them as user-defined
/// operators and fails with `UndefinedVar`.
///
/// **Note (#3967):** In permissive mode (used by bytecode compilation Phase 2
/// and Phase 1.75), this blocklist is bypassed entirely. The bytecode compiler
/// maps `Append`, `Head`, `Tail`, `SubSeq`, `Len`, `Seq`, and `Cardinality` to
/// `CallBuiltin` opcodes with VM-native execution. `SelectSeq` falls through
/// to `CallExternal` (requires higher-order function dispatch).
///
/// This blocklist is still needed for non-permissive mode (Phase 1 zero-arg
/// pre-compilation, Phase 1.5 callee collection) to prevent proof module
/// compilation explosion (MCQuicksort hang from TLAPS/SequenceTheorems).
fn is_unsupported_parameterized_builtin_name(name: &str) -> bool {
    matches!(
        name,
        "Append" | "Head" | "Tail" | "SubSeq" | "SelectSeq" | "Len" | "Seq" | "Cardinality"
    )
}

/// Check if `card_side` is `Apply(Ident("Cardinality"), [Ident(bound_name)])` and return
/// the other side (`k_side`). Used for k-subset pattern detection. Part of #3907.
fn try_match_ast_cardinality_eq<'e>(
    bound_name: &str,
    card_side: &'e Spanned<Expr>,
    k_side: &'e Spanned<Expr>,
) -> Option<&'e Spanned<Expr>> {
    let Expr::Apply(func, args) = &card_side.node else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    let Expr::Ident(func_name, _) = &func.node else {
        return None;
    };
    if func_name != "Cardinality" {
        return None;
    }
    let Expr::Ident(arg_name, _) = &args[0].node else {
        return None;
    };
    if arg_name != bound_name {
        return None;
    }
    Some(k_side)
}

/// Check if an AST expression references a given variable name.
/// Conservative: returns true if the name appears anywhere in the expression tree.
/// Part of #3907.
fn ast_expr_references_name(expr: &Expr, name: &str) -> bool {
    match expr {
        Expr::Ident(n, _) | Expr::StateVar(n, _, _) => n == name,
        Expr::Int(_) | Expr::Bool(_) | Expr::String(_) | Expr::OpRef(_) => false,
        Expr::Apply(f, args) => {
            ast_expr_references_name(&f.node, name)
                || args.iter().any(|a| ast_expr_references_name(&a.node, name))
        }
        Expr::FuncApply(f, a) => {
            ast_expr_references_name(&f.node, name)
                || ast_expr_references_name(&a.node, name)
        }
        Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::Lt(a, b)
        | Expr::Leq(a, b)
        | Expr::Gt(a, b)
        | Expr::Geq(a, b)
        | Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::IntDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Subseteq(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::Pow(a, b)
        | Expr::Range(a, b) => {
            ast_expr_references_name(&a.node, name)
                || ast_expr_references_name(&b.node, name)
        }
        Expr::Not(a)
        | Expr::Neg(a)
        | Expr::Domain(a)
        | Expr::Powerset(a)
        | Expr::BigUnion(a)
        | Expr::Prime(a)
        | Expr::Always(a)
        | Expr::Eventually(a)
        | Expr::Enabled(a)
        | Expr::Unchanged(a) => ast_expr_references_name(&a.node, name),
        Expr::If(c, t, e) => {
            ast_expr_references_name(&c.node, name)
                || ast_expr_references_name(&t.node, name)
                || ast_expr_references_name(&e.node, name)
        }
        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
            elems.iter().any(|e| ast_expr_references_name(&e.node, name))
        }
        // For complex expressions (Let, Case, Record, etc.), conservatively say yes
        _ => true,
    }
}

fn is_except_at_ident(expr: &Expr) -> bool {
    matches!(expr, Expr::Ident(name, _) if name == "@")
}

fn bound_name_expr<'a>(scope: &LoweringScope<'a>, expr: &Expr) -> Option<BoundExpr<'a>> {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => scope.lookup_binding(name),
        _ => None,
    }
}

/// Check if an expression has the canonical shape of a lowered action subscript:
/// `Or(action, Unchanged(subscript))` for `[A]_v`, or
/// `And(action, Not(Unchanged(subscript)))` for `<<A>>_v`.
///
/// This prevents false matches when sub-expressions (e.g., the synthesized
/// `Unchanged` wrapper) share the same span as the registered action-subscript
/// span due to span assignment in `lower_subscript_expr`.
fn has_action_subscript_shape(expr: &Expr) -> bool {
    match expr {
        Expr::Or(_, rhs) => matches!(rhs.node, Expr::Unchanged(_)),
        Expr::And(_, rhs) => {
            matches!(&rhs.node, Expr::Not(inner) if matches!(inner.node, Expr::Unchanged(_)))
        }
        _ => false,
    }
}

fn lower_name_expr(expr: &Expr) -> Option<TirExpr> {
    match expr {
        Expr::Ident(name, name_id) => Some(TirExpr::Name(TirNameRef {
            name: name.clone(),
            name_id: *name_id,
            kind: TirNameKind::Ident,
            ty: TirType::Dyn,
        })),
        Expr::StateVar(name, index, name_id) => Some(TirExpr::Name(TirNameRef {
            name: name.clone(),
            name_id: *name_id,
            kind: TirNameKind::StateVar { index: *index },
            ty: TirType::Dyn,
        })),
        _ => None,
    }
}
