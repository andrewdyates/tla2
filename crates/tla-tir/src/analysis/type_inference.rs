// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared TIR-level type analysis for JIT and codegen consumers.
//!
//! Walks the TIR expression tree once and produces:
//! - Per-variable type classification (always Int, always Bool, compound, or dynamic)
//! - Per-expression type classification
//! - Expression-level classification (pure-integer invariant, pure-boolean, mixed)
//!
//! Both the JIT compiler and code generator can consume [`TirTypeInfo`] instead
//! of independently re-deriving type information from the expression tree.
//!
//! Part of #3930.

use crate::nodes::{
    TirBoundVar, TirCaseArm, TirExceptPathElement, TirExceptSpec, TirExpr, TirLetDef,
};
use crate::types::TirType;
use rustc_hash::FxHashMap;
use tla_core::{NameId, Spanned};

/// Classification of an expression tree for downstream optimization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExprClass {
    /// All operations are integer arithmetic and integer comparisons.
    /// The final result may be Int or Bool (for comparison-only invariants).
    PureInteger,
    /// All operations are boolean connectives and comparisons.
    PureBool,
    /// Expression involves compound types (sets, records, sequences, functions).
    Compound,
    /// Mixed or unknown — cannot be classified into a simpler category.
    Mixed,
}

/// Collected type information for a TIR expression tree.
///
/// Produced by [`analyze_expr`]. Consumers can query variable types,
/// expression classification, and whether the entire expression is
/// JIT-friendly (pure scalar).
#[derive(Debug, Clone)]
pub struct TirTypeInfo {
    /// Inferred type for each named variable encountered during the walk.
    /// Maps `NameId` -> joined `TirType` across all uses.
    var_types: FxHashMap<NameId, TirType>,
    /// Overall classification of the analyzed expression.
    expr_class: ExprClass,
    /// The inferred result type of the root expression.
    result_type: TirType,
}

impl TirTypeInfo {
    /// The inferred type for a variable, or `None` if the variable was
    /// not encountered during analysis.
    #[must_use]
    pub fn var_type(&self, name_id: NameId) -> Option<&TirType> {
        self.var_types.get(&name_id)
    }

    /// Whether a variable is known to always hold an integer.
    #[must_use]
    pub fn var_is_int(&self, name_id: NameId) -> bool {
        matches!(self.var_types.get(&name_id), Some(TirType::Int))
    }

    /// Whether a variable is known to always hold a boolean.
    #[must_use]
    pub fn var_is_bool(&self, name_id: NameId) -> bool {
        matches!(self.var_types.get(&name_id), Some(TirType::Bool))
    }

    /// Whether a variable holds a compound type (set, record, tuple, func, seq).
    #[must_use]
    pub fn var_is_compound(&self, name_id: NameId) -> bool {
        matches!(
            self.var_types.get(&name_id),
            Some(
                TirType::Set(_)
                    | TirType::Seq(_)
                    | TirType::Func(_, _)
                    | TirType::Tuple(_)
                    | TirType::Record(_)
                    | TirType::OpenRecord(_, _)
            )
        )
    }

    /// The overall classification of the expression tree.
    #[must_use]
    pub fn expr_class(&self) -> ExprClass {
        self.expr_class
    }

    /// Whether the expression is a pure-integer invariant (all operations
    /// are integer arithmetic + integer comparisons, result is Int or Bool).
    #[must_use]
    pub fn is_pure_integer(&self) -> bool {
        self.expr_class == ExprClass::PureInteger
    }

    /// Whether the expression is pure-boolean (all operations are boolean
    /// connectives, result is Bool).
    #[must_use]
    pub fn is_pure_bool(&self) -> bool {
        self.expr_class == ExprClass::PureBool
    }

    /// Whether every variable in the expression is a scalar (Int or Bool).
    /// This is a necessary condition for full JIT compilation without fallback.
    #[must_use]
    pub fn all_vars_scalar(&self) -> bool {
        self.var_types.values().all(|ty| matches!(ty, TirType::Int | TirType::Bool))
    }

    /// The inferred result type of the root expression.
    #[must_use]
    pub fn result_type(&self) -> &TirType {
        &self.result_type
    }

    /// All variable types as a map. Useful for bulk inspection.
    #[must_use]
    pub fn var_types(&self) -> &FxHashMap<NameId, TirType> {
        &self.var_types
    }
}

/// Analyze a TIR expression tree and produce shared type information.
///
/// This walks the tree once in O(n) time. The resulting [`TirTypeInfo`]
/// can be consumed by both the JIT compiler and the code generator.
#[must_use]
pub fn analyze_expr(expr: &Spanned<TirExpr>) -> TirTypeInfo {
    let mut ctx = AnalysisCtx {
        var_types: FxHashMap::default(),
    };
    let (result_type, class) = ctx.walk(expr);
    TirTypeInfo {
        var_types: ctx.var_types,
        expr_class: class,
        result_type,
    }
}

/// Internal analysis context accumulating variable type information.
struct AnalysisCtx {
    var_types: FxHashMap<NameId, TirType>,
}

impl AnalysisCtx {
    /// Record a variable reference with its type. Joins with any previously
    /// seen type for the same `NameId`.
    fn record_var(&mut self, name_id: NameId, ty: &TirType) {
        self.var_types
            .entry(name_id)
            .and_modify(|existing| *existing = existing.join(ty))
            .or_insert_with(|| ty.clone());
    }

    /// Walk a TIR expression, returning (inferred type, expression class).
    fn walk(&mut self, expr: &Spanned<TirExpr>) -> (TirType, ExprClass) {
        match &expr.node {
            TirExpr::Const { ty, .. } => {
                let class = type_to_class(ty);
                (ty.clone(), class)
            }

            TirExpr::Name(name_ref) => {
                self.record_var(name_ref.name_id, &name_ref.ty);
                let class = type_to_class(&name_ref.ty);
                (name_ref.ty.clone(), class)
            }

            // --- Arithmetic: operands and result are Int ---
            TirExpr::ArithBinOp { left, op: _, right } => {
                let (_, lc) = self.walk(left);
                let (_, rc) = self.walk(right);
                let class = merge_int_classes(lc, rc);
                (TirType::Int, class)
            }
            TirExpr::ArithNeg(inner) => {
                let (_, ic) = self.walk(inner);
                let class = if is_int_compatible(ic) {
                    ExprClass::PureInteger
                } else {
                    ExprClass::Mixed
                };
                (TirType::Int, class)
            }

            // --- Boolean connectives: operands and result are Bool ---
            TirExpr::BoolBinOp { left, op: _, right } => {
                let (_, lc) = self.walk(left);
                let (_, rc) = self.walk(right);
                let class = merge_bool_classes(lc, rc);
                (TirType::Bool, class)
            }
            TirExpr::BoolNot(inner) => {
                let (_, ic) = self.walk(inner);
                let class = if is_int_compatible(ic) {
                    // Negation of comparison result: still pure-integer
                    ExprClass::PureInteger
                } else if is_bool_compatible(ic) {
                    ExprClass::PureBool
                } else {
                    ExprClass::Mixed
                };
                (TirType::Bool, class)
            }

            // --- Comparisons: operands may be Int, result is Bool ---
            TirExpr::Cmp { left, op: _, right } => {
                let (_, lc) = self.walk(left);
                let (_, rc) = self.walk(right);
                // If both operands are pure-integer, the comparison is
                // part of a pure-integer invariant (result is Bool but
                // the entire expression is integer arithmetic + comparison).
                let class = if is_int_compatible(lc) && is_int_compatible(rc) {
                    ExprClass::PureInteger
                } else {
                    ExprClass::Mixed
                };
                (TirType::Bool, class)
            }

            // --- Set membership and subset: result is Bool, operands are compound ---
            TirExpr::In { elem, set } => {
                self.walk(elem);
                self.walk(set);
                (TirType::Bool, ExprClass::Compound)
            }
            TirExpr::Subseteq { left, right } => {
                self.walk(left);
                self.walk(right);
                (TirType::Bool, ExprClass::Compound)
            }

            // --- Control flow ---
            TirExpr::If { cond, then_, else_ } => {
                let (_, cc) = self.walk(cond);
                let (tt, tc) = self.walk(then_);
                let (et, ec) = self.walk(else_);
                let result_ty = tt.join(&et);
                let class = merge_if_classes(cc, tc, ec);
                (result_ty, class)
            }

            TirExpr::Let { defs, body } => {
                for def in defs {
                    self.walk_let_def(def);
                }
                self.walk(body)
            }

            TirExpr::Case { arms, other } => {
                let mut result_ty = TirType::Dyn;
                let mut result_class = ExprClass::PureBool; // start optimistic
                for arm in arms {
                    let (ac, bc) = self.walk_case_arm(arm);
                    result_ty = result_ty.join(&bc);
                    result_class = merge_general(result_class, ac);
                }
                if let Some(o) = other {
                    let (ot, oc) = self.walk(o);
                    result_ty = result_ty.join(&ot);
                    result_class = merge_general(result_class, oc);
                }
                (result_ty, result_class)
            }

            // --- Quantifiers: result is Bool ---
            TirExpr::Forall { vars, body } | TirExpr::Exists { vars, body } => {
                for var in vars {
                    self.walk_bound_var(var);
                }
                let (_, bc) = self.walk(body);
                // Quantifiers iterate over domains (compound), so even if the
                // body is pure-bool, the overall expression is compound.
                let class = if has_compound_domain(vars) {
                    ExprClass::Compound
                } else {
                    bc
                };
                (TirType::Bool, class)
            }
            TirExpr::Choose { var, body } => {
                self.walk_bound_var(var);
                self.walk(body);
                let result_ty = var
                    .domain
                    .as_ref()
                    .map(|d| {
                        let dt = d.node.ty();
                        match dt {
                            TirType::Set(inner) => *inner,
                            _ => TirType::Dyn,
                        }
                    })
                    .unwrap_or(TirType::Dyn);
                (result_ty, ExprClass::Compound)
            }

            // --- Set expressions: always compound ---
            TirExpr::SetEnum(elems) => {
                for e in elems {
                    self.walk(e);
                }
                (expr.node.ty(), ExprClass::Compound)
            }
            TirExpr::SetFilter { var, body } => {
                self.walk_bound_var(var);
                self.walk(body);
                (expr.node.ty(), ExprClass::Compound)
            }
            TirExpr::SetBuilder { body, vars } => {
                for var in vars {
                    self.walk_bound_var(var);
                }
                self.walk(body);
                (expr.node.ty(), ExprClass::Compound)
            }
            TirExpr::SetBinOp { left, op: _, right } => {
                self.walk(left);
                self.walk(right);
                (expr.node.ty(), ExprClass::Compound)
            }
            TirExpr::Powerset(inner)
            | TirExpr::BigUnion(inner) => {
                self.walk(inner);
                (expr.node.ty(), ExprClass::Compound)
            }
            TirExpr::KSubset { base, k } => {
                self.walk(base);
                self.walk(k);
                (expr.node.ty(), ExprClass::Compound)
            }
            TirExpr::Range { lo, hi } => {
                self.walk(lo);
                self.walk(hi);
                (TirType::Set(Box::new(TirType::Int)), ExprClass::Compound)
            }

            // --- Records, tuples, functions: compound ---
            TirExpr::Record(fields) => {
                for (_, e) in fields {
                    self.walk(e);
                }
                (expr.node.ty(), ExprClass::Compound)
            }
            TirExpr::RecordSet(fields) => {
                for (_, e) in fields {
                    self.walk(e);
                }
                (expr.node.ty(), ExprClass::Compound)
            }
            TirExpr::Tuple(elems) | TirExpr::Times(elems) => {
                for e in elems {
                    self.walk(e);
                }
                (expr.node.ty(), ExprClass::Compound)
            }
            TirExpr::RecordAccess { record, .. } => {
                self.walk(record);
                (expr.node.ty(), ExprClass::Compound)
            }
            TirExpr::Except { base, specs } => {
                self.walk(base);
                for spec in specs {
                    self.walk_except_spec(spec);
                }
                (expr.node.ty(), ExprClass::Compound)
            }
            TirExpr::ExceptAt => (TirType::Dyn, ExprClass::Compound),

            TirExpr::FuncDef { vars, body } => {
                for var in vars {
                    self.walk_bound_var(var);
                }
                self.walk(body);
                (expr.node.ty(), ExprClass::Compound)
            }
            TirExpr::FuncApply { func, arg } => {
                self.walk(func);
                self.walk(arg);
                (expr.node.ty(), ExprClass::Compound)
            }
            TirExpr::FuncSet { domain, range } => {
                self.walk(domain);
                self.walk(range);
                (expr.node.ty(), ExprClass::Compound)
            }
            TirExpr::Domain(inner) => {
                self.walk(inner);
                (expr.node.ty(), ExprClass::Compound)
            }

            // --- Primed variables, actions, temporal: propagate type ---
            TirExpr::Prime(inner) => {
                let (ty, _class) = self.walk(inner);
                (ty, ExprClass::Mixed)
            }
            TirExpr::Unchanged(inner) => {
                self.walk(inner);
                (TirType::Bool, ExprClass::Mixed)
            }
            TirExpr::ActionSubscript { action, subscript, .. } => {
                self.walk(action);
                self.walk(subscript);
                (TirType::Bool, ExprClass::Mixed)
            }

            // --- Temporal operators ---
            TirExpr::Always(inner) | TirExpr::Eventually(inner) | TirExpr::Enabled(inner) => {
                self.walk(inner);
                (TirType::Bool, ExprClass::Mixed)
            }
            TirExpr::LeadsTo { left, right }
            | TirExpr::WeakFair { vars: left, action: right }
            | TirExpr::StrongFair { vars: left, action: right } => {
                self.walk(left);
                self.walk(right);
                (TirType::Bool, ExprClass::Mixed)
            }

            // --- Higher-order and generic: mixed ---
            TirExpr::Apply { op, args } => {
                self.walk(op);
                for a in args {
                    self.walk(a);
                }
                (TirType::Dyn, ExprClass::Mixed)
            }
            TirExpr::Lambda { body, .. } => {
                self.walk(body);
                (TirType::Dyn, ExprClass::Mixed)
            }
            TirExpr::OpRef(_) => (TirType::Dyn, ExprClass::Mixed),

            // --- Labels: transparent ---
            TirExpr::Label { body, .. } => self.walk(body),

            // --- Operator refs: walk argument subexpressions ---
            TirExpr::OperatorRef(op_ref) => {
                for seg in &op_ref.path {
                    for a in &seg.args {
                        self.walk(a);
                    }
                }
                for a in &op_ref.args {
                    self.walk(a);
                }
                (TirType::Dyn, ExprClass::Mixed)
            }
        }
    }

    fn walk_bound_var(&mut self, var: &TirBoundVar) {
        if let Some(domain) = &var.domain {
            self.walk(domain);
        }
    }

    fn walk_let_def(&mut self, def: &TirLetDef) {
        self.walk(&def.body);
    }

    fn walk_case_arm(&mut self, arm: &TirCaseArm) -> (ExprClass, TirType) {
        let (_, gc) = self.walk(&arm.guard);
        let (bt, bc) = self.walk(&arm.body);
        (merge_general(gc, bc), bt)
    }

    fn walk_except_spec(&mut self, spec: &TirExceptSpec) {
        for element in &spec.path {
            if let TirExceptPathElement::Index(idx) = element {
                self.walk(idx);
            }
        }
        self.walk(&spec.value);
    }
}

// ---- Classification helpers ----

/// Map a `TirType` to its natural `ExprClass`.
fn type_to_class(ty: &TirType) -> ExprClass {
    match ty {
        TirType::Int => ExprClass::PureInteger,
        TirType::Bool => ExprClass::PureBool,
        TirType::Set(_)
        | TirType::Seq(_)
        | TirType::Func(_, _)
        | TirType::Tuple(_)
        | TirType::Record(_)
        | TirType::OpenRecord(_, _)
        | TirType::Variant(_) => ExprClass::Compound,
        TirType::Str | TirType::Dyn | TirType::Var(_) => ExprClass::Mixed,
    }
}

/// Whether a class is compatible with pure-integer expressions.
fn is_int_compatible(class: ExprClass) -> bool {
    matches!(class, ExprClass::PureInteger)
}

/// Whether a class is compatible with pure-boolean expressions.
fn is_bool_compatible(class: ExprClass) -> bool {
    matches!(class, ExprClass::PureBool | ExprClass::PureInteger)
}

/// Merge two classes under integer arithmetic.
fn merge_int_classes(a: ExprClass, b: ExprClass) -> ExprClass {
    if is_int_compatible(a) && is_int_compatible(b) {
        ExprClass::PureInteger
    } else {
        ExprClass::Mixed
    }
}

/// Merge two classes under boolean connectives.
fn merge_bool_classes(a: ExprClass, b: ExprClass) -> ExprClass {
    if is_bool_compatible(a) && is_bool_compatible(b) {
        // If both children are pure-integer (comparison results), the
        // conjunction is still part of a pure-integer invariant.
        if a == ExprClass::PureInteger && b == ExprClass::PureInteger {
            ExprClass::PureInteger
        } else {
            ExprClass::PureBool
        }
    } else {
        ExprClass::Mixed
    }
}

/// Merge classes for IF-THEN-ELSE.
fn merge_if_classes(cond: ExprClass, then_: ExprClass, else_: ExprClass) -> ExprClass {
    if is_int_compatible(then_) && is_int_compatible(else_) && is_bool_compatible(cond) {
        ExprClass::PureInteger
    } else if is_bool_compatible(then_) && is_bool_compatible(else_) && is_bool_compatible(cond) {
        ExprClass::PureBool
    } else {
        merge_general(merge_general(cond, then_), else_)
    }
}

/// General class merge: the "weakest" of the two wins.
fn merge_general(a: ExprClass, b: ExprClass) -> ExprClass {
    if a == b {
        return a;
    }
    // PureInteger and PureBool can coexist as Mixed
    match (a, b) {
        (ExprClass::PureInteger, ExprClass::PureBool)
        | (ExprClass::PureBool, ExprClass::PureInteger) => ExprClass::PureBool,
        (ExprClass::Compound, _) | (_, ExprClass::Compound) => ExprClass::Compound,
        _ => ExprClass::Mixed,
    }
}

/// Check whether any bound variable in a quantifier has a compound domain.
fn has_compound_domain(vars: &[TirBoundVar]) -> bool {
    vars.iter().any(|v| {
        v.domain
            .as_ref()
            .is_some_and(|d| matches!(d.node.ty(), TirType::Set(_)))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nodes::*;
    use tla_core::intern_name;
    use tla_core::span::{FileId, Span};
    use tla_value::Value;

    fn span() -> Span {
        Span::new(FileId(0), 0, 0)
    }

    fn spanned(expr: TirExpr) -> Spanned<TirExpr> {
        Spanned::new(expr, span())
    }

    fn int_const(n: i64) -> Spanned<TirExpr> {
        spanned(TirExpr::Const {
            value: Value::int(n),
            ty: TirType::Int,
        })
    }

    fn bool_const(b: bool) -> Spanned<TirExpr> {
        spanned(TirExpr::Const {
            value: Value::bool(b),
            ty: TirType::Bool,
        })
    }

    fn int_var(name: &str) -> Spanned<TirExpr> {
        spanned(TirExpr::Name(TirNameRef {
            name: name.to_string(),
            name_id: intern_name(name),
            kind: TirNameKind::StateVar { index: 0 },
            ty: TirType::Int,
        }))
    }

    fn bool_var(name: &str) -> Spanned<TirExpr> {
        spanned(TirExpr::Name(TirNameRef {
            name: name.to_string(),
            name_id: intern_name(name),
            kind: TirNameKind::StateVar { index: 1 },
            ty: TirType::Bool,
        }))
    }

    fn dyn_var(name: &str) -> Spanned<TirExpr> {
        spanned(TirExpr::Name(TirNameRef {
            name: name.to_string(),
            name_id: intern_name(name),
            kind: TirNameKind::Ident,
            ty: TirType::Dyn,
        }))
    }

    // --- Pure integer expression: x + y > 0 ---
    #[test]
    fn test_pure_integer_arithmetic_comparison() {
        let expr = spanned(TirExpr::Cmp {
            left: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(int_var("x")),
                op: TirArithOp::Add,
                right: Box::new(int_var("y")),
            })),
            op: TirCmpOp::Gt,
            right: Box::new(int_const(0)),
        });
        let info = analyze_expr(&expr);
        assert!(info.is_pure_integer());
        assert_eq!(info.result_type(), &TirType::Bool);
        assert!(info.var_is_int(intern_name("x")));
        assert!(info.var_is_int(intern_name("y")));
        assert!(info.all_vars_scalar());
    }

    // --- Pure integer: x + y (result is Int) ---
    #[test]
    fn test_pure_integer_arithmetic_result_int() {
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_var("x")),
            op: TirArithOp::Add,
            right: Box::new(int_const(1)),
        });
        let info = analyze_expr(&expr);
        assert!(info.is_pure_integer());
        assert_eq!(info.result_type(), &TirType::Int);
    }

    // --- Pure boolean: a /\ b ---
    #[test]
    fn test_pure_bool_conjunction() {
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(bool_var("a")),
            op: TirBoolOp::And,
            right: Box::new(bool_var("b")),
        });
        let info = analyze_expr(&expr);
        assert!(info.is_pure_bool());
        assert_eq!(info.result_type(), &TirType::Bool);
        assert!(info.var_is_bool(intern_name("a")));
        assert!(info.var_is_bool(intern_name("b")));
    }

    // --- Pure integer invariant: (x > 0) /\ (y < 10) ---
    #[test]
    fn test_pure_integer_invariant_conjunction_of_comparisons() {
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(int_var("x")),
                op: TirCmpOp::Gt,
                right: Box::new(int_const(0)),
            })),
            op: TirBoolOp::And,
            right: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(int_var("y")),
                op: TirCmpOp::Lt,
                right: Box::new(int_const(10)),
            })),
        });
        let info = analyze_expr(&expr);
        assert!(info.is_pure_integer());
        assert_eq!(info.result_type(), &TirType::Bool);
    }

    // --- Mixed: comparison with Dyn variable ---
    #[test]
    fn test_mixed_when_dyn_var() {
        let expr = spanned(TirExpr::Cmp {
            left: Box::new(dyn_var("z")),
            op: TirCmpOp::Eq,
            right: Box::new(int_const(0)),
        });
        let info = analyze_expr(&expr);
        assert_eq!(info.expr_class(), ExprClass::Mixed);
    }

    // --- Compound: set membership ---
    #[test]
    fn test_compound_set_membership() {
        let set = spanned(TirExpr::SetEnum(vec![int_const(1), int_const(2)]));
        let expr = spanned(TirExpr::In {
            elem: Box::new(int_var("x")),
            set: Box::new(set),
        });
        let info = analyze_expr(&expr);
        assert_eq!(info.expr_class(), ExprClass::Compound);
        assert_eq!(info.result_type(), &TirType::Bool);
    }

    // --- IF-THEN-ELSE preserves pure-integer ---
    #[test]
    fn test_if_preserves_pure_integer() {
        // IF x > 0 THEN x + 1 ELSE x - 1
        let expr = spanned(TirExpr::If {
            cond: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(int_var("x")),
                op: TirCmpOp::Gt,
                right: Box::new(int_const(0)),
            })),
            then_: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(int_var("x")),
                op: TirArithOp::Add,
                right: Box::new(int_const(1)),
            })),
            else_: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(int_var("x")),
                op: TirArithOp::Sub,
                right: Box::new(int_const(1)),
            })),
        });
        let info = analyze_expr(&expr);
        assert!(info.is_pure_integer());
        assert_eq!(info.result_type(), &TirType::Int);
    }

    // --- Constant only ---
    #[test]
    fn test_int_constant_is_pure_integer() {
        let expr = int_const(42);
        let info = analyze_expr(&expr);
        assert!(info.is_pure_integer());
        assert_eq!(info.result_type(), &TirType::Int);
        assert!(info.var_types().is_empty());
    }

    #[test]
    fn test_bool_constant_is_pure_bool() {
        let expr = bool_const(true);
        let info = analyze_expr(&expr);
        assert!(info.is_pure_bool());
        assert_eq!(info.result_type(), &TirType::Bool);
    }

    // --- Negation ---
    #[test]
    fn test_arith_neg_pure_integer() {
        let expr = spanned(TirExpr::ArithNeg(Box::new(int_var("x"))));
        let info = analyze_expr(&expr);
        assert!(info.is_pure_integer());
        assert_eq!(info.result_type(), &TirType::Int);
    }

    #[test]
    fn test_bool_not_pure_bool() {
        let expr = spanned(TirExpr::BoolNot(Box::new(bool_var("a"))));
        let info = analyze_expr(&expr);
        assert!(info.is_pure_bool());
    }

    // --- Label is transparent ---
    #[test]
    fn test_label_transparent() {
        let inner = int_const(42);
        let expr = spanned(TirExpr::Label {
            name: "lbl".to_string(),
            body: Box::new(inner),
        });
        let info = analyze_expr(&expr);
        assert!(info.is_pure_integer());
    }

    // --- Variable type joining ---
    #[test]
    fn test_var_types_join_across_uses() {
        // x + x: same variable appears twice, type should remain Int.
        let x_id = intern_name("x_join");
        let x_var = || {
            spanned(TirExpr::Name(TirNameRef {
                name: "x_join".to_string(),
                name_id: x_id,
                kind: TirNameKind::StateVar { index: 0 },
                ty: TirType::Int,
            }))
        };
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(x_var()),
            op: TirArithOp::Add,
            right: Box::new(x_var()),
        });
        let info = analyze_expr(&expr);
        assert_eq!(info.var_type(x_id), Some(&TirType::Int));
    }

    // --- all_vars_scalar ---
    #[test]
    fn test_all_vars_scalar_with_compound() {
        let set_var = spanned(TirExpr::Name(TirNameRef {
            name: "s".to_string(),
            name_id: intern_name("s_compound"),
            kind: TirNameKind::StateVar { index: 0 },
            ty: TirType::Set(Box::new(TirType::Int)),
        }));
        let expr = spanned(TirExpr::In {
            elem: Box::new(int_var("x")),
            set: Box::new(set_var),
        });
        let info = analyze_expr(&expr);
        assert!(!info.all_vars_scalar());
    }

    // --- Compound: record access ---
    #[test]
    fn test_record_access_is_compound() {
        let record_var = spanned(TirExpr::Name(TirNameRef {
            name: "r".to_string(),
            name_id: intern_name("r_rec"),
            kind: TirNameKind::StateVar { index: 0 },
            ty: TirType::Record(vec![(intern_name("f"), TirType::Int)]),
        }));
        let expr = spanned(TirExpr::RecordAccess {
            record: Box::new(record_var),
            field: TirFieldName {
                name: "f".to_string(),
                field_id: intern_name("f"),
            },
        });
        let info = analyze_expr(&expr);
        assert_eq!(info.expr_class(), ExprClass::Compound);
        assert!(info.var_is_compound(intern_name("r_rec")));
    }

    // --- Let preserves class ---
    #[test]
    fn test_let_preserves_pure_integer() {
        let def = TirLetDef {
            name: "tmp".to_string(),
            name_id: intern_name("tmp_let"),
            params: vec![],
            body: int_const(5),
        };
        let expr = spanned(TirExpr::Let {
            defs: vec![def],
            body: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(int_var("x")),
                op: TirArithOp::Mul,
                right: Box::new(int_const(2)),
            })),
        });
        let info = analyze_expr(&expr);
        assert!(info.is_pure_integer());
    }

    // --- Range is compound ---
    #[test]
    fn test_range_is_compound() {
        let expr = spanned(TirExpr::Range {
            lo: Box::new(int_const(1)),
            hi: Box::new(int_const(10)),
        });
        let info = analyze_expr(&expr);
        assert_eq!(info.expr_class(), ExprClass::Compound);
        assert_eq!(
            info.result_type(),
            &TirType::Set(Box::new(TirType::Int))
        );
    }

    // --- Negation of comparison stays pure-integer ---
    #[test]
    fn test_bool_not_of_comparison_stays_pure_integer() {
        // ~(x > 0) is still part of a pure-integer invariant
        let expr = spanned(TirExpr::BoolNot(Box::new(spanned(TirExpr::Cmp {
            left: Box::new(int_var("x")),
            op: TirCmpOp::Gt,
            right: Box::new(int_const(0)),
        }))));
        let info = analyze_expr(&expr);
        assert!(info.is_pure_integer());
    }
}
