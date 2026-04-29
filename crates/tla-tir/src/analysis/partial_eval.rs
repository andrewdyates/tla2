// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TIR-level partial evaluation (spec-constant specialization) pass.
//!
//! When the user configures a spec with concrete values for CONSTANTs (e.g.
//! `N = 3`, `Debug = FALSE`), this pass walks the TIR and replaces every free
//! reference to those constants with the corresponding literal value. The
//! downstream pipeline (`inlining` → `const_prop` → tMIR lowering) then sees
//! a fully specialized program where arithmetic involving the constants folds
//! to literals, loops over bounded CONSTANT sets can be unrolled, and branches
//! on constant booleans disappear.
//!
//! TLC does none of this — the Java interpreter dereferences the constant
//! symbol table on every access. A compiled TLA2 binary with partial evaluation
//! beats TLC not by running faster per operation but by eliminating operations
//! entirely.
//!
//! # Pipeline position
//!
//! ```text
//! TirModule (raw)
//!   ↓
//! [partial_eval]   <-- this pass
//!   ↓
//! [inlining]
//!   ↓
//! [const_prop]
//!   ↓
//! [tMIR lowering]
//! ```
//!
//! `partial_eval` runs before `const_prop` so the folding cascade sees concrete
//! values. It runs before `inlining` so inlined operator bodies inherit the
//! substitutions from their call-site context unchanged.
//!
//! # Scalar-first scope
//!
//! This prototype substitutes only *scalar* values (`Value::SmallInt`,
//! `Value::Bool`). Compound values (sets, sequences, records, functions) are
//! counted in [`PartialEvalStats::non_scalar_skips`] but left as `Name`
//! references. Compound-value substitution is planned as a follow-up; it
//! requires recursive `Value → TirExpr` lowering.
//!
//! # Scope discipline
//!
//! The walker maintains a shadow set of `NameId`s. Entering `Let`, `Forall`,
//! `Exists`, `Choose`, `SetFilter`, `SetBuilder`, `FuncDef`, `Lambda`, or an
//! operator parameter list pushes the introduced names onto the shadow set;
//! on exit, they are popped. A constant that shares a `NameId` with a shadowing
//! binder is not substituted inside that scope. This is defense-in-depth:
//! correct interning should never produce such a collision, but the invariant
//! is cheap to enforce.
//!
//! Part of #4251 (LLVM2 + tMIR supremacy, pillar 1).

use crate::lower::{TirModule, TirOperator};
use crate::nodes::{
    TirBoundPattern, TirBoundVar, TirCaseArm, TirExceptPathElement, TirExceptSpec, TirExpr,
    TirLetDef, TirModuleRefSegment, TirOperatorRef,
};
use crate::types::TirType;
use rustc_hash::{FxHashMap, FxHashSet};
use tla_core::{intern_name, NameId, Spanned};
use tla_value::Value;

/// A read-only mapping of `NameId` → `Value` supplied at spec load time.
///
/// Populated from the user's CONSTANT bindings (`CONFIG N = 3`, etc.). The
/// map is keyed by the interned `NameId`; callers must intern their names
/// through the same interner that produced the TIR.
#[derive(Debug, Clone, Default)]
pub struct ConstantEnv {
    bindings: FxHashMap<NameId, Value>,
}

impl ConstantEnv {
    /// Create an empty `ConstantEnv`.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Bind a `NameId` to a concrete value.
    pub fn bind(&mut self, name_id: NameId, value: Value) {
        self.bindings.insert(name_id, value);
    }

    /// Convenience: intern `name` and bind it to `value`.
    pub fn bind_by_name(&mut self, name: &str, value: Value) {
        self.bindings.insert(intern_name(name), value);
    }

    /// Number of bound constants.
    #[must_use]
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Whether any constants are bound.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Look up a binding.
    #[must_use]
    pub fn get(&self, name_id: NameId) -> Option<&Value> {
        self.bindings.get(&name_id)
    }
}

/// Counters from a partial-evaluation pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PartialEvalStats {
    /// Number of `Name` nodes rewritten to `Const`.
    pub constants_substituted: usize,
    /// Number of `Name` hits skipped because a local binder shadowed the name.
    pub shadowed_skips: usize,
    /// Number of `Name` hits skipped because the bound value was compound
    /// (set, record, function, sequence). These are candidates for a future
    /// compound-lowering pass.
    pub non_scalar_skips: usize,
}

impl PartialEvalStats {
    fn add(&mut self, other: &PartialEvalStats) {
        self.constants_substituted += other.constants_substituted;
        self.shadowed_skips += other.shadowed_skips;
        self.non_scalar_skips += other.non_scalar_skips;
    }
}

/// Apply partial evaluation to every operator body in `module`.
pub fn partial_eval_module(module: &mut TirModule, env: &ConstantEnv) -> PartialEvalStats {
    let mut stats = PartialEvalStats::default();
    if env.is_empty() {
        return stats;
    }
    for op in &mut module.operators {
        partial_eval_operator(op, env, &mut stats);
    }
    stats
}

/// Apply partial evaluation to a single operator.
///
/// The operator's own parameters shadow any matching constants: a parameter
/// named `N` in `Foo(N) == ...` hides a module-level `CONSTANT N` inside the
/// body of `Foo`.
pub fn partial_eval_operator(
    op: &mut TirOperator,
    env: &ConstantEnv,
    stats: &mut PartialEvalStats,
) {
    if env.is_empty() {
        return;
    }
    // Operator parameters are names local to this operator's body.
    let mut shadow: FxHashSet<NameId> = FxHashSet::default();
    for param in &op.params {
        shadow.insert(intern_name(param));
    }

    // Swap out the body, substitute, swap it back. Spanned has no Default,
    // so we use a sentinel const value that will be overwritten.
    let sentinel = Spanned::new(
        TirExpr::Const {
            value: Value::bool(false),
            ty: TirType::Bool,
        },
        op.body.span,
    );
    let body = std::mem::replace(&mut op.body, sentinel);
    op.body = substitute(body, env, &mut shadow, stats);
}

/// Apply partial evaluation to a standalone expression.
///
/// Used by tests and by consumers that want to substitute into a synthesized
/// body without a full module.
#[must_use]
pub fn partial_eval_expr(
    expr: Spanned<TirExpr>,
    env: &ConstantEnv,
) -> (Spanned<TirExpr>, PartialEvalStats) {
    let mut stats = PartialEvalStats::default();
    if env.is_empty() {
        return (expr, stats);
    }
    let mut shadow: FxHashSet<NameId> = FxHashSet::default();
    let result = substitute(expr, env, &mut shadow, &mut stats);
    (result, stats)
}

/// Lower a scalar `Value` to a `TirExpr::Const` node.
///
/// Returns `None` for compound values; the caller records a `non_scalar_skips`
/// counter bump and leaves the original `Name` in place.
fn value_to_const_expr(value: &Value) -> Option<TirExpr> {
    if let Some(b) = value.as_bool() {
        return Some(TirExpr::Const {
            value: Value::bool(b),
            ty: TirType::Bool,
        });
    }
    if let Some(n) = value.as_i64() {
        return Some(TirExpr::Const {
            value: Value::int(n),
            ty: TirType::Int,
        });
    }
    None
}

/// Recursively substitute free references to bound constants.
fn substitute(
    expr: Spanned<TirExpr>,
    env: &ConstantEnv,
    shadow: &mut FxHashSet<NameId>,
    stats: &mut PartialEvalStats,
) -> Spanned<TirExpr> {
    let span = expr.span;
    let node = match expr.node {
        // --- The interesting case ---
        TirExpr::Name(ref name_ref) => {
            if shadow.contains(&name_ref.name_id) {
                // Defense-in-depth: a local binder with the same NameId hides
                // a CONSTANT in this scope.
                stats.shadowed_skips += 1;
                return expr;
            }
            match env.get(name_ref.name_id) {
                Some(value) => match value_to_const_expr(value) {
                    Some(const_node) => {
                        stats.constants_substituted += 1;
                        const_node
                    }
                    None => {
                        // Compound value — scalar-first scope defers these.
                        stats.non_scalar_skips += 1;
                        return expr;
                    }
                },
                None => return expr,
            }
        }

        // --- Scopes that introduce new names ---
        TirExpr::Let { defs, body } => {
            let mut new_names: Vec<NameId> = Vec::with_capacity(defs.len());
            // Each def's body sees earlier defs' names in scope. TLA+ LET
            // bindings are evaluated sequentially; we match that ordering.
            let mut new_defs: Vec<TirLetDef> = Vec::with_capacity(defs.len());
            for def in defs {
                // A def with params adds both the def name and (inside its
                // own body) its parameter names. But a LetDef body is not
                // walked while the params are bound — params are not in scope
                // for the outer substitution visit. We only walk the body
                // with the def name (and prior def names) shadowed.
                let folded_body = substitute_let_def_body(&def, env, shadow, stats);
                shadow.insert(def.name_id);
                new_names.push(def.name_id);
                new_defs.push(TirLetDef {
                    name: def.name,
                    name_id: def.name_id,
                    params: def.params,
                    body: folded_body,
                });
            }
            let new_body = substitute(*body, env, shadow, stats);
            for id in &new_names {
                shadow.remove(id);
            }
            TirExpr::Let {
                defs: new_defs,
                body: Box::new(new_body),
            }
        }

        TirExpr::Forall { vars, body } => {
            let added = push_bound_vars(&vars, shadow);
            let new_vars = substitute_bound_vars(vars, env, shadow, stats);
            let new_body = substitute(*body, env, shadow, stats);
            pop_added(shadow, &added);
            TirExpr::Forall {
                vars: new_vars,
                body: Box::new(new_body),
            }
        }
        TirExpr::Exists { vars, body } => {
            let added = push_bound_vars(&vars, shadow);
            let new_vars = substitute_bound_vars(vars, env, shadow, stats);
            let new_body = substitute(*body, env, shadow, stats);
            pop_added(shadow, &added);
            TirExpr::Exists {
                vars: new_vars,
                body: Box::new(new_body),
            }
        }
        TirExpr::Choose { var, body } => {
            let added = push_bound_var(&var, shadow);
            let new_var = substitute_bound_var(var, env, shadow, stats);
            let new_body = substitute(*body, env, shadow, stats);
            pop_added(shadow, &added);
            TirExpr::Choose {
                var: new_var,
                body: Box::new(new_body),
            }
        }
        TirExpr::SetFilter { var, body } => {
            let added = push_bound_var(&var, shadow);
            let new_var = substitute_bound_var(var, env, shadow, stats);
            let new_body = substitute(*body, env, shadow, stats);
            pop_added(shadow, &added);
            TirExpr::SetFilter {
                var: new_var,
                body: Box::new(new_body),
            }
        }
        TirExpr::SetBuilder { body, vars } => {
            let added = push_bound_vars(&vars, shadow);
            let new_vars = substitute_bound_vars(vars, env, shadow, stats);
            let new_body = substitute(*body, env, shadow, stats);
            pop_added(shadow, &added);
            TirExpr::SetBuilder {
                body: Box::new(new_body),
                vars: new_vars,
            }
        }
        TirExpr::FuncDef { vars, body } => {
            let added = push_bound_vars(&vars, shadow);
            let new_vars = substitute_bound_vars(vars, env, shadow, stats);
            let new_body = substitute(*body, env, shadow, stats);
            pop_added(shadow, &added);
            TirExpr::FuncDef {
                vars: new_vars,
                body: Box::new(new_body),
            }
        }
        TirExpr::Lambda {
            params,
            body,
            ast_body,
        } => {
            let added: Vec<NameId> = params.iter().map(|p| intern_name(p)).collect();
            let mut actually_added = Vec::with_capacity(added.len());
            for id in &added {
                if shadow.insert(*id) {
                    actually_added.push(*id);
                }
            }
            let new_body = substitute(*body, env, shadow, stats);
            for id in &actually_added {
                shadow.remove(id);
            }
            TirExpr::Lambda {
                params,
                body: Box::new(new_body),
                ast_body,
            }
        }

        // --- Pure structural recursion ---
        TirExpr::ArithBinOp { left, op, right } => TirExpr::ArithBinOp {
            left: Box::new(substitute(*left, env, shadow, stats)),
            op,
            right: Box::new(substitute(*right, env, shadow, stats)),
        },
        TirExpr::ArithNeg(inner) => {
            TirExpr::ArithNeg(Box::new(substitute(*inner, env, shadow, stats)))
        }
        TirExpr::BoolBinOp { left, op, right } => TirExpr::BoolBinOp {
            left: Box::new(substitute(*left, env, shadow, stats)),
            op,
            right: Box::new(substitute(*right, env, shadow, stats)),
        },
        TirExpr::BoolNot(inner) => {
            TirExpr::BoolNot(Box::new(substitute(*inner, env, shadow, stats)))
        }
        TirExpr::Cmp { left, op, right } => TirExpr::Cmp {
            left: Box::new(substitute(*left, env, shadow, stats)),
            op,
            right: Box::new(substitute(*right, env, shadow, stats)),
        },
        TirExpr::In { elem, set } => TirExpr::In {
            elem: Box::new(substitute(*elem, env, shadow, stats)),
            set: Box::new(substitute(*set, env, shadow, stats)),
        },
        TirExpr::Subseteq { left, right } => TirExpr::Subseteq {
            left: Box::new(substitute(*left, env, shadow, stats)),
            right: Box::new(substitute(*right, env, shadow, stats)),
        },
        TirExpr::Unchanged(inner) => {
            TirExpr::Unchanged(Box::new(substitute(*inner, env, shadow, stats)))
        }
        TirExpr::ActionSubscript {
            kind,
            action,
            subscript,
        } => TirExpr::ActionSubscript {
            kind,
            action: Box::new(substitute(*action, env, shadow, stats)),
            subscript: Box::new(substitute(*subscript, env, shadow, stats)),
        },
        TirExpr::Always(inner) => TirExpr::Always(Box::new(substitute(*inner, env, shadow, stats))),
        TirExpr::Eventually(inner) => {
            TirExpr::Eventually(Box::new(substitute(*inner, env, shadow, stats)))
        }
        TirExpr::RecordAccess { record, field } => TirExpr::RecordAccess {
            record: Box::new(substitute(*record, env, shadow, stats)),
            field,
        },
        TirExpr::Except { base, specs } => TirExpr::Except {
            base: Box::new(substitute(*base, env, shadow, stats)),
            specs: specs
                .into_iter()
                .map(|s| substitute_except_spec(s, env, shadow, stats))
                .collect(),
        },
        TirExpr::Range { lo, hi } => TirExpr::Range {
            lo: Box::new(substitute(*lo, env, shadow, stats)),
            hi: Box::new(substitute(*hi, env, shadow, stats)),
        },
        TirExpr::If { cond, then_, else_ } => TirExpr::If {
            cond: Box::new(substitute(*cond, env, shadow, stats)),
            then_: Box::new(substitute(*then_, env, shadow, stats)),
            else_: Box::new(substitute(*else_, env, shadow, stats)),
        },
        TirExpr::SetEnum(elems) => TirExpr::SetEnum(
            elems
                .into_iter()
                .map(|e| substitute(e, env, shadow, stats))
                .collect(),
        ),
        TirExpr::SetBinOp { left, op, right } => TirExpr::SetBinOp {
            left: Box::new(substitute(*left, env, shadow, stats)),
            op,
            right: Box::new(substitute(*right, env, shadow, stats)),
        },
        TirExpr::Powerset(inner) => {
            TirExpr::Powerset(Box::new(substitute(*inner, env, shadow, stats)))
        }
        TirExpr::BigUnion(inner) => {
            TirExpr::BigUnion(Box::new(substitute(*inner, env, shadow, stats)))
        }
        TirExpr::KSubset { base, k } => TirExpr::KSubset {
            base: Box::new(substitute(*base, env, shadow, stats)),
            k: Box::new(substitute(*k, env, shadow, stats)),
        },
        TirExpr::FuncApply { func, arg } => TirExpr::FuncApply {
            func: Box::new(substitute(*func, env, shadow, stats)),
            arg: Box::new(substitute(*arg, env, shadow, stats)),
        },
        TirExpr::FuncSet { domain, range } => TirExpr::FuncSet {
            domain: Box::new(substitute(*domain, env, shadow, stats)),
            range: Box::new(substitute(*range, env, shadow, stats)),
        },
        TirExpr::Domain(inner) => TirExpr::Domain(Box::new(substitute(*inner, env, shadow, stats))),
        TirExpr::Record(fields) => TirExpr::Record(
            fields
                .into_iter()
                .map(|(f, e)| (f, substitute(e, env, shadow, stats)))
                .collect(),
        ),
        TirExpr::RecordSet(fields) => TirExpr::RecordSet(
            fields
                .into_iter()
                .map(|(f, e)| (f, substitute(e, env, shadow, stats)))
                .collect(),
        ),
        TirExpr::Tuple(elems) => TirExpr::Tuple(
            elems
                .into_iter()
                .map(|e| substitute(e, env, shadow, stats))
                .collect(),
        ),
        TirExpr::Times(elems) => TirExpr::Times(
            elems
                .into_iter()
                .map(|e| substitute(e, env, shadow, stats))
                .collect(),
        ),
        TirExpr::Case { arms, other } => TirExpr::Case {
            arms: arms
                .into_iter()
                .map(|arm| TirCaseArm {
                    guard: substitute(arm.guard, env, shadow, stats),
                    body: substitute(arm.body, env, shadow, stats),
                })
                .collect(),
            other: other.map(|o| Box::new(substitute(*o, env, shadow, stats))),
        },
        TirExpr::Prime(inner) => TirExpr::Prime(Box::new(substitute(*inner, env, shadow, stats))),
        TirExpr::Apply { op, args } => TirExpr::Apply {
            op: Box::new(substitute(*op, env, shadow, stats)),
            args: args
                .into_iter()
                .map(|a| substitute(a, env, shadow, stats))
                .collect(),
        },
        TirExpr::Label { name, body } => TirExpr::Label {
            name,
            body: Box::new(substitute(*body, env, shadow, stats)),
        },
        TirExpr::LeadsTo { left, right } => TirExpr::LeadsTo {
            left: Box::new(substitute(*left, env, shadow, stats)),
            right: Box::new(substitute(*right, env, shadow, stats)),
        },
        TirExpr::WeakFair { vars, action } => TirExpr::WeakFair {
            vars: Box::new(substitute(*vars, env, shadow, stats)),
            action: Box::new(substitute(*action, env, shadow, stats)),
        },
        TirExpr::StrongFair { vars, action } => TirExpr::StrongFair {
            vars: Box::new(substitute(*vars, env, shadow, stats)),
            action: Box::new(substitute(*action, env, shadow, stats)),
        },
        TirExpr::Enabled(inner) => {
            TirExpr::Enabled(Box::new(substitute(*inner, env, shadow, stats)))
        }
        TirExpr::OperatorRef(op_ref) => TirExpr::OperatorRef(TirOperatorRef {
            path: op_ref
                .path
                .into_iter()
                .map(|seg| TirModuleRefSegment {
                    name: seg.name,
                    name_id: seg.name_id,
                    args: seg
                        .args
                        .into_iter()
                        .map(|a| substitute(a, env, shadow, stats))
                        .collect(),
                })
                .collect(),
            operator: op_ref.operator,
            operator_id: op_ref.operator_id,
            args: op_ref
                .args
                .into_iter()
                .map(|a| substitute(a, env, shadow, stats))
                .collect(),
        }),

        // --- Leaves: nothing to substitute. ---
        TirExpr::Const { .. } | TirExpr::ExceptAt | TirExpr::OpRef(_) => {
            return expr;
        }
    };

    Spanned { node, span }
}

/// Walk a `LetDef`'s body with the def's parameters shadowed.
///
/// Parameters are bound only inside the body of the def. The outer scope
/// does not see them.
fn substitute_let_def_body(
    def: &TirLetDef,
    env: &ConstantEnv,
    shadow: &mut FxHashSet<NameId>,
    stats: &mut PartialEvalStats,
) -> Spanned<TirExpr> {
    // If the def has params, intern them and push onto shadow while walking
    // the def body.
    let mut actually_added: Vec<NameId> = Vec::with_capacity(def.params.len());
    for p in &def.params {
        let id = intern_name(p);
        if shadow.insert(id) {
            actually_added.push(id);
        }
    }
    // Clone the body; the outer caller will later rebuild the def with the
    // folded body we return here.
    let body_clone = def.body.clone();
    let new_body = substitute(body_clone, env, shadow, stats);
    for id in &actually_added {
        shadow.remove(id);
    }
    new_body
}

/// Push every bound variable name onto `shadow`. Returns the list of names
/// actually added (i.e. those that were not already present), so
/// `pop_added` can remove only those.
fn push_bound_vars(vars: &[TirBoundVar], shadow: &mut FxHashSet<NameId>) -> Vec<NameId> {
    let mut added = Vec::with_capacity(vars.len());
    for v in vars {
        for id in ids_for_bound_var(v) {
            if shadow.insert(id) {
                added.push(id);
            }
        }
    }
    added
}

fn push_bound_var(var: &TirBoundVar, shadow: &mut FxHashSet<NameId>) -> Vec<NameId> {
    let mut added = Vec::new();
    for id in ids_for_bound_var(var) {
        if shadow.insert(id) {
            added.push(id);
        }
    }
    added
}

fn pop_added(shadow: &mut FxHashSet<NameId>, added: &[NameId]) {
    for id in added {
        shadow.remove(id);
    }
}

/// Names introduced by a bound variable (including destructured tuple names).
fn ids_for_bound_var(var: &TirBoundVar) -> Vec<NameId> {
    let mut out = vec![var.name_id];
    if let Some(TirBoundPattern::Tuple(names)) = &var.pattern {
        for (_, id) in names {
            out.push(*id);
        }
    }
    out
}

/// Substitute inside bound-variable domains, leaving the binder names
/// themselves untouched.
fn substitute_bound_vars(
    vars: Vec<TirBoundVar>,
    env: &ConstantEnv,
    shadow: &mut FxHashSet<NameId>,
    stats: &mut PartialEvalStats,
) -> Vec<TirBoundVar> {
    vars.into_iter()
        .map(|v| substitute_bound_var(v, env, shadow, stats))
        .collect()
}

fn substitute_bound_var(
    var: TirBoundVar,
    env: &ConstantEnv,
    shadow: &mut FxHashSet<NameId>,
    stats: &mut PartialEvalStats,
) -> TirBoundVar {
    TirBoundVar {
        name: var.name,
        name_id: var.name_id,
        domain: var
            .domain
            .map(|d| Box::new(substitute(*d, env, shadow, stats))),
        pattern: var.pattern,
    }
}

fn substitute_except_spec(
    spec: TirExceptSpec,
    env: &ConstantEnv,
    shadow: &mut FxHashSet<NameId>,
    stats: &mut PartialEvalStats,
) -> TirExceptSpec {
    TirExceptSpec {
        path: spec
            .path
            .into_iter()
            .map(|elem| match elem {
                TirExceptPathElement::Index(idx) => {
                    TirExceptPathElement::Index(Box::new(substitute(*idx, env, shadow, stats)))
                }
                TirExceptPathElement::Field(f) => TirExceptPathElement::Field(f),
            })
            .collect(),
        value: substitute(spec.value, env, shadow, stats),
    }
}

// Unused helper retained for future compound-lowering extension. Suppresses
// dead_code warnings.
#[allow(dead_code)]
fn merge_stats(a: &mut PartialEvalStats, b: &PartialEvalStats) {
    a.add(b);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nodes::{TirArithOp, TirBoundVar, TirCmpOp, TirLetDef, TirNameKind, TirNameRef};
    use tla_core::span::{FileId, Span};

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

    #[allow(dead_code)]
    fn bool_const(b: bool) -> Spanned<TirExpr> {
        spanned(TirExpr::Const {
            value: Value::bool(b),
            ty: TirType::Bool,
        })
    }

    fn name_ref(name: &str, ty: TirType) -> Spanned<TirExpr> {
        spanned(TirExpr::Name(TirNameRef {
            name: name.to_string(),
            name_id: intern_name(name),
            kind: TirNameKind::Ident,
            ty,
        }))
    }

    // =========================================================
    // Basic substitution
    // =========================================================

    #[test]
    fn test_substitute_int_constant() {
        // CONSTANT N = 3; body: N + 5
        let mut env = ConstantEnv::new();
        env.bind_by_name("pe_N_int", Value::int(3));

        let body = spanned(TirExpr::ArithBinOp {
            left: Box::new(name_ref("pe_N_int", TirType::Int)),
            op: TirArithOp::Add,
            right: Box::new(int_const(5)),
        });

        let (result, stats) = partial_eval_expr(body, &env);
        assert_eq!(stats.constants_substituted, 1);
        assert_eq!(stats.shadowed_skips, 0);
        assert_eq!(stats.non_scalar_skips, 0);

        // After substitution the LHS is Const(3).
        match result.node {
            TirExpr::ArithBinOp { left, .. } => match &left.node {
                TirExpr::Const { value, .. } => {
                    assert_eq!(value.as_i64(), Some(3));
                }
                other => panic!("expected Const, got {other:?}"),
            },
            _ => panic!("expected ArithBinOp"),
        }
    }

    #[test]
    fn test_substitute_bool_constant() {
        // CONSTANT Debug = FALSE; body: IF Debug THEN 1 ELSE 2
        let mut env = ConstantEnv::new();
        env.bind_by_name("pe_Debug", Value::bool(false));

        let body = spanned(TirExpr::If {
            cond: Box::new(name_ref("pe_Debug", TirType::Bool)),
            then_: Box::new(int_const(1)),
            else_: Box::new(int_const(2)),
        });

        let (result, stats) = partial_eval_expr(body, &env);
        assert_eq!(stats.constants_substituted, 1);
        match result.node {
            TirExpr::If { cond, .. } => match &cond.node {
                TirExpr::Const { value, .. } => {
                    assert_eq!(value.as_bool(), Some(false));
                }
                other => panic!("expected bool const, got {other:?}"),
            },
            _ => panic!("expected If"),
        }
    }

    // =========================================================
    // Scope discipline
    // =========================================================

    #[test]
    fn test_let_shadows_constant() {
        // CONSTANT N = 3
        // LET N == 42 IN N + 1
        // -> LET N == 42 IN N + 1   (inner N is NOT substituted)
        let mut env = ConstantEnv::new();
        env.bind_by_name("pe_letShadow_N", Value::int(3));

        let inner_n = name_ref("pe_letShadow_N", TirType::Int);
        let expr = spanned(TirExpr::Let {
            defs: vec![TirLetDef {
                name: "pe_letShadow_N".to_string(),
                name_id: intern_name("pe_letShadow_N"),
                params: vec![],
                body: int_const(42),
            }],
            body: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(inner_n),
                op: TirArithOp::Add,
                right: Box::new(int_const(1)),
            })),
        });

        let (result, stats) = partial_eval_expr(expr, &env);
        assert_eq!(stats.constants_substituted, 0);
        assert_eq!(stats.shadowed_skips, 1);

        // Structure unchanged.
        match result.node {
            TirExpr::Let { defs, body } => {
                assert_eq!(defs.len(), 1);
                match body.node {
                    TirExpr::ArithBinOp { left, .. } => {
                        assert!(matches!(left.node, TirExpr::Name(_)));
                    }
                    _ => panic!("expected ArithBinOp"),
                }
            }
            _ => panic!("expected Let"),
        }
    }

    #[test]
    fn test_operator_param_shadows_constant() {
        // CONSTANT X = 10
        // Foo(X) == X + 1
        // -> Foo body has X as parameter; the CONSTANT substitution must NOT fire.
        let mut env = ConstantEnv::new();
        env.bind_by_name("pe_paramShadow_X", Value::int(10));

        let body = spanned(TirExpr::ArithBinOp {
            left: Box::new(name_ref("pe_paramShadow_X", TirType::Int)),
            op: TirArithOp::Add,
            right: Box::new(int_const(1)),
        });
        let mut op = TirOperator {
            name: "Foo".to_string(),
            name_id: intern_name("Foo_pe_op"),
            params: vec!["pe_paramShadow_X".to_string()],
            is_recursive: false,
            body,
        };
        let mut stats = PartialEvalStats::default();
        partial_eval_operator(&mut op, &env, &mut stats);
        assert_eq!(stats.constants_substituted, 0);
        assert_eq!(stats.shadowed_skips, 1);
        // Body is unchanged.
        match op.body.node {
            TirExpr::ArithBinOp { left, .. } => {
                assert!(matches!(left.node, TirExpr::Name(_)));
            }
            _ => panic!("expected ArithBinOp"),
        }
    }

    #[test]
    fn test_forall_bound_var_shadows_constant() {
        // CONSTANT i = 7
        // \A i \in 1..10 : i > 0
        // -> inner i is the bound variable; the CONSTANT must not substitute.
        let mut env = ConstantEnv::new();
        env.bind_by_name("pe_forallShadow_i", Value::int(7));

        let expr = spanned(TirExpr::Forall {
            vars: vec![TirBoundVar {
                name: "pe_forallShadow_i".to_string(),
                name_id: intern_name("pe_forallShadow_i"),
                domain: Some(Box::new(spanned(TirExpr::Range {
                    lo: Box::new(int_const(1)),
                    hi: Box::new(int_const(10)),
                }))),
                pattern: None,
            }],
            body: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(name_ref("pe_forallShadow_i", TirType::Int)),
                op: TirCmpOp::Gt,
                right: Box::new(int_const(0)),
            })),
        });
        let (_result, stats) = partial_eval_expr(expr, &env);
        assert_eq!(stats.constants_substituted, 0);
        assert_eq!(stats.shadowed_skips, 1);
    }

    #[test]
    fn test_compound_constant_deferred() {
        // CONSTANT S = {1,2} (set, compound).
        // body: S
        // -> not substituted; non_scalar_skips increments.
        let mut env = ConstantEnv::new();
        env.bind_by_name("pe_compound_S", Value::set([Value::int(1), Value::int(2)]));

        let expr = name_ref("pe_compound_S", TirType::Set(Box::new(TirType::Int)));
        let (result, stats) = partial_eval_expr(expr, &env);
        assert_eq!(stats.constants_substituted, 0);
        assert_eq!(stats.non_scalar_skips, 1);
        // The name reference is preserved.
        assert!(matches!(result.node, TirExpr::Name(_)));
    }

    // =========================================================
    // Full-module
    // =========================================================

    #[test]
    fn test_partial_eval_module_multiple_operators() {
        let mut env = ConstantEnv::new();
        env.bind_by_name("pe_mod_N", Value::int(5));
        env.bind_by_name("pe_mod_Debug", Value::bool(true));

        let op_a = TirOperator {
            name: "A".to_string(),
            name_id: intern_name("A_pe_mod"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ref("pe_mod_N", TirType::Int)),
                op: TirArithOp::Add,
                right: Box::new(int_const(1)),
            }),
        };
        let op_b = TirOperator {
            name: "B".to_string(),
            name_id: intern_name("B_pe_mod"),
            params: vec![],
            is_recursive: false,
            body: name_ref("pe_mod_Debug", TirType::Bool),
        };

        let mut module = TirModule {
            name: "Mod".to_string(),
            operators: vec![op_a, op_b],
        };
        let stats = partial_eval_module(&mut module, &env);
        assert_eq!(stats.constants_substituted, 2);
        assert_eq!(stats.shadowed_skips, 0);
        assert_eq!(stats.non_scalar_skips, 0);
    }

    // =========================================================
    // Acceptance test: "constant is baked into generated IR"
    // =========================================================

    #[test]
    fn test_constant_baked_into_generated_ir() {
        // This is the prototype's headline test.
        //
        // CONSTANT MaxN = 42
        // body:    MaxN
        //
        // After partial_eval, the body MUST be literally `Const(42)` — no
        // `Name` node, no `Apply`, no wrapper. This is what "baked into
        // generated IR" means.
        let mut env = ConstantEnv::new();
        env.bind_by_name("pe_bakedMaxN", Value::int(42));
        let body = name_ref("pe_bakedMaxN", TirType::Int);
        let (result, stats) = partial_eval_expr(body, &env);
        assert_eq!(stats.constants_substituted, 1);
        match result.node {
            TirExpr::Const { value, ty } => {
                assert_eq!(value.as_i64(), Some(42));
                assert!(matches!(ty, TirType::Int));
            }
            other => panic!("expected Const(42), got {other:?}"),
        }
    }

    #[test]
    fn test_empty_env_is_noop() {
        let env = ConstantEnv::new();
        let body = name_ref("pe_noop_X", TirType::Int);
        let original_name_id = match &body.node {
            TirExpr::Name(n) => n.name_id,
            _ => unreachable!(),
        };
        let (result, stats) = partial_eval_expr(body, &env);
        assert_eq!(stats.constants_substituted, 0);
        assert_eq!(stats.shadowed_skips, 0);
        assert_eq!(stats.non_scalar_skips, 0);
        match result.node {
            TirExpr::Name(n) => assert_eq!(n.name_id, original_name_id),
            other => panic!("expected Name, got {other:?}"),
        }
    }
}
