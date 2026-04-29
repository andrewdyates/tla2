// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! AST-walking functions for name resolution.
//!
//! These functions traverse the TLA+ AST, resolving identifier references
//! and managing scopes for quantifiers, LET expressions, function definitions, etc.

use super::context::ResolveCtx;
use super::types::{ResolveOptions, ScopeKind, SymbolKind};
use crate::ast::{
    BoundVar, CaseArm, ExceptSpec, Expr, OperatorDef, Proof, ProofHint, ProofStep, ProofStepKind,
    TheoremDecl,
};
use crate::span::Spanned;

/// Resolve an operator definition
pub(super) fn resolve_operator_def(ctx: &mut ResolveCtx, op: &OperatorDef) {
    // Create scope for parameters
    ctx.push_scope(ScopeKind::Let);

    for param in &op.params {
        let kind = if param.arity > 0 {
            SymbolKind::OpParam
        } else {
            SymbolKind::BoundVar
        };
        ctx.define(&param.name.node, kind, param.name.span, param.arity, false);
    }

    resolve_expr(ctx, &op.body);

    ctx.pop_scope();
}

/// Resolve a theorem declaration
pub(super) fn resolve_theorem(ctx: &mut ResolveCtx, thm: &TheoremDecl, options: ResolveOptions) {
    resolve_expr(ctx, &thm.body);

    if options.resolve_proofs {
        if let Some(proof) = &thm.proof {
            resolve_proof(ctx, &proof.node);
        }
    }
}

/// Resolve an instance declaration
pub(super) fn resolve_instance(ctx: &mut ResolveCtx, inst: &crate::ast::InstanceDecl) {
    for sub in &inst.substitutions {
        // The 'from' name refers to something in the imported module (not checked here)
        // The 'to' expression is resolved in current scope
        resolve_expr(ctx, &sub.to);
    }
}

/// Resolve an expression
pub(super) fn resolve_expr(ctx: &mut ResolveCtx, expr: &Spanned<Expr>) {
    match &expr.node {
        // Literals - nothing to resolve
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) => {}

        // Identifier reference
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            ctx.reference(name, expr.span);
        }

        // Operator reference (bare operator as value: +, -, *, etc.)
        // No resolution needed - these are built-in operators
        Expr::OpRef(_) => {}

        // Operator application
        Expr::Apply(op_expr, args) => {
            resolve_expr(ctx, op_expr);
            for arg in args {
                resolve_expr(ctx, arg);
            }
        }

        // Lambda
        Expr::Lambda(params, body) => {
            ctx.push_scope(ScopeKind::Lambda);
            for param in params {
                ctx.define(&param.node, SymbolKind::BoundVar, param.span, 0, false);
            }
            resolve_expr(ctx, body);
            ctx.pop_scope();
        }
        Expr::Label(label) => resolve_expr(ctx, &label.body),

        // Module reference (M!Op or M!Op(args))
        // The module and operator references are resolved at evaluation time
        // based on INSTANCE declarations. For now, just resolve the arguments.
        Expr::ModuleRef(_module, _op, args) => {
            for arg in args {
                resolve_expr(ctx, arg);
            }
        }

        // Instance expression (INSTANCE Module WITH ...)
        // Resolve substitution expressions
        Expr::InstanceExpr(_module, substitutions) => {
            for sub in substitutions {
                resolve_expr(ctx, &sub.to);
            }
        }

        // SubstIn: deferred INSTANCE substitution wrapper
        // Resolve substitution RHS expressions and the body
        Expr::SubstIn(subs, body) => {
            for sub in subs {
                resolve_expr(ctx, &sub.to);
            }
            resolve_expr(ctx, body);
        }

        // Binary logical operators
        Expr::And(l, r)
        | Expr::Or(l, r)
        | Expr::Implies(l, r)
        | Expr::Equiv(l, r)
        | Expr::In(l, r)
        | Expr::NotIn(l, r)
        | Expr::Subseteq(l, r)
        | Expr::Union(l, r)
        | Expr::Intersect(l, r)
        | Expr::SetMinus(l, r)
        | Expr::Eq(l, r)
        | Expr::Neq(l, r)
        | Expr::Lt(l, r)
        | Expr::Leq(l, r)
        | Expr::Gt(l, r)
        | Expr::Geq(l, r)
        | Expr::Add(l, r)
        | Expr::Sub(l, r)
        | Expr::Mul(l, r)
        | Expr::Div(l, r)
        | Expr::IntDiv(l, r)
        | Expr::Mod(l, r)
        | Expr::Pow(l, r)
        | Expr::Range(l, r)
        | Expr::LeadsTo(l, r) => {
            resolve_expr(ctx, l);
            resolve_expr(ctx, r);
        }

        // Unary operators
        Expr::Not(e)
        | Expr::Powerset(e)
        | Expr::BigUnion(e)
        | Expr::Domain(e)
        | Expr::Prime(e)
        | Expr::Always(e)
        | Expr::Eventually(e)
        | Expr::Enabled(e)
        | Expr::Unchanged(e)
        | Expr::Neg(e) => {
            resolve_expr(ctx, e);
        }

        // Quantifiers with bound variables
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            ctx.push_scope(ScopeKind::Quantifier);
            for bv in bounds {
                resolve_bound_var(ctx, bv);
            }
            resolve_expr(ctx, body);
            ctx.pop_scope();
        }

        // CHOOSE
        Expr::Choose(bv, body) => {
            ctx.push_scope(ScopeKind::Quantifier);
            resolve_bound_var(ctx, bv);
            resolve_expr(ctx, body);
            ctx.pop_scope();
        }

        // Set enumeration
        Expr::SetEnum(elems) => {
            for e in elems {
                resolve_expr(ctx, e);
            }
        }

        // Set builder {e : x \in S}
        Expr::SetBuilder(body, bounds) => {
            ctx.push_scope(ScopeKind::SetBuilder);
            for bv in bounds {
                resolve_bound_var(ctx, bv);
            }
            resolve_expr(ctx, body);
            ctx.pop_scope();
        }

        // Set filter {x \in S : P}
        Expr::SetFilter(bv, pred) => {
            ctx.push_scope(ScopeKind::SetFilter);
            resolve_bound_var(ctx, bv);
            resolve_expr(ctx, pred);
            ctx.pop_scope();
        }

        // Function definition [x \in S |-> e]
        Expr::FuncDef(bounds, body) => {
            ctx.push_scope(ScopeKind::Function);
            for bv in bounds {
                resolve_bound_var(ctx, bv);
            }
            resolve_expr(ctx, body);
            ctx.pop_scope();
        }

        // Function application f[x]
        Expr::FuncApply(f, arg) => {
            resolve_expr(ctx, f);
            resolve_expr(ctx, arg);
        }

        // Function set [S -> T]
        Expr::FuncSet(domain, codomain) => {
            resolve_expr(ctx, domain);
            resolve_expr(ctx, codomain);
        }

        // EXCEPT
        Expr::Except(base, specs) => {
            resolve_expr(ctx, base);
            for spec in specs {
                resolve_except_spec(ctx, spec);
            }
        }

        // Record constructor
        Expr::Record(fields) => {
            for (_, value) in fields {
                resolve_expr(ctx, value);
            }
        }

        // Record access
        Expr::RecordAccess(rec, _field) => {
            resolve_expr(ctx, rec);
            // Field names are not resolved as identifiers
        }

        // Record set
        Expr::RecordSet(fields) => {
            for (_, value) in fields {
                resolve_expr(ctx, value);
            }
        }

        // Tuple
        Expr::Tuple(elems) => {
            for e in elems {
                resolve_expr(ctx, e);
            }
        }

        // Cartesian product
        Expr::Times(factors) => {
            for f in factors {
                resolve_expr(ctx, f);
            }
        }

        // Temporal fairness
        Expr::WeakFair(vars, action) | Expr::StrongFair(vars, action) => {
            resolve_expr(ctx, vars);
            resolve_expr(ctx, action);
        }

        // IF-THEN-ELSE
        Expr::If(cond, then_e, else_e) => {
            resolve_expr(ctx, cond);
            resolve_expr(ctx, then_e);
            resolve_expr(ctx, else_e);
        }

        // CASE
        Expr::Case(arms, other) => {
            for arm in arms {
                resolve_case_arm(ctx, arm);
            }
            if let Some(o) = other {
                resolve_expr(ctx, o);
            }
        }

        // LET
        Expr::Let(defs, body) => {
            ctx.push_scope(ScopeKind::Let);

            // First pass: define all names
            for def in defs {
                ctx.define(
                    &def.name.node,
                    SymbolKind::Operator,
                    def.name.span,
                    def.params.len(),
                    def.local,
                );
            }

            // Second pass: resolve bodies (they can reference each other)
            for def in defs {
                resolve_operator_def(ctx, def);
            }

            resolve_expr(ctx, body);
            ctx.pop_scope();
        }
    }
}

/// Resolve a bound variable (define it and resolve its domain)
fn resolve_bound_var(ctx: &mut ResolveCtx, bv: &BoundVar) {
    // First resolve domain (it's in outer scope)
    if let Some(domain) = &bv.domain {
        resolve_expr(ctx, domain);
    }
    // Then define the bound variables (they're now in scope for body and later bounds).
    match &bv.pattern {
        Some(crate::ast::BoundPattern::Var(v)) => {
            ctx.define(&v.node, SymbolKind::BoundVar, v.span, 0, false);
        }
        Some(crate::ast::BoundPattern::Tuple(vs)) => {
            for v in vs {
                ctx.define(&v.node, SymbolKind::BoundVar, v.span, 0, false);
            }
        }
        None => {
            ctx.define(&bv.name.node, SymbolKind::BoundVar, bv.name.span, 0, false);
        }
    }
}

/// Resolve an EXCEPT specification
fn resolve_except_spec(ctx: &mut ResolveCtx, spec: &ExceptSpec) {
    use crate::ast::ExceptPathElement;
    for elem in &spec.path {
        match elem {
            ExceptPathElement::Index(idx) => resolve_expr(ctx, idx),
            ExceptPathElement::Field(_) => {} // Field names not resolved
        }
    }

    // `@` is a special placeholder only valid in EXCEPT update values.
    // It refers to the old value at the updated path.
    ctx.push_scope(ScopeKind::Except);
    ctx.define(
        "@",
        SymbolKind::BoundVar,
        crate::span::Span::dummy(),
        0,
        false,
    );
    resolve_expr(ctx, &spec.value);
    ctx.pop_scope();
}

/// Resolve a CASE arm
fn resolve_case_arm(ctx: &mut ResolveCtx, arm: &CaseArm) {
    resolve_expr(ctx, &arm.guard);
    resolve_expr(ctx, &arm.body);
}

/// Resolve a proof
fn resolve_proof(ctx: &mut ResolveCtx, proof: &Proof) {
    match proof {
        Proof::By(hints) => {
            for hint in hints {
                resolve_proof_hint(ctx, hint);
            }
        }
        Proof::Obvious | Proof::Omitted => {}
        Proof::Steps(steps) => {
            ctx.push_scope(ScopeKind::Proof);
            for step in steps {
                resolve_proof_step(ctx, step);
            }
            ctx.pop_scope();
        }
    }
}

/// Resolve a proof hint
fn resolve_proof_hint(ctx: &mut ResolveCtx, hint: &ProofHint) {
    match hint {
        ProofHint::Ref(name) => {
            ctx.reference(&name.node, name.span);
        }
        ProofHint::Def(names) => {
            for name in names {
                ctx.reference(&name.node, name.span);
            }
        }
        ProofHint::Module(_) => {
            // Module references not resolved here
        }
    }
}

/// Resolve a proof step
fn resolve_proof_step(ctx: &mut ResolveCtx, step: &ProofStep) {
    // Step labels are defined in proof scope
    if let Some(label) = &step.label {
        ctx.define(&label.node, SymbolKind::Operator, label.span, 0, false);
    }

    match &step.kind {
        ProofStepKind::Assert(expr, proof) => {
            resolve_expr(ctx, expr);
            if let Some(p) = proof {
                resolve_proof(ctx, &p.node);
            }
        }
        ProofStepKind::Suffices(expr, proof) => {
            resolve_expr(ctx, expr);
            if let Some(p) = proof {
                resolve_proof(ctx, &p.node);
            }
        }
        ProofStepKind::Have(expr) => {
            resolve_expr(ctx, expr);
        }
        ProofStepKind::Take(bounds) => {
            for bv in bounds {
                resolve_bound_var(ctx, bv);
            }
        }
        ProofStepKind::Witness(exprs) => {
            for e in exprs {
                resolve_expr(ctx, e);
            }
        }
        ProofStepKind::Pick(bounds, expr, proof) => {
            ctx.push_scope(ScopeKind::Quantifier);
            for bv in bounds {
                resolve_bound_var(ctx, bv);
            }
            resolve_expr(ctx, expr);
            if let Some(p) = proof {
                resolve_proof(ctx, &p.node);
            }
            ctx.pop_scope();
        }
        ProofStepKind::UseOrHide { facts, .. } => {
            for hint in facts {
                resolve_proof_hint(ctx, hint);
            }
        }
        ProofStepKind::Define(defs) => {
            for def in defs {
                ctx.define(
                    &def.name.node,
                    SymbolKind::Operator,
                    def.name.span,
                    def.params.len(),
                    def.local,
                );
                resolve_operator_def(ctx, def);
            }
        }
        ProofStepKind::Qed(proof) => {
            if let Some(p) = proof {
                resolve_proof(ctx, &p.node);
            }
        }
    }
}
