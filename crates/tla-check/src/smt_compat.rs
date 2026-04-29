// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SMT compatibility analysis for TLA+ expressions.
//!
//! Determines whether an expression tree is within the SMT-compatible
//! fragment for oracle routing decisions. Accepts finite set constructs
//! (SetEnum, In/NotIn, FuncDef, SetFilter, Subseteq, FuncSet, RecordSet,
//! Times, Tuple, BigUnion) since z4 has encoders for all of these.
//! Also accepts bounded CHOOSE and SetBuilder since z4 translates these
//! via Skolemization and quantifier expansion respectively.
//! Only rejects higher-order constructs (Lambda, OpRef), temporal
//! operators, and InstanceExpr.
//!
//! Part of #3954: Widened from Bool/Int-only to accept finite enums +
//! bounded quantifiers that z4 already supports.
//! Further widened in #3954 Phase 1: CHOOSE (bounded) and SetBuilder
//! (bounded) accepted -- z4 CHC/BMC translators handle both via
//! Skolemization (quantifier.rs, translate_bmc.rs) and membership
//! rewriting (membership/mod.rs, chc/translation.rs).
//! BigUnion accepted when inner is SMT-compatible (BMC translator
//! handles via translate_big_union_bool, Part of #3778).

use tla_core::ast::Expr;
use tla_core::Spanned;

/// Check whether an action's expression tree is within the SMT-compatible
/// fragment for CDEMC oracle routing.
///
/// Accepts: Bool/Int/String ops, finite set constructs (SetEnum, In/NotIn,
/// FuncDef, SetFilter, Subseteq, Union/Intersect/SetMinus, FuncSet,
/// RecordSet, Times, Tuple of any size, BigUnion when inner is compatible),
/// bounded quantifiers, records, function application, EXCEPT,
/// bounded CHOOSE (Skolemization), bounded SetBuilder (quantifier expansion).
///
/// Rejects: Lambda, OpRef, temporal operators, InstanceExpr.
///
/// Part of #3784, widened in #3954.
pub(crate) fn is_expr_smt_compatible(expr: &Spanned<Expr>) -> bool {
    match &expr.node {
        // === SMT-compatible leaves ===
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) => true,
        Expr::Ident(_, _) | Expr::StateVar(_, _, _) => true,

        // === SMT-compatible logic ===
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b) | Expr::Equiv(a, b) => {
            is_expr_smt_compatible(a) && is_expr_smt_compatible(b)
        }
        Expr::Not(a) => is_expr_smt_compatible(a),

        // === SMT-compatible comparison ===
        Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::Lt(a, b)
        | Expr::Leq(a, b)
        | Expr::Gt(a, b)
        | Expr::Geq(a, b) => is_expr_smt_compatible(a) && is_expr_smt_compatible(b),

        // === SMT-compatible arithmetic ===
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::IntDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Pow(a, b)
        | Expr::Range(a, b) => is_expr_smt_compatible(a) && is_expr_smt_compatible(b),
        Expr::Neg(a) => is_expr_smt_compatible(a),

        // === SMT-compatible control ===
        Expr::If(c, t, e) => {
            is_expr_smt_compatible(c) && is_expr_smt_compatible(t) && is_expr_smt_compatible(e)
        }
        Expr::Case(arms, other) => {
            arms.iter()
                .all(|arm| is_expr_smt_compatible(&arm.guard) && is_expr_smt_compatible(&arm.body))
                && other.as_ref().map_or(true, |o| is_expr_smt_compatible(o))
        }
        Expr::Let(defs, body) => {
            defs.iter().all(|d| is_expr_smt_compatible(&d.body)) && is_expr_smt_compatible(body)
        }

        // === SMT-compatible actions/temporal ===
        Expr::Prime(a) | Expr::Unchanged(a) => is_expr_smt_compatible(a),

        // === SMT-compatible: record/tuple (any size — z4 has RecordEncoder) ===
        Expr::RecordAccess(a, _) => is_expr_smt_compatible(a),
        Expr::Record(fields) => fields.iter().all(|(_, v)| is_expr_smt_compatible(v)),
        Expr::Tuple(elems) => elems.iter().all(is_expr_smt_compatible),

        // === SMT-compatible: function application (array read) ===
        Expr::FuncApply(f, arg) => is_expr_smt_compatible(f) && is_expr_smt_compatible(arg),
        Expr::Except(f, specs) => {
            is_expr_smt_compatible(f)
                && specs.iter().all(|s| {
                    s.path.iter().all(|elem| match elem {
                        tla_core::ast::ExceptPathElement::Index(idx) => is_expr_smt_compatible(idx),
                        tla_core::ast::ExceptPathElement::Field(_) => true,
                    }) && is_expr_smt_compatible(&s.value)
                })
        }
        Expr::Domain(a) => is_expr_smt_compatible(a),

        // === SMT-compatible: operator application (recurse into args) ===
        Expr::Apply(op, args) => {
            is_expr_smt_compatible(op) && args.iter().all(is_expr_smt_compatible)
        }
        Expr::ModuleRef(_, _, args) => args.iter().all(is_expr_smt_compatible),
        Expr::SubstIn(_, body) => is_expr_smt_compatible(body),
        Expr::Label(label) => is_expr_smt_compatible(&label.body),

        // === SMT-compatible: bounded quantifiers over SMT-compatible domains ===
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            bounds.iter().all(|b| {
                b.domain
                    .as_ref()
                    .map_or(false, |d| is_expr_smt_compatible(d))
            }) && is_expr_smt_compatible(body)
        }

        // === SMT-compatible: finite set constructs (z4 has encoders) ===
        // SetEnum {1,2,3} — finite, encoded as (Array Int Bool) disjunction
        Expr::SetEnum(elems) => elems.iter().all(is_expr_smt_compatible),
        // x \in S, x \notin S — membership test, z4 array lookup
        Expr::In(a, b) | Expr::NotIn(a, b) => {
            is_expr_smt_compatible(a) && is_expr_smt_compatible(b)
        }
        // S \subseteq T — z4 forall encoding
        Expr::Subseteq(a, b) => is_expr_smt_compatible(a) && is_expr_smt_compatible(b),
        // S \cup T, S \cap T, S \ T — z4 array ops
        Expr::Union(a, b) | Expr::Intersect(a, b) | Expr::SetMinus(a, b) => {
            is_expr_smt_compatible(a) && is_expr_smt_compatible(b)
        }
        // {x \in S : P(x)} — z4 filtered set encoding
        Expr::SetFilter(bound, body) => {
            bound
                .domain
                .as_ref()
                .map_or(false, |d| is_expr_smt_compatible(d))
                && is_expr_smt_compatible(body)
        }
        // [x \in S |-> e] — z4 FunctionEncoder (1056 LOC)
        Expr::FuncDef(bounds, body) => {
            bounds.iter().all(|b| {
                b.domain
                    .as_ref()
                    .map_or(false, |d| is_expr_smt_compatible(d))
            }) && is_expr_smt_compatible(body)
        }
        // [S -> T] — z4 function set encoding
        Expr::FuncSet(a, b) => is_expr_smt_compatible(a) && is_expr_smt_compatible(b),
        // [a : S, b : T] — z4 RecordEncoder (414 LOC)
        Expr::RecordSet(fields) => fields.iter().all(|(_, v)| is_expr_smt_compatible(v)),
        // S \X T — Cartesian product, z4 tuple encoding
        Expr::Times(sets) => sets.iter().all(is_expr_smt_compatible),

        // === SMT-compatible: powerset + big union for finite sets ===
        // SUBSET S — for finite base sets, the BMC translator enumerates
        // all 2^n subsets or uses symbolic subset constraints.
        Expr::Powerset(inner) => is_expr_smt_compatible(inner),
        // UNION S — big union. The BMC translator handles this via
        // translate_big_union_bool (compound_dispatch.rs) when the inner
        // expression is SMT-compatible (e.g., UNION {S1, S2, ...}).
        // Part of #3778: Apalache parity — BigUnion in BMC.
        Expr::BigUnion(inner) => is_expr_smt_compatible(inner),
        // === SMT-compatible: bounded CHOOSE (z4 Skolemization) ===
        // CHOOSE x \in S : P(x) -- translated via Skolem constants in z4.
        // Both CHC translator (translate/quantifier.rs) and BMC translator
        // (bmc/translate_bmc.rs) handle bounded CHOOSE for SetEnum, Range,
        // BOOLEAN, and SetFilter domains.
        // Only accepted when domain is present and both domain + body are
        // SMT-compatible. Unbounded CHOOSE (no domain) is rejected.
        // Part of #3954.
        Expr::Choose(bound, body) => {
            bound
                .domain
                .as_ref()
                .map_or(false, |d| is_expr_smt_compatible(d))
                && is_expr_smt_compatible(body)
        }

        // === SMT-compatible: bounded SetBuilder (z4 quantifier expansion) ===
        // {e : x \in S} -- translated via membership rewriting in z4:
        //   elem \in {f(x) : x \in S} => \E x \in S : elem = f(x)
        // Both CHC translator (chc/translation.rs) and membership translator
        // (translate/membership/mod.rs) handle this pattern.
        // Only accepted when all bounds have domains and both body + domains
        // are SMT-compatible.
        // Part of #3954.
        Expr::SetBuilder(body, bounds) => {
            bounds.iter().all(|b| {
                b.domain
                    .as_ref()
                    .map_or(false, |d| is_expr_smt_compatible(d))
            }) && is_expr_smt_compatible(body)
        }

        // === SMT-INCOMPATIBLE: Lambda, higher-order ===
        Expr::Lambda(_, _) | Expr::OpRef(_) => false,

        // === SMT-INCOMPATIBLE: Temporal operators (not action-level) ===
        Expr::Always(_)
        | Expr::Eventually(_)
        | Expr::LeadsTo(_, _)
        | Expr::WeakFair(_, _)
        | Expr::StrongFair(_, _)
        | Expr::Enabled(_) => false,

        // === SMT-INCOMPATIBLE: Instance expressions ===
        Expr::InstanceExpr(_, _) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::Span;

    #[test]
    fn test_smt_compatibility_bool_int_expr() {
        let span = Span::dummy();

        // x + 1 > 0 should be SMT-compatible
        let expr = Spanned::new(
            Expr::Gt(
                Box::new(Spanned::new(
                    Expr::Add(
                        Box::new(Spanned::new(
                            Expr::Ident("x".to_string(), tla_core::NameId::INVALID),
                            span,
                        )),
                        Box::new(Spanned::new(Expr::Int(1.into()), span)),
                    ),
                    span,
                )),
                Box::new(Spanned::new(Expr::Int(0.into()), span)),
            ),
            span,
        );
        assert!(
            is_expr_smt_compatible(&expr),
            "x + 1 > 0 should be SMT-compatible"
        );
    }

    #[test]
    fn test_smt_compatibility_finite_set_operations() {
        let span = Span::dummy();

        // {1, 2, 3} -- finite set enumeration IS SMT-compatible (#3954)
        let set_enum = Spanned::new(
            Expr::SetEnum(vec![
                Spanned::new(Expr::Int(1.into()), span),
                Spanned::new(Expr::Int(2.into()), span),
                Spanned::new(Expr::Int(3.into()), span),
            ]),
            span,
        );
        assert!(
            is_expr_smt_compatible(&set_enum),
            "SetEnum should be SMT-compatible (finite, z4 Array encoding)"
        );

        // x \in S -- membership IS SMT-compatible (#3954)
        let membership = Spanned::new(
            Expr::In(
                Box::new(Spanned::new(
                    Expr::Ident("x".to_string(), tla_core::NameId::INVALID),
                    span,
                )),
                Box::new(Spanned::new(
                    Expr::Ident("S".to_string(), tla_core::NameId::INVALID),
                    span,
                )),
            ),
            span,
        );
        assert!(
            is_expr_smt_compatible(&membership),
            "x \\in S should be SMT-compatible (z4 array select)"
        );

        // SUBSET S -- Powerset IS SMT-compatible (z4 powerset encoder)
        let powerset = Spanned::new(
            Expr::Powerset(Box::new(Spanned::new(
                Expr::Ident("S".to_string(), tla_core::NameId::INVALID),
                span,
            ))),
            span,
        );
        assert!(
            is_expr_smt_compatible(&powerset),
            "SUBSET S should be SMT-compatible (z4 powerset encoder)"
        );
    }

    #[test]
    fn test_smt_compatibility_bounded_choose_compatible() {
        use tla_core::ast::BoundVar;
        let span = Span::dummy();

        // CHOOSE x \in S : P(x) -- bounded CHOOSE IS compatible (#3954)
        // z4 translates via Skolemization (quantifier.rs, translate_bmc.rs)
        let choose = Spanned::new(
            Expr::Choose(
                BoundVar {
                    name: Spanned::new("x".to_string(), span),
                    domain: Some(Box::new(Spanned::new(
                        Expr::Ident("S".to_string(), tla_core::NameId::INVALID),
                        span,
                    ))),
                    pattern: None,
                },
                Box::new(Spanned::new(Expr::Bool(true), span)),
            ),
            span,
        );
        assert!(
            is_expr_smt_compatible(&choose),
            "Bounded CHOOSE should be SMT-compatible (z4 Skolemization)"
        );
    }

    #[test]
    fn test_smt_compatibility_unbounded_choose_incompatible() {
        use tla_core::ast::BoundVar;
        let span = Span::dummy();

        // CHOOSE x : P(x) -- unbounded CHOOSE (no domain) is incompatible
        let choose = Spanned::new(
            Expr::Choose(
                BoundVar {
                    name: Spanned::new("x".to_string(), span),
                    domain: None,
                    pattern: None,
                },
                Box::new(Spanned::new(Expr::Bool(true), span)),
            ),
            span,
        );
        assert!(
            !is_expr_smt_compatible(&choose),
            "Unbounded CHOOSE (no domain) should be SMT-incompatible"
        );
    }

    #[test]
    fn test_smt_compatibility_choose_with_incompatible_body() {
        use tla_core::ast::BoundVar;
        let span = Span::dummy();

        // CHOOSE x \in S : ENABLED(y) -- body contains temporal operator
        let choose = Spanned::new(
            Expr::Choose(
                BoundVar {
                    name: Spanned::new("x".to_string(), span),
                    domain: Some(Box::new(Spanned::new(
                        Expr::Ident("S".to_string(), tla_core::NameId::INVALID),
                        span,
                    ))),
                    pattern: None,
                },
                Box::new(Spanned::new(
                    Expr::Enabled(Box::new(Spanned::new(
                        Expr::Ident("y".to_string(), tla_core::NameId::INVALID),
                        span,
                    ))),
                    span,
                )),
            ),
            span,
        );
        assert!(
            !is_expr_smt_compatible(&choose),
            "CHOOSE with incompatible body should be SMT-incompatible"
        );
    }

    #[test]
    fn test_smt_compatibility_if_then_else() {
        let span = Span::dummy();

        // IF x > 0 THEN x ELSE -x -- SMT-compatible
        let ite = Spanned::new(
            Expr::If(
                Box::new(Spanned::new(
                    Expr::Gt(
                        Box::new(Spanned::new(
                            Expr::Ident("x".to_string(), tla_core::NameId::INVALID),
                            span,
                        )),
                        Box::new(Spanned::new(Expr::Int(0.into()), span)),
                    ),
                    span,
                )),
                Box::new(Spanned::new(
                    Expr::Ident("x".to_string(), tla_core::NameId::INVALID),
                    span,
                )),
                Box::new(Spanned::new(
                    Expr::Neg(Box::new(Spanned::new(
                        Expr::Ident("x".to_string(), tla_core::NameId::INVALID),
                        span,
                    ))),
                    span,
                )),
            ),
            span,
        );
        assert!(
            is_expr_smt_compatible(&ite),
            "IF x > 0 THEN x ELSE -x should be SMT-compatible"
        );
    }

    #[test]
    fn test_smt_compatibility_mixed_set_inside_logic() {
        let span = Span::dummy();

        // x > 0 /\ y \in S -- NOW compatible (#3954: \in accepted)
        let mixed = Spanned::new(
            Expr::And(
                Box::new(Spanned::new(
                    Expr::Gt(
                        Box::new(Spanned::new(
                            Expr::Ident("x".to_string(), tla_core::NameId::INVALID),
                            span,
                        )),
                        Box::new(Spanned::new(Expr::Int(0.into()), span)),
                    ),
                    span,
                )),
                Box::new(Spanned::new(
                    Expr::In(
                        Box::new(Spanned::new(
                            Expr::Ident("y".to_string(), tla_core::NameId::INVALID),
                            span,
                        )),
                        Box::new(Spanned::new(
                            Expr::Ident("S".to_string(), tla_core::NameId::INVALID),
                            span,
                        )),
                    ),
                    span,
                )),
            ),
            span,
        );
        assert!(
            is_expr_smt_compatible(&mixed),
            "x > 0 /\\ y \\in S should be SMT-compatible (#3954)"
        );
    }

    #[test]
    fn test_smt_compatibility_bounded_set_builder_compatible() {
        use tla_core::ast::BoundVar;
        let span = Span::dummy();

        // {e : x \in S} with bounded set builder -- IS compatible (#3954)
        // z4 translates via quantifier expansion (membership rewriting)
        let set_builder = Spanned::new(
            Expr::SetBuilder(
                Box::new(Spanned::new(Expr::Bool(true), span)),
                vec![BoundVar {
                    name: Spanned::new("x".to_string(), span),
                    domain: Some(Box::new(Spanned::new(
                        Expr::Ident("S".to_string(), tla_core::NameId::INVALID),
                        span,
                    ))),
                    pattern: None,
                }],
            ),
            span,
        );
        assert!(
            is_expr_smt_compatible(&set_builder),
            "Bounded SetBuilder should be SMT-compatible (z4 quantifier expansion)"
        );
    }

    #[test]
    fn test_smt_compatibility_unbounded_set_builder_incompatible() {
        use tla_core::ast::BoundVar;
        let span = Span::dummy();

        // {e : x} -- unbounded set builder (no domain) is incompatible
        let set_builder = Spanned::new(
            Expr::SetBuilder(
                Box::new(Spanned::new(Expr::Bool(true), span)),
                vec![BoundVar {
                    name: Spanned::new("x".to_string(), span),
                    domain: None,
                    pattern: None,
                }],
            ),
            span,
        );
        assert!(
            !is_expr_smt_compatible(&set_builder),
            "Unbounded SetBuilder (no domain) should be SMT-incompatible"
        );
    }

    #[test]
    fn test_smt_compatibility_set_builder_with_incompatible_body() {
        use tla_core::ast::BoundVar;
        let span = Span::dummy();

        // {ENABLED(x) : x \in S} -- body contains temporal operator
        let set_builder = Spanned::new(
            Expr::SetBuilder(
                Box::new(Spanned::new(
                    Expr::Enabled(Box::new(Spanned::new(
                        Expr::Ident("x".to_string(), tla_core::NameId::INVALID),
                        span,
                    ))),
                    span,
                )),
                vec![BoundVar {
                    name: Spanned::new("x".to_string(), span),
                    domain: Some(Box::new(Spanned::new(
                        Expr::Ident("S".to_string(), tla_core::NameId::INVALID),
                        span,
                    ))),
                    pattern: None,
                }],
            ),
            span,
        );
        assert!(
            !is_expr_smt_compatible(&set_builder),
            "SetBuilder with incompatible body should be SMT-incompatible"
        );
    }

    #[test]
    fn test_smt_compatibility_big_union_smt_compatible_inner() {
        let span = Span::dummy();

        // UNION {S1, S2} where S1 and S2 are identifiers (SMT-compatible)
        // — should now be accepted since BMC translator handles this via
        // translate_big_union_bool (Part of #3778).
        let big_union_compat = Spanned::new(
            Expr::BigUnion(Box::new(Spanned::new(
                Expr::SetEnum(vec![
                    Spanned::new(
                        Expr::Ident("S1".to_string(), tla_core::NameId::INVALID),
                        span,
                    ),
                    Spanned::new(
                        Expr::Ident("S2".to_string(), tla_core::NameId::INVALID),
                        span,
                    ),
                ]),
                span,
            ))),
            span,
        );
        assert!(
            is_expr_smt_compatible(&big_union_compat),
            "BigUnion with SMT-compatible inner should be accepted"
        );

        // UNION S where S is a simple identifier — also accepted
        let big_union_ident = Spanned::new(
            Expr::BigUnion(Box::new(Spanned::new(
                Expr::Ident("S".to_string(), tla_core::NameId::INVALID),
                span,
            ))),
            span,
        );
        assert!(
            is_expr_smt_compatible(&big_union_ident),
            "BigUnion over an identifier should be SMT-compatible"
        );
    }

    #[test]
    fn test_smt_compatibility_big_union_powerset_inner_compatible() {
        let span = Span::dummy();

        // UNION (SUBSET S) -- both BigUnion and Powerset are SMT-compatible
        // since z4 has encoders for both. Inner Powerset(S) is accepted
        // (powerset_encoder.rs), and BigUnion dispatches through
        // translate_big_union_bool (compound_dispatch.rs).
        let big_union_powerset = Spanned::new(
            Expr::BigUnion(Box::new(Spanned::new(
                Expr::Powerset(Box::new(Spanned::new(
                    Expr::Ident("S".to_string(), tla_core::NameId::INVALID),
                    span,
                ))),
                span,
            ))),
            span,
        );
        assert!(
            is_expr_smt_compatible(&big_union_powerset),
            "BigUnion over Powerset should be SMT-compatible"
        );
    }

    #[test]
    fn test_smt_compatibility_big_union_incompatible_inner() {
        let span = Span::dummy();

        // UNION (ENABLED(P)) -- inner is temporal operator, so BigUnion rejected
        let big_union_temporal = Spanned::new(
            Expr::BigUnion(Box::new(Spanned::new(
                Expr::Enabled(Box::new(Spanned::new(
                    Expr::Ident("P".to_string(), tla_core::NameId::INVALID),
                    span,
                ))),
                span,
            ))),
            span,
        );
        assert!(
            !is_expr_smt_compatible(&big_union_temporal),
            "BigUnion over temporal operator should be SMT-incompatible"
        );
    }

    #[test]
    fn test_smt_compatibility_lambda_still_rejected() {
        let span = Span::dummy();

        // LAMBDA x : x + 1 -- higher-order, always rejected
        let lambda = Spanned::new(
            Expr::Lambda(
                vec![Spanned::new("x".to_string(), span)],
                Box::new(Spanned::new(
                    Expr::Add(
                        Box::new(Spanned::new(
                            Expr::Ident("x".to_string(), tla_core::NameId::INVALID),
                            span,
                        )),
                        Box::new(Spanned::new(Expr::Int(1.into()), span)),
                    ),
                    span,
                )),
            ),
            span,
        );
        assert!(
            !is_expr_smt_compatible(&lambda),
            "Lambda should be SMT-incompatible (higher-order)"
        );
    }

    #[test]
    fn test_smt_compatibility_temporal_still_rejected() {
        let span = Span::dummy();

        // ENABLED(x) -- temporal, always rejected
        let enabled = Spanned::new(
            Expr::Enabled(Box::new(Spanned::new(
                Expr::Ident("x".to_string(), tla_core::NameId::INVALID),
                span,
            ))),
            span,
        );
        assert!(
            !is_expr_smt_compatible(&enabled),
            "ENABLED should be SMT-incompatible (temporal)"
        );

        // []P -- temporal, always rejected
        let always = Spanned::new(
            Expr::Always(Box::new(Spanned::new(
                Expr::Ident("P".to_string(), tla_core::NameId::INVALID),
                span,
            ))),
            span,
        );
        assert!(
            !is_expr_smt_compatible(&always),
            "Always should be SMT-incompatible (temporal)"
        );
    }
}
