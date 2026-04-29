// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Translation from Quint IR types to TLA2 AST nodes.
//!
//! The Quint IR uses a flat expression representation with opcodes for built-in
//! operators. This module maps each Quint opcode to the corresponding TLA2
//! `Expr` variant, producing a complete `Module` from a `QuintModule`.

use std::cell::RefCell;
use std::collections::HashSet;

use crate::ast::{
    AssumeDecl, BoundVar, ConstantDecl, ExceptPathElement, ExceptSpec, Expr, ExprLabel,
    InstanceDecl, Module, OpParam, OperatorDef, RecordFieldName, Substitution, Unit,
};
use crate::name_intern::NameId;
use crate::span::{Span, Spanned};

use super::ir::{QuintDeclaration, QuintDef, QuintExpr, QuintModule, QuintParam};
use super::QuintError;

// Thread-local set of stdlib modules referenced during translation.
// Populated by `translate_app` when it encounters opcodes that map to
// TLA+ standard library operators (e.g., `Append` -> Sequences module).
thread_local! {
    static REQUIRED_EXTENDS: RefCell<HashSet<&'static str>> = RefCell::new(HashSet::new());
}

/// Record that a standard library module is needed by the translated spec.
fn require_extends(module: &'static str) {
    REQUIRED_EXTENDS.with(|r| {
        r.borrow_mut().insert(module);
    });
}

/// Drain and return the set of required standard library modules.
fn take_required_extends() -> HashSet<&'static str> {
    REQUIRED_EXTENDS.with(|r| std::mem::take(&mut *r.borrow_mut()))
}

/// Translate a `QuintModule` into a TLA2 `Module`.
///
/// Two-pass process: first translate all declarations, then analyze which
/// TLA+ standard library modules are referenced and inject EXTENDS.
pub(crate) fn translate_module(qmod: &QuintModule) -> Result<Module, QuintError> {
    // Clear any leftover state from a previous translation.
    take_required_extends();

    let mut units = Vec::new();

    for decl in &qmod.declarations {
        match decl {
            QuintDeclaration::Var(v) => {
                units.push(spanned(Unit::Variable(vec![spanned_str(&v.name)])));
            }
            QuintDeclaration::Const(c) => {
                units.push(spanned(Unit::Constant(vec![ConstantDecl {
                    name: spanned_str(&c.name),
                    arity: None,
                }])));
            }
            QuintDeclaration::Def(def) => {
                let op = translate_def(def)?;
                units.push(spanned(Unit::Operator(op)));
            }
            QuintDeclaration::Assume(a) => {
                let expr = translate_expr(&a.assumption)?;
                units.push(spanned(Unit::Assume(AssumeDecl {
                    name: Some(spanned_str(&a.name)),
                    expr,
                })));
            }
            QuintDeclaration::Instance(inst) => {
                let substitutions = inst
                    .overrides
                    .iter()
                    .map(|(name, expr)| {
                        let to = translate_expr(expr)?;
                        Ok(Substitution {
                            from: spanned_str(name),
                            to,
                        })
                    })
                    .collect::<Result<Vec<_>, QuintError>>()?;
                units.push(spanned(Unit::Instance(InstanceDecl {
                    module: spanned_str(&inst.proto_name),
                    substitutions,
                    local: false,
                })));
            }
            // TypeDef, Import, Export have no direct TLA+ AST equivalent; skip.
            QuintDeclaration::TypeDef(_)
            | QuintDeclaration::Import(_)
            | QuintDeclaration::Export(_) => {}
        }
    }

    // Collect stdlib modules referenced during translation and add EXTENDS.
    // Always include Integers (Quint uses integer arithmetic pervasively).
    require_extends("Integers");
    let required = take_required_extends();
    // Stable ordering for deterministic output.
    let mut extends: Vec<Spanned<String>> = required.iter().map(|m| spanned_str(m)).collect();
    extends.sort_by(|a, b| a.node.cmp(&b.node));

    Ok(Module {
        name: spanned_str(&qmod.name),
        extends,
        units,
        action_subscript_spans: Default::default(),
        span: Span::dummy(),
    })
}

/// Translate a Quint definition into a TLA2 `OperatorDef`.
fn translate_def(def: &QuintDef) -> Result<OperatorDef, QuintError> {
    let params = def
        .params
        .iter()
        .map(|p| OpParam {
            name: spanned_str(&p.name),
            arity: 0,
        })
        .collect();
    let body = translate_expr(&def.expr)?;

    Ok(OperatorDef {
        name: translate_label_name(&def.name),
        params,
        body,
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    })
}

/// Translate a Quint expression into a TLA2 `Spanned<Expr>`.
pub(crate) fn translate_expr(qexpr: &QuintExpr) -> Result<Spanned<Expr>, QuintError> {
    match qexpr {
        QuintExpr::Bool(b) => Ok(spanned(Expr::Bool(b.value))),
        QuintExpr::Int(i) => Ok(spanned(Expr::Int(i.value.into()))),
        QuintExpr::Str(s) => Ok(spanned(Expr::String(s.value.clone()))),
        QuintExpr::Name(n) => Ok(spanned(Expr::Ident(n.name.clone(), NameId::INVALID))),
        QuintExpr::App(app) => translate_app(&app.opcode, &app.args),
        QuintExpr::Lambda(lam) => {
            let params: Vec<Spanned<String>> =
                lam.params.iter().map(|p| spanned_str(&p.name)).collect();
            let body = translate_expr(&lam.expr)?;
            Ok(spanned(Expr::Lambda(params, Box::new(body))))
        }
        QuintExpr::Let(let_expr) => {
            let op = translate_def(&let_expr.opdef)?;
            let body = translate_expr(&let_expr.expr)?;
            Ok(spanned(Expr::Let(vec![op], Box::new(body))))
        }
    }
}

/// Translate a Quint application node by mapping its opcode.
fn translate_app(opcode: &str, args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    match opcode {
        // === Boolean operators ===
        "and" | "iff_and" => binary_op(args, |l, r| Expr::And(bx(l), bx(r))),
        "or" | "iff_or" => binary_op(args, |l, r| Expr::Or(bx(l), bx(r))),
        "not" => unary_op(args, |e| Expr::Not(bx(e))),
        "implies" | "iff_implies" => binary_op(args, |l, r| Expr::Implies(bx(l), bx(r))),
        "iff" => binary_op(args, |l, r| Expr::Equiv(bx(l), bx(r))),

        // === Comparison ===
        "eq" | "ieq" => binary_op(args, |l, r| Expr::Eq(bx(l), bx(r))),
        "neq" | "ineq" => binary_op(args, |l, r| Expr::Neq(bx(l), bx(r))),
        "lt" | "ilt" => binary_op(args, |l, r| Expr::Lt(bx(l), bx(r))),
        "lte" | "ilte" => binary_op(args, |l, r| Expr::Leq(bx(l), bx(r))),
        "gt" | "igt" => binary_op(args, |l, r| Expr::Gt(bx(l), bx(r))),
        "gte" | "igte" => binary_op(args, |l, r| Expr::Geq(bx(l), bx(r))),

        // === Arithmetic ===
        "iadd" => binary_op(args, |l, r| Expr::Add(bx(l), bx(r))),
        "isub" => binary_op(args, |l, r| Expr::Sub(bx(l), bx(r))),
        "imul" => binary_op(args, |l, r| Expr::Mul(bx(l), bx(r))),
        "idiv" => binary_op(args, |l, r| Expr::IntDiv(bx(l), bx(r))),
        "imod" => binary_op(args, |l, r| Expr::Mod(bx(l), bx(r))),
        "ipow" => binary_op(args, |l, r| Expr::Pow(bx(l), bx(r))),
        "iuminus" => unary_op(args, |e| Expr::Neg(bx(e))),

        // === Sets ===
        "Set" => {
            let elems = args
                .iter()
                .map(translate_expr)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(spanned(Expr::SetEnum(elems)))
        }
        "in" => binary_op(args, |l, r| Expr::In(bx(l), bx(r))),
        "notin" => binary_op(args, |l, r| Expr::NotIn(bx(l), bx(r))),
        "subseteq" => binary_op(args, |l, r| Expr::Subseteq(bx(l), bx(r))),
        "union" => binary_op(args, |l, r| Expr::Union(bx(l), bx(r))),
        "intersect" => binary_op(args, |l, r| Expr::Intersect(bx(l), bx(r))),
        "exclude" => binary_op(args, |l, r| Expr::SetMinus(bx(l), bx(r))),
        "powerset" | "SUBSET" => unary_op(args, |e| Expr::Powerset(bx(e))),
        "flatten" | "UNION" => unary_op(args, |e| Expr::BigUnion(bx(e))),
        "filter" => translate_quantifier_op(args, |bv, body| Expr::SetFilter(bv, bx(body))),
        "map" => translate_set_map(args),
        "chooseSome" | "CHOOSE" => translate_choose(args),
        "to" => binary_op(args, |l, r| Expr::Range(bx(l), bx(r))),

        // === Quantifiers ===
        "forall" => translate_quantifier_op(args, |bv, body| Expr::Forall(vec![bv], bx(body))),
        "exists" => translate_quantifier_op(args, |bv, body| Expr::Exists(vec![bv], bx(body))),

        // === Tuples ===
        "Tup" => {
            let elems = args
                .iter()
                .map(translate_expr)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(spanned(Expr::Tuple(elems)))
        }
        "tuples" | "cross" => {
            let elems = args
                .iter()
                .map(translate_expr)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(spanned(Expr::Times(elems)))
        }

        // === Records ===
        "Rec" => translate_record(args),
        "field" => translate_field_access(args),
        "with" => translate_record_with(args),

        // === Functions ===
        "setFunConst" | "funConst" => translate_func_def(args),
        "get" | "of" => translate_func_apply(args),
        "setOfFuns" | "funSet" => binary_op(args, |l, r| Expr::FuncSet(bx(l), bx(r))),
        "DOMAIN" => unary_op(args, |e| Expr::Domain(bx(e))),

        // === Sequences (map to TLA+ Sequences module operators) ===
        "append" | "Append" => {
            require_extends("Sequences");
            stdlib_apply("Append", args)
        }
        "concat" | "Concat" => {
            // Quint concat(s, t) -> s \o t (TLA+ sequence concatenation).
            require_extends("Sequences");
            stdlib_apply("Concat", args)
        }
        "head" | "Head" => {
            require_extends("Sequences");
            stdlib_apply("Head", args)
        }
        "tail" | "Tail" => {
            require_extends("Sequences");
            stdlib_apply("Tail", args)
        }
        "length" | "Len" => {
            require_extends("Sequences");
            stdlib_apply("Len", args)
        }
        "nth" => {
            // Quint nth(seq, idx): seq[idx + 1] (0-based to 1-based).
            ensure_arity("nth", args, 2)?;
            let seq = translate_expr(&args[0])?;
            let idx = translate_expr(&args[1])?;
            let one = spanned(Expr::Int(1.into()));
            let adjusted = spanned(Expr::Add(bx(idx), bx(one)));
            Ok(spanned(Expr::FuncApply(bx(seq), bx(adjusted))))
        }
        "replaceAt" => {
            // Quint replaceAt(seq, idx, val): [seq EXCEPT ![idx + 1] = val].
            ensure_arity("replaceAt", args, 3)?;
            let seq = translate_expr(&args[0])?;
            let idx = translate_expr(&args[1])?;
            let val = translate_expr(&args[2])?;
            let one = spanned(Expr::Int(1.into()));
            let adjusted = spanned(Expr::Add(bx(idx), bx(one)));
            Ok(spanned(Expr::Except(
                bx(seq),
                vec![ExceptSpec {
                    path: vec![ExceptPathElement::Index(adjusted)],
                    value: val,
                }],
            )))
        }
        "slice" => {
            // Quint slice(seq, from, to): SubSeq(seq, from+1, to).
            require_extends("Sequences");
            ensure_arity("slice", args, 3)?;
            let seq = translate_expr(&args[0])?;
            let from = translate_expr(&args[1])?;
            let to = translate_expr(&args[2])?;
            let one = spanned(Expr::Int(1.into()));
            let from_adj = spanned(Expr::Add(bx(from), bx(one)));
            let subseq = spanned(Expr::Ident("SubSeq".to_string(), NameId::INVALID));
            Ok(spanned(Expr::Apply(bx(subseq), vec![seq, from_adj, to])))
        }
        "SubSeq" => {
            require_extends("Sequences");
            stdlib_apply("SubSeq", args)
        }
        "select" | "SelectSeq" => {
            require_extends("Sequences");
            stdlib_apply("SelectSeq", args)
        }
        "foldl" => translate_foldl(args),
        "foldr" => translate_foldr(args),
        "range" => {
            // Quint range(n): <<0, 1, ..., n-1>> as a TLA+ function.
            ensure_arity("range", args, 1)?;
            let n = translate_expr(&args[0])?;
            let zero = spanned(Expr::Int(0.into()));
            let one = spanned(Expr::Int(1.into()));
            let upper = spanned(Expr::Sub(bx(n), bx(one)));
            let domain = spanned(Expr::Range(bx(zero), bx(upper)));
            let bv = BoundVar {
                name: spanned_str("__i"),
                domain: Some(bx(domain)),
                pattern: None,
            };
            let body = spanned(Expr::Ident("__i".to_string(), NameId::INVALID));
            Ok(spanned(Expr::FuncDef(vec![bv], bx(body))))
        }

        // === Set cardinality (FiniteSets module) ===
        "size" | "Cardinality" => {
            require_extends("FiniteSets");
            stdlib_apply("Cardinality", args)
        }
        "isFinite" | "IsFiniteSet" => {
            require_extends("FiniteSets");
            stdlib_apply("IsFiniteSet", args)
        }

        // === Type constants ===
        "Nat" if args.is_empty() => {
            require_extends("Naturals");
            Ok(spanned(Expr::Ident("Nat".to_string(), NameId::INVALID)))
        }
        "Int" if args.is_empty() => Ok(spanned(Expr::Ident("Int".to_string(), NameId::INVALID))),
        "Bool" if args.is_empty() => {
            Ok(spanned(Expr::Ident("BOOLEAN".to_string(), NameId::INVALID)))
        }
        "String" if args.is_empty() => {
            Ok(spanned(Expr::Ident("STRING".to_string(), NameId::INVALID)))
        }

        // === Nondet ===
        "oneOf" => {
            // Quint S.oneOf(): nondeterministic choice -> CHOOSE x \in S : TRUE.
            ensure_arity("oneOf", args, 1)?;
            let domain = translate_expr(&args[0])?;
            let bv = BoundVar {
                name: spanned_str("__chosen"),
                domain: Some(bx(domain)),
                pattern: None,
            };
            Ok(spanned(Expr::Choose(bv, bx(spanned(Expr::Bool(true))))))
        }

        // === Map/function operations ===
        "keys" => unary_op(args, |e| Expr::Domain(bx(e))),
        "mapBy" => translate_func_def(args),
        "setOfMaps" => binary_op(args, |l, r| Expr::FuncSet(bx(l), bx(r))),
        "put" | "setBy" => {
            // Quint put(map, key, val): [map EXCEPT ![key] = val].
            ensure_arity(opcode, args, 3)?;
            let map = translate_expr(&args[0])?;
            let key = translate_expr(&args[1])?;
            let val = translate_expr(&args[2])?;
            Ok(spanned(Expr::Except(
                bx(map),
                vec![ExceptSpec {
                    path: vec![ExceptPathElement::Index(key)],
                    value: val,
                }],
            )))
        }

        // === Record set ===
        "RecordSet" | "setOfRecs" => translate_record_set(args),

        // === Temporal ===
        "prime" | "next" => unary_op(args, |e| Expr::Prime(bx(e))),
        "always" => unary_op(args, |e| Expr::Always(bx(e))),
        "eventually" => unary_op(args, |e| Expr::Eventually(bx(e))),
        "ENABLED" => unary_op(args, |e| Expr::Enabled(bx(e))),
        "UNCHANGED" => unary_op(args, |e| Expr::Unchanged(bx(e))),
        "weakFair" => binary_op(args, |l, r| Expr::WeakFair(bx(l), bx(r))),
        "strongFair" => binary_op(args, |l, r| Expr::StrongFair(bx(l), bx(r))),

        // === Control flow ===
        "ite" => {
            ensure_arity(opcode, args, 3)?;
            let cond = translate_expr(&args[0])?;
            let then_br = translate_expr(&args[1])?;
            let else_br = translate_expr(&args[2])?;
            Ok(spanned(Expr::If(bx(cond), bx(then_br), bx(else_br))))
        }

        // === Misc ===
        "assign" => {
            // Quint `x' = e` is `assign(x, e)`.
            // In TLA+, this is `x' = e`, i.e., Eq(Prime(x), e).
            ensure_arity(opcode, args, 2)?;
            let lhs = translate_expr(&args[0])?;
            let rhs = translate_expr(&args[1])?;
            let primed = spanned(Expr::Prime(bx(lhs)));
            Ok(spanned(Expr::Eq(bx(primed), bx(rhs))))
        }
        "actionAll" | "allOf" => nary_and(args),
        "actionAny" | "anyOf" => nary_or(args),
        "then" => binary_op(args, |l, r| Expr::And(bx(l), bx(r))),
        "expect" => {
            if args.len() == 1 {
                translate_expr(&args[0])
            } else {
                binary_op(args, |l, r| Expr::And(bx(l), bx(r)))
            }
        }
        // Quint assert: treated as identity (the expression itself).
        "assert" => {
            if args.len() == 1 {
                translate_expr(&args[0])
            } else {
                fallback_apply(opcode, args)
            }
        }

        // === Labels ===
        "label" => translate_label(args),

        // === Fallback: user-defined operator application ===
        _ => fallback_apply(opcode, args),
    }
}

// === Helper functions ===

/// Translate a quantifier-style operation: `set.forall(x => body)`.
/// Quint encodes this as `app("forall", [set, lambda([x], body)])`.
fn translate_quantifier_op(
    args: &[QuintExpr],
    make: impl FnOnce(BoundVar, Spanned<Expr>) -> Expr,
) -> Result<Spanned<Expr>, QuintError> {
    ensure_arity("quantifier", args, 2)?;
    let domain = translate_expr(&args[0])?;
    match &args[1] {
        QuintExpr::Lambda(lam) if !lam.params.is_empty() => {
            let bv = BoundVar {
                name: spanned_str(&lam.params[0].name),
                domain: Some(Box::new(domain)),
                pattern: None,
            };
            let body = translate_expr(&lam.expr)?;
            Ok(spanned(make(bv, body)))
        }
        _ => Err(QuintError::Translation(
            "expected lambda as second argument to quantifier".to_string(),
        )),
    }
}

/// Translate `set.map(x => expr)` -> `SetBuilder(expr, [x \in set])`.
fn translate_set_map(args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    ensure_arity("map", args, 2)?;
    let domain = translate_expr(&args[0])?;
    match &args[1] {
        QuintExpr::Lambda(lam) if !lam.params.is_empty() => {
            let bv = BoundVar {
                name: spanned_str(&lam.params[0].name),
                domain: Some(Box::new(domain)),
                pattern: None,
            };
            let body = translate_expr(&lam.expr)?;
            Ok(spanned(Expr::SetBuilder(Box::new(body), vec![bv])))
        }
        _ => Err(QuintError::Translation(
            "expected lambda as second argument to map".to_string(),
        )),
    }
}

/// Translate CHOOSE: `set.chooseSome()` or `CHOOSE(set, lambda)`.
fn translate_choose(args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    if args.len() == 2 {
        // CHOOSE x \in S : P(x)
        let domain = translate_expr(&args[0])?;
        match &args[1] {
            QuintExpr::Lambda(lam) if !lam.params.is_empty() => {
                let bv = BoundVar {
                    name: spanned_str(&lam.params[0].name),
                    domain: Some(Box::new(domain)),
                    pattern: None,
                };
                let body = translate_expr(&lam.expr)?;
                Ok(spanned(Expr::Choose(bv, Box::new(body))))
            }
            _ => Err(QuintError::Translation(
                "expected lambda as second argument to CHOOSE".to_string(),
            )),
        }
    } else if args.len() == 1 {
        // CHOOSE x \in S : TRUE
        let domain = translate_expr(&args[0])?;
        let bv = BoundVar {
            name: spanned_str("__chosen"),
            domain: Some(Box::new(domain)),
            pattern: None,
        };
        Ok(spanned(Expr::Choose(
            bv,
            Box::new(spanned(Expr::Bool(true))),
        )))
    } else {
        Err(QuintError::Translation(format!(
            "CHOOSE expects 1 or 2 arguments, got {}",
            args.len()
        )))
    }
}

/// Translate `Rec("a", v1, "b", v2)` -> `[a |-> v1, b |-> v2]`.
fn translate_record(args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    if args.len() % 2 != 0 {
        return Err(QuintError::Translation(
            "Rec expects an even number of arguments (key-value pairs)".to_string(),
        ));
    }
    let mut fields = Vec::new();
    for chunk in args.chunks(2) {
        let key = match &chunk[0] {
            QuintExpr::Str(s) => s.value.clone(),
            _ => {
                return Err(QuintError::Translation(
                    "Rec field name must be a string literal".to_string(),
                ))
            }
        };
        let val = translate_expr(&chunk[1])?;
        fields.push((spanned_str(&key), val));
    }
    Ok(spanned(Expr::Record(fields)))
}

/// Translate `field(rec, "f")` -> `rec.f`.
fn translate_field_access(args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    ensure_arity("field", args, 2)?;
    let rec = translate_expr(&args[0])?;
    let field_name = match &args[1] {
        QuintExpr::Str(s) => s.value.clone(),
        _ => {
            return Err(QuintError::Translation(
                "field name must be a string literal".to_string(),
            ))
        }
    };
    Ok(spanned(Expr::RecordAccess(
        Box::new(rec),
        RecordFieldName::new(spanned_str(&field_name)),
    )))
}

/// Translate `with(rec, "f", val)` -> `[rec EXCEPT !["f"] = val]`.
fn translate_record_with(args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    ensure_arity("with", args, 3)?;
    let rec = translate_expr(&args[0])?;
    let field_name = match &args[1] {
        QuintExpr::Str(s) => s.value.clone(),
        _ => {
            return Err(QuintError::Translation(
                "with field name must be a string literal".to_string(),
            ))
        }
    };
    let val = translate_expr(&args[2])?;
    let field_expr = spanned(Expr::String(field_name));
    Ok(spanned(Expr::Except(
        Box::new(rec),
        vec![ExceptSpec {
            path: vec![ExceptPathElement::Index(field_expr)],
            value: val,
        }],
    )))
}

/// Translate function definition: `setFunConst(domain, lambda)` -> `[x \in domain |-> body]`.
fn translate_func_def(args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    ensure_arity("funConst", args, 2)?;
    let domain = translate_expr(&args[0])?;
    match &args[1] {
        QuintExpr::Lambda(lam) if !lam.params.is_empty() => {
            let bv = BoundVar {
                name: spanned_str(&lam.params[0].name),
                domain: Some(Box::new(domain)),
                pattern: None,
            };
            let body = translate_expr(&lam.expr)?;
            Ok(spanned(Expr::FuncDef(vec![bv], Box::new(body))))
        }
        _ => Err(QuintError::Translation(
            "expected lambda as second argument to function definition".to_string(),
        )),
    }
}

/// Translate function application: `get(f, x)` -> `f[x]`.
fn translate_func_apply(args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    ensure_arity("get", args, 2)?;
    let func = translate_expr(&args[0])?;
    let arg = translate_expr(&args[1])?;
    Ok(spanned(Expr::FuncApply(Box::new(func), Box::new(arg))))
}

/// Translate `label("name", body)` -> `name:: body` (TLA+ label).
fn translate_label(args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    ensure_arity("label", args, 2)?;
    let name = match &args[0] {
        QuintExpr::Str(s) => s.value.clone(),
        _ => {
            return Err(QuintError::Translation(
                "label name must be a string literal".to_string(),
            ))
        }
    };
    // Strip the `__label_` prefix if present (Quint convention).
    let label_name = name.strip_prefix("__label_").unwrap_or(&name).to_string();
    let body = translate_expr(&args[1])?;
    Ok(spanned(Expr::Label(ExprLabel {
        name: spanned_str(&label_name),
        body: Box::new(body),
    })))
}

/// Translate `foldl(collection, init, lambda(acc, elem) => body)`.
///
/// Quint foldl applies a left fold over a sequence/set. There is no direct
/// TLA+ AST equivalent for general folds, so we emit as a user-defined
/// operator call (ApaFoldSeqLeft) that the evaluator can handle if defined.
fn translate_foldl(args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    fallback_apply("ApaFoldSeqLeft", args)
}

/// Translate `foldr(collection, init, lambda(elem, acc) => body)`.
/// Same strategy as foldl.
fn translate_foldr(args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    fallback_apply("ApaFoldSeqRight", args)
}

/// Translate `RecordSet("a", S, "b", T)` -> `[a : S, b : T]`.
fn translate_record_set(args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    if args.len() % 2 != 0 {
        return Err(QuintError::Translation(
            "RecordSet expects even number of arguments (key-domain pairs)".to_string(),
        ));
    }
    let mut fields = Vec::new();
    for chunk in args.chunks(2) {
        let key = match &chunk[0] {
            QuintExpr::Str(s) => s.value.clone(),
            _ => {
                return Err(QuintError::Translation(
                    "RecordSet field name must be a string literal".to_string(),
                ))
            }
        };
        let domain = translate_expr(&chunk[1])?;
        fields.push((spanned_str(&key), domain));
    }
    Ok(spanned(Expr::RecordSet(fields)))
}

/// Translate a Quint opcode to a TLA+ standard library operator call.
///
/// Produces `Apply(Ident(tla_name), translated_args)`, or just `Ident(tla_name)`
/// for zero-arg operators.
fn stdlib_apply(tla_name: &str, args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    let translated_args = args
        .iter()
        .map(translate_expr)
        .collect::<Result<Vec<_>, _>>()?;
    let op_expr = spanned(Expr::Ident(tla_name.to_string(), NameId::INVALID));
    if translated_args.is_empty() {
        Ok(op_expr)
    } else {
        Ok(spanned(Expr::Apply(bx(op_expr), translated_args)))
    }
}

/// Fallback: translate as a user-defined operator application.
fn fallback_apply(opcode: &str, args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    let translated_args = args
        .iter()
        .map(translate_expr)
        .collect::<Result<Vec<_>, _>>()?;
    let op_expr = spanned(Expr::Ident(opcode.to_string(), NameId::INVALID));
    if translated_args.is_empty() {
        Ok(op_expr)
    } else {
        Ok(spanned(Expr::Apply(bx(op_expr), translated_args)))
    }
}

/// N-ary conjunction: fold args with /\.
fn nary_and(args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    if args.is_empty() {
        return Ok(spanned(Expr::Bool(true)));
    }
    let mut result = translate_expr(&args[0])?;
    for arg in &args[1..] {
        let right = translate_expr(arg)?;
        result = spanned(Expr::And(Box::new(result), Box::new(right)));
    }
    Ok(result)
}

/// N-ary disjunction: fold args with \/.
fn nary_or(args: &[QuintExpr]) -> Result<Spanned<Expr>, QuintError> {
    if args.is_empty() {
        return Ok(spanned(Expr::Bool(false)));
    }
    let mut result = translate_expr(&args[0])?;
    for arg in &args[1..] {
        let right = translate_expr(arg)?;
        result = spanned(Expr::Or(Box::new(result), Box::new(right)));
    }
    Ok(result)
}

/// Binary operator helper.
fn binary_op(
    args: &[QuintExpr],
    make: impl FnOnce(Spanned<Expr>, Spanned<Expr>) -> Expr,
) -> Result<Spanned<Expr>, QuintError> {
    ensure_arity("binary op", args, 2)?;
    let left = translate_expr(&args[0])?;
    let right = translate_expr(&args[1])?;
    Ok(spanned(make(left, right)))
}

/// Unary operator helper.
fn unary_op(
    args: &[QuintExpr],
    make: impl FnOnce(Spanned<Expr>) -> Expr,
) -> Result<Spanned<Expr>, QuintError> {
    ensure_arity("unary op", args, 1)?;
    let inner = translate_expr(&args[0])?;
    Ok(spanned(make(inner)))
}

/// Ensure argument count.
fn ensure_arity(op: &str, args: &[QuintExpr], expected: usize) -> Result<(), QuintError> {
    if args.len() != expected {
        return Err(QuintError::Translation(format!(
            "{op} expects {expected} arguments, got {}",
            args.len()
        )));
    }
    Ok(())
}

/// Create a `Spanned<T>` with a dummy span (Quint IR has no byte offsets).
fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::dummy(node)
}

/// Create a `Spanned<String>` with a dummy span.
fn spanned_str(s: &str) -> Spanned<String> {
    Spanned::dummy(s.to_string())
}

/// Shorthand for `Box::new`.
fn bx<T>(val: T) -> Box<T> {
    Box::new(val)
}

/// Translate Quint label names: `__label_Foo` -> `Foo`.
fn translate_label_name(name: &str) -> Spanned<String> {
    let clean = name.strip_prefix("__label_").unwrap_or(name);
    spanned_str(clean)
}

/// Translate a list of Quint params into TLA2 OpParams.
#[allow(dead_code)]
fn translate_params(params: &[QuintParam]) -> Vec<OpParam> {
    params
        .iter()
        .map(|p| OpParam {
            name: spanned_str(&p.name),
            arity: 0,
        })
        .collect()
}
