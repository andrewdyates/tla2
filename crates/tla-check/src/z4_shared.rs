// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared utilities for z4-based symbolic checking (PDR and BMC).
//!
//! Extracted from duplicated code in `z4_pdr.rs` and `z4_bmc.rs` to provide
//! a single sort inference implementation. The PDR version is the superset,
//! supporting function sorts, set enums, FuncSet, SetFilter, FuncDef, Except,
//! and IF/THEN/ELSE.

use std::sync::Arc;

use tla_core::ast::{Expr, Module, Unit};
use tla_core::Spanned;
use tla_z4::TlaSort;

use crate::check::ResolvedSpec;
use crate::config::Config;
use crate::eval::EvalCtx;

/// Clone an EvalCtx and bind TLC config constants/operator replacements into it.
///
/// Symbolic entrypoints must do this themselves so direct `check_bmc` /
/// `check_pdr` calls honor config-provided values and operator replacements
/// without requiring the caller to pre-mutate the shared EvalCtx.
pub(crate) fn symbolic_ctx_with_config(ctx: &EvalCtx, config: &Config) -> Result<EvalCtx, String> {
    let mut ctx = ctx.clone();
    crate::bind_constants_from_config(&mut ctx, config)
        .map_err(|error| format!("failed to bind config constants: {error}"))?;
    Ok(ctx)
}

/// Collect state variable names from the module.
pub(crate) fn collect_state_vars(module: &Module) -> Vec<Arc<str>> {
    let mut vars = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(var_names) = &unit.node {
            for var in var_names {
                vars.push(Arc::from(var.node.as_str()));
            }
        }
    }
    vars
}

/// Resolve Init/Next operator names from config after constant/operator
/// replacements have been bound into the evaluation context.
///
/// Returns a `ResolvedSpec` or an error string for the missing part.
pub(crate) fn resolve_init_next(config: &Config, ctx: &EvalCtx) -> Result<ResolvedSpec, String> {
    match (&config.init, &config.next) {
        (Some(init), Some(next)) => Ok(ResolvedSpec {
            init: ctx.resolve_op_name(init).to_string(),
            next: ctx.resolve_op_name(next).to_string(),
            next_node: None,
            fairness: Vec::new(),
            stuttering_allowed: true,
        }),
        (None, _) => Err("INIT not specified".to_string()),
        (_, None) => Err("NEXT not specified".to_string()),
    }
}

/// Get operator body expression from EvalCtx.
///
/// Returns the operator body or an error string.
pub(crate) fn get_operator_body(ctx: &EvalCtx, name: &str) -> Result<Spanned<Expr>, String> {
    if let Some(def) = ctx.get_op(name) {
        if !def.params.is_empty() {
            return Err(format!(
                "Operator '{}' has parameters; symbolic checking requires parameterless Init/Next",
                name
            ));
        }
        Ok(def.body.clone())
    } else {
        Err(format!("Operator '{}' not found", name))
    }
}

/// Build conjunction of invariant expressions.
pub(crate) fn build_safety_conjunction(
    ctx: &EvalCtx,
    invariant_names: &[String],
) -> Result<Spanned<Expr>, String> {
    let mut exprs: Vec<Spanned<Expr>> = Vec::new();

    for name in invariant_names {
        let resolved_name = ctx.resolve_op_name(name);
        let body = get_operator_body(ctx, resolved_name)?;
        exprs.push(body);
    }

    if exprs.is_empty() {
        return Err("No invariants configured".to_string());
    }

    let mut result = exprs.pop().expect("exprs non-empty after empty check");
    while let Some(expr) = exprs.pop() {
        result = Spanned::dummy(Expr::And(Box::new(expr), Box::new(result)));
    }

    Ok(result)
}

/// Infer variable sorts from TypeOK invariant or Init constraints.
///
/// Inference strategy:
/// 1. Look for TypeOK in invariants and check for `x \in BOOLEAN` or `x \in Int`
/// 2. Fall back to Init constraints of the form `x = TRUE/FALSE` (Bool) or `x = n` (Int)
/// 3. Default to Int if ambiguous (most TLA+ specs use integers)
pub(crate) fn infer_var_sorts(
    vars: &[Arc<str>],
    init_expr: &Spanned<Expr>,
    invariant_names: &[String],
    ctx: &EvalCtx,
) -> Vec<(String, TlaSort)> {
    let mut sorts: Vec<(String, TlaSort)> = Vec::new();

    let type_ok_body = invariant_names.iter().find_map(|name| {
        let resolved_name = ctx.resolve_op_name(name);
        let lower = resolved_name.to_lowercase();
        if !(lower == "typeok" || lower == "typeinvariant" || lower == "type_ok") {
            return None;
        }
        ctx.get_op(resolved_name).map(|def| &def.body)
    });

    for var in vars {
        let sort = infer_single_var_sort(var, init_expr, type_ok_body);
        sorts.push((var.to_string(), sort));
    }

    sorts
}

fn infer_single_var_sort(
    var: &str,
    init_expr: &Spanned<Expr>,
    type_ok_body: Option<&Spanned<Expr>>,
) -> TlaSort {
    if let Some(body) = type_ok_body {
        if let Some(sort) = check_membership_constraint(var, body) {
            return sort;
        }
    }

    if let Some(sort) = check_init_assignment(var, init_expr) {
        return sort;
    }

    TlaSort::Int
}

/// Check if expression contains `var \in S` constraint that reveals the variable sort.
pub(crate) fn check_membership_constraint(var: &str, expr: &Spanned<Expr>) -> Option<TlaSort> {
    match &expr.node {
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b) | Expr::Equiv(a, b) => {
            check_membership_constraint(var, a).or_else(|| check_membership_constraint(var, b))
        }
        Expr::Let(_, body) => check_membership_constraint(var, body),
        Expr::Label(label) => check_membership_constraint(var, &label.body),
        Expr::In(elem, set) => {
            let is_var = matches!(&elem.node, Expr::Ident(name, _) | Expr::StateVar(name, _, _) if name == var);
            if !is_var {
                return None;
            }
            infer_sort_from_set_expr(set)
        }
        _ => None,
    }
}

/// Check Init for assignment or membership patterns that reveal the variable sort.
pub(crate) fn check_init_assignment(var: &str, expr: &Spanned<Expr>) -> Option<TlaSort> {
    match &expr.node {
        Expr::And(a, b) | Expr::Or(a, b) => {
            check_init_assignment(var, a).or_else(|| check_init_assignment(var, b))
        }
        Expr::Let(_, body) => check_init_assignment(var, body),
        Expr::Label(label) => check_init_assignment(var, &label.body),
        Expr::Eq(lhs, rhs) => {
            let is_var = matches!(&lhs.node, Expr::Ident(name, _) | Expr::StateVar(name, _, _) if name == var);
            if !is_var {
                return None;
            }
            infer_sort_from_value_expr(rhs).or_else(|| infer_sort_from_set_expr(rhs))
        }
        Expr::In(elem, set) => {
            let is_var = matches!(&elem.node, Expr::Ident(name, _) | Expr::StateVar(name, _, _) if name == var);
            if !is_var {
                return None;
            }
            infer_sort_from_set_expr(set)
        }
        _ => None,
    }
}

fn infer_sort_from_value_expr(expr: &Spanned<Expr>) -> Option<TlaSort> {
    match &expr.node {
        Expr::Label(label) => infer_sort_from_value_expr(&label.body),
        Expr::Bool(_) => Some(TlaSort::Bool),
        Expr::Int(_) => Some(TlaSort::Int),
        Expr::String(_) => Some(TlaSort::String),
        // Part of #3749: set literal as a value — infer Set sort from elements.
        Expr::SetEnum(elements) => {
            let element_sort = infer_sort_from_set_enum(elements)?;
            Some(TlaSort::Set {
                element_sort: Box::new(element_sort),
            })
        }
        // Part of #3749: tuple literal as a sequence value candidate.
        Expr::Tuple(elements) if !elements.is_empty() => {
            // Try to infer a uniform element sort (for sequences).
            // If elements have mixed sorts, fall back to tuple sort.
            let first_sort = infer_sort_from_value_expr(&elements[0])?;
            let all_same = elements
                .iter()
                .skip(1)
                .all(|e| infer_sort_from_value_expr(e).as_ref() == Some(&first_sort));
            if all_same {
                // Could be either a tuple or a sequence — conservatively return Tuple.
                let element_sorts = elements
                    .iter()
                    .map(|e| infer_sort_from_value_expr(e))
                    .collect::<Option<Vec<_>>>()?;
                Some(TlaSort::Tuple { element_sorts })
            } else {
                let element_sorts = elements
                    .iter()
                    .map(|e| infer_sort_from_value_expr(e))
                    .collect::<Option<Vec<_>>>()?;
                Some(TlaSort::Tuple { element_sorts })
            }
        }
        Expr::Record(fields) => {
            let mut field_sorts = Vec::with_capacity(fields.len());
            for (field_name, field_expr) in fields {
                field_sorts.push((
                    field_name.node.clone(),
                    infer_sort_from_value_expr(field_expr)?,
                ));
            }
            Some((TlaSort::Record { field_sorts }).canonicalized())
        }
        Expr::RecordAccess(base, field) => {
            let TlaSort::Record { field_sorts } = infer_sort_from_value_expr(base)? else {
                return None;
            };
            field_sorts
                .into_iter()
                .find(|(name, _)| name == &field.name.node)
                .map(|(_, sort)| sort)
        }
        Expr::FuncDef(bounds, body) => {
            if bounds.len() != 1 {
                return None;
            }
            let domain = bounds[0].domain.as_ref()?;
            let domain_keys = extract_finite_domain_keys(domain)?;
            let range_sort = infer_sort_from_value_expr(body)?;
            Some(
                (TlaSort::Function {
                    domain_keys,
                    range: Box::new(range_sort),
                })
                .canonicalized(),
            )
        }
        Expr::Except(base, _) => infer_sort_from_value_expr(base),
        Expr::If(_, then_branch, else_branch) => {
            let then_sort = infer_sort_from_value_expr(then_branch)?;
            let else_sort = infer_sort_from_value_expr(else_branch)?;
            (then_sort == else_sort).then_some(then_sort)
        }
        _ => None,
    }
}

fn infer_sort_from_set_expr(expr: &Spanned<Expr>) -> Option<TlaSort> {
    match &expr.node {
        Expr::Label(label) => infer_sort_from_set_expr(&label.body),
        Expr::Ident(name, _) if name == "BOOLEAN" => Some(TlaSort::Bool),
        Expr::Ident(name, _) if name == "Int" || name == "Nat" => Some(TlaSort::Int),
        Expr::Range(_, _) => Some(TlaSort::Int),
        Expr::SetEnum(elements) => infer_sort_from_set_enum(elements),
        Expr::RecordSet(fields) => {
            let mut field_sorts = Vec::with_capacity(fields.len());
            for (field_name, domain) in fields {
                field_sorts.push((field_name.node.clone(), infer_sort_from_set_expr(domain)?));
            }
            Some((TlaSort::Record { field_sorts }).canonicalized())
        }
        Expr::FuncSet(domain, range) => Some(
            (TlaSort::Function {
                domain_keys: extract_finite_domain_keys(domain)?,
                range: Box::new(infer_sort_from_set_expr(range)?),
            })
            .canonicalized(),
        ),
        Expr::SetFilter(bound, _) => infer_sort_from_set_expr(bound.domain.as_ref()?),
        // Part of #3749: SUBSET S — variable is a set of element_sort
        Expr::Powerset(inner) => {
            let element_sort = infer_sort_from_set_expr(inner)?;
            Some(TlaSort::Set {
                element_sort: Box::new(element_sort),
            })
        }
        // Part of #3749: Seq(S) — variable is a sequence of element_sort.
        // Seq(S) is lowered to Apply(OpRef("Seq"), [S]).
        Expr::Apply(op, args) if args.len() == 1 => {
            let is_seq = matches!(
                &op.node,
                Expr::Ident(name, _) | Expr::OpRef(name) if name == "Seq"
            );
            if is_seq {
                let element_sort = infer_sort_from_set_expr(&args[0])?;
                // Default max_len of 10 for finite model checking;
                // the caller can override if known.
                Some(TlaSort::Sequence {
                    element_sort: Box::new(element_sort),
                    max_len: 10,
                })
            } else {
                None
            }
        }
        _ => None,
    }
}

fn infer_sort_from_set_enum(elements: &[Spanned<Expr>]) -> Option<TlaSort> {
    let first = elements.first()?;
    let first_sort = infer_sort_from_value_expr(first)?;
    if elements
        .iter()
        .skip(1)
        .all(|expr| infer_sort_from_value_expr(expr).as_ref() == Some(&first_sort))
    {
        Some(first_sort)
    } else {
        None
    }
}

fn encode_domain_key_expr(expr: &Spanned<Expr>) -> Option<String> {
    match &expr.node {
        Expr::Int(n) => Some(format!("int:{n}")),
        Expr::Bool(b) => Some(format!("bool:{b}")),
        Expr::String(s) => Some(format!("str:{s}")),
        Expr::Ident(name, _) => Some(format!("id:{name}")),
        _ => None,
    }
}

fn extract_finite_domain_keys(domain: &Spanned<Expr>) -> Option<Vec<String>> {
    match &domain.node {
        Expr::SetEnum(elements) => elements.iter().map(encode_domain_key_expr).collect(),
        Expr::Range(lo, hi) => {
            let lo: i64 = match &lo.node {
                Expr::Int(n) => n.try_into().ok()?,
                _ => return None,
            };
            let hi: i64 = match &hi.node {
                Expr::Int(n) => n.try_into().ok()?,
                _ => return None,
            };
            if hi < lo {
                return Some(Vec::new());
            }
            Some((lo..=hi).map(|n| format!("int:{n}")).collect())
        }
        Expr::Ident(name, _) if name == "BOOLEAN" => {
            Some(vec!["bool:false".to_string(), "bool:true".to_string()])
        }
        _ => None,
    }
}

/// Check if any variable sort requires array-based SMT encoding.
///
/// Sets, Functions, and Sequences are encoded as SMT arrays, which
/// requires `QF_AUFLIA` logic instead of `QF_LIA`.
///
/// Extracted from `z4_bmc.rs` for reuse in k-induction, symbolic sim,
/// and inductive check entrypoints.
pub(crate) fn needs_array_logic(var_sorts: &[(String, TlaSort)]) -> bool {
    var_sorts.iter().any(|(_, sort)| {
        matches!(
            sort,
            TlaSort::Set { .. } | TlaSort::Function { .. } | TlaSort::Sequence { .. }
        )
    })
}

/// Create a BMC translator with the appropriate logic for the given variable sorts.
///
/// Uses `QF_AUFLIA` if any variable requires array encoding (sets, functions,
/// sequences), otherwise `QF_LIA`.
///
/// Extracted from `z4_bmc.rs` for reuse in k-induction, symbolic sim,
/// and inductive check entrypoints.
pub(crate) fn make_translator(
    var_sorts: &[(String, TlaSort)],
    depth: usize,
) -> Result<tla_z4::BmcTranslator, tla_z4::Z4Error> {
    if needs_array_logic(var_sorts) {
        tla_z4::BmcTranslator::new_with_arrays(depth)
    } else {
        tla_z4::BmcTranslator::new(depth)
    }
}
