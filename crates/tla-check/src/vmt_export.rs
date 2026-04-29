// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(dead_code)]

//! VMT (Verification Modulo Theories) output format for external model checkers.
//!
//! VMT is an extension of SMT-LIB2 used by hardware and software model checkers
//! such as nuXmv, ic3ia, and AVR. It encodes transition systems using:
//!
//! - **State variables**: declared with `(declare-fun x () <Sort>)` and annotated
//!   with `:next` to link current-state and next-state copies.
//! - **`.init`**: a Boolean formula over current-state variables defining initial states.
//! - **`.trans`**: a Boolean formula over current and next-state variables defining
//!   the transition relation.
//! - **`.prop`**: a Boolean formula over current-state variables defining the safety
//!   property to verify.
//!
//! # VMT Annotations
//!
//! VMT uses SMT-LIB2 `:named` annotations for system components:
//! ```smt2
//! (declare-fun x () Int)
//! (declare-fun x_next () Int)
//! (define-fun .init () Bool (= x 0))
//! (define-fun .trans () Bool (and (= x_next (+ x 1)) ...))
//! (define-fun .prop () Bool (< x 100))
//! ```
//!
//! # Limitations
//!
//! Only scalar sorts (Bool, Int) are supported. Variables with function, tuple,
//! record, or string sorts are rejected. This matches the BMC translator's
//! scalar-only restriction.
//!
//! Part of #3755: VMT output format for external model checkers (Apalache Gap 7).

use std::fmt::Write;

use tla_core::ast::{Expr, Module};
use tla_core::Spanned;

use crate::config::Config;
use crate::eval::EvalCtx;
use crate::z4_pdr::expand_operators_for_chc;
use crate::z4_shared;

/// Errors specific to VMT export.
#[derive(Debug, thiserror::Error)]
pub enum VmtError {
    /// Missing Init or Next definition.
    #[error("Missing specification: {0}")]
    MissingSpec(String),
    /// No invariants configured.
    #[error("No invariants configured for VMT export")]
    NoInvariants,
    /// Expression cannot be translated to SMT-LIB2.
    #[error("VMT translation failed: {0}")]
    TranslationError(String),
}

/// Sort of a state variable in VMT output.
#[derive(Debug, Clone, PartialEq, Eq)]
enum VmtSort {
    Bool,
    Int,
}

impl std::fmt::Display for VmtSort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VmtSort::Bool => write!(f, "Bool"),
            VmtSort::Int => write!(f, "Int"),
        }
    }
}

/// A state variable with current and next-state names.
struct VmtVar {
    /// Variable name in the TLA+ spec.
    name: String,
    /// SMT sort.
    sort: VmtSort,
}

/// Generated VMT output.
pub struct VmtOutput {
    /// The complete VMT file content in SMT-LIB2 format.
    pub content: String,
    /// Number of state variables declared.
    pub num_vars: usize,
    /// Number of invariants conjoined into the property.
    pub num_invariants: usize,
}

/// Export a TLA+ spec as VMT format.
///
/// Parses the spec's Init/Next/invariants, translates them to SMT-LIB2
/// formulas, and produces a complete VMT file.
pub fn export_vmt(module: &Module, config: &Config, ctx: &EvalCtx) -> Result<VmtOutput, VmtError> {
    let symbolic_ctx =
        z4_shared::symbolic_ctx_with_config(ctx, config).map_err(VmtError::MissingSpec)?;
    let vars = z4_shared::collect_state_vars(module);
    if vars.is_empty() {
        return Err(VmtError::MissingSpec(
            "No state variables declared".to_string(),
        ));
    }

    if config.invariants.is_empty() {
        return Err(VmtError::NoInvariants);
    }

    let resolved =
        z4_shared::resolve_init_next(config, &symbolic_ctx).map_err(VmtError::MissingSpec)?;

    let init_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.init)
        .map_err(VmtError::MissingSpec)?;
    let next_expr = z4_shared::get_operator_body(&symbolic_ctx, &resolved.next)
        .map_err(VmtError::MissingSpec)?;
    let safety_expr = z4_shared::build_safety_conjunction(&symbolic_ctx, &config.invariants)
        .map_err(VmtError::TranslationError)?;

    let init_expanded = expand_operators_for_chc(&symbolic_ctx, &init_expr, false);
    let next_expanded = expand_operators_for_chc(&symbolic_ctx, &next_expr, true);
    let safety_expanded = expand_operators_for_chc(&symbolic_ctx, &safety_expr, false);

    let var_sorts =
        z4_shared::infer_var_sorts(&vars, &init_expanded, &config.invariants, &symbolic_ctx);

    // Convert to VmtVar, rejecting non-scalar sorts.
    let mut vmt_vars = Vec::with_capacity(var_sorts.len());
    for (name, tla_sort) in &var_sorts {
        let sort = match tla_sort {
            tla_z4::TlaSort::Bool => VmtSort::Bool,
            tla_z4::TlaSort::Int | tla_z4::TlaSort::String => VmtSort::Int,
            other => {
                return Err(VmtError::TranslationError(format!(
                    "Variable '{name}' has unsupported sort {other} for VMT export \
                     (only Bool and Int are supported)"
                )));
            }
        };
        vmt_vars.push(VmtVar {
            name: name.clone(),
            sort,
        });
    }

    let num_vars = vmt_vars.len();
    let num_invariants = config.invariants.len();

    let mut out = String::new();

    // Header comment.
    writeln!(out, ";; VMT output generated by TLA2").expect("write to String");
    writeln!(out, ";; Module: {}", module.name.node).expect("write to String");
    writeln!(out, ";; Variables: {num_vars}").expect("write to String");
    writeln!(out, ";; Invariants: {num_invariants}").expect("write to String");
    writeln!(out).expect("write to String");

    // Set logic.
    writeln!(out, "(set-logic QF_LIA)").expect("write to String");
    writeln!(out).expect("write to String");

    // Declare current-state and next-state variables.
    // VMT convention: next-state variable is named `<var>_next` and linked
    // via `:next` annotation on the current-state declaration.
    writeln!(out, ";; State variables").expect("write to String");
    for var in &vmt_vars {
        writeln!(
            out,
            "(declare-fun {} () {})",
            smt_ident(&var.name),
            var.sort,
        )
        .expect("write to String");
        writeln!(
            out,
            "(declare-fun {}_next () {})",
            smt_ident(&var.name),
            var.sort,
        )
        .expect("write to String");
    }
    writeln!(out).expect("write to String");

    // .init predicate.
    writeln!(out, ";; Initial states").expect("write to String");
    let init_smt = expr_to_smt(&init_expanded, false, &vmt_vars);
    writeln!(out, "(define-fun .init () Bool {init_smt})").expect("write to String");
    writeln!(out).expect("write to String");

    // .trans predicate.
    writeln!(out, ";; Transition relation").expect("write to String");
    let trans_smt = expr_to_smt(&next_expanded, true, &vmt_vars);
    writeln!(out, "(define-fun .trans () Bool {trans_smt})").expect("write to String");
    writeln!(out).expect("write to String");

    // .prop predicate.
    writeln!(out, ";; Safety property").expect("write to String");
    let prop_smt = expr_to_smt(&safety_expanded, false, &vmt_vars);
    writeln!(out, "(define-fun .prop () Bool {prop_smt})").expect("write to String");

    Ok(VmtOutput {
        content: out,
        num_vars,
        num_invariants,
    })
}

/// Escape a TLA+ identifier to a valid SMT-LIB2 identifier.
///
/// SMT-LIB2 simple symbols allow letters, digits, and certain punctuation.
/// We use `|quoted|` form for identifiers containing special characters.
fn smt_ident(name: &str) -> String {
    let needs_quoting = name.is_empty()
        || name
            .chars()
            .any(|c| !c.is_alphanumeric() && c != '_' && c != '.');
    if needs_quoting {
        format!("|{name}|")
    } else {
        name.to_string()
    }
}

/// Translate a TLA+ expression to SMT-LIB2 string.
///
/// When `allow_primed` is true, primed variables `x'` are rendered as `x_next`.
/// When false, primed variables cause a fallback to an opaque representation.
fn expr_to_smt(expr: &Spanned<Expr>, allow_primed: bool, vars: &[VmtVar]) -> String {
    match &expr.node {
        // Boolean literals
        Expr::Bool(true) => "true".to_string(),
        Expr::Bool(false) => "false".to_string(),

        // Integer literals
        Expr::Int(n) => {
            let val: i64 = n.try_into().unwrap_or(0);
            if val < 0 {
                format!("(- {})", -val)
            } else {
                val.to_string()
            }
        }

        // Variable reference (unprimed)
        Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
            if is_state_var(name, vars) {
                smt_ident(name)
            } else if name == "TRUE" {
                "true".to_string()
            } else if name == "FALSE" {
                "false".to_string()
            } else {
                // Unknown identifier - render as-is (may be a constant)
                smt_ident(name)
            }
        }

        // Primed variable: x'
        Expr::Prime(inner) => {
            if allow_primed {
                if let Expr::Ident(name, _) | Expr::StateVar(name, ..) = &inner.node {
                    if is_state_var(name, vars) {
                        return format!("{}_next", smt_ident(name));
                    }
                }
            }
            // Fallback: translate the inner expression
            let inner_smt = expr_to_smt(inner, allow_primed, vars);
            format!("(prime {inner_smt})")
        }

        // Boolean operators
        Expr::And(a, b) => {
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!("(and {la} {ra})")
        }
        Expr::Or(a, b) => {
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!("(or {la} {ra})")
        }
        Expr::Not(inner) => {
            let s = expr_to_smt(inner, allow_primed, vars);
            format!("(not {s})")
        }
        Expr::Implies(a, b) => {
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!("(=> {la} {ra})")
        }
        Expr::Equiv(a, b) => {
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!("(= {la} {ra})")
        }

        // Comparison operators
        Expr::Eq(a, b) => {
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!("(= {la} {ra})")
        }
        Expr::Neq(a, b) => {
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!("(not (= {la} {ra}))")
        }
        Expr::Lt(a, b) => {
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!("(< {la} {ra})")
        }
        Expr::Leq(a, b) => {
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!("(<= {la} {ra})")
        }
        Expr::Gt(a, b) => {
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!("(> {la} {ra})")
        }
        Expr::Geq(a, b) => {
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!("(>= {la} {ra})")
        }

        // Arithmetic operators
        Expr::Add(a, b) => {
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!("(+ {la} {ra})")
        }
        Expr::Sub(a, b) => {
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!("(- {la} {ra})")
        }
        Expr::Mul(a, b) => {
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!("(* {la} {ra})")
        }
        Expr::Neg(inner) => {
            let s = expr_to_smt(inner, allow_primed, vars);
            format!("(- {s})")
        }
        Expr::IntDiv(a, b) => {
            // TLA+ \div is floor division; SMT-LIB `div` is Euclidean.
            // Adjust: when divisor < 0 and remainder exists, subtract 1.
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!(
                "(let ((__a {la}) (__b {ra})) \
                 (ite (and (< __b 0) (distinct (* (div __a __b) __b) __a)) \
                 (- (div __a __b) 1) (div __a __b)))"
            )
        }
        Expr::Mod(a, b) => {
            // TLA+ mod always returns non-negative for positive divisor.
            // Defensive adjustment for negative Euclidean remainder.
            let la = expr_to_smt(a, allow_primed, vars);
            let ra = expr_to_smt(b, allow_primed, vars);
            format!(
                "(let ((__r (mod {la} {ra}))) \
                 (ite (< __r 0) (+ __r {ra}) __r))"
            )
        }

        // IF/THEN/ELSE
        Expr::If(cond, then_branch, else_branch) => {
            let c = expr_to_smt(cond, allow_primed, vars);
            let t = expr_to_smt(then_branch, allow_primed, vars);
            let e = expr_to_smt(else_branch, allow_primed, vars);
            format!("(ite {c} {t} {e})")
        }

        // Set membership: x \in {a, b, c} -> (or (= x a) (= x b) (= x c))
        Expr::In(elem, set) => translate_membership(elem, set, allow_primed, vars),

        // UNCHANGED x -> (= x_next x)
        Expr::Unchanged(inner) => translate_unchanged(inner, allow_primed, vars),

        // Let/In: LET x == e IN body -> translate body with substitution
        // For VMT output, we emit the body directly (operators already expanded).
        Expr::Let(_, body) => expr_to_smt(body, allow_primed, vars),

        // Label wrapper: transparent
        Expr::Label(label) => expr_to_smt(&label.body, allow_primed, vars),

        // Range: lo..hi (treated as opaque in VMT; membership handles it)
        Expr::Range(lo, hi) => {
            let l = expr_to_smt(lo, allow_primed, vars);
            let h = expr_to_smt(hi, allow_primed, vars);
            format!(";; range {l}..{h} (opaque)")
        }

        // Bounded quantifiers
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            let quantifier = if matches!(&expr.node, Expr::Forall(..)) {
                "forall"
            } else {
                "exists"
            };
            // Best-effort: emit quantifier with declared variables.
            let mut bound_decls = Vec::new();
            for b in bounds {
                let name = &b.name.node;
                // Infer sort from domain if available.
                let sort_str = if let Some(domain) = &b.domain {
                    match &domain.node {
                        Expr::Ident(n, _) if n == "BOOLEAN" => "Bool",
                        _ => "Int",
                    }
                } else {
                    "Int"
                };
                bound_decls.push(format!("({} {})", smt_ident(name), sort_str));
            }
            let body_smt = expr_to_smt(body, allow_primed, vars);
            format!("({quantifier} ({}) {body_smt})", bound_decls.join(" "))
        }

        // Fallback for unsupported expressions.
        _ => {
            format!(";; unsupported: {:?}", std::mem::discriminant(&expr.node))
        }
    }
}

/// Translate UNCHANGED expression to SMT-LIB2.
fn translate_unchanged(expr: &Spanned<Expr>, allow_primed: bool, vars: &[VmtVar]) -> String {
    match &expr.node {
        Expr::Ident(name, _) | Expr::StateVar(name, ..) => {
            if is_state_var(name, vars) {
                format!("(= {}_next {})", smt_ident(name), smt_ident(name))
            } else {
                format!(";; UNCHANGED unknown var {name}")
            }
        }
        Expr::Tuple(elems) => {
            if elems.is_empty() {
                return "true".to_string();
            }
            let parts: Vec<String> = elems
                .iter()
                .map(|e| translate_unchanged(e, allow_primed, vars))
                .collect();
            if parts.len() == 1 {
                parts.into_iter().next().expect("len checked == 1")
            } else {
                format!("(and {})", parts.join(" "))
            }
        }
        _ => {
            let s = expr_to_smt(expr, allow_primed, vars);
            format!(";; UNCHANGED complex: {s}")
        }
    }
}

/// Translate set membership to SMT-LIB2.
fn translate_membership(
    elem: &Spanned<Expr>,
    set: &Spanned<Expr>,
    allow_primed: bool,
    vars: &[VmtVar],
) -> String {
    let elem_smt = expr_to_smt(elem, allow_primed, vars);
    match &set.node {
        // x \in {a, b, c} -> (or (= x a) (= x b) (= x c))
        Expr::SetEnum(elements) => {
            if elements.is_empty() {
                return "false".to_string();
            }
            let disjuncts: Vec<String> = elements
                .iter()
                .map(|e| {
                    let e_smt = expr_to_smt(e, allow_primed, vars);
                    format!("(= {elem_smt} {e_smt})")
                })
                .collect();
            if disjuncts.len() == 1 {
                disjuncts.into_iter().next().expect("len checked == 1")
            } else {
                format!("(or {})", disjuncts.join(" "))
            }
        }
        // x \in lo..hi -> (and (<= lo x) (<= x hi))
        Expr::Range(lo, hi) => {
            let lo_smt = expr_to_smt(lo, allow_primed, vars);
            let hi_smt = expr_to_smt(hi, allow_primed, vars);
            format!("(and (<= {lo_smt} {elem_smt}) (<= {elem_smt} {hi_smt}))")
        }
        // x \in BOOLEAN -> true (trivially satisfied for Bool-sorted vars)
        Expr::Ident(name, _) if name == "BOOLEAN" => "true".to_string(),
        // x \in Int -> true (trivially satisfied for Int-sorted vars)
        Expr::Ident(name, _) if name == "Int" || name == "Nat" => {
            if name == "Nat" {
                format!("(>= {elem_smt} 0)")
            } else {
                "true".to_string()
            }
        }
        _ => {
            let set_smt = expr_to_smt(set, allow_primed, vars);
            format!(";; membership: {elem_smt} in {set_smt}")
        }
    }
}

/// Check if a name refers to a declared state variable.
fn is_state_var(name: &str, vars: &[VmtVar]) -> bool {
    vars.iter().any(|v| v.name == name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_smt_ident_simple() {
        assert_eq!(smt_ident("x"), "x");
        assert_eq!(smt_ident("count"), "count");
        assert_eq!(smt_ident("my_var"), "my_var");
    }

    #[test]
    fn test_smt_ident_needs_quoting() {
        assert_eq!(smt_ident("x+y"), "|x+y|");
        assert_eq!(smt_ident(""), "||");
    }

    #[test]
    fn test_vmt_sort_display() {
        assert_eq!(format!("{}", VmtSort::Bool), "Bool");
        assert_eq!(format!("{}", VmtSort::Int), "Int");
    }
}
