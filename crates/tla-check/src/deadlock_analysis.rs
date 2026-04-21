// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deadlock analysis engine.
//!
//! When the model checker detects a deadlocked state (no enabled actions),
//! this module provides detailed diagnostics explaining WHY each action is
//! disabled. For each action, it identifies which guard conjuncts are false
//! and reports the variable values that make them false, then ranks actions
//! by how close they are to being enabled.

use std::fmt;
use std::sync::Arc;

use tla_core::ast::{Expr, OperatorDef};
use tla_core::Spanned;

use crate::action_instance::{split_action_instances, ActionInstance};
use crate::eval::EvalCtx;
use crate::state::State;
use crate::value::Value;

/// Result of analyzing a deadlocked state.
#[derive(Debug, Clone)]
pub struct DeadlockAnalysis {
    /// Per-action diagnostics, sorted by closeness (fewest false conjuncts first).
    pub actions: Vec<ActionDiagnostic>,
}

/// Diagnostic for a single action in the deadlocked state.
#[derive(Debug, Clone)]
pub struct ActionDiagnostic {
    /// Action name (e.g., "SendMsg", "RcvMsg(p1)").
    pub name: String,
    /// Total number of top-level conjuncts in the action guard.
    pub total_conjuncts: usize,
    /// Number of conjuncts that evaluated to false.
    pub false_conjuncts: usize,
    /// Detailed results for each conjunct.
    pub conjuncts: Vec<ConjunctResult>,
}

/// Result of evaluating a single conjunct of an action guard.
#[derive(Debug, Clone)]
pub struct ConjunctResult {
    /// Human-readable representation of the conjunct expression.
    pub expression: String,
    /// Whether the conjunct evaluated to true.
    pub satisfied: bool,
    /// Variable values relevant to this conjunct (name -> value string).
    /// Only populated for false conjuncts.
    pub relevant_variables: Vec<(String, String)>,
    /// Error message if evaluation failed (treated as false).
    pub eval_error: Option<String>,
}

impl DeadlockAnalysis {
    /// The action closest to being enabled (fewest false conjuncts).
    #[must_use]
    pub fn closest_action(&self) -> Option<&ActionDiagnostic> {
        self.actions.first()
    }
}

impl fmt::Display for DeadlockAnalysis {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Deadlock Analysis: {} action(s) examined",
            self.actions.len()
        )?;
        writeln!(f)?;
        for (i, action) in self.actions.iter().enumerate() {
            let status = if action.false_conjuncts == 0 {
                "ENABLED (unexpected)".to_string()
            } else {
                format!(
                    "{}/{} guard conjuncts FALSE",
                    action.false_conjuncts, action.total_conjuncts
                )
            };
            writeln!(f, "  Action #{}: {} -- {}", i + 1, action.name, status)?;
            for conjunct in &action.conjuncts {
                let marker = if conjunct.satisfied { "[OK]" } else { "[FAIL]" };
                writeln!(f, "    {} {}", marker, conjunct.expression)?;
                if !conjunct.satisfied {
                    for (var, val) in &conjunct.relevant_variables {
                        writeln!(f, "         where {} = {}", var, val)?;
                    }
                    if let Some(err) = &conjunct.eval_error {
                        writeln!(f, "         eval error: {}", err)?;
                    }
                }
            }
            writeln!(f)?;
        }

        if let Some(closest) = self.closest_action() {
            if closest.false_conjuncts > 0 {
                writeln!(
                    f,
                    "  Closest to enabled: {} ({} conjunct(s) away)",
                    closest.name, closest.false_conjuncts
                )?;
                writeln!(f, "  To enable, make these conjuncts true:")?;
                for conjunct in &closest.conjuncts {
                    if !conjunct.satisfied {
                        writeln!(f, "    - {}", conjunct.expression)?;
                        for (var, val) in &conjunct.relevant_variables {
                            writeln!(f, "      currently: {} = {}", var, val)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

/// Analyze a deadlocked state to determine why each action is disabled.
///
/// For each action instance (split from the Next relation), evaluates each
/// top-level conjunct of the guard individually to identify which are false.
/// Actions are ranked by number of false conjuncts (fewest first = closest
/// to being enabled).
pub fn analyze_deadlock(
    ctx: &mut EvalCtx,
    next_def: &OperatorDef,
    deadlocked_state: &State,
    var_names: &[Arc<str>],
) -> DeadlockAnalysis {
    // Split the Next relation into action instances.
    let instances = match split_action_instances(ctx, &next_def.body) {
        Ok(instances) => instances,
        Err(_) => {
            // If splitting fails, try analyzing the monolithic Next as a single action.
            return analyze_monolithic_next(ctx, next_def, deadlocked_state, var_names);
        }
    };

    if instances.is_empty() {
        return analyze_monolithic_next(ctx, next_def, deadlocked_state, var_names);
    }

    let mut actions = Vec::with_capacity(instances.len());
    for instance in &instances {
        let diag = analyze_action_instance(ctx, instance, deadlocked_state, var_names);
        actions.push(diag);
    }

    // Sort by number of false conjuncts (fewest first = closest to enabled).
    actions.sort_by_key(|a| a.false_conjuncts);

    DeadlockAnalysis { actions }
}

/// Analyze the monolithic Next relation when action splitting is not possible.
fn analyze_monolithic_next(
    ctx: &mut EvalCtx,
    next_def: &OperatorDef,
    state: &State,
    var_names: &[Arc<str>],
) -> DeadlockAnalysis {
    let name = next_def.name.node.clone();
    let conjuncts = flatten_conjuncts(&next_def.body);
    let results = evaluate_conjuncts(ctx, &conjuncts, state, var_names);
    let false_count = results.iter().filter(|c| !c.satisfied).count();

    DeadlockAnalysis {
        actions: vec![ActionDiagnostic {
            name,
            total_conjuncts: results.len(),
            false_conjuncts: false_count,
            conjuncts: results,
        }],
    }
}

/// Analyze a single action instance in the deadlocked state.
fn analyze_action_instance(
    ctx: &mut EvalCtx,
    instance: &ActionInstance,
    state: &State,
    var_names: &[Arc<str>],
) -> ActionDiagnostic {
    let name = format_action_name(instance);
    let conjuncts = flatten_conjuncts(&instance.expr);

    // Push the bindings from the action instance (e.g., quantifier witnesses).
    let mark = ctx.mark_stack();
    for (k, v) in &instance.bindings {
        ctx.push_binding(Arc::clone(k), v.clone());
    }

    let results = evaluate_conjuncts(ctx, &conjuncts, state, var_names);

    ctx.pop_to_mark(&mark);

    let false_count = results.iter().filter(|c| !c.satisfied).count();

    ActionDiagnostic {
        name,
        total_conjuncts: results.len(),
        false_conjuncts: false_count,
        conjuncts: results,
    }
}

/// Flatten a conjunction tree into a list of top-level conjuncts.
///
/// Given `A /\ B /\ C`, returns `[A, B, C]`.
/// Non-conjunction expressions return as a single-element list.
fn flatten_conjuncts(expr: &Spanned<Expr>) -> Vec<Spanned<Expr>> {
    let mut out = Vec::new();
    flatten_conjuncts_rec(expr, &mut out);
    out
}

fn flatten_conjuncts_rec(expr: &Spanned<Expr>, out: &mut Vec<Spanned<Expr>>) {
    match &expr.node {
        Expr::And(lhs, rhs) => {
            flatten_conjuncts_rec(lhs, out);
            flatten_conjuncts_rec(rhs, out);
        }
        Expr::Label(label) => {
            // Unwrap labels (P0:: expr) to get at the underlying expression.
            flatten_conjuncts_rec(&label.body, out);
        }
        _ => {
            out.push(expr.clone());
        }
    }
}

/// Evaluate a list of conjuncts individually against the given state.
fn evaluate_conjuncts(
    ctx: &mut EvalCtx,
    conjuncts: &[Spanned<Expr>],
    state: &State,
    var_names: &[Arc<str>],
) -> Vec<ConjunctResult> {
    let registry = ctx.var_registry().clone();

    // Bind state variables.
    let values = state.to_values(&registry);
    let prev_env = ctx.bind_state_array(&values);

    let mut results = Vec::with_capacity(conjuncts.len());
    for conjunct in conjuncts {
        let expr_str = format_expr_brief(&conjunct.node);

        match crate::eval::eval(ctx, conjunct) {
            Ok(Value::Bool(true)) => {
                results.push(ConjunctResult {
                    expression: expr_str,
                    satisfied: true,
                    relevant_variables: Vec::new(),
                    eval_error: None,
                });
            }
            Ok(Value::Bool(false)) => {
                let relevant = collect_relevant_variables(&conjunct.node, state, var_names);
                results.push(ConjunctResult {
                    expression: expr_str,
                    satisfied: false,
                    relevant_variables: relevant,
                    eval_error: None,
                });
            }
            Ok(_non_bool) => {
                let relevant = collect_relevant_variables(&conjunct.node, state, var_names);
                results.push(ConjunctResult {
                    expression: expr_str,
                    satisfied: false,
                    relevant_variables: relevant,
                    eval_error: Some("conjunct did not evaluate to boolean".to_string()),
                });
            }
            Err(e) => {
                let relevant = collect_relevant_variables(&conjunct.node, state, var_names);
                results.push(ConjunctResult {
                    expression: expr_str,
                    satisfied: false,
                    relevant_variables: relevant,
                    eval_error: Some(format!("{}", e)),
                });
            }
        }
    }

    // Restore previous env.
    if let Some(prev) = prev_env {
        ctx.bind_state_env(prev);
    }

    results
}

/// Collect variable names referenced in an expression and their current values.
fn collect_relevant_variables(
    expr: &Expr,
    state: &State,
    var_names: &[Arc<str>],
) -> Vec<(String, String)> {
    let mut referenced = Vec::new();
    collect_var_refs(expr, &mut referenced);

    // Deduplicate and filter to state variables only.
    referenced.sort();
    referenced.dedup();

    let mut result = Vec::new();
    for var_ref in &referenced {
        for var_name in var_names {
            if var_ref == var_name.as_ref() {
                if let Some(val) = state.get(var_name.as_ref()) {
                    result.push((var_ref.clone(), format_value_brief(val)));
                }
                break;
            }
        }
    }
    result
}

/// Recursively collect variable references from an expression.
///
/// Uses a simple recursive walk that catches `StateVar` and `Ident` nodes.
/// For any composite expression, recurses into children. Unknown or terminal
/// nodes are silently skipped -- this is best-effort for diagnostics, not
/// evaluation correctness.
fn collect_var_refs(expr: &Expr, refs: &mut Vec<String>) {
    match expr {
        Expr::StateVar(name, _, _) => {
            refs.push(name.clone());
        }
        Expr::Ident(name, _) => {
            refs.push(name.clone());
        }
        // Binary operators (two subexpressions).
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Subseteq(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::FuncApply(a, b)
        | Expr::FuncSet(a, b)
        | Expr::Eq(a, b)
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
        | Expr::Pow(a, b)
        | Expr::Range(a, b)
        | Expr::LeadsTo(a, b)
        | Expr::WeakFair(a, b)
        | Expr::StrongFair(a, b) => {
            collect_var_refs(&a.node, refs);
            collect_var_refs(&b.node, refs);
        }
        // Unary operators (one subexpression).
        Expr::Not(a)
        | Expr::Domain(a)
        | Expr::Powerset(a)
        | Expr::BigUnion(a)
        | Expr::Neg(a)
        | Expr::Prime(a)
        | Expr::Always(a)
        | Expr::Eventually(a)
        | Expr::Enabled(a)
        | Expr::Unchanged(a) => {
            collect_var_refs(&a.node, refs);
        }
        Expr::Apply(op, args) => {
            collect_var_refs(&op.node, refs);
            for arg in args {
                collect_var_refs(&arg.node, refs);
            }
        }
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            for bound in bounds {
                if let Some(domain) = &bound.domain {
                    collect_var_refs(&domain.node, refs);
                }
            }
            collect_var_refs(&body.node, refs);
        }
        Expr::Choose(bound, body) => {
            if let Some(domain) = &bound.domain {
                collect_var_refs(&domain.node, refs);
            }
            collect_var_refs(&body.node, refs);
        }
        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
            for elem in elems {
                collect_var_refs(&elem.node, refs);
            }
        }
        Expr::SetBuilder(body, bounds) => {
            collect_var_refs(&body.node, refs);
            for bound in bounds {
                if let Some(domain) = &bound.domain {
                    collect_var_refs(&domain.node, refs);
                }
            }
        }
        Expr::SetFilter(bound, body) => {
            if let Some(domain) = &bound.domain {
                collect_var_refs(&domain.node, refs);
            }
            collect_var_refs(&body.node, refs);
        }
        Expr::FuncDef(bounds, body) => {
            for bound in bounds {
                if let Some(domain) = &bound.domain {
                    collect_var_refs(&domain.node, refs);
                }
            }
            collect_var_refs(&body.node, refs);
        }
        Expr::Except(base, specs) => {
            collect_var_refs(&base.node, refs);
            for spec in specs {
                for elem in &spec.path {
                    match elem {
                        tla_core::ast::ExceptPathElement::Index(idx) => {
                            collect_var_refs(&idx.node, refs);
                        }
                        tla_core::ast::ExceptPathElement::Field(_) => {}
                    }
                }
                collect_var_refs(&spec.value.node, refs);
            }
        }
        Expr::If(cond, then, else_) => {
            collect_var_refs(&cond.node, refs);
            collect_var_refs(&then.node, refs);
            collect_var_refs(&else_.node, refs);
        }
        Expr::Case(arms, other) => {
            for arm in arms {
                collect_var_refs(&arm.guard.node, refs);
                collect_var_refs(&arm.body.node, refs);
            }
            if let Some(other) = other {
                collect_var_refs(&other.node, refs);
            }
        }
        Expr::Let(defs, body) => {
            for def in defs {
                collect_var_refs(&def.body.node, refs);
            }
            collect_var_refs(&body.node, refs);
        }
        Expr::SubstIn(_, body) => {
            collect_var_refs(&body.node, refs);
        }
        Expr::Record(fields) | Expr::RecordSet(fields) => {
            for (_name, value) in fields {
                collect_var_refs(&value.node, refs);
            }
        }
        Expr::RecordAccess(base, _field) => {
            collect_var_refs(&base.node, refs);
        }
        Expr::Label(label) => {
            collect_var_refs(&label.body.node, refs);
        }
        Expr::ModuleRef(_, _, args) => {
            for arg in args {
                collect_var_refs(&arg.node, refs);
            }
        }
        Expr::Lambda(_, body) => {
            collect_var_refs(&body.node, refs);
        }
        // Terminals that don't reference variables.
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::OpRef(_)
        | Expr::InstanceExpr(_, _) => {}
    }
}

/// Format an action instance name with bindings.
fn format_action_name(instance: &ActionInstance) -> String {
    let base = instance.name.as_deref().unwrap_or("<anonymous>");
    if instance.bindings.is_empty() {
        base.to_string()
    } else {
        let params: Vec<String> = instance
            .bindings
            .iter()
            .map(|(k, v)| format!("{} = {}", k, format_value_brief(v)))
            .collect();
        format!("{}({})", base, params.join(", "))
    }
}

/// Format a value briefly for display (truncate very large values).
fn format_value_brief(val: &Value) -> String {
    let s = format!("{}", val);
    if s.len() > 120 {
        format!("{}...", &s[..117])
    } else {
        s
    }
}

/// Format an expression briefly for display.
///
/// Produces a compact human-readable representation of the expression.
/// For complex expressions, this may be a simplified summary.
fn format_expr_brief(expr: &Expr) -> String {
    match expr {
        Expr::Bool(b) => format!("{}", b),
        Expr::Int(n) => format!("{}", n),
        Expr::String(s) => format!("\"{}\"", s),
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => name.clone(),
        Expr::Apply(op, args) => {
            let op_str = format_expr_brief(&op.node);
            if args.is_empty() {
                op_str
            } else {
                let arg_strs: Vec<String> =
                    args.iter().map(|a| format_expr_brief(&a.node)).collect();
                format!("{}({})", op_str, arg_strs.join(", "))
            }
        }
        Expr::And(a, b) => format!(
            "{} /\\ {}",
            format_expr_brief(&a.node),
            format_expr_brief(&b.node)
        ),
        Expr::Or(a, b) => format!(
            "{} \\/ {}",
            format_expr_brief(&a.node),
            format_expr_brief(&b.node)
        ),
        Expr::Not(a) => format!("~({})", format_expr_brief(&a.node)),
        Expr::Implies(a, b) => format!(
            "{} => {}",
            format_expr_brief(&a.node),
            format_expr_brief(&b.node)
        ),
        Expr::In(a, b) => format!(
            "{} \\in {}",
            format_expr_brief(&a.node),
            format_expr_brief(&b.node)
        ),
        Expr::Eq(a, b) => format!(
            "{} = {}",
            format_expr_brief(&a.node),
            format_expr_brief(&b.node)
        ),
        Expr::Neq(a, b) => format!(
            "{} /= {}",
            format_expr_brief(&a.node),
            format_expr_brief(&b.node)
        ),
        Expr::Lt(a, b) => format!(
            "{} < {}",
            format_expr_brief(&a.node),
            format_expr_brief(&b.node)
        ),
        Expr::Leq(a, b) => format!(
            "{} <= {}",
            format_expr_brief(&a.node),
            format_expr_brief(&b.node)
        ),
        Expr::Gt(a, b) => format!(
            "{} > {}",
            format_expr_brief(&a.node),
            format_expr_brief(&b.node)
        ),
        Expr::Geq(a, b) => format!(
            "{} >= {}",
            format_expr_brief(&a.node),
            format_expr_brief(&b.node)
        ),
        Expr::Exists(bounds, body) => {
            let bound_strs: Vec<String> = bounds
                .iter()
                .map(|b| {
                    if let Some(domain) = &b.domain {
                        format!("{} \\in {}", b.name.node, format_expr_brief(&domain.node))
                    } else {
                        b.name.node.clone()
                    }
                })
                .collect();
            format!(
                "\\E {} : {}",
                bound_strs.join(", "),
                format_expr_brief(&body.node)
            )
        }
        Expr::Forall(bounds, body) => {
            let bound_strs: Vec<String> = bounds
                .iter()
                .map(|b| {
                    if let Some(domain) = &b.domain {
                        format!("{} \\in {}", b.name.node, format_expr_brief(&domain.node))
                    } else {
                        b.name.node.clone()
                    }
                })
                .collect();
            format!(
                "\\A {} : {}",
                bound_strs.join(", "),
                format_expr_brief(&body.node)
            )
        }
        Expr::Prime(inner) => format!("{}'", format_expr_brief(&inner.node)),
        Expr::Unchanged(inner) => format!("UNCHANGED {}", format_expr_brief(&inner.node)),
        Expr::Label(label) => format_expr_brief(&label.body.node),
        _ => "<expr>".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_deadlock_analysis_display_format() {
        let analysis = DeadlockAnalysis {
            actions: vec![
                ActionDiagnostic {
                    name: "Send".to_string(),
                    total_conjuncts: 3,
                    false_conjuncts: 1,
                    conjuncts: vec![
                        ConjunctResult {
                            expression: "buffer_full = FALSE".to_string(),
                            satisfied: false,
                            relevant_variables: vec![(
                                "buffer_full".to_string(),
                                "TRUE".to_string(),
                            )],
                            eval_error: None,
                        },
                        ConjunctResult {
                            expression: "msg \\in Messages".to_string(),
                            satisfied: true,
                            relevant_variables: Vec::new(),
                            eval_error: None,
                        },
                        ConjunctResult {
                            expression: "msg' = msg".to_string(),
                            satisfied: true,
                            relevant_variables: Vec::new(),
                            eval_error: None,
                        },
                    ],
                },
                ActionDiagnostic {
                    name: "Receive".to_string(),
                    total_conjuncts: 2,
                    false_conjuncts: 2,
                    conjuncts: vec![
                        ConjunctResult {
                            expression: "queue /= <<>>".to_string(),
                            satisfied: false,
                            relevant_variables: vec![("queue".to_string(), "<<>>".to_string())],
                            eval_error: None,
                        },
                        ConjunctResult {
                            expression: "ready = TRUE".to_string(),
                            satisfied: false,
                            relevant_variables: vec![("ready".to_string(), "FALSE".to_string())],
                            eval_error: None,
                        },
                    ],
                },
            ],
        };

        let display = format!("{}", analysis);
        assert!(display.contains("Deadlock Analysis: 2 action(s) examined"));
        assert!(display.contains("Send -- 1/3 guard conjuncts FALSE"));
        assert!(display.contains("Receive -- 2/2 guard conjuncts FALSE"));
        assert!(display.contains("[FAIL] buffer_full = FALSE"));
        assert!(display.contains("[OK] msg \\in Messages"));
        assert!(display.contains("where buffer_full = TRUE"));
        assert!(display.contains("Closest to enabled: Send"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flatten_conjuncts() {
        use tla_core::span::Span;
        use tla_core::{FileId, Spanned};

        let span = Span::new(FileId(0), 0, 0);

        // Single expression -> 1 conjunct.
        let single = Spanned {
            node: Expr::Bool(true),
            span,
        };
        assert_eq!(flatten_conjuncts(&single).len(), 1);

        // A /\ B -> 2 conjuncts.
        let a = Spanned {
            node: Expr::Bool(true),
            span,
        };
        let b = Spanned {
            node: Expr::Bool(false),
            span,
        };
        let conj = Spanned {
            node: Expr::And(Box::new(a), Box::new(b)),
            span,
        };
        assert_eq!(flatten_conjuncts(&conj).len(), 2);

        // (A /\ B) /\ C -> 3 conjuncts.
        let c = Spanned {
            node: Expr::Int(42.into()),
            span,
        };
        let nested = Spanned {
            node: Expr::And(Box::new(conj.clone()), Box::new(c)),
            span,
        };
        assert_eq!(flatten_conjuncts(&nested).len(), 3);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_action_name() {
        let instance_no_bindings = ActionInstance {
            name: Some("Foo".to_string()),
            expr: Spanned {
                node: Expr::Bool(true),
                span: tla_core::span::Span::new(tla_core::FileId(0), 0, 0),
            },
            bindings: Vec::new(),
        };
        assert_eq!(format_action_name(&instance_no_bindings), "Foo");

        let instance_with_bindings = ActionInstance {
            name: Some("Send".to_string()),
            expr: Spanned {
                node: Expr::Bool(true),
                span: tla_core::span::Span::new(tla_core::FileId(0), 0, 0),
            },
            bindings: vec![(Arc::from("p"), Value::string("p1"))],
        };
        assert_eq!(
            format_action_name(&instance_with_bindings),
            "Send(p = \"p1\")"
        );

        let instance_anonymous = ActionInstance {
            name: None,
            expr: Spanned {
                node: Expr::Bool(true),
                span: tla_core::span::Span::new(tla_core::FileId(0), 0, 0),
            },
            bindings: Vec::new(),
        };
        assert_eq!(format_action_name(&instance_anonymous), "<anonymous>");
    }
}
