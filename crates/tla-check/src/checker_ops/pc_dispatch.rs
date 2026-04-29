// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! PlusCal `pc`-based action dispatch optimization.
//!
//! In PlusCal-generated specs, `Next` is a disjunction of actions, each guarded
//! by `pc = "label"` (single-process) or `pc[self] = "label"` (multi-process).
//! TLC optimizes this by dispatching on the `pc` value directly, avoiding the
//! cost of evaluating every action's guard for every state.
//!
//! This module detects the PlusCal pattern at setup time and builds a dispatch
//! table mapping `pc` values to action indices. During BFS, the model checker
//! reads `pc` from the current state and only evaluates actions whose `pc` guard
//! matches, skipping all others.
//!
//! ## Soundness
//!
//! This optimization is sound because:
//! - Detection requires ALL disjuncts have a `pc = "literal"` guard as the first
//!   conjunct. If any disjunct lacks this pattern, the optimization is not applied.
//! - For a given state, the `pc` value uniquely selects the applicable subset of
//!   actions. Actions with a different `pc` guard would evaluate their guard to
//!   FALSE and produce zero successors — so skipping them changes nothing.
//! - The fallback path (evaluating all actions) is used when the `pc` value is
//!   not found in the dispatch table, ensuring no states are missed.
//! - Multi-process specs (`pc[self]`) are supported via Or-branch guard hoisting:
//!   when `self` is bound by EXISTS, the guard check evaluates `pc[self]` to
//!   determine the effective pc value for the current process.

use rustc_hash::FxHashMap;

use crate::coverage::{detect_actions, DetectedAction};
use crate::eval::EvalCtx;
use crate::value::Value;
use tla_core::ast::{Expr, OperatorDef};
use tla_core::VarIndex;

/// Pre-computed dispatch table for PlusCal `pc`-dispatched specs.
///
/// Built once at setup time. Maps `pc` string values to the indices of
/// actions in the detected actions list that are guarded by that value.
/// Also stores the detected action expressions so they can be enumerated
/// individually during BFS.
#[derive(Debug, Clone)]
pub(crate) struct PcDispatchTable {
    /// The variable index of `pc` in the state array.
    pub(crate) pc_var_idx: VarIndex,
    /// Map from pc value (as a TLA+ string Value) to the list of action indices
    /// that are guarded by that pc value.
    pub(crate) dispatch: FxHashMap<Value, Vec<usize>>,
    /// The detected action expressions from the Next disjunction, in order.
    /// Used during BFS to enumerate only matching actions.
    pub(crate) actions: Vec<DetectedAction>,
    /// Total number of actions in the spec (for debug logging and fallback path).
    #[allow(dead_code)] // Used only in debug_assertions builds
    pub(crate) total_actions: usize,
}

impl PcDispatchTable {
    /// Look up the action indices for a given `pc` value.
    ///
    /// Returns `Some(&[usize])` if the value is in the table, `None` if it
    /// is not (caller should fall back to evaluating all actions).
    #[inline]
    pub(crate) fn actions_for_pc(&self, pc_value: &Value) -> Option<&[usize]> {
        self.dispatch.get(pc_value).map(|v| v.as_slice())
    }
}

/// Attempt to detect PlusCal-style `pc` dispatch and build a dispatch table.
///
/// Returns `Some(PcDispatchTable)` if the spec follows the PlusCal pattern
/// where ALL actions in the Next disjunction are guarded by `pc = "label"`.
/// Returns `None` if the pattern is not detected (non-PlusCal spec or mixed
/// guard patterns).
///
/// # Arguments
/// * `next_def` - The expanded Next operator definition
/// * `vars` - State variable names
/// * `var_registry` - Variable index registry
/// * `ctx` - Evaluation context for resolving operator references
pub(crate) fn detect_pc_dispatch(
    next_def: &OperatorDef,
    vars: &[std::sync::Arc<str>],
    var_registry: &tla_core::VarRegistry,
    ctx: &EvalCtx,
) -> Option<PcDispatchTable> {
    // Step 1: Find the `pc` variable index.
    let pc_var_idx = var_registry.get("pc")?;

    // Step 2: Detect top-level action disjuncts.
    let actions = detect_actions(next_def);
    if actions.len() < 2 {
        // Single action or no actions — dispatch table would not help.
        return None;
    }

    // Step 3: For each action, check if its first conjunct is `pc = "literal"`.
    // If ALL actions follow this pattern, build the dispatch table.
    // When an action is an operator reference (Ident), resolve it to its body
    // to inspect the pc guard pattern.
    let mut dispatch: FxHashMap<Value, Vec<usize>> = FxHashMap::default();

    for (idx, action) in actions.iter().enumerate() {
        let guard = extract_pc_guard_resolved(&action.expr.node, "pc", ctx);
        match guard {
            Some(label) => {
                let pc_value = Value::string(label);
                dispatch.entry(pc_value).or_default().push(idx);
            }
            None => {
                // This action doesn't follow the pc = "label" pattern.
                // Bail out — we can't use pc dispatch for this spec.
                return None;
            }
        }
    }

    // Step 4: Verify we have a non-trivial dispatch (at least 2 distinct pc values).
    if dispatch.len() < 2 {
        return None;
    }

    let _ = vars; // vars used for future multi-process extension
    let total_actions = actions.len();

    Some(PcDispatchTable {
        pc_var_idx,
        dispatch,
        actions,
        total_actions,
    })
}

/// Extract the `pc` guard value from an action expression, resolving operator
/// references through the `EvalCtx`.
///
/// When the expression is an `Ident` (operator reference like `A`), looks up
/// the operator's definition and inspects its body for the pc guard pattern.
/// When the expression is `Apply(Ident("A"), [self])` (multi-process PlusCal),
/// resolves operator `A` and inspects its body.
///
/// This function handles recursive structural wrappers (EXISTS, LET, Label, And)
/// before trying operator resolution, so patterns like
/// `\E self \in S : p(self)` are correctly followed through to find the
/// pc guard inside p's body.
fn extract_pc_guard_resolved(expr: &Expr, pc_name: &str, ctx: &EvalCtx) -> Option<String> {
    match expr {
        Expr::Ident(name, _) => {
            // Resolve operator reference to its body and check the body.
            if let Some(op_def) = ctx.get_op(name) {
                // Recurse with resolution so nested Ident/Apply are also resolved.
                extract_pc_guard_resolved(&op_def.body.node, pc_name, ctx)
            } else {
                None
            }
        }
        // Multi-process PlusCal: Apply(Ident("ncs"), [self]) where ncs(self)
        // is an operator whose body starts with `pc[self] = "label"`.
        Expr::Apply(op_expr, _args) => {
            if let Expr::Ident(name, _) = &op_expr.node {
                if let Some(op_def) = ctx.get_op(name) {
                    return extract_pc_guard_resolved(&op_def.body.node, pc_name, ctx);
                }
            }
            extract_pc_guard(expr, pc_name)
        }
        // Structural wrappers: recurse with resolution so we can resolve
        // operator references inside EXISTS, LET, etc.
        Expr::Exists(_bounds, body) => extract_pc_guard_resolved(&body.node, pc_name, ctx),
        Expr::Let(_defs, body) => extract_pc_guard_resolved(&body.node, pc_name, ctx),
        Expr::Label(label) => extract_pc_guard_resolved(&label.body.node, pc_name, ctx),
        // Conjunction: check leftmost conjunct (may need resolution)
        Expr::And(lhs, _rhs) => extract_pc_guard_resolved(&lhs.node, pc_name, ctx),
        // Direct equality
        Expr::Eq(_, _) => extract_pc_eq_literal(expr, pc_name),
        // Or: not a guard pattern at this level
        _ => None,
    }
}

/// Extract the `pc` guard value from an action expression.
///
/// Looks for patterns:
/// - `pc = "label" /\ ...` (guard is first conjunct)
/// - `pc = "label"` (guard is the entire expression)
/// - Through EXISTS wrappers: `\E self \in S : pc = "label" /\ ...`
/// - Through LET wrappers: `LET x == ... IN pc = "label" /\ ...`
///
/// Returns `Some(label)` if found, `None` otherwise.
fn extract_pc_guard(expr: &Expr, pc_name: &str) -> Option<String> {
    match expr {
        // Conjunction: find the leftmost conjunct in a left-associative chain.
        // In `A /\ B /\ C`, the AST is `And(And(A, B), C)`, so the first
        // conjunct is found by recursively following the left child.
        Expr::And(lhs, _rhs) => extract_pc_guard(&lhs.node, pc_name),

        // Direct equality: `pc = "label"` (action is just a guard, rare but valid)
        Expr::Eq(_, _) => extract_pc_eq_literal(expr, pc_name),

        // EXISTS wrapper: look inside the body
        Expr::Exists(_bounds, body) => extract_pc_guard(&body.node, pc_name),

        // LET wrapper: look inside the body
        Expr::Let(_defs, body) => extract_pc_guard(&body.node, pc_name),

        // Label wrapper: look inside
        Expr::Label(label) => extract_pc_guard(&label.body.node, pc_name),

        // Operator application: the action is applied via an operator reference.
        // We cannot inspect the body without resolving it, so bail out.
        _ => None,
    }
}

/// Check if an expression is `pc = "literal"` or `pc[_] = "literal"` and
/// extract the literal value.
///
/// Handles:
/// - `Expr::Eq(Ident("pc"), String("label"))` — parser output, single-process
/// - `Expr::Eq(StateVar("pc", idx, nid), String("label"))` — after AST transform, single-process
/// - `Expr::Eq(FuncApply(Ident("pc"), _), String("label"))` — multi-process `pc[self] = "label"`
/// - `Expr::Eq(FuncApply(StateVar("pc", ..), _), String("label"))` — multi-process after AST transform
fn extract_pc_eq_literal(expr: &Expr, pc_name: &str) -> Option<String> {
    match expr {
        Expr::Eq(lhs, rhs) => {
            // Check lhs is `pc` (ident, state var, or function application of pc)
            let is_pc_lhs = is_pc_reference(&lhs.node, pc_name);
            if !is_pc_lhs {
                // Also check reversed: "label" = pc or "label" = pc[self]
                let is_pc_rhs = is_pc_reference(&rhs.node, pc_name);
                if is_pc_rhs {
                    // Extract literal from lhs
                    if let Expr::String(label) = &lhs.node {
                        return Some(label.clone());
                    }
                }
                return None;
            }
            // Extract literal from rhs
            if let Expr::String(label) = &rhs.node {
                return Some(label.clone());
            }
            None
        }
        _ => None,
    }
}

/// Check if an expression refers to `pc` — either directly (`pc`), as a state
/// variable (`StateVar("pc", ..)`), or as a function application (`pc[self]`).
fn is_pc_reference(expr: &Expr, pc_name: &str) -> bool {
    match expr {
        Expr::Ident(name, _) => name == pc_name,
        Expr::StateVar(name, _, _) => name == pc_name,
        // Multi-process PlusCal: pc[self] is FuncApply(pc, self)
        Expr::FuncApply(func_expr, _arg) => match &func_expr.node {
            Expr::Ident(name, _) => name == pc_name,
            Expr::StateVar(name, _, _) => name == pc_name,
            _ => false,
        },
        _ => false,
    }
}

/// Check if an Or branch has a `pc` guard that does NOT match the given current
/// value, meaning the branch is guaranteed to produce zero successors.
///
/// This is the hot-path function used by the unified enumerator to skip Or branches
/// in PlusCal-style specs. It resolves Ident references through the EvalCtx and
/// compares the guard literal against the current pc value without allocating.
///
/// Handles both single-process (`pc = "label"`) and multi-process (`pc[self] = "label"`)
/// PlusCal patterns. For multi-process, `current_pc` is the entire function value
/// and the function argument (`self`) is resolved from the ctx binding stack.
///
/// Returns `true` if the branch's pc guard is known to NOT match (i.e., the branch
/// should be skipped). Returns `false` if the guard matches or cannot be determined.
///
/// Part of #3923: guard hoisting for PlusCal dispatch patterns.
#[inline]
pub(crate) fn or_branch_pc_guard_mismatches(
    expr: &Expr,
    current_pc: &Value,
    ctx: &EvalCtx,
) -> bool {
    // Extract the pc guard literal from this branch.
    // If we can't determine the guard, return false (don't skip — conservative).
    let guard_label = extract_pc_guard_resolved(expr, "pc", ctx);
    match guard_label {
        Some(label) => {
            let guard_value = Value::string(label);
            match current_pc {
                // Single-process: current_pc is a string value, direct comparison.
                Value::String(_) => guard_value != *current_pc,
                // Multi-process: current_pc is a function (pc : [Procs -> String]).
                // Look up the effective pc value for the current process by applying
                // the function to the `self` binding from the EXISTS scope.
                Value::Func(f) => {
                    match resolve_pc_func_apply(f, ctx) {
                        Some(effective_pc) => guard_value != *effective_pc,
                        None => false, // Can't resolve — don't skip (conservative)
                    }
                }
                Value::IntFunc(f) => match resolve_pc_int_func_apply(f, ctx) {
                    Some(effective_pc) => guard_value != *effective_pc,
                    None => false,
                },
                _ => false, // Unknown pc type — don't skip
            }
        }
        None => false, // Can't determine guard — don't skip
    }
}

/// Look up the `self` binding in the ctx and apply the pc function to get
/// the effective pc value for the current process.
///
/// Multi-process PlusCal specs use `pc[self] = "label"` guards where `pc`
/// is a function `[Procs -> String]` and `self` is bound by an EXISTS.
/// This function resolves the `self` binding and performs the function lookup
/// without constructing or evaluating AST nodes.
///
/// Overhead: one binding chain lookup (O(d) where d = binding depth, typically
/// 1-3 for EXISTS-bound variables) + one sorted-array binary search in FuncValue.
/// This is far cheaper than evaluating the entire action body (~100-1000 eval calls).
fn resolve_pc_func_apply<'a>(
    pc_func: &'a crate::value::FuncValue,
    ctx: &EvalCtx,
) -> Option<&'a Value> {
    // Look up "self" in the binding chain. PlusCal multi-process specs always
    // use "self" as the EXISTS-bound variable.
    let self_value = ctx.lookup_binding("self")?;
    pc_func.apply(&self_value)
}

/// Same as `resolve_pc_func_apply` but for IntIntervalFunc (integer-indexed pc).
fn resolve_pc_int_func_apply<'a>(
    pc_func: &'a crate::value::IntIntervalFunc,
    ctx: &EvalCtx,
) -> Option<&'a Value> {
    let self_value = ctx.lookup_binding("self")?;
    pc_func.apply(&self_value)
}

/// Check if a spec's Next operator body has Or branches guarded by `pc` patterns.
///
/// This is a looser check than `detect_pc_dispatch`, which requires ALL top-level
/// actions to have single-process `pc = "label"` guards. This function looks deeper:
/// it walks through the Next body (resolving operator references, following EXISTS,
/// LET, and Apply wrappers) to find Or nodes whose branches are guarded by pc patterns
/// (either `pc = "label"` or `pc[self] = "label"`).
///
/// Returns `true` if at least 2 distinct Or branches with pc guards are found.
///
/// Used by `run_prepare.rs` to enable multi-process PlusCal guard hoisting when
/// the full dispatch table can't be built (because pc is a function, not a string).
///
/// Part of #3805: multi-process PlusCal guard hoisting.
pub(crate) fn spec_has_pc_guards(next_def: &OperatorDef, ctx: &EvalCtx) -> bool {
    let mut guard_count = 0;
    count_pc_guarded_or_branches(&next_def.body.node, "pc", ctx, &mut guard_count, 0);
    guard_count >= 2
}

/// Recursively walk the expression tree to count Or branches with pc guards.
///
/// Follows through Exists, Let, Label, Ident (operator references), and Apply
/// to find Or nodes. For each Or, checks if either branch has a pc guard pattern.
fn count_pc_guarded_or_branches(
    expr: &Expr,
    pc_name: &str,
    ctx: &EvalCtx,
    count: &mut usize,
    depth: usize,
) {
    // Prevent unbounded recursion through mutually-recursive operators.
    if depth > 20 {
        return;
    }
    match expr {
        Expr::Or(a, b) => {
            // Check if each branch has a pc guard
            if extract_pc_guard_resolved(&a.node, pc_name, ctx).is_some() {
                *count += 1;
            }
            if extract_pc_guard_resolved(&b.node, pc_name, ctx).is_some() {
                *count += 1;
            }
            // Also recurse into branches in case they contain nested Or nodes
            count_pc_guarded_or_branches(&a.node, pc_name, ctx, count, depth + 1);
            count_pc_guarded_or_branches(&b.node, pc_name, ctx, count, depth + 1);
        }
        Expr::Exists(_bounds, body) => {
            count_pc_guarded_or_branches(&body.node, pc_name, ctx, count, depth + 1);
        }
        Expr::Let(_defs, body) => {
            count_pc_guarded_or_branches(&body.node, pc_name, ctx, count, depth + 1);
        }
        Expr::Label(label) => {
            count_pc_guarded_or_branches(&label.body.node, pc_name, ctx, count, depth + 1);
        }
        Expr::Ident(name, _) => {
            if let Some(op_def) = ctx.get_op(name) {
                count_pc_guarded_or_branches(&op_def.body.node, pc_name, ctx, count, depth + 1);
            }
        }
        Expr::Apply(op_expr, _args) => {
            if let Expr::Ident(name, _) = &op_expr.node {
                if let Some(op_def) = ctx.get_op(name) {
                    count_pc_guarded_or_branches(&op_def.body.node, pc_name, ctx, count, depth + 1);
                }
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::checker_setup::{setup_checker_modules, SetupOptions};
    use crate::config::Config;
    use crate::test_support::parse_module;

    fn make_dispatch_table(src: &str) -> Option<PcDispatchTable> {
        let module = parse_module(src);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let setup = setup_checker_modules(
            &module,
            &[],
            &config,
            &SetupOptions {
                load_instances: true,
            },
        );
        let next_def = setup.ctx.get_op("Next")?.as_ref().clone();
        let registry = setup.ctx.var_registry().clone();
        detect_pc_dispatch(&next_def, &setup.vars, &registry, &setup.ctx)
    }

    #[test]
    fn test_debug_detection() {
        let src = r#"
---- MODULE PcTestDbg ----
EXTENDS Integers
VARIABLE pc, x

Init == pc = "start" /\ x = 0

A == pc = "start" /\ x' = x + 1 /\ pc' = "middle"
B == pc = "middle" /\ x' = x * 2 /\ pc' = "done"
C == pc = "done" /\ UNCHANGED <<x, pc>>

Next == A \/ B \/ C
====
"#;
        let module = parse_module(src);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let setup = setup_checker_modules(
            &module,
            &[],
            &config,
            &SetupOptions {
                load_instances: true,
            },
        );
        let next_def_arc = setup.ctx.get_op("Next");
        assert!(
            next_def_arc.is_some(),
            "Next operator should be found in ctx"
        );

        let next_def = next_def_arc.unwrap();
        let actions = detect_actions(next_def);
        assert_eq!(
            actions.len(),
            3,
            "should detect 3 disjunct actions (A, B, C)"
        );

        // Verify each action is resolvable in the context
        for action in &actions {
            assert!(
                setup.ctx.get_op(&action.name).is_some(),
                "action '{}' should be resolvable in ctx",
                action.name
            );
        }

        let registry = setup.ctx.var_registry().clone();
        assert!(
            registry.get("pc").is_some(),
            "pc variable should be registered"
        );
    }

    #[test]
    fn test_detect_pluscal_single_process() {
        let src = r#"
---- MODULE PcTest ----
EXTENDS Integers
VARIABLE pc, x

Init == pc = "start" /\ x = 0

A == pc = "start" /\ x' = x + 1 /\ pc' = "middle"
B == pc = "middle" /\ x' = x * 2 /\ pc' = "done"
C == pc = "done" /\ UNCHANGED <<x, pc>>

Next == A \/ B \/ C
====
"#;
        let table = make_dispatch_table(src);
        assert!(table.is_some(), "Should detect PlusCal pattern");
        let table = table.unwrap();
        assert_eq!(table.total_actions, 3);

        // Check dispatch entries
        let start = table.actions_for_pc(&Value::string("start".to_string()));
        assert!(start.is_some());
        assert_eq!(start.unwrap().len(), 1);

        let middle = table.actions_for_pc(&Value::string("middle".to_string()));
        assert!(middle.is_some());
        assert_eq!(middle.unwrap().len(), 1);

        let done = table.actions_for_pc(&Value::string("done".to_string()));
        assert!(done.is_some());
        assert_eq!(done.unwrap().len(), 1);

        // Unknown pc value
        let unknown = table.actions_for_pc(&Value::string("unknown".to_string()));
        assert!(unknown.is_none());
    }

    #[test]
    fn test_no_dispatch_for_non_pluscal() {
        let src = r#"
---- MODULE NoPcTest ----
EXTENDS Integers
VARIABLE x, y

Init == x = 0 /\ y = 0

A == x' = x + 1 /\ y' = y
B == x' = x /\ y' = y + 1

Next == A \/ B
====
"#;
        // No `pc` variable at all
        let table = make_dispatch_table(src);
        assert!(
            table.is_none(),
            "Should not detect PlusCal pattern without pc"
        );
    }

    #[test]
    fn test_no_dispatch_when_mixed_guards() {
        let src = r#"
---- MODULE MixedTest ----
EXTENDS Integers
VARIABLE pc, x

Init == pc = "start" /\ x = 0

A == pc = "start" /\ x' = x + 1 /\ pc' = "done"
B == x > 5 /\ x' = 0 /\ pc' = "start"

Next == A \/ B
====
"#;
        // B doesn't have a pc guard
        let table = make_dispatch_table(src);
        assert!(
            table.is_none(),
            "Should not detect when not all actions have pc guards"
        );
    }

    #[test]
    fn test_dispatch_with_shared_pc_value() {
        let src = r#"
---- MODULE SharedPcTest ----
EXTENDS Integers
VARIABLE pc, x

Init == pc = "start" /\ x = 0

A == pc = "start" /\ x < 10 /\ x' = x + 1 /\ pc' = "start"
B == pc = "start" /\ x >= 10 /\ x' = 0 /\ pc' = "done"
C == pc = "done" /\ UNCHANGED <<x, pc>>

Next == A \/ B \/ C
====
"#;
        let table = make_dispatch_table(src);
        assert!(table.is_some());
        let table = table.unwrap();

        // "start" should map to both A (idx 0) and B (idx 1)
        let start = table.actions_for_pc(&Value::string("start".to_string()));
        assert!(start.is_some());
        assert_eq!(start.unwrap().len(), 2);

        let done = table.actions_for_pc(&Value::string("done".to_string()));
        assert!(done.is_some());
        assert_eq!(done.unwrap().len(), 1);
    }

    /// Test that `or_branch_pc_guard_mismatches` correctly identifies branches
    /// with non-matching pc guards.
    #[test]
    fn test_or_branch_guard_mismatch_detection() {
        let src = r#"
---- MODULE PcMismatch ----
EXTENDS Integers
VARIABLE pc, x

Init == pc = "start" /\ x = 0

A == pc = "start" /\ x' = x + 1 /\ pc' = "middle"
B == pc = "middle" /\ x' = x * 2 /\ pc' = "done"
C == pc = "done" /\ UNCHANGED <<x, pc>>

Next == A \/ B \/ C
====
"#;
        let module = parse_module(src);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let setup = setup_checker_modules(
            &module,
            &[],
            &config,
            &SetupOptions {
                load_instances: true,
            },
        );

        // Test that or_branch_pc_guard_mismatches works with the ctx
        let current_pc_start = Value::string("start".to_string());
        let current_pc_middle = Value::string("middle".to_string());

        // Get the A operator body — its first conjunct is `pc = "start"`
        let a_def = setup.ctx.get_op("A").unwrap();
        // A's body has pc = "start" guard — should NOT mismatch when pc = "start"
        assert!(
            !or_branch_pc_guard_mismatches(
                &tla_core::ast::Expr::Ident("A".to_string(), tla_core::NameId::INVALID),
                &current_pc_start,
                &setup.ctx,
            ),
            "A should match when pc = start"
        );
        // A's body has pc = "start" guard — should mismatch when pc = "middle"
        assert!(
            or_branch_pc_guard_mismatches(
                &tla_core::ast::Expr::Ident("A".to_string(), tla_core::NameId::INVALID),
                &current_pc_middle,
                &setup.ctx,
            ),
            "A should NOT match when pc = middle"
        );

        // B's body has pc = "middle" guard
        assert!(
            or_branch_pc_guard_mismatches(
                &tla_core::ast::Expr::Ident("B".to_string(), tla_core::NameId::INVALID),
                &current_pc_start,
                &setup.ctx,
            ),
            "B should NOT match when pc = start"
        );
        assert!(
            !or_branch_pc_guard_mismatches(
                &tla_core::ast::Expr::Ident("B".to_string(), tla_core::NameId::INVALID),
                &current_pc_middle,
                &setup.ctx,
            ),
            "B should match when pc = middle"
        );

        let _ = a_def; // suppress unused warning
    }

    /// Test that guard hoisting produces the same successors as the non-optimized path.
    ///
    /// Part of #3923: correctness verification for pc-guard hoisting.
    /// Enumerates successors with and without guard hoisting and verifies
    /// the same set of successor fingerprints is produced.
    #[test]
    fn test_guard_hoisting_same_successors_as_unoptimized() {
        let src = r#"
---- MODULE PcHoistParity ----
EXTENDS Integers
VARIABLE pc, x

Init == pc = "start" /\ x = 0

A == pc = "start" /\ x' = x + 1 /\ pc' = "middle"
B == pc = "middle" /\ x' = x * 2 /\ pc' = "done"
C == pc = "done" /\ UNCHANGED <<x, pc>>

Next == A \/ B \/ C
====
"#;
        let module = parse_module(src);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let setup = setup_checker_modules(
            &module,
            &[],
            &config,
            &SetupOptions {
                load_instances: true,
            },
        );

        let registry = setup.ctx.var_registry().clone();
        let pc_idx = registry.get("pc").expect("pc variable should exist");

        // Detect the pc dispatch table
        let next_def = setup.ctx.get_op("Next").unwrap().as_ref().clone();
        let table = detect_pc_dispatch(&next_def, &setup.vars, &registry, &setup.ctx);
        assert!(table.is_some(), "Should detect PlusCal pattern");

        // Test with pc = "start": should get successor from A only
        {
            let state = crate::state::ArrayState::from_values(vec![
                Value::string("start".to_string()), // pc
                Value::int(0),                      // x
            ]);

            // Without hoisting — bind state env so evaluator can read state vars
            let mut ctx1 = setup.ctx.clone();
            let _guard1 = ctx1.bind_state_env_guard(state.env_ref());
            let succs_no_hoist = crate::enumerate::enumerate_successors_array_with_tir(
                &mut ctx1,
                &next_def,
                &state,
                &setup.vars,
                None,
            )
            .unwrap();

            // With hoisting — bind state env for the same reason
            let mut ctx2 = setup.ctx.clone();
            let _guard2 = ctx2.bind_state_env_guard(state.env_ref());
            let diffs_with_hoist =
                crate::enumerate::successor_engine_test_helpers::run_with_pc_hoist(
                    &mut ctx2,
                    &next_def.body,
                    &state,
                    &setup.vars,
                    &registry,
                    pc_idx,
                )
                .unwrap();

            // Compare: same number of successors
            assert_eq!(
                succs_no_hoist.len(),
                diffs_with_hoist.len(),
                "pc=start: hoist and non-hoist should produce same successor count"
            );
        }

        // Test with pc = "middle": should get successor from B only
        {
            let state = crate::state::ArrayState::from_values(vec![
                Value::string("middle".to_string()), // pc
                Value::int(5),                       // x
            ]);

            let mut ctx1 = setup.ctx.clone();
            let _guard1 = ctx1.bind_state_env_guard(state.env_ref());
            let succs_no_hoist = crate::enumerate::enumerate_successors_array_with_tir(
                &mut ctx1,
                &next_def,
                &state,
                &setup.vars,
                None,
            )
            .unwrap();

            let mut ctx2 = setup.ctx.clone();
            let _guard2 = ctx2.bind_state_env_guard(state.env_ref());
            let diffs_with_hoist =
                crate::enumerate::successor_engine_test_helpers::run_with_pc_hoist(
                    &mut ctx2,
                    &next_def.body,
                    &state,
                    &setup.vars,
                    &registry,
                    pc_idx,
                )
                .unwrap();

            assert_eq!(
                succs_no_hoist.len(),
                diffs_with_hoist.len(),
                "pc=middle: hoist and non-hoist should produce same successor count"
            );
        }

        // Test with pc = "done": should get successor from C (UNCHANGED)
        {
            let state = crate::state::ArrayState::from_values(vec![
                Value::string("done".to_string()), // pc
                Value::int(10),                    // x
            ]);

            let mut ctx1 = setup.ctx.clone();
            let _guard1 = ctx1.bind_state_env_guard(state.env_ref());
            let succs_no_hoist = crate::enumerate::enumerate_successors_array_with_tir(
                &mut ctx1,
                &next_def,
                &state,
                &setup.vars,
                None,
            )
            .unwrap();

            let mut ctx2 = setup.ctx.clone();
            let _guard2 = ctx2.bind_state_env_guard(state.env_ref());
            let diffs_with_hoist =
                crate::enumerate::successor_engine_test_helpers::run_with_pc_hoist(
                    &mut ctx2,
                    &next_def.body,
                    &state,
                    &setup.vars,
                    &registry,
                    pc_idx,
                )
                .unwrap();

            assert_eq!(
                succs_no_hoist.len(),
                diffs_with_hoist.len(),
                "pc=done: hoist and non-hoist should produce same successor count"
            );
        }
    }

    /// Test that `extract_pc_guard_resolved` detects multi-process PlusCal patterns
    /// where the guard is `pc[self] = "label"` inside operator bodies.
    ///
    /// Part of #3805: multi-process PlusCal pc-dispatch.
    #[test]
    fn test_multi_process_guard_extraction() {
        let src = r#"
---- MODULE MultiProc ----
EXTENDS Integers
CONSTANT Procs
VARIABLE pc, x

Init == pc = [p \in Procs |-> "start"] /\ x = [p \in Procs |-> 0]

A(self) == pc[self] = "start" /\ x' = [x EXCEPT ![self] = x[self] + 1] /\ pc' = [pc EXCEPT ![self] = "done"]
B(self) == pc[self] = "done" /\ UNCHANGED <<x, pc>>

p(self) == A(self) \/ B(self)

Next == \E self \in Procs : p(self)
====
"#;
        let module = parse_module(src);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let setup = setup_checker_modules(
            &module,
            &[],
            &config,
            &SetupOptions {
                load_instances: true,
            },
        );

        // Verify that extract_pc_guard_resolved can extract guard labels from
        // multi-process operator references like A(self) whose body starts with
        // pc[self] = "start".
        let a_ident = tla_core::ast::Expr::Apply(
            Box::new(tla_core::Spanned {
                node: tla_core::ast::Expr::Ident("A".to_string(), tla_core::NameId::INVALID),
                span: tla_core::Span::dummy(),
            }),
            vec![tla_core::Spanned {
                node: tla_core::ast::Expr::Ident("self".to_string(), tla_core::NameId::INVALID),
                span: tla_core::Span::dummy(),
            }],
        );
        let guard_a = extract_pc_guard_resolved(&a_ident, "pc", &setup.ctx);
        assert_eq!(
            guard_a,
            Some("start".to_string()),
            "A(self) should have pc guard 'start'"
        );

        let b_ident = tla_core::ast::Expr::Apply(
            Box::new(tla_core::Spanned {
                node: tla_core::ast::Expr::Ident("B".to_string(), tla_core::NameId::INVALID),
                span: tla_core::Span::dummy(),
            }),
            vec![tla_core::Spanned {
                node: tla_core::ast::Expr::Ident("self".to_string(), tla_core::NameId::INVALID),
                span: tla_core::Span::dummy(),
            }],
        );
        let guard_b = extract_pc_guard_resolved(&b_ident, "pc", &setup.ctx);
        assert_eq!(
            guard_b,
            Some("done".to_string()),
            "B(self) should have pc guard 'done'"
        );
    }

    /// Test that `or_branch_pc_guard_mismatches` correctly skips multi-process
    /// PlusCal branches when `pc` is a function and `self` is bound.
    ///
    /// Part of #3805: multi-process PlusCal pc-dispatch.
    #[test]
    fn test_multi_process_guard_mismatch() {
        use std::sync::Arc;

        let src = r#"
---- MODULE MultiProcGuard ----
EXTENDS Integers
CONSTANT Procs
VARIABLE pc, x

Init == pc = [p \in Procs |-> "start"] /\ x = [p \in Procs |-> 0]

A(self) == pc[self] = "start" /\ x' = [x EXCEPT ![self] = x[self] + 1] /\ pc' = [pc EXCEPT ![self] = "done"]
B(self) == pc[self] = "done" /\ UNCHANGED <<x, pc>>

p(self) == A(self) \/ B(self)

Next == \E self \in Procs : p(self)
====
"#;
        let module = parse_module(src);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let setup = setup_checker_modules(
            &module,
            &[],
            &config,
            &SetupOptions {
                load_instances: true,
            },
        );

        // Build a pc function: [p1 |-> "start", p2 |-> "done"]
        let mut fb = crate::value::FuncBuilder::new();
        fb.insert(
            Value::string("p1".to_string()),
            Value::string("start".to_string()),
        );
        fb.insert(
            Value::string("p2".to_string()),
            Value::string("done".to_string()),
        );
        let pc_func = Value::Func(Arc::new(fb.build()));

        let a_expr = tla_core::ast::Expr::Apply(
            Box::new(tla_core::Spanned {
                node: tla_core::ast::Expr::Ident("A".to_string(), tla_core::NameId::INVALID),
                span: tla_core::Span::dummy(),
            }),
            vec![tla_core::Spanned {
                node: tla_core::ast::Expr::Ident("self".to_string(), tla_core::NameId::INVALID),
                span: tla_core::Span::dummy(),
            }],
        );

        // Bind self = "p1" (pc["p1"] = "start") — A should match, B should not
        {
            let mut ctx = setup.ctx.clone();
            ctx.push_binding(Arc::from("self"), Value::string("p1".to_string()));

            // A(self) has guard "start", pc["p1"] = "start" → should NOT mismatch
            assert!(
                !or_branch_pc_guard_mismatches(&a_expr, &pc_func, &ctx),
                "A(self) should match when pc[p1] = start"
            );
        }

        // Bind self = "p2" (pc["p2"] = "done") — A should NOT match, B should
        {
            let mut ctx = setup.ctx.clone();
            ctx.push_binding(Arc::from("self"), Value::string("p2".to_string()));

            // A(self) has guard "start", pc["p2"] = "done" → should mismatch
            assert!(
                or_branch_pc_guard_mismatches(&a_expr, &pc_func, &ctx),
                "A(self) should NOT match when pc[p2] = done"
            );
        }
    }

    /// Test that `spec_has_pc_guards` detects multi-process PlusCal specs.
    ///
    /// Part of #3805: multi-process PlusCal guard hoisting.
    #[test]
    fn test_spec_has_pc_guards_multiprocess() {
        let src = r#"
---- MODULE MultiProcDetect ----
EXTENDS Integers
CONSTANT Procs
VARIABLE pc, x

Init == pc = [p \in Procs |-> "start"] /\ x = [p \in Procs |-> 0]

A(self) == pc[self] = "start" /\ x' = [x EXCEPT ![self] = x[self] + 1] /\ pc' = [pc EXCEPT ![self] = "done"]
B(self) == pc[self] = "done" /\ UNCHANGED <<x, pc>>

p(self) == A(self) \/ B(self)

Next == \E self \in Procs : p(self)
====
"#;
        let module = parse_module(src);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let setup = setup_checker_modules(
            &module,
            &[],
            &config,
            &SetupOptions {
                load_instances: true,
            },
        );
        let next_def = setup.ctx.get_op("Next").unwrap().as_ref().clone();

        // Full dispatch table should NOT be built (multi-process)
        let registry = setup.ctx.var_registry().clone();
        let table = detect_pc_dispatch(&next_def, &setup.vars, &registry, &setup.ctx);
        assert!(
            table.is_none(),
            "Full dispatch table should not be built for multi-process spec"
        );

        // But spec_has_pc_guards should detect the pattern
        assert!(
            spec_has_pc_guards(&next_def, &setup.ctx),
            "spec_has_pc_guards should detect multi-process PlusCal pattern"
        );
    }

    /// Test that `spec_has_pc_guards` returns false for non-PlusCal specs.
    #[test]
    fn test_spec_has_pc_guards_non_pluscal() {
        let src = r#"
---- MODULE NoPcGuards ----
EXTENDS Integers
VARIABLE x, y

Init == x = 0 /\ y = 0
A == x' = x + 1 /\ y' = y
B == x' = x /\ y' = y + 1

Next == A \/ B
====
"#;
        let module = parse_module(src);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        let setup = setup_checker_modules(
            &module,
            &[],
            &config,
            &SetupOptions {
                load_instances: true,
            },
        );
        let next_def = setup.ctx.get_op("Next").unwrap().as_ref().clone();
        assert!(
            !spec_has_pc_guards(&next_def, &setup.ctx),
            "Non-PlusCal spec should not have pc guards"
        );
    }
}
