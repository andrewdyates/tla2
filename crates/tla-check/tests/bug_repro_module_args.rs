// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parallel modules, UNCHANGED alias, disjunctive action - Bugs #1253, #1089, #1278
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::parse_module;
use ntest::timeout;
use std::path::PathBuf;
use tla_check::{check_module, check_module_parallel, CheckResult, Config, ModelChecker};
use tla_core::{parse_to_syntax_tree, FileId, ModuleLoader};

// ============================================================================
// Bug #1253: Parallel setup does not initialize extended_module_names
// ============================================================================

/// Bug #1253: DyadicRationals builtin overrides must work in parallel setup.
///
/// The parallel checker setup path was missing the initialization of
/// `ctx.shared.extended_module_names`, which gates whether DyadicRationals
/// builtin operators (Add, Zero, One, Half, etc.) override user-defined
/// operators with the same name. Without this, the parallel checker would
/// treat user-defined `Add` as the builtin DyadicRationals.Add (or vice
/// versa), causing divergent behavior between sequential and parallel modes.
///
/// This test verifies that:
/// 1. A spec EXTENDING DyadicRationals gets the builtin Add override in both modes
/// 2. A spec NOT extending DyadicRationals uses the user-defined Add in both modes
/// 3. Sequential and parallel produce identical results
///
/// Part of #1253, Re: #1248, Re: #1250
#[cfg_attr(test, timeout(30000))]
#[test]
fn test_bug_1253_parallel_extended_module_names_dyadic_rationals() {
    // Spec that EXTENDS DyadicRationals -- builtin Add should fire
    let spec_with_dr = r#"
---- MODULE DyadicRationalsParParity ----
EXTENDS DyadicRationals

VARIABLE result

Init == result = Add(One, One)
Next == UNCHANGED result

\* DyadicRationals.Add(One, One) should produce a dyadic rational record
\* representing 2/1, i.e. [num |-> 2, den |-> 1]
TypeOK == result.num = 2 /\ result.den = 1
====
"#;

    let module_dr = parse_module(spec_with_dr);
    let config_dr = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    // Load DyadicRationals module from test_specs/tla_library
    let mut loader = ModuleLoader::with_base_dir(PathBuf::from("."));
    loader.add_search_path(PathBuf::from("../../test_specs/tla_library"));

    let extended_module_names = loader
        .load_extends(&module_dr)
        .expect("Failed to load DyadicRationals");

    let extended_modules: Vec<_> = extended_module_names
        .iter()
        .filter_map(|name| loader.get(name).map(|l| &l.module))
        .collect();

    // Sequential: should succeed (builtin Add produces dyadic rational)
    let mut seq_checker = ModelChecker::new_with_extends(&module_dr, &extended_modules, &config_dr);
    seq_checker.set_deadlock_check(false);
    let seq_result = seq_checker.check();

    match &seq_result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 1, "Sequential: expected 1 state");
        }
        other => panic!(
            "Bug #1253: Sequential DyadicRationals.Add failed: {:?}",
            other
        ),
    }

    // Parallel: should also succeed (builtin Add produces dyadic rational)
    let mut par_checker =
        tla_check::ParallelChecker::new_with_extends(&module_dr, &extended_modules, &config_dr, 2);
    par_checker.set_deadlock_check(false);
    let par_result = par_checker.check();

    match &par_result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 1, "Parallel: expected 1 state");
        }
        other => panic!(
            "Bug #1253: Parallel DyadicRationals.Add failed. \
             If parallel setup did not initialize extended_module_names, \
             the builtin Add override would not fire: {:?}",
            other
        ),
    }
}

/// Bug #1253 (part 2): User-defined Add must NOT be overridden when
/// DyadicRationals is NOT extended, in both sequential and parallel modes.
///
/// Part of #1253
#[cfg_attr(test, timeout(30000))]
#[test]
fn test_bug_1253_user_defined_add_not_overridden_without_dyadic_rationals() {
    // Spec that does NOT extend DyadicRationals -- user Add should be used
    let spec_no_dr = r#"
---- MODULE UserAddNoDR ----
VARIABLE result

Add(a, b) == a + b

Init == result = Add(3, 4)
Next == UNCHANGED result

TypeOK == result = 7
====
"#;

    let module = parse_module(spec_no_dr);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    // Sequential: user Add(3,4) = 7
    let seq_result = check_module(&module, &config);
    match &seq_result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 1, "Sequential: expected 1 state");
        }
        other => panic!("Bug #1253: Sequential user-defined Add failed: {:?}", other),
    }

    // Parallel: user Add(3,4) = 7
    let par_result = check_module_parallel(&module, &config, 2);
    match &par_result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 1, "Parallel: expected 1 state");
        }
        other => panic!("Bug #1253: Parallel user-defined Add failed: {:?}", other),
    }
}

// ============================================================================
// Bug #1089: UNCHANGED alias + action-level Apply arguments
// ============================================================================

/// Bug #1089: UNCHANGED with definition alias crashes during enumeration
///
/// When an action operator passes action-level arguments (containing primed
/// variables) to a user-defined operator, and that operator uses `UNCHANGED vars`
/// where `vars` is defined as a tuple (e.g., `vars == <<x, y>>`), two bugs
/// caused "Primed variable cannot be evaluated (no next-state context)":
///
/// 1. Compiled action UNCHANGED extraction didn't resolve definition aliases
///    through ctx.get_op() — only handled direct variable identifiers.
/// 2. AST enumeration paths (array_rec, and_enumeration) eagerly evaluated
///    action-level arguments instead of using call-by-name substitution.
///
/// Minimal reproduction of the LockHS / PostStutter pattern.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_issue_1089_unchanged_alias_with_action_arg() {
    // Minimal spec: operator takes an action argument, uses UNCHANGED via alias.
    // Pattern from LockHS/PostStutter: auxiliary variable `aux` is managed via
    // an operator that takes the base action as argument and applies UNCHANGED
    // to the auxiliary variable(s) via a definition alias.
    let spec = r#"
---- MODULE UnchangedAliasActionArg ----
VARIABLES x, aux

auxvars == <<aux>>

Init == x = 0 /\ aux = 0

\* NoAuxChange: wraps action A with UNCHANGED auxvars (alias for <<aux>>).
\* Before fix, UNCHANGED auxvars would fail because the compiled action extractor
\* didn't resolve the `auxvars` alias to the actual variable tuple.
NoAuxChange(A) == A /\ UNCHANGED auxvars

\* Step modifies x only
Step == x' = 1 - x

\* Next passes the action to NoAuxChange
Next == NoAuxChange(Step)

Inv == x \in {0, 1} /\ aux = 0
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    // Before fix: crashes with "Primed variable cannot be evaluated"
    // After fix: finds 2 states (x=0,aux=0 and x=1,aux=0)
    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 2,
                "Bug #1089: expected 2 states, got {}",
                stats.states_found
            );
        }
        other => panic!(
            "Bug #1089: UNCHANGED alias with action arg failed: {:?}",
            other
        ),
    }
}

/// Bug #1089 variant: action-level argument without UNCHANGED alias.
/// Tests the call-by-name fix in array_rec and and_enumeration independently
/// of the UNCHANGED alias resolution fix.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_issue_1089_action_arg_call_by_name() {
    // Operator that takes an action and wraps it with an extra UNCHANGED
    let spec = r#"
---- MODULE ActionArgCallByName ----
VARIABLES x, y

Init == x = 0 /\ y = 0

\* NoChange wraps action A and keeps y unchanged
NoChange(A) == A /\ UNCHANGED y

\* Step modifies x
Step == x' = 1 - x

Next == NoChange(Step)

Inv == x \in {0, 1} /\ y = 0
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 2,
                "Bug #1089 variant: expected 2 states, got {}",
                stats.states_found
            );
        }
        other => panic!("Bug #1089: action arg call-by-name failed: {:?}", other),
    }
}

// ============================================================================
// Bug #1278: Disjunctive action in [A]_v subscript silently dropped
// ============================================================================

/// Bug #1278: `[Next \/ UNCHANGED vars]_vars` extracts only `Next`, dropping
/// the `\/ UNCHANGED vars` disjunct.
///
/// Trace validation specs commonly use `[][Next \/ UNCHANGED vars]_vars` to
/// allow both real transitions and stuttering. Before fix, extract_action_with_node()
/// only checked for QuantExpr, falling through to extract_action_name() which
/// returned the first Ident token ("Next"), silently discarding the disjunction.
///
/// This test verifies:
/// 1. extract_spec_formula correctly identifies the disjunctive action and sets next_node
/// 2. The inline next lowering + registration pipeline works end-to-end
/// 3. State count matches TLC (4 states)
#[timeout(30000)]
#[test]
fn bug_1278_disjunction_in_action_subscript() {
    // Parse the spec with the SPECIFICATION formula containing disjunction
    let src = r#"
---- MODULE Bug1278 ----
EXTENDS Integers
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = x + 1 /\ x < 3
TraceSpec == Init /\ [][Next \/ UNCHANGED vars]_vars
===="#;

    let tree = parse_to_syntax_tree(src);
    let module = parse_module(src);

    // Find TraceSpec operator body in the CST
    fn find_op_body(node: &tla_core::SyntaxNode, name: &str) -> Option<tla_core::SyntaxNode> {
        use tla_core::{SyntaxElement, SyntaxKind};
        if node.kind() == SyntaxKind::OperatorDef {
            let mut found_name = false;
            for child in node.children_with_tokens() {
                if let SyntaxElement::Token(t) = child {
                    if t.kind() == SyntaxKind::Ident && t.text() == name {
                        found_name = true;
                        break;
                    }
                }
            }
            if found_name {
                let mut past_def_eq = false;
                for child in node.children_with_tokens() {
                    match child {
                        SyntaxElement::Token(t) if t.kind() == SyntaxKind::DefEqOp => {
                            past_def_eq = true;
                        }
                        SyntaxElement::Node(n) if past_def_eq => {
                            return Some(n);
                        }
                        _ => {}
                    }
                }
            }
        }
        for child in node.children() {
            if let Some(found) = find_op_body(&child, name) {
                return Some(found);
            }
        }
        None
    }

    // Step 1: Verify extraction correctly identifies the disjunctive action
    let spec_body = find_op_body(&tree, "TraceSpec").expect("TraceSpec not found in CST");
    let formula =
        tla_check::extract_spec_formula(&spec_body).expect("Failed to extract spec formula");

    assert!(
        formula.next_node.is_some(),
        "Bug #1278: next_node should be Some for disjunctive action, got next='{}'",
        formula.next
    );
    assert!(
        formula.next.contains("UNCHANGED"),
        "Bug #1278: next should contain 'UNCHANGED', got '{}'",
        formula.next
    );
    assert_eq!(formula.init, "Init");
    assert!(formula.stuttering_allowed);

    // Step 2: Verify the inline next node can be lowered to an AST expression.
    // This confirms the CST node from the extraction is valid for the lowering pipeline
    // that register_inline_next() uses.
    let next_node = formula.next_node.as_ref().unwrap();
    let lowered = tla_core::lower_single_expr(FileId(0), next_node);
    assert!(
        lowered.is_some(),
        "Bug #1278: Failed to lower disjunctive action node to AST: '{}'",
        next_node.text()
    );

    // Step 3: Verify the base spec still works with direct Init/Next (4 states + deadlock).
    // With [Next \/ UNCHANGED vars]_vars the deadlock at x=3 is not an error (stuttering OK).
    // With direct Next as the action, the checker will find the deadlock at x=3.
    let config_direct = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config_direct);
    match &result {
        CheckResult::Deadlock { stats, .. } => {
            assert_eq!(
                stats.states_found, 4,
                "Bug #1278: expected 4 states with direct Init/Next, got {}",
                stats.states_found
            );
        }
        other => panic!(
            "Bug #1278: expected deadlock with direct Next (no stuttering), got: {:?}",
            other
        ),
    }
}
