// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test SpanTree-like pattern: nested EXISTS with guard at intermediate level
/// and two variables updated by assignments depending on different EXISTS levels.
///
/// This pattern caused TLA2 to miss states because the `mom` assignment
/// depends on `m` from the outer EXISTS, while `dist` depends on `d` from inner EXISTS.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_spantree_nested_exists_two_variables() {
    use crate::config::ConstantValue;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Simplified SpanTree pattern with 3 nodes
    // TLC finds 22 states for this configuration
    let src = r#"
---- MODULE SpanTreeMinimal ----
EXTENDS Integers

CONSTANTS Nodes, Edges, MaxCardinality, Root

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

VARIABLES mom, dist

Init == /\ mom = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next == \E n \in Nodes :
      \E m \in Nbrs(n) :
         /\ dist[m] < 1 + dist[n]
         /\ \E d \in (dist[m]+1) .. (dist[n] - 1) :
                /\ dist' = [dist EXCEPT ![n] = d]
                /\ mom'  = [mom  EXCEPT ![n] = m]

Spec == Init /\ [][Next]_<<mom, dist>>
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Set up constants: Nodes = {1,2,3}, Edges = {{1,2},{1,3},{2,3}}, MaxCardinality = 4, Root = 1
    let mut constants = std::collections::HashMap::new();
    constants.insert(
        "Nodes".to_string(),
        ConstantValue::Value("{1, 2, 3}".to_string()),
    );
    constants.insert(
        "Edges".to_string(),
        ConstantValue::Value("{{1, 2}, {1, 3}, {2, 3}}".to_string()),
    );
    constants.insert(
        "MaxCardinality".to_string(),
        ConstantValue::Value("4".to_string()),
    );
    constants.insert("Root".to_string(), ConstantValue::Value("1".to_string()));

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constants,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // TLC finds 22 distinct states for this configuration
            // If TLA2 finds fewer, there's a bug in nested EXISTS enumeration
            assert_eq!(
                stats.states_found, 22,
                "SpanTree should find 22 states (TLC baseline). Found {}",
                stats.states_found
            );
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

/// Regression test for bug #458: LET-bound variables not substituted in symbolic assignments
///
/// When state variable updates occur inside LET expressions, the LET-bound variables
/// must be substituted into the expression before it's stored as a SymbolicAssignment::Expr.
/// Otherwise, when the expression is later evaluated, the LET-bound variables won't be in scope.
///
/// This was causing "Undefined variable: s" errors in specs like MultiPaxos where
/// PlusCal `with` clauses translated to LET expressions containing state updates.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_let_bound_var_substitution_in_state_update() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Minimal repro: LET binds 's' and 'c', which are used in the msgs' update
    let src = r#"
---- MODULE LetBoundVarSubst ----
VARIABLE msgs

Init == msgs = {}

\* When EXISTS binds 's' and 'c', they're in a LET scope during extraction
\* The state update uses these variables
Next ==
\E s \in {"server1", "server2"} :
\E c \in {"cmd1", "cmd2"} :
LET newMsg == [src |-> s, cmd |-> c]
IN msgs' = msgs \cup {newMsg}

====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("Module should parse");

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // 1 initial state + 4 states from 2x2 combinations = 5 states total
            // (Actually more because msgs accumulates: {}, {m1}, {m1,m2}, etc.)
            assert!(
                stats.states_found >= 5,
                "Should find at least 5 states, found {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "LET-bound variables not properly substituted! Error: {:?}",
                error
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Regression test for #1448: RECURSIVE operator parameters must be preserved
/// across recursive calls in the model checker.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compiled_action_recursive_sum_preserves_params() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Minimal spec: RECURSIVE Sum(f, S) called from Next action.
    // No state variable dependency in the RHS — pure function.
    let src = r#"
---- MODULE RecursiveSumBinding ----
EXTENDS Integers
VARIABLE x

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                   ELSE LET z == CHOOSE z \in S : TRUE
                        IN  f[z] + Sum(f, S \ {z})

Init == x = 0

Next == x' = LET sc == [i \in {1, 2} |-> i]
             IN Sum(sc, {1, 2})
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("module should lower");

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            // x=0 initially, then x=3 (Sum(sc, {1,2}) = 1+2 = 3).
            // Exactly 2 states: deadlock disabled, so x=3 is terminal.
            assert_eq!(
                stats.states_found, 2,
                "expected exactly 2 states (x=0, x=3), got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "recursive Sum should not lose parameter bindings: {:?}",
                error
            );
        }
        other => panic!("unexpected result: {:?}", other),
    }
}
