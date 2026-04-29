// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_terminal_states_not_reported_as_deadlock() {
    use crate::config::TerminalSpec;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Simple spec that terminates at state = "SAT" or state = "UNSAT"
    // Without TERMINAL directive, this would be a deadlock
    let src = r#"
---- MODULE SATSolver ----
VARIABLE state
Init == state = "searching"
Next ==
\/ (state = "searching" /\ state' = "SAT")
\/ (state = "searching" /\ state' = "UNSAT")
TypeOK == state \in {"searching", "SAT", "UNSAT"}
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config WITHOUT terminal - should report deadlock
    let config_no_terminal = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        check_deadlock: true,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config_no_terminal);
    let result = checker.check();

    // Without TERMINAL, this should deadlock at SAT or UNSAT
    assert!(
        matches!(result, CheckResult::Deadlock { .. }),
        "Without TERMINAL, should report deadlock. Got: {:?}",
        result
    );

    // Config WITH terminal predicates - should NOT report deadlock
    let config_with_terminal = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        check_deadlock: true,
        terminal: Some(TerminalSpec::Predicates(vec![
            ("state".to_string(), "\"SAT\"".to_string()),
            ("state".to_string(), "\"UNSAT\"".to_string()),
        ])),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config_with_terminal);
    let result = checker.check();

    // With TERMINAL, should succeed (SAT/UNSAT are terminal states)
    match result {
        CheckResult::Success(stats) => {
            // Should have 3 states: searching, SAT, UNSAT
            assert_eq!(
                stats.states_found, 3,
                "Should find 3 states: searching, SAT, UNSAT"
            );
        }
        other => panic!(
            "With TERMINAL predicates, expected Success but got {:?}",
            other
        ),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_terminal_operator() {
    use crate::config::TerminalSpec;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Spec with IsTerminal operator
    let src = r#"
---- MODULE TerminalOp ----
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
TypeOK == x \in 0..3
IsTerminal == x = 3
====
"#;
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    // Config with terminal operator
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        check_deadlock: true,
        terminal: Some(TerminalSpec::Operator("IsTerminal".to_string())),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    let result = checker.check();

    // With TERMINAL IsTerminal, x=3 should not be a deadlock
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 4, "Should find 4 states: x=0,1,2,3");
        }
        other => panic!("Expected Success with TERMINAL operator, got {:?}", other),
    }
}
