// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_view() {
    let input = "VIEW ViewExpr\n";
    let config = Config::parse(input).unwrap();
    assert_eq!(config.view, Some("ViewExpr".to_string()));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_view_multiline() {
    let input = r#"
VIEW
    ViewExpr
"#;
    let config = Config::parse(input).unwrap();
    assert_eq!(config.view, Some("ViewExpr".to_string()));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_view_with_other_directives() {
    let input = r#"
INIT Init
NEXT Next
VIEW StateView
INVARIANT TypeOK
"#;
    let config = Config::parse(input).unwrap();
    assert_eq!(config.init, Some("Init".to_string()));
    assert_eq!(config.next, Some("Next".to_string()));
    assert_eq!(config.view, Some("StateView".to_string()));
    assert_eq!(config.invariants, vec!["TypeOK"]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_default_view_none() {
    let config = Config::new();
    assert!(config.view.is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_to_cfg_string_with_view() {
    let mut config = Config::new();
    config.init = Some("Init".to_string());
    config.view = Some("ViewExpr".to_string());

    let output = config.to_cfg_string();
    assert!(output.contains("VIEW ViewExpr"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_terminal_operator() {
    let input = "TERMINAL IsTerminal\n";
    let config = Config::parse(input).unwrap();
    assert!(matches!(
        config.terminal,
        Some(TerminalSpec::Operator(ref op)) if op == "IsTerminal"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_terminal_single_predicate() {
    let input = "TERMINAL state = \"SAT\"\n";
    let config = Config::parse(input).unwrap();
    match config.terminal {
        Some(TerminalSpec::Predicates(preds)) => {
            assert_eq!(preds.len(), 1);
            assert_eq!(preds[0].0, "state");
            assert_eq!(preds[0].1, "\"SAT\"");
        }
        _ => panic!("Expected predicates"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_terminal_multiline_predicates() {
    let input = r#"
TERMINAL
    state = "SAT"
    state = "UNSAT"
"#;
    let config = Config::parse(input).unwrap();
    match config.terminal {
        Some(TerminalSpec::Predicates(preds)) => {
            assert_eq!(preds.len(), 2);
            assert_eq!(preds[0].0, "state");
            assert_eq!(preds[0].1, "\"SAT\"");
            assert_eq!(preds[1].0, "state");
            assert_eq!(preds[1].1, "\"UNSAT\"");
        }
        _ => panic!("Expected predicates"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_terminal_multiline_operator() {
    let input = r#"
TERMINAL
    IsTerminal
"#;
    let config = Config::parse(input).unwrap();
    assert!(matches!(
        config.terminal,
        Some(TerminalSpec::Operator(ref op)) if op == "IsTerminal"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parse_terminal_with_other_directives() {
    let input = r#"
INIT Init
NEXT Next
TERMINAL state = "SAT"
INVARIANT TypeOK
"#;
    let config = Config::parse(input).unwrap();
    assert_eq!(config.init, Some("Init".to_string()));
    assert_eq!(config.next, Some("Next".to_string()));
    assert!(matches!(config.terminal, Some(TerminalSpec::Predicates(_))));
    assert_eq!(config.invariants, vec!["TypeOK"]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_default_terminal_none() {
    let config = Config::new();
    assert!(config.terminal.is_none());
}
