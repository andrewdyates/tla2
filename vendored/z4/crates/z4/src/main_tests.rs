// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::chc_runner::{portfolio_budget_from_timeout, portfolio_time_budget};
use crate::dimacs::{has_cnf_extension, is_dimacs_format};

#[test]
fn test_is_horn_logic() {
    // HORN logic
    let horn_content = "(set-logic HORN)
(declare-fun Inv (Int) Bool)
(check-sat)";
    assert!(is_horn_logic(horn_content));

    // Non-HORN logic
    let non_horn_content = "(set-logic QF_LIA)
(declare-const x Int)
(check-sat)";
    assert!(!is_horn_logic(non_horn_content));

    // No logic specified
    let no_logic = "(declare-const x Int)
(check-sat)";
    assert!(!is_horn_logic(no_logic));
}

#[test]
fn test_is_dimacs_format() {
    // Valid DIMACS
    let dimacs = "p cnf 3 2
1 -2 0
-1 2 0";
    assert!(is_dimacs_format(dimacs));

    // DIMACS with comments
    let dimacs_comments = "c A comment
c Another comment
p cnf 3 2
1 -2 0
-1 2 0";
    assert!(is_dimacs_format(dimacs_comments));

    // SMT-LIB is not DIMACS
    let smtlib = "(set-logic QF_LIA)
(declare-const x Int)
(check-sat)";
    assert!(!is_dimacs_format(smtlib));

    // Empty is not DIMACS
    assert!(!is_dimacs_format(""));

    // Comments only is not DIMACS
    assert!(!is_dimacs_format("c comment"));
}

#[test]
fn test_has_cnf_extension() {
    assert!(has_cnf_extension("test.cnf"));
    assert!(has_cnf_extension("test.CNF"));
    assert!(has_cnf_extension("/path/to/file.cnf"));
    assert!(!has_cnf_extension("test.smt2"));
    assert!(!has_cnf_extension("test.cnf.bak"));
}

#[test]
fn test_portfolio_time_budget_accounts_for_elapsed() {
    // 1000ms timeout, 200ms already elapsed => 800ms remaining => 760ms budget (95%)
    assert_eq!(
        portfolio_time_budget(1000, Duration::from_millis(200)),
        Duration::from_millis(760)
    );
}

#[test]
fn test_portfolio_time_budget_zero_when_no_time_left() {
    // No time remaining
    assert_eq!(
        portfolio_time_budget(1000, Duration::from_millis(1000)),
        Duration::from_millis(0)
    );
    // More elapsed than timeout (saturating_sub protects us)
    assert_eq!(
        portfolio_time_budget(1000, Duration::from_millis(5000)),
        Duration::from_millis(0)
    );
}

#[test]
fn test_portfolio_time_budget_no_overflow() {
    // Large timeout shouldn't overflow
    let budget = portfolio_time_budget(u64::MAX, Duration::ZERO);
    let expected_ms = u64::try_from((u128::from(u64::MAX) * 19) / 20).unwrap();
    assert_eq!(budget, Duration::from_millis(expected_ms));
}

#[test]
fn test_portfolio_budget_from_timeout_default() {
    assert_eq!(
        portfolio_budget_from_timeout(None),
        portfolio_time_budget(15_000, Duration::ZERO)
    );
}

#[test]
fn test_portfolio_budget_from_timeout_zero_override() {
    assert_eq!(portfolio_budget_from_timeout(Some(0)), Duration::ZERO);
}

#[test]
fn test_determine_execution_mode_chc_aliases_portfolio_file() {
    let file = String::from("input.smt2");
    let mode = determine_execution_mode(false, Some(&file), ChcMode::Chc);
    assert_eq!(mode, ExecutionMode::PortfolioFile);
}

#[test]
fn test_determine_execution_mode_portfolio_file() {
    let file = String::from("input.smt2");
    let mode = determine_execution_mode(false, Some(&file), ChcMode::Portfolio);
    assert_eq!(mode, ExecutionMode::PortfolioFile);
}

#[test]
fn test_determine_execution_mode_auto_file() {
    let file = String::from("input.smt2");
    let mode = determine_execution_mode(false, Some(&file), ChcMode::None);
    assert_eq!(mode, ExecutionMode::AutoFile);
}

#[test]
fn test_determine_execution_mode_interactive_without_file() {
    let mode = determine_execution_mode(false, None, ChcMode::Portfolio);
    assert_eq!(mode, ExecutionMode::Interactive);
}

#[test]
fn test_determine_execution_mode_stdin_takes_precedence() {
    let file = String::from("input.smt2");
    let mode = determine_execution_mode(true, Some(&file), ChcMode::Portfolio);
    assert_eq!(mode, ExecutionMode::Interactive);
}
