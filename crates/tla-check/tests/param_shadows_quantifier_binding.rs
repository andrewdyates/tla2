// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test: operator formal parameters must shadow quantifier bindings.
//!
//! Bug: When an operator's formal parameter has the same name as a quantifier
//! variable in the enclosing scope (e.g., `\E queens \in S: ... Op(Append(queens, c), ...)`
//! where `Op(queens, ...) == queens[i]`), the formal parameter `queens` inside
//! the operator body resolved to the quantifier binding instead of the argument.
//!
//! Root cause: `bind_all_fast` pushed operator parameters to `local_stack` and
//! `fast_bindings` but NOT to the `BindingChain`. Since `eval_ident` checks
//! the `BindingChain` first (where the quantifier's binding lives), the formal
//! parameter was never found.
//!
//! Fix: `bind_all_fast` now also pushes to `BindingChain` via `cons_local`.
//!
//! Reproduces: N-Queens QueensPluscal variant (FourQueens_2), GitHub issue #2328.

mod common;

use tla_check::{check_module, CheckResult, Config, ConstantValue};
use tla_core::FileId;

/// Minimal spec where operator parameter `qs` shadows the `\E qs \in S` binding.
///
/// The `Access(qs, i)` operator takes a sequence `qs` and returns `qs[i]`.
/// When called as `Access(Append(qs, c), 2)` inside `\E qs \in todo: ...`,
/// the formal parameter `qs` in Access must bind to `Append(qs_outer, c)`,
/// NOT to the existential `qs` from `\E qs \in todo`.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_formal_param_shadows_quantifier_binding() {
    let module = common::parse_module_strict_with_id(
        r#"
---- MODULE ParamShadow ----
EXTENDS Naturals, Sequences

CONSTANT N

\* Operator with formal parameter "qs" — same name as quantifier variable below
Access(qs, i) == qs[i]

VARIABLES todo

Init == todo = { << >> }

Step == \E qs \in todo :
  LET nextIdx == Len(qs) + 1 IN
    LET cols == { c \in 1..N : Access(Append(qs, c), nextIdx) # 0 } IN
      LET exts == { Append(qs, c) : c \in cols } IN
        IF nextIdx = N
        THEN todo' = todo \ {qs}
        ELSE todo' = (todo \ {qs}) \union exts

Spec == Init /\ [][Step]_<<todo>>
====
"#,
        FileId(0),
    );

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Step".to_string()),
        check_deadlock: false,
        ..Default::default()
    };
    config
        .constants
        .insert("N".to_string(), ConstantValue::Value("3".to_string()));

    let result = check_module(&module, &config);

    // Must complete without error — if parameter shadowing is broken,
    // this would fail with "index 2 of tuple <<1>> out of bounds"
    match &result {
        CheckResult::Success(stats) => {
            assert!(
                stats.states_found > 10,
                "expected substantial state exploration, got only {} states",
                stats.states_found
            );
        }
        CheckResult::Deadlock { stats, .. } => {
            // Deadlock is acceptable (no liveness spec) — just verify exploration worked
            assert!(
                stats.states_found > 10,
                "expected substantial state exploration before deadlock, got only {} states",
                stats.states_found
            );
        }
        other => {
            panic!(
                "expected Success or Deadlock, got error (parameter shadowing likely broken): {:?}",
                other
            );
        }
    }
}

/// Same test pattern but using the exact N-Queens `Attacks` function structure.
/// This matches the original QueensPluscal bug more closely.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_attacks_pattern_param_shadows_exists() {
    let module = common::parse_module_strict_with_id(
        r#"
---- MODULE AttacksParamShadow ----
EXTENDS Naturals, Sequences

CONSTANT N

\* Formal parameter "queens" shadows `\E queens \in todo` in the action below
Attacks(queens, i, j) ==
  \/ queens[i] = queens[j]
  \/ queens[i] - queens[j] = i - j
  \/ queens[j] - queens[i] = i - j

VARIABLES todo

Init == todo = { << >> }

PlaceQueen == \E queens \in todo :
  LET nxtQ == Len(queens) + 1
      cols == { c \in 1..N : ~ \E i \in 1 .. Len(queens) :
                                  Attacks( Append(queens, c), i, nxtQ ) }
      exts == { Append(queens, c) : c \in cols }
  IN  IF nxtQ = N
      THEN todo' = todo \ {queens}
      ELSE todo' = (todo \ {queens}) \union exts

Spec == Init /\ [][PlaceQueen]_<<todo>>
====
"#,
        FileId(0),
    );

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("PlaceQueen".to_string()),
        check_deadlock: false,
        ..Default::default()
    };
    config
        .constants
        .insert("N".to_string(), ConstantValue::Value("4".to_string()));

    let result = check_module(&module, &config);

    // N-Queens with N=4: TLC finds 785 distinct states (full exploration, no invariant).
    // TLA2 should match.
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 785,
                "N-Queens N=4 full exploration should find 785 states (matching TLC)"
            );
        }
        CheckResult::Deadlock { stats, .. } => {
            assert_eq!(
                stats.states_found, 785,
                "N-Queens N=4 should explore 785 states before deadlock"
            );
        }
        other => {
            panic!(
                "expected Success or Deadlock for N-Queens N=4, got: {:?}",
                other
            );
        }
    }
}
