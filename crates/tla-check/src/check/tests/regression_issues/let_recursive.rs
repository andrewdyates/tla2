// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::config::ConstantValue;

/// Parse source, configure with constants and invariants, run checker with deadlock disabled.
fn check_with_constants(
    src: &str,
    constants: std::collections::HashMap<String, ConstantValue>,
    invariants: &[&str],
) -> CheckResult {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Parse errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("module should lower");

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: invariants.iter().map(|s| (*s).to_string()).collect(),
        constants,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.check()
}

/// Regression test for #2464: LET RECURSIVE inside Init that transitively accesses
/// state variables (e.g., `mem[addr].next` where `mem` is a state variable).
///
/// Root cause: `collect_state_var_refs` only recursed into zero-parameter operator
/// bodies, so when the filter `WellFormed(head)` was analyzed for state-var deps,
/// only `head` was found — `mem` (accessed transitively through WellFormed →
/// Reachable → ReachableFrom's body) was missed.
///
/// Fix: Remove the `def.params.is_empty()` guard in `CollectStateVarRefsVisitor`
/// so it traces into ALL operator bodies (including parameterized ones).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_let_recursive_init_filter_accesses_state_vars() {
    let src = r#"
---- MODULE LetRecursiveInitFilter ----
EXTENDS Integers

CONSTANTS NULL

VARIABLES mem, head

\* Reachable set via LET RECURSIVE
Reachable(h) ==
    LET RECURSIVE ReachableFrom(_, _)
        ReachableFrom(addr, seen) ==
            IF addr = NULL THEN seen
            ELSE IF addr \in seen THEN seen
            ELSE ReachableFrom(mem[addr].next, seen \cup {addr})
    IN ReachableFrom(h, {})

WellFormed(h) ==
    \A addr \in Reachable(h) : addr \in {1, 2, 3}

Init ==
    /\ mem \in [1..3 -> [next: 1..3 \cup {NULL}, val: {0, 1}]]
    /\ head \in 1..3 \cup {NULL}
    /\ WellFormed(head)

Next ==
    /\ head' = IF head # NULL THEN mem[head].next ELSE head
    /\ mem' = mem

Inv == TRUE

Spec == Init /\ [][Next]_<<mem, head>>
====
"#;
    let mut constants = std::collections::HashMap::new();
    constants.insert("NULL".to_string(), ConstantValue::Value("NULL".to_string()));

    match check_with_constants(src, constants, &["Inv"]) {
        CheckResult::Success(stats) => {
            assert!(
                stats.states_found > 0,
                "LET RECURSIVE in Init should produce at least one valid state. \
                 If 0, the recursive operator cannot access state variable `mem` \
                 during Init enumeration (#2464)."
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "LET RECURSIVE inside Init that transitively accesses state variables \
                 should not error (#2464). Got: {error:?}"
            );
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Test that LET RECURSIVE operators that access state variables work correctly
/// in INVARIANT checking, not just Init enumeration.
///
/// This covers the ListReversal pattern from #2464 where `Reachable(head)` is
/// called from both Init and an invariant.
///
/// Part of #2464.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_let_recursive_state_vars_in_invariant() {
    let src = r#"
---- MODULE LetRecursiveInvariant ----
EXTENDS Integers

CONSTANTS NULL, ADDR

VARIABLES mem, head

\* Reachable set via LET RECURSIVE — accesses state variable `mem`
Reachable(h) ==
    LET RECURSIVE ReachableFrom(_, _)
        ReachableFrom(addr, seen) ==
            IF addr = NULL THEN seen
            ELSE IF addr \in seen THEN seen
            ELSE ReachableFrom(mem[addr].next, seen \cup {addr})
    IN ReachableFrom(h, {})

\* Invariant that calls Reachable — exercises LET RECURSIVE during invariant checking
TypeInv ==
    /\ \A a \in ADDR : mem[a].next \in ADDR \cup {NULL}
    /\ head \in ADDR \cup {NULL}
    /\ Reachable(head) \subseteq ADDR
    /\ head /= NULL => head \in Reachable(head)

Init ==
    /\ mem = [a \in ADDR |-> [next |-> NULL, val |-> 0]]
    /\ head = NULL

\* Simple Next: set head to an address and link it
Next ==
    \E a \in ADDR :
        /\ mem' = [mem EXCEPT ![a].next = head]
        /\ head' = a

====
"#;
    let mut constants = std::collections::HashMap::new();
    constants.insert("NULL".to_string(), ConstantValue::Value("NULL".to_string()));
    constants.insert(
        "ADDR".to_string(),
        ConstantValue::ModelValueSet(vec!["a1".to_string(), "a2".to_string()]),
    );

    match check_with_constants(src, constants, &["TypeInv"]) {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 15,
                "LET RECURSIVE in invariant: expected 15 states with 2 addresses (#2464)"
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "LET RECURSIVE inside invariant that accesses state variables \
                 should not error (#2464). Got: {error:?}"
            );
        }
        other => panic!("unexpected result: {other:?}"),
    }
}
