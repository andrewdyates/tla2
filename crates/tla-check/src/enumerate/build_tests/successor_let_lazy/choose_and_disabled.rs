// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Choose/disabled-action parity regressions for LET lazy evaluation.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_let_unused_choose_does_not_disable_action() {
    // Regression test: guard checking must not eagerly evaluate unused LET bindings.
    //
    // This matches btree's `WhichToSplit`: when splitting the root, `parent == ParentOf(node)`
    // is unused, and `ParentOf(root)` has no witness (CHOOSE fails). TLC doesn't evaluate it,
    // so the action remains enabled. Our enumeration guard check must do the same.
    let src = r#"
---- MODULE Test ----
VARIABLE x

BadChoose == CHOOSE p \in {} : TRUE

Action ==
    LET parent == BadChoose
    IN x' = 1

Init == x = 0
Next == Action
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);

    let next_def = find_operator(&module, "Next");

    let successors = enumerate_successors(&mut ctx, next_def, &current_state, &vars).unwrap();
    assert_eq!(successors.len(), 1);
    assert_eq!(successors[0].get("x"), Some(&Value::int(1)));
}

/// Fix #1552: ChooseFailed from used LET binding propagates fatally (TLC semantics).
/// TLC: "Attempted to compute CHOOSE x \\in S: P, but no element of S satisfied P."
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_let_used_choose_disables_action() {
    let src = r#"
---- MODULE Test ----
VARIABLE x

BadChoose == CHOOSE p \in {} : TRUE

Action ==
    LET parent == BadChoose
    IN x' = parent

Init == x = 0
Next == Action
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);

    let next_def = find_operator(&module, "Next");

    let result = enumerate_successors(&mut ctx, next_def, &current_state, &vars);
    let err = result.expect_err("#1552: ChooseFailed must propagate as fatal error (TLC behavior)");
    assert!(
        matches!(err, EvalError::ChooseFailed { .. }),
        "#1634: expected ChooseFailed, got {err:?}"
    );
}

/// Fix #1552: ChooseFailed in Or disjunct propagates fatally (TLC semantics).
/// TLC does NOT silently disable disjuncts with errors — any error terminates.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enumerate_successors_let_used_choose_disables_only_one_branch() {
    let src = r#"
---- MODULE Test ----
VARIABLE x

BadChoose == CHOOSE p \in {} : TRUE

Action ==
    LET parent == BadChoose
    IN x' = parent

Good == x' = 1

Init == x = 0
Next == Action \/ Good
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);

    let next_def = find_operator(&module, "Next");

    let result = enumerate_successors(&mut ctx, next_def, &current_state, &vars);
    let err = result
        .expect_err("#1552: ChooseFailed in Or disjunct must propagate fatally (TLC behavior)");
    assert!(
        matches!(err, EvalError::ChooseFailed { .. }),
        "#1634: expected ChooseFailed, got {err:?}"
    );
}

/// Test that LET bindings in disabled actions don't cause evaluation errors.
///
/// This reproduces a bug found in MCCheckpointCoordination where:
/// ```tla
/// SendReplicatedRequest(prospect) ==
///   LET currentLease == F[Leader] IN  \* Fails when Leader=NoNode!
///   /\ Guard                          \* Would be FALSE anyway
///   ...
/// ```
/// When Leader=NoNode, F[Leader] fails because NoNode is not in the domain of F.
/// But the Guard would be FALSE anyway, so the action should be disabled, not error.
/// TLC handles this gracefully; TLA2 should too.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_let_in_disabled_action_does_not_error() {
    let src = r#"
---- MODULE Test ----
CONSTANTS NoNode
VARIABLE Leader, F

\* Guard checks Leader is valid BEFORE using it
Guard == Leader /= NoNode

\* Action has LET that would fail if Leader=NoNode
\* but Guard would be FALSE anyway
ActionWithLet ==
  LET val == F[Leader] IN
  /\ Guard
  /\ Leader' = Leader
  /\ F' = F

Init == Leader = NoNode /\ F = [n \in {1,2,3} |-> n]

Next == ActionWithLet
====
"#;
    let (module, mut ctx, vars) = setup_module(src);

    // Bind NoNode constant
    ctx.bind_mut(
        "NoNode".to_string(),
        Value::try_model_value("NoNode").unwrap(),
    );

    let init_def = find_operator(&module, "Init");
    let next_def = find_operator(&module, "Next");

    // Generate initial state where Leader = NoNode
    let branches = extract_init_constraints(&ctx, &init_def.body, &vars, None).unwrap();
    let init_states = enumerate_states_from_constraint_branches(Some(&ctx), &vars, &branches)
        .unwrap()
        .unwrap();
    assert!(!init_states.is_empty(), "Should have initial states");
    let init_state = &init_states[0];

    // Verify Leader is NoNode
    let leader_val = init_state
        .vars()
        .find(|(n, _)| n.as_ref() == "Leader")
        .map(|(_, v)| v)
        .unwrap();
    assert!(
        matches!(leader_val, Value::ModelValue(s) if s.as_ref() == "NoNode"),
        "Leader should be NoNode, got {:?}",
        leader_val
    );

    // Enumerate successors - this should NOT error, but return empty (action disabled)
    // Before the fix, this would fail with "NotInDomain: @NoNode not in domain"
    let result = enumerate_successors(&mut ctx, next_def, init_state, &vars);
    assert!(
        result.is_ok(),
        "Should not error on LET in disabled action, got: {:?}",
        result.err()
    );

    let successors = result.unwrap();
    // Action should be disabled (Guard is FALSE because Leader = NoNode)
    assert_eq!(
        successors.len(),
        0,
        "Action should be disabled (no successors) when Leader=NoNode"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disabled_action_let_does_not_force_side_effectful_zero_arg_defs() {
    crate::eval::clear_for_test_reset();

    let src = r#"
---- MODULE Test ----
EXTENDS TLC, TLCExt
VARIABLE x

Action ==
  LET side == TLCSet(13, TRUE) IN
  /\ x = 1
  /\ x' = 2

ReadReg == TLCGetOrDefault(13, FALSE)

Init == x = 0
Next == Action
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);

    let next_def = find_operator(&module, "Next");
    let read_reg_def = find_operator(&module, "ReadReg");

    let successors = enumerate_successors(&mut ctx, next_def, &current_state, &vars).unwrap();
    assert!(
        successors.is_empty(),
        "guard is false, so Action should remain disabled"
    );

    let register = crate::eval::eval(&ctx, &read_reg_def.body)
        .expect("TLCGetOrDefault should evaluate after successor enumeration");
    assert_eq!(
        register,
        Value::Bool(false),
        "disabled LET actions must not force side-effectful zero-arg defs before the guard"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disabled_conjunct_let_does_not_force_side_effectful_zero_arg_defs() {
    crate::eval::clear_for_test_reset();

    let src = r#"
---- MODULE Test ----
EXTENDS TLC, TLCExt
VARIABLE x

Next ==
  /\ TRUE
  /\ LET side == TLCSet(14, TRUE) IN
     /\ x = 1
     /\ x' = 2

ReadReg == TLCGetOrDefault(14, FALSE)

Init == x = 0
====
"#;

    let (module, mut ctx, vars) = setup_module(src);
    let current_state = State::from_pairs([("x", Value::int(0))]);

    let next_def = find_operator(&module, "Next");
    let read_reg_def = find_operator(&module, "ReadReg");

    let successors = enumerate_successors(&mut ctx, next_def, &current_state, &vars).unwrap();
    assert!(
        successors.is_empty(),
        "guard is false, so the LET conjunct should not produce successors"
    );

    let register = crate::eval::eval(&ctx, &read_reg_def.body)
        .expect("TLCGetOrDefault should evaluate after successor enumeration");
    assert_eq!(
        register,
        Value::Bool(false),
        "disabled LET conjuncts must not force side-effectful zero-arg defs before the guard"
    );
}
