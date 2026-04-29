// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for call-by-name substitution when an operator body primes one of its
//! formal parameters. Without the `expr_has_primed_param` check, these operators
//! would incorrectly use call-by-value, breaking state enumeration.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_top_level_apply_with_primed_param_uses_call_by_name() {
    let src = r#"
---- MODULE Test ----
EXTENDS Sequences
VARIABLE q, y

DropOne(seq) ==
  /\ \E i \in 1..Len(seq) :
       seq' = [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]
  /\ UNCHANGED y

Init == /\ q = <<1, 2>>
        /\ y = 0

Next == DropOne(q)
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .expect("invariant: Next operator must exist in test module");

    let init_state = State::from_pairs([
        ("q", Value::seq([Value::int(1), Value::int(2)])),
        ("y", Value::int(0)),
    ]);
    let successors = enumerate_successors(&mut ctx, &next_def, &init_state, &vars)
        .expect("enumerate should succeed");

    let mut q_values: Vec<Value> = successors
        .iter()
        .map(|state| state.get("q").cloned().expect("successor missing q"))
        .collect();
    q_values.sort();

    assert_eq!(
        q_values,
        vec![Value::seq([Value::int(1)]), Value::seq([Value::int(2)])],
        "top-level Apply must substitute state-level args when the operator primes its parameter"
    );
    assert!(
        successors
            .iter()
            .all(|state| state.get("y") == Some(&Value::int(0))),
        "UNCHANGED y should survive top-level Apply substitution"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_conjunct_apply_with_primed_param_uses_call_by_name() {
    let src = r#"
---- MODULE Test ----
EXTENDS Sequences
VARIABLE q, y

DropOnly(seq) ==
  \E i \in 1..Len(seq) :
    seq' = [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

Init == /\ q = <<1, 2>>
        /\ y = 0

Next == /\ DropOnly(q)
        /\ UNCHANGED y
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .expect("invariant: Next operator must exist in test module");

    let init_state = State::from_pairs([
        ("q", Value::seq([Value::int(1), Value::int(2)])),
        ("y", Value::int(0)),
    ]);
    let successors = enumerate_successors(&mut ctx, &next_def, &init_state, &vars)
        .expect("enumerate should succeed");

    let mut q_values: Vec<Value> = successors
        .iter()
        .map(|state| state.get("q").cloned().expect("successor missing q"))
        .collect();
    q_values.sort();

    assert_eq!(
        q_values,
        vec![Value::seq([Value::int(1)]), Value::seq([Value::int(2)])],
        "conjunct Apply must substitute state-level args when the operator primes its parameter"
    );
    assert!(
        successors
            .iter()
            .all(|state| state.get("y") == Some(&Value::int(0))),
        "UNCHANGED y should survive conjunct Apply substitution"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_zero_arg_wrapper_apply_with_primed_param_uses_call_by_name() {
    let src = r#"
---- MODULE Test ----
EXTENDS Sequences
VARIABLE q, y

DropOnly(seq) ==
  \E i \in 1..Len(seq) :
    seq' = [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

DropQ == DropOnly(q)

Init == /\ q = <<1, 2>>
        /\ y = 0

Next == /\ DropQ
        /\ UNCHANGED y
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let next_def = module
        .units
        .iter()
        .find_map(|u| {
            if let tla_core::ast::Unit::Operator(def) = &u.node {
                if def.name.node == "Next" {
                    return Some(def.clone());
                }
            }
            None
        })
        .expect("invariant: Next operator must exist in test module");

    let init_state = State::from_pairs([
        ("q", Value::seq([Value::int(1), Value::int(2)])),
        ("y", Value::int(0)),
    ]);
    let successors = enumerate_successors(&mut ctx, &next_def, &init_state, &vars)
        .expect("enumerate should succeed");

    let mut q_values: Vec<Value> = successors
        .iter()
        .map(|state| state.get("q").cloned().expect("successor missing q"))
        .collect();
    q_values.sort();

    assert_eq!(
        q_values,
        vec![Value::seq([Value::int(1)]), Value::seq([Value::int(2)])],
        "zero-arg action wrappers must preserve call-by-name substitution for primed parameters"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alternating_bit_lose_msg_wrapper_drops_message() {
    let src = r#"
---- MODULE Test ----
EXTENDS Naturals, Sequences
VARIABLES msgQ, ackQ, sBit, sAck, rBit, sent, rcvd

Lose(q) ==
  /\ q # << >>
  /\ \E i \in 1..Len(q) :
       q' = [j \in 1..(Len(q) - 1) |-> IF j < i THEN q[j] ELSE q[j + 1]]
  /\ UNCHANGED <<sBit, sAck, rBit, sent, rcvd>>

LoseMsg == Lose(msgQ) /\ UNCHANGED ackQ

Init == TRUE
Next == LoseMsg
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let next_def = find_operator(&module, "Next");

    let message = Value::tuple([Value::int(0), Value::String("d1".into())]);
    let init_state = State::from_pairs([
        ("msgQ", Value::seq([message])),
        ("ackQ", Value::seq([Value::int(1)])),
        ("sBit", Value::int(0)),
        ("sAck", Value::int(0)),
        ("rBit", Value::int(0)),
        ("sent", Value::String("d1".into())),
        ("rcvd", Value::String("d1".into())),
    ]);

    let successors = enumerate_successors(&mut ctx, next_def, &init_state, &vars)
        .expect("LoseMsg enumeration should succeed");

    assert_eq!(successors.len(), 1, "LoseMsg should drop the only queued message");
    let successor = &successors[0];
    assert_eq!(successor.get("msgQ"), Some(&Value::seq([])));
    assert_eq!(successor.get("ackQ"), init_state.get("ackQ"));
    assert_eq!(successor.get("sBit"), init_state.get("sBit"));
    assert_eq!(successor.get("sAck"), init_state.get("sAck"));
    assert_eq!(successor.get("rBit"), init_state.get("rBit"));
    assert_eq!(successor.get("sent"), init_state.get("sent"));
    assert_eq!(successor.get("rcvd"), init_state.get("rcvd"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alternating_bit_full_next_includes_late_lose_msg_branch() {
    let src = r#"
---- MODULE Test ----
EXTENDS Naturals, Sequences
VARIABLES msgQ, ackQ, sBit, sAck, rBit, sent, rcvd

Data == {"d1", "d2"}

SndNewValue(d) ==
  /\ sAck = sBit
  /\ sent' = d
  /\ sBit' = 1 - sBit
  /\ msgQ' = Append(msgQ, <<sBit', d>>)
  /\ UNCHANGED <<ackQ, sAck, rBit, rcvd>>

ReSndMsg ==
  /\ sAck # sBit
  /\ msgQ' = Append(msgQ, <<sBit, sent>>)
  /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

RcvMsg ==
  /\ msgQ # <<>>
  /\ msgQ' = Tail(msgQ)
  /\ rBit' = Head(msgQ)[1]
  /\ rcvd' = Head(msgQ)[2]
  /\ UNCHANGED <<ackQ, sBit, sAck, sent>>

SndAck == /\ ackQ' = Append(ackQ, rBit)
          /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

RcvAck == /\ ackQ # << >>
          /\ ackQ' = Tail(ackQ)
          /\ sAck' = Head(ackQ)
          /\ UNCHANGED <<msgQ, sBit, rBit, sent, rcvd>>

Lose(q) ==
  /\ q # << >>
  /\ \E i \in 1..Len(q) :
       q' = [j \in 1..(Len(q) - 1) |-> IF j < i THEN q[j] ELSE q[j + 1]]
  /\ UNCHANGED <<sBit, sAck, rBit, sent, rcvd>>

LoseMsg == Lose(msgQ) /\ UNCHANGED ackQ
LoseAck == Lose(ackQ) /\ UNCHANGED msgQ

ABNext == \/ \E d \in Data : SndNewValue(d)
          \/ ReSndMsg \/ RcvMsg \/ SndAck \/ RcvAck
          \/ LoseMsg \/ LoseAck

Init == TRUE
Next == ABNext
====
"#;
    let (module, mut ctx, vars) = setup_module(src);
    let next_def = find_operator(&module, "Next");

    let message = Value::tuple([Value::int(0), Value::String("d1".into())]);
    let init_state = State::from_pairs([
        ("msgQ", Value::seq([message])),
        ("ackQ", Value::seq([])),
        ("sBit", Value::int(0)),
        ("sAck", Value::int(1)),
        ("rBit", Value::int(0)),
        ("sent", Value::String("d1".into())),
        ("rcvd", Value::String("d2".into())),
    ]);

    let successors = enumerate_successors(&mut ctx, next_def, &init_state, &vars)
        .expect("ABNext enumeration should succeed");

    assert!(
        successors.iter().any(|successor| {
            successor.get("msgQ") == Some(&Value::seq([]))
                && successor.get("ackQ") == init_state.get("ackQ")
                && successor.get("sBit") == init_state.get("sBit")
                && successor.get("sAck") == init_state.get("sAck")
                && successor.get("rBit") == init_state.get("rBit")
                && successor.get("sent") == init_state.get("sent")
                && successor.get("rcvd") == init_state.get("rcvd")
        }),
        "full ABNext monolithic enumeration must include the late LoseMsg branch"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alternating_bit_full_next_model_value_queue_includes_late_lose_msg_branch() {
    let src = alternating_bit_model_value_src();
    let (module, mut ctx, vars) = setup_module(src);
    let next_def = find_operator(&module, "Next");

    let d1 = Value::ModelValue(Arc::from("d1"));
    let message = Value::tuple([Value::int(1), d1.clone()]);
    let init_state = State::from_pairs([
        ("msgQ", Value::seq([message])),
        ("ackQ", Value::seq([])),
        ("sBit", Value::int(1)),
        ("sAck", Value::int(1)),
        ("rBit", Value::int(0)),
        ("sent", d1.clone()),
        ("rcvd", d1),
    ]);

    let successors = enumerate_successors(&mut ctx, next_def, &init_state, &vars)
        .expect("ABNext enumeration should succeed");

    assert!(
        successors.iter().any(|successor| {
            successor.get("msgQ") == Some(&Value::seq([]))
                && successor.get("ackQ") == init_state.get("ackQ")
                && successor.get("sBit") == init_state.get("sBit")
                && successor.get("sAck") == init_state.get("sAck")
                && successor.get("rBit") == init_state.get("rBit")
                && successor.get("sent") == init_state.get("sent")
                && successor.get("rcvd") == init_state.get("rcvd")
        }),
        "full ABNext monolithic enumeration must include LoseMsg with model-value messages"
    );
}

fn alternating_bit_model_value_src() -> &'static str {
    r#"
---- MODULE Test ----
EXTENDS Naturals, Sequences
VARIABLES msgQ, ackQ, sBit, sAck, rBit, sent, rcvd

Data == {TLCModelValue("d1"), TLCModelValue("d2")}

SndNewValue(d) ==
  /\ sAck = sBit
  /\ sent' = d
  /\ sBit' = 1 - sBit
  /\ msgQ' = Append(msgQ, <<sBit', d>>)
  /\ UNCHANGED <<ackQ, sAck, rBit, rcvd>>

ReSndMsg ==
  /\ sAck # sBit
  /\ msgQ' = Append(msgQ, <<sBit, sent>>)
  /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

RcvMsg ==
  /\ msgQ # <<>>
  /\ msgQ' = Tail(msgQ)
  /\ rBit' = Head(msgQ)[1]
  /\ rcvd' = Head(msgQ)[2]
  /\ UNCHANGED <<ackQ, sBit, sAck, sent>>

SndAck == /\ ackQ' = Append(ackQ, rBit)
          /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

RcvAck == /\ ackQ # << >>
          /\ ackQ' = Tail(ackQ)
          /\ sAck' = Head(ackQ)
          /\ UNCHANGED <<msgQ, sBit, rBit, sent, rcvd>>

Lose(q) ==
  /\ q # << >>
  /\ \E i \in 1..Len(q) :
       q' = [j \in 1..(Len(q) - 1) |-> IF j < i THEN q[j] ELSE q[j + 1]]
  /\ UNCHANGED <<sBit, sAck, rBit, sent, rcvd>>

LoseMsg == Lose(msgQ) /\ UNCHANGED ackQ
LoseAck == Lose(ackQ) /\ UNCHANGED msgQ

ABNext == \/ \E d \in Data : SndNewValue(d)
          \/ ReSndMsg \/ RcvMsg \/ SndAck \/ RcvAck
          \/ LoseMsg \/ LoseAck

Init == /\ msgQ = <<>>
        /\ ackQ = <<>>
        /\ sBit \in {0, 1}
        /\ sAck = sBit
        /\ rBit = sBit
        /\ sent \in Data
        /\ rcvd \in Data
MsgBound == Len(msgQ) <= 2
AckBound == Len(ackQ) <= 2
Next == ABNext
====
"#
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_alternating_bit_model_checker_uses_per_action_for_primed_param_actions() {
    let (module, _, _) = setup_module(alternating_bit_model_value_src());
    let mut config = crate::Config::parse(
        r#"
INIT Init
NEXT Next
CONSTRAINT MsgBound
CONSTRAINT AckBound
CHECK_DEADLOCK FALSE
"#,
    )
    .expect("config should parse");
    config.auto_por = Some(false);
    config.por_enabled = false;

    let mut checker = crate::ModelChecker::new(&module, &config);
    checker.set_store_states(true);

    match checker.check() {
        crate::CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 240,
                "per-action fallback should preserve TLC's constrained ABNext state count"
            );
        }
        other => panic!("ABNext model check should succeed: {other:?}"),
    }
}
