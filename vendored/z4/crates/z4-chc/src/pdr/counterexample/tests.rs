// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::predicate::PredicateId;

fn pred(id: u32) -> PredicateId {
    PredicateId::new(id)
}

fn make_state(val: i64) -> ChcExpr {
    ChcExpr::Op(
        crate::ChcOp::Eq,
        vec![
            std::sync::Arc::new(ChcExpr::Var(crate::ChcVar::new("x", crate::ChcSort::Int))),
            std::sync::Arc::new(ChcExpr::Int(val)),
        ],
    )
}

#[test]
fn witness_builder_node_creates_entry() {
    let mut wb = WitnessBuilder::default();
    let state = make_state(42);
    let idx = wb.node(pred(0), 0, &state, None);
    assert_eq!(idx, 0);
    assert_eq!(wb.entries.len(), 1);
    assert_eq!(wb.entries[0].predicate, pred(0));
    assert_eq!(wb.entries[0].level, 0);
    assert_eq!(wb.entries[0].state, state);
    assert!(wb.entries[0].instances.is_empty());
}

#[test]
fn witness_builder_node_deduplicates_same_state() {
    let mut wb = WitnessBuilder::default();
    let state = make_state(10);
    let idx1 = wb.node(pred(0), 1, &state, None);
    let idx2 = wb.node(pred(0), 1, &state, None);
    assert_eq!(
        idx1, idx2,
        "same (pred, level, state) should return same index"
    );
    assert_eq!(wb.entries.len(), 1, "should not create duplicate entry");
}

#[test]
fn witness_builder_node_updates_instances_on_dedup() {
    let mut wb = WitnessBuilder::default();
    let state = make_state(5);

    // First call without instances
    let idx1 = wb.node(pred(0), 0, &state, None);
    assert!(wb.entries[idx1].instances.is_empty());

    // Second call with instances -- should update
    let mut instances = FxHashMap::default();
    instances.insert("x".to_string(), SmtValue::Int(5));
    let idx2 = wb.node(pred(0), 0, &state, Some(&instances));
    assert_eq!(idx1, idx2);
    assert_eq!(
        wb.entries[idx1].instances.get("x"),
        Some(&SmtValue::Int(5)),
        "dedup should update empty instances"
    );
}

#[test]
fn witness_builder_node_does_not_overwrite_existing_instances() {
    let mut wb = WitnessBuilder::default();
    let state = make_state(7);

    let mut first = FxHashMap::default();
    first.insert("x".to_string(), SmtValue::Int(7));
    let idx1 = wb.node(pred(0), 0, &state, Some(&first));

    // Second call with different instances -- should NOT overwrite
    let mut second = FxHashMap::default();
    second.insert("x".to_string(), SmtValue::Int(999));
    let idx2 = wb.node(pred(0), 0, &state, Some(&second));
    assert_eq!(idx1, idx2);
    assert_eq!(
        wb.entries[idx1].instances.get("x"),
        Some(&SmtValue::Int(7)),
        "non-empty instances must not be overwritten"
    );
}

#[test]
fn witness_builder_different_predicates_are_distinct() {
    let mut wb = WitnessBuilder::default();
    let state = make_state(1);
    let idx0 = wb.node(pred(0), 0, &state, None);
    let idx1 = wb.node(pred(1), 0, &state, None);
    assert_ne!(
        idx0, idx1,
        "different predicates must produce different entries"
    );
    assert_eq!(wb.entries.len(), 2);
}

#[test]
fn witness_builder_different_levels_are_distinct() {
    let mut wb = WitnessBuilder::default();
    let state = make_state(1);
    let idx0 = wb.node(pred(0), 0, &state, None);
    let idx1 = wb.node(pred(0), 1, &state, None);
    assert_ne!(
        idx0, idx1,
        "different levels must produce different entries"
    );
    assert_eq!(wb.entries.len(), 2);
}

#[test]
fn witness_builder_different_states_are_distinct() {
    let mut wb = WitnessBuilder::default();
    let s1 = make_state(1);
    let s2 = make_state(2);
    let idx0 = wb.node(pred(0), 0, &s1, None);
    let idx1 = wb.node(pred(0), 0, &s2, None);
    assert_ne!(
        idx0, idx1,
        "different states must produce different entries"
    );
    assert_eq!(wb.entries.len(), 2);
}

#[test]
fn witness_builder_set_derivation_basic() {
    let mut wb = WitnessBuilder::default();
    let s0 = make_state(0);
    let s1 = make_state(1);
    let premise_idx = wb.node(pred(0), 0, &s0, None);
    let head_idx = wb.node(pred(0), 1, &s1, None);

    wb.set_derivation(head_idx, 42, vec![premise_idx]);

    assert_eq!(wb.entries[head_idx].incoming_clause, Some(42));
    assert_eq!(wb.entries[head_idx].premises, vec![premise_idx]);
}

#[test]
fn witness_builder_set_derivation_idempotent() {
    let mut wb = WitnessBuilder::default();
    let s0 = make_state(0);
    let s1 = make_state(1);
    let premise_idx = wb.node(pred(0), 0, &s0, None);
    let head_idx = wb.node(pred(0), 1, &s1, None);

    wb.set_derivation(head_idx, 42, vec![premise_idx]);
    // Second call should not overwrite
    wb.set_derivation(head_idx, 99, vec![]);

    assert_eq!(
        wb.entries[head_idx].incoming_clause,
        Some(42),
        "first set_derivation must win"
    );
    assert_eq!(
        wb.entries[head_idx].premises,
        vec![premise_idx],
        "first set_derivation premises must persist"
    );
}

#[test]
fn witness_builder_multi_step_derivation_dag() {
    // Build a 3-node derivation: init -> mid -> bad
    let mut wb = WitnessBuilder::default();
    let init_state = make_state(0);
    let mid_state = make_state(5);
    let bad_state = make_state(10);

    let init_idx = wb.node(pred(0), 0, &init_state, None);
    let mid_idx = wb.node(pred(0), 1, &mid_state, None);
    let bad_idx = wb.node(pred(0), 2, &bad_state, None);

    wb.set_derivation(mid_idx, 0, vec![init_idx]);
    wb.set_derivation(bad_idx, 1, vec![mid_idx]);

    assert_eq!(wb.entries.len(), 3);
    // Verify DAG structure
    assert!(
        wb.entries[init_idx].premises.is_empty(),
        "init has no premises"
    );
    assert_eq!(wb.entries[mid_idx].premises, vec![init_idx]);
    assert_eq!(wb.entries[bad_idx].premises, vec![mid_idx]);
    assert_eq!(wb.entries[mid_idx].incoming_clause, Some(0));
    assert_eq!(wb.entries[bad_idx].incoming_clause, Some(1));
}
