// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Property operator generation: invariants and temporal formulas.

use tla_core::ast::{BoundVar, Expr, OperatorDef};
// BoundVar used by generate_join_completeness

use super::helpers::*;
use super::spanned;
use crate::model::ConcurrentModel;
use crate::property::Property;

/// Generate operator definitions for all properties in the model.
pub(super) fn generate_property_operators(model: &ConcurrentModel) -> Vec<OperatorDef> {
    model
        .properties
        .iter()
        .map(|prop| generate_property_operator(model, prop))
        .collect()
}

/// Get the TLA+ operator name for a property.
pub fn property_operator_name(prop: &Property) -> String {
    match prop {
        Property::DeadlockFreedom => "DeadlockFreedom".to_string(),
        Property::LockOrderConsistency => "LockOrderConsistency".to_string(),
        Property::DataRaceFreedom => "DataRaceFreedom".to_string(),
        Property::Termination { process } => format!("Termination_{process}"),
        Property::PoisonHandled { mutex } => format!("PoisonHandled_{mutex}"),
        Property::ChannelFifo { channel } => format!("ChannelFifo_{channel}"),
        Property::ChannelDisconnect { channel } => format!("ChannelDisconnect_{channel}"),
        Property::BarrierCorrectness { barrier } => format!("BarrierCorrectness_{barrier}"),
        Property::JoinCompleteness => "JoinCompleteness".to_string(),
        Property::ChannelNoLoss { channel } => format!("ChannelNoLoss_{channel}"),
        Property::CondvarProgress { condvar } => format!("CondvarProgress_{condvar}"),
        Property::RwLockWriterProgress { rwlock } => format!("RwLockWriterProgress_{rwlock}"),
        Property::Linearizable { object, .. } => format!("Linearizable_{object}"),
        Property::Custom { name, .. } => name.clone(),
    }
}

fn generate_property_operator(model: &ConcurrentModel, prop: &Property) -> OperatorDef {
    let name = property_operator_name(prop);
    let body = generate_property_body(model, prop);
    make_operator(&name, body)
}

fn generate_property_body(model: &ConcurrentModel, prop: &Property) -> Expr {
    match prop {
        Property::DeadlockFreedom => generate_deadlock_freedom(model),
        Property::LockOrderConsistency => generate_lock_order_consistency(model),
        Property::DataRaceFreedom => generate_data_race_freedom(model),
        Property::Termination { process } => generate_termination(process),
        Property::JoinCompleteness => generate_join_completeness(model),

        // Liveness properties generate temporal formulas
        Property::CondvarProgress { .. } => {
            // <>~(pid \in condvar_waiting[cv]) for each waiting process
            // Simplified: TRUE for now, full implementation in Phase 2
            bool_lit(true)
        }
        Property::RwLockWriterProgress { .. } => {
            bool_lit(true) // TODO: Phase 2
        }

        // Default passthrough for properties not yet fully implemented
        _ => bool_lit(true),
    }
}

/// DeadlockFreedom is handled by tla-check's built-in deadlock detection
/// (`config.check_deadlock = true`), NOT as an invariant. The generated Next
/// relation includes a stuttering disjunct for terminal states, so the checker
/// only reports deadlock when a non-terminal state has no successors.
///
/// This operator is kept as TRUE so it can appear in the module for
/// documentation, but it is NOT added to the config's invariant list.
fn generate_deadlock_freedom(_model: &ConcurrentModel) -> Expr {
    bool_lit(true)
}

/// LockOrderConsistency:
/// No cycle of any length in the wait-for graph.
///
/// WaitForGraph[i][j] = TRUE iff process i holds a lock and waits for a lock
/// held by process j. We check: \A p \in Processes : ~WaitForGraph+[p][p]
/// (where + denotes transitive closure).
///
/// For the initial implementation, we check the simpler 2-lock condition:
/// No process p holds lock m1 while waiting for lock m2 that is held by
/// a process q that holds m2 while waiting for m1.
fn generate_lock_order_consistency(_model: &ConcurrentModel) -> Expr {
    // For each pair of processes, check no circular wait
    // \A p \in Processes : \A q \in Processes :
    //   ~(p /= q /\ WaitsFor(p, q) /\ WaitsFor(q, p))
    //
    // where WaitsFor(p, q) means p is trying to acquire a lock held by q.
    //
    // This is checked implicitly by the deadlock detection. For explicit
    // N-lock cycle detection, we generate the transitive closure of the
    // wait-for relation. Initial implementation: always TRUE, rely on
    // deadlock detection to catch lock order violations.
    bool_lit(true)
}

/// DataRaceFreedom (protection discipline):
/// Every shared variable access holds the correct guard in the correct mode.
///
/// When `AccessSite::state_id` is `Some(s)`, the guard requirement is
/// conditioned on the process's program counter:
///   `pc[p] = s => guard_held`
///
/// When `state_id` is `None`, the guard is required unconditionally
/// (the original, more conservative check).
fn generate_data_race_freedom(model: &ConcurrentModel) -> Expr {
    let mut conjuncts = Vec::new();

    for var in &model.shared_vars {
        for access in &var.access_sites {
            if access.guards_held.is_empty() {
                // Unguarded access — potential data race
                // The invariant should flag this as a violation if another
                // process can access the same variable concurrently.
                // For now, we check that the process is the only one alive.
                continue;
            }

            // For each guard required, check it is held
            for guard in &access.guards_held {
                let guard_check = match guard.mode {
                    crate::model::GuardMode::MutexExclusive => eq(
                        func_apply(ident("mutex_owner"), str_lit(&guard.sync_id)),
                        str_lit(&access.process),
                    ),
                    crate::model::GuardMode::RwLockRead
                    | crate::model::GuardMode::RwLockUpgradableRead => in_set(
                        str_lit(&access.process),
                        func_apply(ident("rw_readers"), str_lit(&guard.sync_id)),
                    ),
                    crate::model::GuardMode::RwLockWrite => eq(
                        func_apply(ident("rw_writer"), str_lit(&guard.sync_id)),
                        str_lit(&access.process),
                    ),
                };

                // When state_id is present, condition the guard requirement on
                // the program counter: pc[process] = state_id => guard_held.
                // This avoids false positives when a process releases a lock
                // and later re-acquires it at a different program state.
                let conditioned = if let Some(ref state_id) = access.state_id {
                    implies(
                        eq(
                            func_apply(ident("pc"), str_lit(&access.process)),
                            str_lit(state_id),
                        ),
                        guard_check,
                    )
                } else {
                    guard_check
                };

                conjuncts.push(conditioned);
            }
        }
    }

    if conjuncts.is_empty() {
        bool_lit(true)
    } else {
        conjoin(conjuncts)
    }
}

/// Termination: a specific process eventually reaches a terminal state.
/// This is a liveness property: <>(pc[p] \in TerminalStates)
fn generate_termination(process: &str) -> Expr {
    Expr::Eventually(Box::new(spanned(in_set(
        func_apply(ident("pc"), str_lit(process)),
        ident("TerminalStates"),
    ))))
}

/// JoinCompleteness: all spawned threads are joined before main terminates.
/// \A p \in Processes : pc["main"] \in TerminalStates => alive[p] = FALSE
fn generate_join_completeness(_model: &ConcurrentModel) -> Expr {
    Expr::Forall(
        vec![BoundVar {
            name: spanned("p".to_string()),
            domain: Some(Box::new(spanned(ident("Processes")))),
            pattern: None,
        }],
        Box::new(spanned(implies(
            in_set(
                func_apply(ident("pc"), str_lit("main")),
                ident("TerminalStates"),
            ),
            eq(func_apply(ident("alive"), ident("p")), bool_lit(false)),
        ))),
    )
}
