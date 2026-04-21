// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Init predicate generation.

use tla_core::ast::{Expr, OperatorDef};

use super::helpers::*;
use super::spanned;
use crate::model::ConcurrentModel;
use crate::sync_kind::SyncKind;

/// Generate the Init operator.
///
/// ```tla
/// Init ==
///     /\ pc = [p \in Processes |-> initial_state(p)]
///     /\ alive = [p \in Processes |-> TRUE]
///     /\ mutex_owner = [m \in Mutexes |-> NoOwner]
///     /\ mutex_poisoned = [m \in Mutexes |-> FALSE]
///     /\ locks_held = [p \in Processes |-> {}]
///     /\ rw_readers = [rw \in RwLocks |-> {}]
///     /\ rw_writer = [rw \in RwLocks |-> NoOwner]
///     /\ condvar_waiting = [cv \in Condvars |-> {}]
///     /\ channel_buf = [ch \in Channels |-> <<>>]
///     /\ senders_alive = [ch \in Channels |-> initial_sender_count(ch)]
///     /\ receiver_alive = [ch \in Channels |-> TRUE]
///     /\ <shared_var> = <initial_value>  (for each shared var)
/// ```
pub(super) fn generate_init(model: &ConcurrentModel) -> OperatorDef {
    let mut conjuncts = Vec::new();

    // pc: map each process to its initial state
    let pc_pairs: Vec<_> = model
        .processes
        .iter()
        .map(|p| (str_lit(&p.id), str_lit(&p.initial_state)))
        .collect();
    conjuncts.push(eq(ident("pc"), func_literal(&pc_pairs)));

    // alive: all processes start alive
    let alive_pairs: Vec<_> = model
        .processes
        .iter()
        .map(|p| (str_lit(&p.id), bool_lit(true)))
        .collect();
    conjuncts.push(eq(ident("alive"), func_literal(&alive_pairs)));

    // Mutex state
    let has_mutex = model
        .sync_primitives
        .iter()
        .any(|s| matches!(s.kind, SyncKind::Mutex { .. }));
    if has_mutex {
        let mutex_owner_pairs: Vec<_> = model
            .sync_primitives
            .iter()
            .filter(|s| matches!(s.kind, SyncKind::Mutex { .. }))
            .map(|s| (str_lit(&s.id), ident("NoOwner")))
            .collect();
        conjuncts.push(eq(ident("mutex_owner"), func_literal(&mutex_owner_pairs)));

        let mutex_poison_pairs: Vec<_> = model
            .sync_primitives
            .iter()
            .filter(|s| matches!(s.kind, SyncKind::Mutex { .. }))
            .map(|s| (str_lit(&s.id), bool_lit(false)))
            .collect();
        conjuncts.push(eq(
            ident("mutex_poisoned"),
            func_literal(&mutex_poison_pairs),
        ));

        let locks_held_pairs: Vec<_> = model
            .processes
            .iter()
            .map(|p| (str_lit(&p.id), empty_set()))
            .collect();
        conjuncts.push(eq(ident("locks_held"), func_literal(&locks_held_pairs)));
    }

    // RwLock state
    let has_rwlock = model
        .sync_primitives
        .iter()
        .any(|s| matches!(s.kind, SyncKind::RwLock { .. }));
    if has_rwlock {
        let rw_reader_pairs: Vec<_> = model
            .sync_primitives
            .iter()
            .filter(|s| matches!(s.kind, SyncKind::RwLock { .. }))
            .map(|s| (str_lit(&s.id), empty_set()))
            .collect();
        conjuncts.push(eq(ident("rw_readers"), func_literal(&rw_reader_pairs)));

        let rw_writer_pairs: Vec<_> = model
            .sync_primitives
            .iter()
            .filter(|s| matches!(s.kind, SyncKind::RwLock { .. }))
            .map(|s| (str_lit(&s.id), ident("NoOwner")))
            .collect();
        conjuncts.push(eq(ident("rw_writer"), func_literal(&rw_writer_pairs)));
    }

    // Condvar state
    let has_condvar = model
        .sync_primitives
        .iter()
        .any(|s| matches!(s.kind, SyncKind::Condvar { .. }));
    if has_condvar {
        let cv_pairs: Vec<_> = model
            .sync_primitives
            .iter()
            .filter(|s| matches!(s.kind, SyncKind::Condvar { .. }))
            .map(|s| (str_lit(&s.id), empty_set()))
            .collect();
        conjuncts.push(eq(ident("condvar_waiting"), func_literal(&cv_pairs)));
    }

    // Channel state
    let has_channel = model
        .sync_primitives
        .iter()
        .any(|s| matches!(s.kind, SyncKind::Channel { .. }));
    if has_channel {
        let buf_pairs: Vec<_> = model
            .sync_primitives
            .iter()
            .filter(|s| matches!(s.kind, SyncKind::Channel { .. }))
            .map(|s| (str_lit(&s.id), empty_seq()))
            .collect();
        conjuncts.push(eq(ident("channel_buf"), func_literal(&buf_pairs)));

        // senders_alive: count of processes that can send (initially = number of producers)
        let sender_pairs: Vec<_> = model
            .sync_primitives
            .iter()
            .filter(|s| matches!(s.kind, SyncKind::Channel { .. }))
            .map(|s| (str_lit(&s.id), int_lit(1))) // default 1 sender
            .collect();
        conjuncts.push(eq(ident("senders_alive"), func_literal(&sender_pairs)));

        let recv_pairs: Vec<_> = model
            .sync_primitives
            .iter()
            .filter(|s| matches!(s.kind, SyncKind::Channel { .. }))
            .map(|s| (str_lit(&s.id), bool_lit(true)))
            .collect();
        conjuncts.push(eq(ident("receiver_alive"), func_literal(&recv_pairs)));
    }

    // Shared variables
    for var in &model.shared_vars {
        let init_val = var
            .initial_value
            .as_deref()
            .map_or_else(|| int_lit(0), |_v| int_lit(0)); // TODO: parse initial value expressions
        conjuncts.push(eq(ident(&var.name), init_val));
    }

    make_operator("Init", conjoin(conjuncts))
}

/// Build a function literal from key-value pairs: (k1 :> v1 @@ k2 :> v2 @@ ...)
///
/// We encode this as a record [k1 |-> v1, k2 |-> v2, ...] since TLA2
/// evaluates records as functions.
fn func_literal(pairs: &[(Expr, Expr)]) -> Expr {
    Expr::Record(
        pairs
            .iter()
            .map(|(k, v)| {
                // Extract the string from the key expression for the record field name
                let key_str = match k {
                    Expr::String(s) => s.clone(),
                    Expr::Ident(s, _) => s.clone(),
                    _ => format!("{k:?}"),
                };
                (spanned(key_str), spanned(v.clone()))
            })
            .collect(),
    )
}
