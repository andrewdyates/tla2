// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State variable collection for the generated TLA+ module.

use crate::model::ConcurrentModel;
use crate::sync_kind::SyncKind;

/// Collect all TLA+ variable names needed for this concurrent model.
///
/// Variables:
/// - `pc`: process program counter (function: ProcessId -> StateId)
/// - `alive`: which processes are currently alive (function: ProcessId -> BOOLEAN)
/// - `mutex_owner`: who holds each mutex (function: MutexId -> ProcessId | "none")
/// - `mutex_poisoned`: whether each mutex is poisoned (function: MutexId -> BOOLEAN)
/// - `locks_held`: set of locks held per process (function: ProcessId -> SUBSET MutexIds)
/// - `rw_readers`: set of reader processes per rwlock (function: RwLockId -> SUBSET ProcessIds)
/// - `rw_writer`: writer process per rwlock (function: RwLockId -> ProcessId | "none")
/// - `condvar_waiting`: set of processes waiting on each condvar
/// - `channel_buf`: channel buffer (function: ChannelId -> Seq(Messages))
/// - `senders_alive`: sender refcount per channel
/// - `receiver_alive`: whether receiver exists per channel
/// - Shared variables from the model
pub(super) fn collect_variable_names(model: &ConcurrentModel) -> Vec<String> {
    let mut vars = vec!["pc".to_string(), "alive".to_string()];

    let has_mutex = model
        .sync_primitives
        .iter()
        .any(|s| matches!(s.kind, SyncKind::Mutex { .. }));
    let has_rwlock = model
        .sync_primitives
        .iter()
        .any(|s| matches!(s.kind, SyncKind::RwLock { .. }));
    let has_condvar = model
        .sync_primitives
        .iter()
        .any(|s| matches!(s.kind, SyncKind::Condvar { .. }));
    let has_channel = model
        .sync_primitives
        .iter()
        .any(|s| matches!(s.kind, SyncKind::Channel { .. }));

    if has_mutex {
        vars.push("mutex_owner".to_string());
        vars.push("mutex_poisoned".to_string());
        vars.push("locks_held".to_string());
    }

    if has_rwlock {
        vars.push("rw_readers".to_string());
        vars.push("rw_writer".to_string());
    }

    if has_condvar {
        vars.push("condvar_waiting".to_string());
    }

    if has_channel {
        vars.push("channel_buf".to_string());
        vars.push("senders_alive".to_string());
        vars.push("receiver_alive".to_string());
    }

    // Shared variables from the model
    for var in &model.shared_vars {
        vars.push(var.name.clone());
    }

    vars
}
