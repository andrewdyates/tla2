// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-transition action generation for the 54 TransitionKind variants.

use tla_core::ast::{Expr, OperatorDef};

use super::helpers::*;
use super::spanned;
use super::variables;
use crate::model::{ConcurrentModel, Process};
use crate::transition::{Transition, TransitionKind};

/// Generate action operators for all transitions of a process.
///
/// Each transition becomes a named operator:
/// `Action_<process>_<from>_<to> == guard /\ state_updates /\ UNCHANGED others`
pub(super) fn generate_process_actions(
    model: &ConcurrentModel,
    process: &Process,
) -> Vec<OperatorDef> {
    let all_vars = variables::collect_variable_names(model);

    process
        .transitions
        .iter()
        .map(|t| generate_single_action(model, process, t, &all_vars))
        .collect()
}

/// Generate the action name for a transition.
pub(super) fn action_name(process_id: &str, transition: &Transition) -> String {
    format!(
        "Action_{}_{}_{}",
        process_id, transition.from, transition.to
    )
}

fn generate_single_action(
    model: &ConcurrentModel,
    process: &Process,
    transition: &Transition,
    all_vars: &[String],
) -> OperatorDef {
    let pid = &process.id;
    let name = action_name(pid, transition);

    // Common guard: process is alive and at the right pc state
    let pc_guard = and(
        eq(func_apply(ident("alive"), str_lit(pid)), bool_lit(true)),
        eq(
            func_apply(ident("pc"), str_lit(pid)),
            str_lit(&transition.from),
        ),
    );

    // Transition-specific guard and updates
    let (specific_guard, mut updated_vars) = generate_transition_body(model, pid, transition);

    // pc always updates
    updated_vars.push("pc".to_string());
    let pc_update = eq(
        prime(ident("pc")),
        except(ident("pc"), str_lit(pid), str_lit(&transition.to)),
    );

    // Build UNCHANGED for variables not in updated_vars
    let unchanged_vars: Vec<&str> = all_vars
        .iter()
        .filter(|v| !updated_vars.contains(v))
        .map(String::as_str)
        .collect();

    let mut body_parts = vec![pc_guard];
    if let Some(guard) = specific_guard {
        body_parts.push(guard);
    }
    body_parts.push(pc_update);

    // Add transition-specific state updates
    let updates = generate_transition_updates(model, pid, transition);
    body_parts.extend(updates);

    if !unchanged_vars.is_empty() {
        body_parts.push(unchanged(&unchanged_vars));
    }

    make_operator_with_prime(&name, conjoin(body_parts))
}

/// Generate guard and list of updated variable names for a transition.
fn generate_transition_body(
    model: &ConcurrentModel,
    pid: &str,
    transition: &Transition,
) -> (Option<Expr>, Vec<String>) {
    match &transition.kind {
        // ── Thread Lifecycle ──────────────────────────────────────
        TransitionKind::Spawn { child } => {
            // Guard: child not yet alive
            let guard = eq(func_apply(ident("alive"), str_lit(child)), bool_lit(false));
            (Some(guard), vec!["alive".to_string()])
        }

        TransitionKind::JoinOk { child } => {
            // Guard: child is at a terminal state and no longer alive
            let guard = and(
                eq(func_apply(ident("alive"), str_lit(child)), bool_lit(false)),
                in_set(
                    func_apply(ident("pc"), str_lit(child)),
                    ident("TerminalStates"),
                ),
            );
            (Some(guard), vec![])
        }

        TransitionKind::JoinErr { child } => {
            // Guard: child panicked (marked by a special terminal state)
            let guard = eq(func_apply(ident("alive"), str_lit(child)), bool_lit(false));
            (Some(guard), vec![])
        }

        TransitionKind::ScopeEnd { scope_id } => {
            // Guard: all scoped threads belonging to this scope have reached
            // a terminal state or are no longer alive. This enforces the core
            // safety guarantee of `thread::scope`: all scoped threads must
            // terminate before the scope exits.
            let scoped_guards: Vec<Expr> = model
                .processes
                .iter()
                .filter(|p| matches!(&p.kind, crate::model::ProcessKind::Scoped { scope_id: sid, .. } if sid == scope_id))
                .map(|p| {
                    // For each scoped process: pc[p] \in TerminalStates \/ alive[p] = FALSE
                    or(
                        in_set(
                            func_apply(ident("pc"), str_lit(&p.id)),
                            ident("TerminalStates"),
                        ),
                        eq(
                            func_apply(ident("alive"), str_lit(&p.id)),
                            bool_lit(false),
                        ),
                    )
                })
                .collect();

            if scoped_guards.is_empty() {
                // No scoped processes found for this scope — no additional guard
                (None, vec![])
            } else {
                (Some(conjoin(scoped_guards)), vec![])
            }
        }

        // ── Mutex Operations ─────────────────────────────────────
        TransitionKind::Lock { mutex } => {
            // Guard: mutex not owned and not poisoned
            let guard = and(
                eq(
                    func_apply(ident("mutex_owner"), str_lit(mutex)),
                    ident("NoOwner"),
                ),
                eq(
                    func_apply(ident("mutex_poisoned"), str_lit(mutex)),
                    bool_lit(false),
                ),
            );
            (
                Some(guard),
                vec!["mutex_owner".to_string(), "locks_held".to_string()],
            )
        }

        TransitionKind::TryLockOk { mutex } => {
            // Guard: mutex not owned AND not poisoned
            // In Rust, try_lock() on a poisoned mutex returns Err(TryLockError::Poisoned(...))
            let guard = and(
                eq(
                    func_apply(ident("mutex_owner"), str_lit(mutex)),
                    ident("NoOwner"),
                ),
                not(func_apply(ident("mutex_poisoned"), str_lit(mutex))),
            );
            (
                Some(guard),
                vec!["mutex_owner".to_string(), "locks_held".to_string()],
            )
        }

        TransitionKind::TryLockErr { mutex } => {
            // Guard: mutex IS owned by someone else
            let guard = and(
                neq(
                    func_apply(ident("mutex_owner"), str_lit(mutex)),
                    ident("NoOwner"),
                ),
                neq(
                    func_apply(ident("mutex_owner"), str_lit(mutex)),
                    str_lit(pid),
                ),
            );
            (Some(guard), vec![])
        }

        TransitionKind::Unlock { mutex } => {
            // Guard: this process owns the mutex
            let guard = eq(
                func_apply(ident("mutex_owner"), str_lit(mutex)),
                str_lit(pid),
            );
            (
                Some(guard),
                vec!["mutex_owner".to_string(), "locks_held".to_string()],
            )
        }

        TransitionKind::LockPoisonOk { mutex } => {
            // Guard: mutex not owned AND poisoned, handler present
            let guard = and(
                eq(
                    func_apply(ident("mutex_owner"), str_lit(mutex)),
                    ident("NoOwner"),
                ),
                eq(
                    func_apply(ident("mutex_poisoned"), str_lit(mutex)),
                    bool_lit(true),
                ),
            );
            (
                Some(guard),
                vec!["mutex_owner".to_string(), "locks_held".to_string()],
            )
        }

        TransitionKind::LockPoisonPanic { mutex } => {
            // Guard: mutex not owned AND poisoned, no handler → propagate panic
            let guard = and(
                eq(
                    func_apply(ident("mutex_owner"), str_lit(mutex)),
                    ident("NoOwner"),
                ),
                eq(
                    func_apply(ident("mutex_poisoned"), str_lit(mutex)),
                    bool_lit(true),
                ),
            );
            (Some(guard), vec!["alive".to_string()])
        }

        // ── RwLock Operations ────────────────────────────────────
        TransitionKind::ReadLock { rwlock } => {
            // Guard: no writer holds the lock
            let guard = eq(
                func_apply(ident("rw_writer"), str_lit(rwlock)),
                ident("NoOwner"),
            );
            (Some(guard), vec!["rw_readers".to_string()])
        }

        TransitionKind::WriteLock { rwlock } => {
            // Guard: no writer AND no readers
            let guard = and(
                eq(
                    func_apply(ident("rw_writer"), str_lit(rwlock)),
                    ident("NoOwner"),
                ),
                eq(
                    func_apply(ident("rw_readers"), str_lit(rwlock)),
                    empty_set(),
                ),
            );
            (Some(guard), vec!["rw_writer".to_string()])
        }

        TransitionKind::TryReadOk { rwlock } => {
            let guard = eq(
                func_apply(ident("rw_writer"), str_lit(rwlock)),
                ident("NoOwner"),
            );
            (Some(guard), vec!["rw_readers".to_string()])
        }

        TransitionKind::TryReadErr { rwlock } => {
            let guard = neq(
                func_apply(ident("rw_writer"), str_lit(rwlock)),
                ident("NoOwner"),
            );
            (Some(guard), vec![])
        }

        TransitionKind::TryWriteOk { rwlock } => {
            let guard = and(
                eq(
                    func_apply(ident("rw_writer"), str_lit(rwlock)),
                    ident("NoOwner"),
                ),
                eq(
                    func_apply(ident("rw_readers"), str_lit(rwlock)),
                    empty_set(),
                ),
            );
            (Some(guard), vec!["rw_writer".to_string()])
        }

        TransitionKind::TryWriteErr { rwlock } => {
            let guard = or(
                neq(
                    func_apply(ident("rw_writer"), str_lit(rwlock)),
                    ident("NoOwner"),
                ),
                neq(
                    func_apply(ident("rw_readers"), str_lit(rwlock)),
                    empty_set(),
                ),
            );
            (Some(guard), vec![])
        }

        TransitionKind::ReadUnlock { rwlock } => {
            let guard = in_set(
                str_lit(pid),
                func_apply(ident("rw_readers"), str_lit(rwlock)),
            );
            (Some(guard), vec!["rw_readers".to_string()])
        }

        TransitionKind::WriteUnlock { rwlock } => {
            let guard = eq(
                func_apply(ident("rw_writer"), str_lit(rwlock)),
                str_lit(pid),
            );
            (Some(guard), vec!["rw_writer".to_string()])
        }

        TransitionKind::UpgradableReadLock { rwlock } => {
            let guard = eq(
                func_apply(ident("rw_writer"), str_lit(rwlock)),
                ident("NoOwner"),
            );
            (Some(guard), vec!["rw_readers".to_string()])
        }

        TransitionKind::UpgradeToWrite { rwlock } => {
            // Upgrade: must be only reader, then become writer
            let guard = and(
                in_set(
                    str_lit(pid),
                    func_apply(ident("rw_readers"), str_lit(rwlock)),
                ),
                eq(
                    func_apply(ident("rw_readers"), str_lit(rwlock)),
                    Expr::SetEnum(vec![spanned(str_lit(pid))]),
                ),
            );
            (
                Some(guard),
                vec!["rw_readers".to_string(), "rw_writer".to_string()],
            )
        }

        TransitionKind::DowngradeToRead { rwlock } => {
            let guard = eq(
                func_apply(ident("rw_writer"), str_lit(rwlock)),
                str_lit(pid),
            );
            (
                Some(guard),
                vec!["rw_readers".to_string(), "rw_writer".to_string()],
            )
        }

        // ── Atomic Operations (SeqCst for Phase 1) ──────────────
        TransitionKind::AtomicLoad { .. } => {
            (None, vec![]) // Read-only under SeqCst
        }

        TransitionKind::AtomicStore { variable, .. } => (None, vec![variable.clone()]),

        TransitionKind::AtomicRmw { variable, .. } => (None, vec![variable.clone()]),

        TransitionKind::CasOk { variable, .. } => (None, vec![variable.clone()]),

        TransitionKind::CasFail { .. } => (None, vec![]),

        TransitionKind::Fence { .. } => {
            (None, vec![]) // No-op under SeqCst
        }

        // ── Channel Operations ───────────────────────────────────
        TransitionKind::ChannelSend { channel } => {
            // Guard: receiver is alive
            let receiver_guard = eq(
                func_apply(ident("receiver_alive"), str_lit(channel)),
                bool_lit(true),
            );

            // For bounded channels, also guard on buffer not full:
            //   Len(channel_buf[ch]) < capacity
            let capacity = model
                .sync_primitives
                .iter()
                .find(|sp| sp.id == *channel)
                .and_then(|sp| match &sp.kind {
                    crate::sync_kind::SyncKind::Channel { capacity, .. } => *capacity,
                    _ => None,
                });

            let guard = if let Some(cap) = capacity {
                let len_expr = Expr::Apply(
                    Box::new(spanned(ident("Len"))),
                    vec![spanned(func_apply(ident("channel_buf"), str_lit(channel)))],
                );
                let capacity_guard = Expr::Lt(
                    Box::new(spanned(len_expr)),
                    Box::new(spanned(int_lit(cap as i64))),
                );
                and(receiver_guard, capacity_guard)
            } else {
                receiver_guard
            };

            (Some(guard), vec!["channel_buf".to_string()])
        }

        TransitionKind::ChannelSendErr { channel } => {
            let guard = eq(
                func_apply(ident("receiver_alive"), str_lit(channel)),
                bool_lit(false),
            );
            (Some(guard), vec![])
        }

        TransitionKind::ChannelRecv { channel } => {
            // Guard: buffer non-empty OR (buffer empty AND all senders dead → disconnect)
            let guard = and(
                Expr::Gt(
                    Box::new(spanned(Expr::Apply(
                        Box::new(spanned(ident("Len"))),
                        vec![spanned(func_apply(ident("channel_buf"), str_lit(channel)))],
                    ))),
                    Box::new(spanned(int_lit(0))),
                ),
                eq(
                    func_apply(ident("receiver_alive"), str_lit(channel)),
                    bool_lit(true),
                ),
            );
            (Some(guard), vec!["channel_buf".to_string()])
        }

        TransitionKind::ChannelRecvDisconnected { channel } => {
            let guard = and(
                eq(
                    Expr::Apply(
                        Box::new(spanned(ident("Len"))),
                        vec![spanned(func_apply(ident("channel_buf"), str_lit(channel)))],
                    ),
                    int_lit(0),
                ),
                eq(
                    func_apply(ident("senders_alive"), str_lit(channel)),
                    int_lit(0),
                ),
            );
            (Some(guard), vec![])
        }

        TransitionKind::TryRecvOk { channel } => {
            let guard = Expr::Gt(
                Box::new(spanned(Expr::Apply(
                    Box::new(spanned(ident("Len"))),
                    vec![spanned(func_apply(ident("channel_buf"), str_lit(channel)))],
                ))),
                Box::new(spanned(int_lit(0))),
            );
            (Some(guard), vec!["channel_buf".to_string()])
        }

        TransitionKind::TryRecvEmpty { channel } => {
            let guard = eq(
                Expr::Apply(
                    Box::new(spanned(ident("Len"))),
                    vec![spanned(func_apply(ident("channel_buf"), str_lit(channel)))],
                ),
                int_lit(0),
            );
            (Some(guard), vec![])
        }

        TransitionKind::TryRecvDisconnected { channel } => {
            let guard = and(
                eq(
                    Expr::Apply(
                        Box::new(spanned(ident("Len"))),
                        vec![spanned(func_apply(ident("channel_buf"), str_lit(channel)))],
                    ),
                    int_lit(0),
                ),
                eq(
                    func_apply(ident("senders_alive"), str_lit(channel)),
                    int_lit(0),
                ),
            );
            (Some(guard), vec![])
        }

        TransitionKind::SenderDrop { .. } => (None, vec!["senders_alive".to_string()]),

        TransitionKind::ReceiverDrop { .. } => (None, vec!["receiver_alive".to_string()]),

        // ── Condvar Operations ───────────────────────────────────
        TransitionKind::CondvarWaitRelease { condvar: _, mutex } => {
            // Guard: process holds the mutex
            let guard = eq(
                func_apply(ident("mutex_owner"), str_lit(mutex)),
                str_lit(pid),
            );
            (
                Some(guard),
                vec![
                    "mutex_owner".to_string(),
                    "locks_held".to_string(),
                    "condvar_waiting".to_string(),
                ],
            )
        }

        TransitionKind::CondvarWaitReacquire { condvar, mutex } => {
            // Guard: process is in wait set AND mutex is free
            let guard = and(
                in_set(
                    str_lit(pid),
                    func_apply(ident("condvar_waiting"), str_lit(condvar)),
                ),
                eq(
                    func_apply(ident("mutex_owner"), str_lit(mutex)),
                    ident("NoOwner"),
                ),
            );
            (
                Some(guard),
                vec![
                    "mutex_owner".to_string(),
                    "locks_held".to_string(),
                    "condvar_waiting".to_string(),
                ],
            )
        }

        TransitionKind::SpuriousWake { condvar, mutex } => {
            // Same guard as WaitReacquire — always enabled for waiting processes
            let guard = and(
                in_set(
                    str_lit(pid),
                    func_apply(ident("condvar_waiting"), str_lit(condvar)),
                ),
                eq(
                    func_apply(ident("mutex_owner"), str_lit(mutex)),
                    ident("NoOwner"),
                ),
            );
            (
                Some(guard),
                vec![
                    "mutex_owner".to_string(),
                    "locks_held".to_string(),
                    "condvar_waiting".to_string(),
                ],
            )
        }

        TransitionKind::NotifyOne { .. } => {
            (None, vec![]) // Notification doesn't change state directly
        }

        TransitionKind::NotifyAll { .. } => (None, vec![]),

        TransitionKind::WaitTimeoutExpired { condvar, mutex } => {
            let guard = and(
                in_set(
                    str_lit(pid),
                    func_apply(ident("condvar_waiting"), str_lit(condvar)),
                ),
                eq(
                    func_apply(ident("mutex_owner"), str_lit(mutex)),
                    ident("NoOwner"),
                ),
            );
            (
                Some(guard),
                vec![
                    "mutex_owner".to_string(),
                    "locks_held".to_string(),
                    "condvar_waiting".to_string(),
                ],
            )
        }

        // ── Barrier ──────────────────────────────────────────────
        TransitionKind::BarrierWait { .. } => {
            (None, vec![]) // TODO: barrier counting
        }

        // ── Once ─────────────────────────────────────────────────
        TransitionKind::OnceCallOnce { .. } | TransitionKind::OnceLockSet { .. } => (None, vec![]),

        // ── Park/Unpark ──────────────────────────────────────────
        TransitionKind::Park => (None, vec![]),

        TransitionKind::Unpark { .. } => (None, vec![]),

        // ── Panic ────────────────────────────────────────────────
        TransitionKind::Panic { guards } => {
            let mut updated = vec!["alive".to_string()];
            for g in guards {
                match g.mode {
                    crate::model::GuardMode::MutexExclusive => {
                        updated.push("mutex_owner".to_string());
                        updated.push("mutex_poisoned".to_string());
                        updated.push("locks_held".to_string());
                    }
                    crate::model::GuardMode::RwLockWrite => {
                        updated.push("rw_writer".to_string());
                        // RwLock write guard poisons on panic
                    }
                    crate::model::GuardMode::RwLockRead => {
                        updated.push("rw_readers".to_string());
                        // RwLock read guard does NOT poison
                    }
                    crate::model::GuardMode::RwLockUpgradableRead => {
                        updated.push("rw_readers".to_string());
                    }
                }
            }
            updated.sort();
            updated.dedup();
            (None, updated)
        }

        // ── Internal ─────────────────────────────────────────────
        TransitionKind::Internal { .. } => (None, vec![]),
    }
}

/// Generate state update expressions for a transition.
fn generate_transition_updates(
    _model: &ConcurrentModel,
    pid: &str,
    transition: &Transition,
) -> Vec<Expr> {
    let mut updates = Vec::new();

    match &transition.kind {
        TransitionKind::Spawn { child } => {
            // alive'[child] = TRUE
            updates.push(eq(
                prime(ident("alive")),
                except(ident("alive"), str_lit(child), bool_lit(true)),
            ));
        }

        TransitionKind::Lock { mutex }
        | TransitionKind::TryLockOk { mutex }
        | TransitionKind::LockPoisonOk { mutex } => {
            // mutex_owner'[m] = pid
            updates.push(eq(
                prime(ident("mutex_owner")),
                except(ident("mutex_owner"), str_lit(mutex), str_lit(pid)),
            ));
            // locks_held'[pid] = locks_held[pid] \union {m}
            updates.push(eq(
                prime(ident("locks_held")),
                except(
                    ident("locks_held"),
                    str_lit(pid),
                    set_union(
                        func_apply(ident("locks_held"), str_lit(pid)),
                        Expr::SetEnum(vec![spanned(str_lit(mutex))]),
                    ),
                ),
            ));
        }

        TransitionKind::Unlock { mutex } => {
            // mutex_owner'[m] = NoOwner
            updates.push(eq(
                prime(ident("mutex_owner")),
                except(ident("mutex_owner"), str_lit(mutex), ident("NoOwner")),
            ));
            // locks_held'[pid] = locks_held[pid] \ {m}
            updates.push(eq(
                prime(ident("locks_held")),
                except(
                    ident("locks_held"),
                    str_lit(pid),
                    set_minus(
                        func_apply(ident("locks_held"), str_lit(pid)),
                        Expr::SetEnum(vec![spanned(str_lit(mutex))]),
                    ),
                ),
            ));
        }

        TransitionKind::LockPoisonPanic { .. } => {
            // Process dies
            updates.push(eq(
                prime(ident("alive")),
                except(ident("alive"), str_lit(pid), bool_lit(false)),
            ));
        }

        TransitionKind::ReadLock { rwlock }
        | TransitionKind::TryReadOk { rwlock }
        | TransitionKind::UpgradableReadLock { rwlock } => {
            // rw_readers'[rw] = rw_readers[rw] \union {pid}
            updates.push(eq(
                prime(ident("rw_readers")),
                except(
                    ident("rw_readers"),
                    str_lit(rwlock),
                    set_union(
                        func_apply(ident("rw_readers"), str_lit(rwlock)),
                        Expr::SetEnum(vec![spanned(str_lit(pid))]),
                    ),
                ),
            ));
        }

        TransitionKind::WriteLock { rwlock } | TransitionKind::TryWriteOk { rwlock } => {
            // rw_writer'[rw] = pid
            updates.push(eq(
                prime(ident("rw_writer")),
                except(ident("rw_writer"), str_lit(rwlock), str_lit(pid)),
            ));
        }

        TransitionKind::ReadUnlock { rwlock } => {
            // rw_readers'[rw] = rw_readers[rw] \ {pid}
            updates.push(eq(
                prime(ident("rw_readers")),
                except(
                    ident("rw_readers"),
                    str_lit(rwlock),
                    set_minus(
                        func_apply(ident("rw_readers"), str_lit(rwlock)),
                        Expr::SetEnum(vec![spanned(str_lit(pid))]),
                    ),
                ),
            ));
        }

        TransitionKind::WriteUnlock { rwlock } => {
            // rw_writer'[rw] = NoOwner
            updates.push(eq(
                prime(ident("rw_writer")),
                except(ident("rw_writer"), str_lit(rwlock), ident("NoOwner")),
            ));
        }

        TransitionKind::UpgradeToWrite { rwlock } => {
            // Remove from readers, set as writer
            updates.push(eq(
                prime(ident("rw_readers")),
                except(
                    ident("rw_readers"),
                    str_lit(rwlock),
                    set_minus(
                        func_apply(ident("rw_readers"), str_lit(rwlock)),
                        Expr::SetEnum(vec![spanned(str_lit(pid))]),
                    ),
                ),
            ));
            updates.push(eq(
                prime(ident("rw_writer")),
                except(ident("rw_writer"), str_lit(rwlock), str_lit(pid)),
            ));
        }

        TransitionKind::DowngradeToRead { rwlock } => {
            // Remove as writer, add to readers
            updates.push(eq(
                prime(ident("rw_writer")),
                except(ident("rw_writer"), str_lit(rwlock), ident("NoOwner")),
            ));
            updates.push(eq(
                prime(ident("rw_readers")),
                except(
                    ident("rw_readers"),
                    str_lit(rwlock),
                    set_union(
                        func_apply(ident("rw_readers"), str_lit(rwlock)),
                        Expr::SetEnum(vec![spanned(str_lit(pid))]),
                    ),
                ),
            ));
        }

        TransitionKind::ChannelSend { channel } => {
            // channel_buf'[ch] = Append(channel_buf[ch], msg)
            // For Phase 1, we use a unit message "msg"
            updates.push(eq(
                prime(ident("channel_buf")),
                except(
                    ident("channel_buf"),
                    str_lit(channel),
                    Expr::Apply(
                        Box::new(spanned(ident("Append"))),
                        vec![
                            spanned(func_apply(ident("channel_buf"), str_lit(channel))),
                            spanned(str_lit("msg")),
                        ],
                    ),
                ),
            ));
        }

        TransitionKind::ChannelRecv { channel } | TransitionKind::TryRecvOk { channel } => {
            // channel_buf'[ch] = Tail(channel_buf[ch])
            updates.push(eq(
                prime(ident("channel_buf")),
                except(
                    ident("channel_buf"),
                    str_lit(channel),
                    Expr::Apply(
                        Box::new(spanned(ident("Tail"))),
                        vec![spanned(func_apply(ident("channel_buf"), str_lit(channel)))],
                    ),
                ),
            ));
        }

        TransitionKind::SenderDrop { channel } => {
            // senders_alive'[ch] = senders_alive[ch] - 1
            updates.push(eq(
                prime(ident("senders_alive")),
                except(
                    ident("senders_alive"),
                    str_lit(channel),
                    Expr::Sub(
                        Box::new(spanned(func_apply(
                            ident("senders_alive"),
                            str_lit(channel),
                        ))),
                        Box::new(spanned(int_lit(1))),
                    ),
                ),
            ));
        }

        TransitionKind::ReceiverDrop { channel } => {
            // receiver_alive'[ch] = FALSE
            updates.push(eq(
                prime(ident("receiver_alive")),
                except(ident("receiver_alive"), str_lit(channel), bool_lit(false)),
            ));
        }

        TransitionKind::CondvarWaitRelease { condvar, mutex } => {
            // Release mutex
            updates.push(eq(
                prime(ident("mutex_owner")),
                except(ident("mutex_owner"), str_lit(mutex), ident("NoOwner")),
            ));
            // Remove from locks_held
            updates.push(eq(
                prime(ident("locks_held")),
                except(
                    ident("locks_held"),
                    str_lit(pid),
                    set_minus(
                        func_apply(ident("locks_held"), str_lit(pid)),
                        Expr::SetEnum(vec![spanned(str_lit(mutex))]),
                    ),
                ),
            ));
            // Add to condvar wait set
            updates.push(eq(
                prime(ident("condvar_waiting")),
                except(
                    ident("condvar_waiting"),
                    str_lit(condvar),
                    set_union(
                        func_apply(ident("condvar_waiting"), str_lit(condvar)),
                        Expr::SetEnum(vec![spanned(str_lit(pid))]),
                    ),
                ),
            ));
        }

        TransitionKind::CondvarWaitReacquire { condvar, mutex }
        | TransitionKind::SpuriousWake { condvar, mutex }
        | TransitionKind::WaitTimeoutExpired { condvar, mutex } => {
            // Reacquire mutex
            updates.push(eq(
                prime(ident("mutex_owner")),
                except(ident("mutex_owner"), str_lit(mutex), str_lit(pid)),
            ));
            // Add to locks_held
            updates.push(eq(
                prime(ident("locks_held")),
                except(
                    ident("locks_held"),
                    str_lit(pid),
                    set_union(
                        func_apply(ident("locks_held"), str_lit(pid)),
                        Expr::SetEnum(vec![spanned(str_lit(mutex))]),
                    ),
                ),
            ));
            // Remove from condvar wait set
            updates.push(eq(
                prime(ident("condvar_waiting")),
                except(
                    ident("condvar_waiting"),
                    str_lit(condvar),
                    set_minus(
                        func_apply(ident("condvar_waiting"), str_lit(condvar)),
                        Expr::SetEnum(vec![spanned(str_lit(pid))]),
                    ),
                ),
            ));
        }

        TransitionKind::Panic { guards } => {
            // Kill the process
            updates.push(eq(
                prime(ident("alive")),
                except(ident("alive"), str_lit(pid), bool_lit(false)),
            ));
            // Release and poison held guards
            for g in guards {
                match g.mode {
                    crate::model::GuardMode::MutexExclusive => {
                        updates.push(eq(
                            prime(ident("mutex_owner")),
                            except(ident("mutex_owner"), str_lit(&g.sync_id), ident("NoOwner")),
                        ));
                        updates.push(eq(
                            prime(ident("mutex_poisoned")),
                            except(ident("mutex_poisoned"), str_lit(&g.sync_id), bool_lit(true)),
                        ));
                        // Remove mutex from locks_held for the panicking process
                        updates.push(eq(
                            prime(ident("locks_held")),
                            except(
                                ident("locks_held"),
                                str_lit(pid),
                                set_minus(
                                    func_apply(ident("locks_held"), str_lit(pid)),
                                    Expr::SetEnum(vec![spanned(str_lit(&g.sync_id))]),
                                ),
                            ),
                        ));
                    }
                    crate::model::GuardMode::RwLockWrite => {
                        updates.push(eq(
                            prime(ident("rw_writer")),
                            except(ident("rw_writer"), str_lit(&g.sync_id), ident("NoOwner")),
                        ));
                        // RwLock write guard DOES poison (would need rw_poisoned var)
                    }
                    crate::model::GuardMode::RwLockRead => {
                        // Read guard does NOT poison
                        updates.push(eq(
                            prime(ident("rw_readers")),
                            except(
                                ident("rw_readers"),
                                str_lit(&g.sync_id),
                                set_minus(
                                    func_apply(ident("rw_readers"), str_lit(&g.sync_id)),
                                    Expr::SetEnum(vec![spanned(str_lit(pid))]),
                                ),
                            ),
                        ));
                    }
                    crate::model::GuardMode::RwLockUpgradableRead => {
                        updates.push(eq(
                            prime(ident("rw_readers")),
                            except(
                                ident("rw_readers"),
                                str_lit(&g.sync_id),
                                set_minus(
                                    func_apply(ident("rw_readers"), str_lit(&g.sync_id)),
                                    Expr::SetEnum(vec![spanned(str_lit(pid))]),
                                ),
                            ),
                        ));
                    }
                }
            }
        }

        // No state updates needed for these
        TransitionKind::TryLockErr { .. }
        | TransitionKind::TryReadErr { .. }
        | TransitionKind::TryWriteErr { .. }
        | TransitionKind::JoinOk { .. }
        | TransitionKind::JoinErr { .. }
        | TransitionKind::ScopeEnd { .. }
        | TransitionKind::AtomicLoad { .. }
        | TransitionKind::AtomicStore { .. }
        | TransitionKind::AtomicRmw { .. }
        | TransitionKind::CasOk { .. }
        | TransitionKind::CasFail { .. }
        | TransitionKind::Fence { .. }
        | TransitionKind::ChannelSendErr { .. }
        | TransitionKind::ChannelRecvDisconnected { .. }
        | TransitionKind::TryRecvEmpty { .. }
        | TransitionKind::TryRecvDisconnected { .. }
        | TransitionKind::NotifyOne { .. }
        | TransitionKind::NotifyAll { .. }
        | TransitionKind::BarrierWait { .. }
        | TransitionKind::OnceCallOnce { .. }
        | TransitionKind::OnceLockSet { .. }
        | TransitionKind::Park
        | TransitionKind::Unpark { .. }
        | TransitionKind::Internal { .. } => {}
    }

    updates
}
