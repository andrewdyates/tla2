// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checker integration: feeds generated TLA+ modules through tla-check.

use serde::{Deserialize, Serialize};

use crate::assumptions::Assumptions;
use crate::model::ConcurrentModel;
use crate::output::VerificationReport;

/// Options for model checking a concurrent model.
#[derive(Debug, Clone)]
pub struct CheckOptions {
    /// Number of BFS worker threads (0 = auto).
    pub workers: usize,
    /// Maximum number of states to explore (0 = unlimited).
    pub max_states: usize,
    /// Maximum BFS depth (0 = unlimited).
    pub max_depth: usize,
    /// Whether to emit the generated TLA+ source (for debugging).
    pub emit_tla: bool,
}

impl Default for CheckOptions {
    fn default() -> Self {
        Self {
            workers: 0,
            max_states: 0,
            max_depth: 0,
            emit_tla: false,
        }
    }
}

/// Result of checking a concurrent model.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConcurrentCheckResult {
    /// The verification outcome.
    pub report: VerificationReport,
    /// Assumptions under which verification was performed.
    pub assumptions: Assumptions,
    /// The generated TLA+ source (if `emit_tla` was set).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub generated_tla: Option<String>,
}

/// Errors that can occur during concurrent model checking.
#[derive(Debug, thiserror::Error)]
pub enum ConcurrentError {
    #[error("failed to deserialize concurrent model: {0}")]
    DeserializeModel(#[from] serde_json::Error),
    #[error("model validation error: {0}")]
    Validation(String),
    #[error("TLA+ generation error: {0}")]
    Generation(String),
    #[error("model checking error: {0}")]
    Check(String),
}

/// Check a concurrent model end-to-end.
///
/// 1. Validate the model
/// 2. Generate TLA+ Module AST
/// 3. Build Config
/// 4. Run model checker
/// 5. Map traces to Rust source
/// 6. Return structured result with assumptions
pub fn check_concurrent_model(
    model: &ConcurrentModel,
    options: &CheckOptions,
) -> Result<ConcurrentCheckResult, ConcurrentError> {
    // Phase 1: Validate
    validate_model(model)?;

    // Phase 2: Generate TLA+ module
    let module = crate::generate::generate_tla_module(model);

    // Phase 3: Build config
    let config = crate::generate::build_config(model);

    // Phase 4: Run checker
    let check_result = tla_check::check_module(&module, &config);

    // Phase 5: Map result
    let report = crate::output::check_result_to_report(&check_result, model);

    Ok(ConcurrentCheckResult {
        report,
        assumptions: model.assumptions.clone(),
        generated_tla: if options.emit_tla {
            Some(format!("{module:?}")) // TODO: proper TLA+ pretty-printing
        } else {
            None
        },
    })
}

fn validate_model(model: &ConcurrentModel) -> Result<(), ConcurrentError> {
    if model.processes.is_empty() {
        return Err(ConcurrentError::Validation(
            "model must have at least one process".to_string(),
        ));
    }

    // Verify all processes have at least one transition
    for process in &model.processes {
        if process.transitions.is_empty() {
            return Err(ConcurrentError::Validation(format!(
                "process '{}' has no transitions",
                process.id
            )));
        }
    }

    // Verify all sync IDs referenced in transitions exist
    let sync_ids: std::collections::HashSet<&str> = model
        .sync_primitives
        .iter()
        .map(|s| s.id.as_str())
        .collect();

    for process in &model.processes {
        for transition in &process.transitions {
            if let Some(sync_id) = transition.kind.sync_id() {
                if !sync_ids.contains(sync_id) {
                    return Err(ConcurrentError::Validation(format!(
                        "process '{}' references unknown sync primitive '{}'",
                        process.id, sync_id
                    )));
                }
            }
        }
    }

    Ok(())
}

impl TransitionKindExt for crate::transition::TransitionKind {
    fn sync_id(&self) -> Option<&str> {
        use crate::transition::TransitionKind;
        match self {
            TransitionKind::Lock { mutex }
            | TransitionKind::TryLockOk { mutex }
            | TransitionKind::TryLockErr { mutex }
            | TransitionKind::Unlock { mutex }
            | TransitionKind::LockPoisonOk { mutex }
            | TransitionKind::LockPoisonPanic { mutex } => Some(mutex),

            TransitionKind::ReadLock { rwlock }
            | TransitionKind::WriteLock { rwlock }
            | TransitionKind::TryReadOk { rwlock }
            | TransitionKind::TryReadErr { rwlock }
            | TransitionKind::TryWriteOk { rwlock }
            | TransitionKind::TryWriteErr { rwlock }
            | TransitionKind::ReadUnlock { rwlock }
            | TransitionKind::WriteUnlock { rwlock }
            | TransitionKind::UpgradableReadLock { rwlock }
            | TransitionKind::UpgradeToWrite { rwlock }
            | TransitionKind::DowngradeToRead { rwlock } => Some(rwlock),

            TransitionKind::ChannelSend { channel }
            | TransitionKind::ChannelSendErr { channel }
            | TransitionKind::ChannelRecv { channel }
            | TransitionKind::ChannelRecvDisconnected { channel }
            | TransitionKind::TryRecvOk { channel }
            | TransitionKind::TryRecvEmpty { channel }
            | TransitionKind::TryRecvDisconnected { channel }
            | TransitionKind::SenderDrop { channel }
            | TransitionKind::ReceiverDrop { channel } => Some(channel),

            TransitionKind::CondvarWaitRelease { condvar, .. }
            | TransitionKind::CondvarWaitReacquire { condvar, .. }
            | TransitionKind::SpuriousWake { condvar, .. }
            | TransitionKind::NotifyOne { condvar }
            | TransitionKind::NotifyAll { condvar }
            | TransitionKind::WaitTimeoutExpired { condvar, .. } => Some(condvar),

            TransitionKind::BarrierWait { barrier } => Some(barrier),
            TransitionKind::OnceCallOnce { once } | TransitionKind::OnceLockSet { once } => {
                Some(once)
            }

            TransitionKind::Spawn { .. }
            | TransitionKind::JoinOk { .. }
            | TransitionKind::JoinErr { .. }
            | TransitionKind::ScopeEnd { .. }
            | TransitionKind::AtomicLoad { .. }
            | TransitionKind::AtomicStore { .. }
            | TransitionKind::AtomicRmw { .. }
            | TransitionKind::CasOk { .. }
            | TransitionKind::CasFail { .. }
            | TransitionKind::Fence { .. }
            | TransitionKind::Park
            | TransitionKind::Unpark { .. }
            | TransitionKind::Panic { .. }
            | TransitionKind::Internal { .. } => None,
        }
    }
}

trait TransitionKindExt {
    fn sync_id(&self) -> Option<&str>;
}
