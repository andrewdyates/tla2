// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;
use tla_core::ast::Substitution;

/// Instance declaration info for INSTANCE WITH evaluation
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct InstanceInfo {
    /// The module being instanced
    pub module_name: String,
    /// Substitutions from the WITH clause
    pub substitutions: Vec<Substitution>,
}

/// TLC configuration values exposed via TLCGet("config")
/// These are static configuration values that don't change during model checking.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct TlcConfig {
    /// Exploration mode: "bfs" (model checking), "generate" (random behaviors), or "simulate"
    pub mode: Arc<str>,
    /// Max depth (-1 for unlimited)
    pub depth: i64,
    /// Whether deadlock checking is enabled
    pub deadlock: bool,
    /// Number of simulation traces (-1 for default/unlimited)
    pub traces: i64,
    /// Random seed for simulation (0 = system-generated)
    pub seed: i64,
    /// Worker count (number of parallel threads)
    pub worker: i64,
}

impl TlcConfig {
    /// Create a new TlcConfig with the given exploration parameters.
    pub fn new(mode: Arc<str>, depth: i64, deadlock: bool) -> Self {
        TlcConfig {
            mode,
            depth,
            deadlock,
            traces: -1,
            seed: 0,
            worker: 1,
        }
    }
}

impl Default for TlcConfig {
    fn default() -> Self {
        TlcConfig {
            mode: Arc::from("bfs"),
            depth: -1,
            deadlock: true,
            traces: -1,
            seed: 0,
            worker: 1,
        }
    }
}

/// Runtime TLC statistics exposed via TLCGet("stats") and TLCGet("diameter").
///
/// These values change while a run is in progress and therefore live in
/// `EvalRuntimeState` rather than `SharedCtx`.
#[derive(Debug, Clone, Copy, Default)]
pub struct TlcRuntimeStats {
    /// Total states generated so far.
    pub generated: i64,
    /// Distinct states observed so far.
    pub distinct: i64,
    /// States currently left on the queue (0 in simulation mode).
    pub queue: i64,
    /// Trace count visible to TLCGet("stats").traces.
    pub traces: i64,
    /// TLCGet("diameter") value.
    pub diameter: i64,
}

impl TlcRuntimeStats {
    /// Construct a new runtime stats snapshot.
    pub fn new(generated: i64, distinct: i64, queue: i64, traces: i64, diameter: i64) -> Self {
        Self {
            generated,
            distinct,
            queue,
            traces,
            diameter,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct TlcActionContext {
    pub(crate) name: Arc<str>,
    pub(crate) params: Arc<[Arc<str>]>,
}
