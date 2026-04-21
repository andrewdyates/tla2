// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Data types for simulation mode: config, stats, and result.
//!
//! Extracted from simulation.rs to reduce file size.

use super::{CheckError, Trace};

/// Configuration for simulation mode
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct SimulationConfig {
    /// Number of random traces to generate
    pub num_traces: usize,
    /// Maximum length of each trace (steps from initial state)
    pub max_trace_length: usize,
    /// Random seed for reproducibility (None = random seed)
    pub seed: Option<u64>,
    /// Whether to check invariants during simulation
    pub check_invariants: bool,
    /// Action constraints from config
    pub action_constraints: Vec<String>,
}

impl Default for SimulationConfig {
    fn default() -> Self {
        SimulationConfig {
            num_traces: 1000,
            max_trace_length: 100,
            seed: None,
            check_invariants: true,
            action_constraints: Vec::new(),
        }
    }
}

/// Statistics from simulation
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct SimulationStats {
    /// Total number of traces generated
    pub traces_generated: usize,
    /// Total number of states visited (may include duplicates across traces)
    pub states_visited: usize,
    /// Number of distinct states seen
    pub distinct_states: usize,
    /// Number of transitions taken
    pub transitions: usize,
    /// Maximum trace length achieved
    pub max_trace_length: usize,
    /// Average trace length
    pub avg_trace_length: f64,
    /// Number of traces that hit deadlock
    pub deadlocked_traces: usize,
    /// Number of traces that hit max length limit
    pub truncated_traces: usize,
    /// Elapsed time in seconds
    pub elapsed_secs: f64,
}

/// Result of simulation
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum SimulationResult {
    /// Simulation completed without finding violations
    Success(SimulationStats),
    /// An invariant was violated during simulation
    InvariantViolation {
        invariant: String,
        trace: Trace,
        stats: SimulationStats,
    },
    /// Deadlock detected during simulation (no enabled actions and not a terminal state).
    /// Only returned when `check_deadlock` is true in the model config.
    /// Matches TLC's `SimulationWorkerError(EC.TLC_DEADLOCK_REACHED, ...)`.
    Deadlock {
        trace: Trace,
        stats: SimulationStats,
    },
    /// Error during simulation
    Error {
        error: CheckError,
        stats: SimulationStats,
    },
}
