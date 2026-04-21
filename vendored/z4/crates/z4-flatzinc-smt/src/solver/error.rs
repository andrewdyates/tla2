// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::io;

/// Errors from the solver driver.
#[derive(Debug)]
pub enum SolverError {
    SpawnFailed {
        path: String,
        source: io::Error,
    },
    IoError(io::Error),
    SolverError(String),
    EmptyOutput,
    UnexpectedOutput(String),
    MissingObjective(String),
    ParseIntError(String),
    /// z4 does not support incremental solving over pipes.
    ///
    /// z4 reads all stdin before processing when stdin is a pipe (not a terminal).
    /// The IncrementalSolver requires z4 to process commands incrementally.
    /// Callers should fall back to one-shot solving (`run_z4_oneshot`).
    PipeBuffering,
}

impl std::fmt::Display for SolverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SpawnFailed { path, source } => {
                write!(f, "failed to spawn solver at '{path}': {source}")
            }
            Self::IoError(e) => write!(f, "I/O error: {e}"),
            Self::SolverError(s) => write!(f, "solver error: {s}"),
            Self::EmptyOutput => write!(f, "solver produced no output"),
            Self::UnexpectedOutput(s) => write!(f, "unexpected solver output: {s}"),
            Self::MissingObjective(s) => write!(f, "objective '{s}' not in model"),
            Self::ParseIntError(s) => write!(f, "cannot parse integer: {s}"),
            Self::PipeBuffering => write!(
                f,
                "z4 does not respond over pipes (reads all stdin before processing); \
                 falling back to one-shot solving"
            ),
        }
    }
}

impl std::error::Error for SolverError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::SpawnFailed { source, .. } | Self::IoError(source) => Some(source),
            _ => None,
        }
    }
}

impl From<io::Error> for SolverError {
    fn from(e: io::Error) -> Self {
        Self::IoError(e)
    }
}
