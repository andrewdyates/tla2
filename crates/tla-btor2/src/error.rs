// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates
// Error types for BTOR2 parsing and validation.

/// Unique identifier for a BTOR2 line/node.
pub type NodeId = i64;

/// Error type for BTOR2 parsing and validation.
#[derive(Debug, thiserror::Error)]
pub enum Btor2Error {
    /// I/O error when reading a BTOR2 file.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    /// Parse error at a specific line.
    #[error("parse error at line {line}: {message}")]
    ParseError { line: usize, message: String },

    /// Reference to an invalid or undefined sort.
    #[error("invalid sort id {sort_id} at line {line}")]
    InvalidSort { line: usize, sort_id: NodeId },

    /// Reference to an undefined node.
    #[error("undefined node id {node_id} at line {line}")]
    UndefinedNode { line: usize, node_id: NodeId },

    /// A sort ID does not reference a `sort` node.
    #[error("node {node_id} at line {line} is not a sort")]
    NotASort { line: usize, node_id: NodeId },

    /// Duplicate node ID.
    #[error("duplicate node id {node_id} at line {line}")]
    DuplicateId { line: usize, node_id: NodeId },

    /// Wrong number of arguments for an operator.
    #[error("invalid argument count for {op} at line {line}: expected {expected}, got {got}")]
    InvalidArgCount {
        line: usize,
        op: String,
        expected: usize,
        got: usize,
    },
}
