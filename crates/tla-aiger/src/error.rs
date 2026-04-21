// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use thiserror::Error;

#[derive(Debug, Error)]
pub enum AigerError {
    #[error("parse error at line {line}: {message}")]
    Parse { line: usize, message: String },

    #[error("invalid header: {0}")]
    InvalidHeader(String),

    #[error("unexpected EOF while reading binary delta encoding")]
    UnexpectedEof,

    #[error("invalid literal {literal}: exceeds maxvar {maxvar}")]
    InvalidLiteral { literal: u64, maxvar: u64 },

    #[error("undefined literal {0} referenced")]
    UndefinedLiteral(u64),

    #[error("duplicate definition for variable {0}")]
    DuplicateDefinition(u64),

    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("translation error: {0}")]
    Translation(String),
}
