// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Error types for PNML parsing and Petri net exploration.

use std::path::PathBuf;

#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum PnmlError {
    #[error("I/O error reading {path}: {source}")]
    Io {
        path: PathBuf,
        source: std::io::Error,
    },

    #[error("XML parse error: {0}")]
    XmlParse(String),

    /// The PNML input uses a net kind or construct that `tla-petri` does not support.
    ///
    /// [`crate::parser::parse_pnml_dir`] emits this for non-`ptnet` inputs.
    /// [`crate::model::load_model_dir`] may also emit it for colored-model
    /// encodings outside the supported unfolding subset or for unfold-size
    /// guardrails.
    #[error("unsupported PNML net or construct: {net_type}")]
    UnsupportedNetType { net_type: String },

    #[error("missing required element: {0}")]
    MissingElement(String),

    #[error("invalid arc: source={src_id}, target={tgt_id}: {reason}")]
    InvalidArc {
        src_id: String,
        tgt_id: String,
        reason: String,
    },

    #[error("invalid marking value: {0}")]
    InvalidMarking(String),

    #[error("reduction arithmetic overflow: {context}")]
    ReductionOverflow { context: String },

    #[error("unknown examination: {0}")]
    UnknownExamination(String),

    #[error("examination {examination} does not use property XML")]
    ExaminationDoesNotUsePropertyXml { examination: String },
}
