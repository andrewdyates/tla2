// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trace-related tooling (parsing, validation, visualization).

mod validate_format;
mod validate_spec;
pub(crate) mod view;

use std::path::PathBuf;

use anyhow::Result;
use clap::{Subcommand, ValueEnum};
use tla_check::{ActionLabelMode, TraceInputFormatSelection};

use crate::cli_schema::TraceViewOutputFormat;

/// Trace-related tooling (parsing, validation, visualization).
///
/// Spec-based validation (#1082) uses TraceValidationEngine from tla-check.
#[derive(Debug, Subcommand)]
pub enum TraceCommand {
    /// View a counterexample trace with variable diffs between states.
    View {
        /// Path to the JSON output file from `tla2 check --output json`.
        trace_file: PathBuf,
        /// Output format: human (colored with change markers), json, or table.
        #[arg(long, value_enum, default_value = "human")]
        format: TraceViewOutputFormat,
        /// Show only specified variables (can be repeated).
        #[arg(long = "var", value_name = "VARIABLE")]
        filter: Vec<String>,
        /// Show only a specific step in detail.
        #[arg(long)]
        step: Option<usize>,
        /// Show variable diffs between consecutive steps (default: true).
        #[arg(long, default_value = "true", action = clap::ArgAction::Set)]
        diff: bool,
        /// Show unchanged variables alongside diffs.
        #[arg(long)]
        show_unchanged: bool,
    },
    /// Validate trace input parsing and invariants (header, indices, variable keys).
    ///
    /// Without --spec: validates trace format only (JSON structure, indices, variable keys).
    /// With --spec: validates trace against TLA+ specification (states match Init/Next).
    Validate {
        /// Trace input file (`.json` or `.jsonl`). Use `-` for stdin.
        file: PathBuf,
        /// Input format selection (default: `auto`).
        ///
        /// `auto` prefers JSONL by extension (`.jsonl`), otherwise falls back to JSON.
        /// When reading from stdin (`-`), `auto` defaults to JSON; use `--input-format jsonl` for JSONL.
        #[arg(long, value_enum, default_value = "auto")]
        input_format: TraceInputFormatArg,
        /// TLA+ specification file for spec-based validation.
        ///
        /// When provided, validates that each trace step matches a valid spec state
        /// reachable via Init/Next transitions.
        #[arg(long)]
        spec: Option<PathBuf>,
        /// Configuration file for the specification (default: <code>&lt;spec&gt;.cfg</code>).
        ///
        /// Specifies INIT, NEXT, CONSTANTS, etc. Required when --spec is provided.
        #[arg(long)]
        config: Option<PathBuf>,
        /// Action label enforcement mode (default: `error`).
        ///
        /// `error`: action label mismatches fail validation.
        /// `warn`: action label mismatches produce warnings but validation continues
        /// using observation-matched candidates. Useful for traces where the runtime
        /// combines multiple spec actions into a single step.
        #[arg(long, value_enum, default_value = "error")]
        action_label_mode: ActionLabelModeArg,
    },
}

#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub enum ActionLabelModeArg {
    /// Action label mismatches are hard errors (default).
    #[default]
    Error,
    /// Action label mismatches produce warnings but do not fail validation.
    Warn,
}

impl From<ActionLabelModeArg> for ActionLabelMode {
    fn from(arg: ActionLabelModeArg) -> Self {
        match arg {
            ActionLabelModeArg::Error => ActionLabelMode::Error,
            ActionLabelModeArg::Warn => ActionLabelMode::Warn,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub enum TraceInputFormatArg {
    /// Auto-detect by extension (`.jsonl` => JSONL), else JSON.
    #[default]
    Auto,
    /// JSON object form: `{version,module,variables,steps:[...]}`.
    Json,
    /// JSON Lines form: `header` then `step` events, one JSON object per line.
    #[value(name = "jsonl")]
    Jsonl,
}

impl From<TraceInputFormatArg> for TraceInputFormatSelection {
    fn from(arg: TraceInputFormatArg) -> Self {
        match arg {
            TraceInputFormatArg::Auto => TraceInputFormatSelection::Auto,
            TraceInputFormatArg::Json => TraceInputFormatSelection::Json,
            TraceInputFormatArg::Jsonl => TraceInputFormatSelection::Jsonl,
        }
    }
}

pub fn cmd_trace(command: TraceCommand) -> Result<()> {
    match command {
        TraceCommand::View {
            trace_file,
            format,
            filter,
            step,
            diff,
            show_unchanged,
        } => view::cmd_trace_view(&trace_file, format, &filter, step, diff, show_unchanged),
        TraceCommand::Validate {
            file,
            input_format,
            spec,
            config,
            action_label_mode,
        } => {
            if let Some(spec_path) = spec {
                validate_spec::cmd_trace_validate_with_spec(
                    &file,
                    input_format,
                    &spec_path,
                    config.as_deref(),
                    action_label_mode.into(),
                )
            } else {
                validate_format::cmd_trace_validate_format(&file, input_format)
            }
        }
    }
}
