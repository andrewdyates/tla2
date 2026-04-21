// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 completions` subcommand: generate shell completion scripts.
//!
//! Prints a completion script for the specified shell to stdout.
//! Users redirect the output to the appropriate location for their shell.

use anyhow::Result;
use clap::CommandFactory;
use clap_complete::Shell;

use crate::cli_schema::Cli;

/// Generate and print shell completions to stdout.
pub(crate) fn cmd_completions(shell: Shell) -> Result<()> {
    let mut cmd = Cli::command();
    clap_complete::generate(shell, &mut cmd, "tla2", &mut std::io::stdout());
    Ok(())
}
