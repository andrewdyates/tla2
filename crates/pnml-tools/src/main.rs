// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;

use clap::Parser;

#[derive(Debug, Parser)]
#[command(
    name = "pnml-tools",
    about = "Compatibility wrapper for tla2's PNML/MCC engine"
)]
struct Cli {
    /// Model directory containing model.pnml (also reads BK_INPUT env var)
    model_dir: Option<PathBuf>,

    /// MCC examination name (also reads BK_EXAMINATION env var)
    #[arg(long)]
    examination: Option<String>,
    #[command(flatten)]
    args: pnml_tools::cli::PetriRunArgs,
}

/// Stack size for the worker thread. CTL/LTL model checking recurses through
/// both formula depth and state-space successors, which can overflow the
/// default 8 MB main-thread stack on deeply nested formulas (e.g.,
/// FunctionPointer-PT-b004 CTLFireability). 64 MB is generous enough for any
/// realistic MCC model.
const WORKER_STACK_SIZE: usize = 64 * 1024 * 1024;

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    // Spawn the real work on a thread with a larger stack to avoid stack
    // overflow in deeply recursive CTL/LTL evaluation and formula
    // simplification.
    let builder = std::thread::Builder::new()
        .name("pnml-main".into())
        .stack_size(WORKER_STACK_SIZE);
    let handle = builder.spawn(move || run(cli))?;
    handle.join().expect("worker thread panicked")
}

fn run(cli: Cli) -> anyhow::Result<()> {
    pnml_tools::cli::run_cli(
        pnml_tools::cli::PetriCommandMode::Mcc,
        cli.model_dir,
        cli.examination,
        cli.args,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cli_threads_default_to_one() {
        let cli = Cli::try_parse_from(["pnml-tools"]).expect("default args should parse");
        assert_eq!(cli.args.threads, 1);
    }

    #[test]
    fn cli_threads_accept_explicit_value() {
        let cli = Cli::try_parse_from(["pnml-tools", "--threads", "4"])
            .expect("--threads 4 should parse");
        assert_eq!(cli.args.threads, 4);
    }

    #[test]
    fn cli_threads_reject_zero() {
        let err = Cli::try_parse_from(["pnml-tools", "--threads", "0"])
            .expect_err("--threads 0 should be rejected");
        assert!(err.to_string().contains("--threads"));
        assert!(err.to_string().contains(">= 1"));
    }

    #[test]
    fn cli_storage_defaults_to_auto() {
        let cli = Cli::try_parse_from(["pnml-tools"]).expect("default args should parse");
        assert_eq!(
            cli.args.storage,
            pnml_tools::cli::RequestedStorageMode::Auto
        );
    }

    #[test]
    fn cli_checkpoint_resume_requires_dir() {
        let err = Cli::try_parse_from(["pnml-tools", "--resume-checkpoint"])
            .expect_err("--resume-checkpoint should require --checkpoint-dir");
        assert!(err.to_string().contains("--checkpoint-dir"));
    }

    #[test]
    fn cli_checkpoint_interval_rejects_zero() {
        let err = Cli::try_parse_from(["pnml-tools", "--checkpoint-interval-states", "0"])
            .expect_err("--checkpoint-interval-states 0 should be rejected");
        assert!(err.to_string().contains("--checkpoint-interval-states"));
        assert!(err.to_string().contains(">= 1"));
    }
}
