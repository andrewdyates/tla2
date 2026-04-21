// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Interactive TLA+ state-space exploration.
//!
//! Two modes:
//!
//! 1. **REPL** (default) — terminal-based interactive explorer with commands:
//!    `init`, `step`, `pick`, `eval`, `inv`, `back`, `forward`, `trace`, `help`, `quit`.
//!
//! 2. **HTTP** — JSON API server (legacy, `--mode http`):
//!    `POST /explore/init`, `/explore/eval`, `/explore/successors`, `/explore/random-trace`.
//!
//! Part of #3795: Interactive symbolic exploration API.

mod http_server;
mod repl;

use std::path::Path;
use std::sync::Arc;

use anyhow::{bail, Context, Result};

/// Exploration mode — REPL (terminal) or HTTP (server).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ExploreMode {
    Repl,
    Http,
}

/// Run the explore command in the selected mode.
pub(crate) fn cmd_explore(
    file: &Path,
    config_path: Option<&Path>,
    port: u16,
    mode: ExploreMode,
    engine: tla_check::ServerExploreMode,
    max_symbolic_depth: usize,
    no_invariants: bool,
) -> Result<()> {
    let source = crate::read_source(file)?;
    let tree = crate::parse_or_report(file, &source)?;
    let result = tla_core::lower(tla_core::FileId(0), &tree);
    if !result.errors.is_empty() {
        bail!("TLA+ lowering failed with {} error(s)", result.errors.len());
    }
    let module = result
        .module
        .ok_or_else(|| anyhow::anyhow!("no module produced"))?;

    let config_path_buf = match config_path {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            cfg
        }
    };
    let config = if config_path_buf.exists() {
        let cfg_source = std::fs::read_to_string(&config_path_buf).context("read config file")?;
        tla_check::Config::parse(&cfg_source).map_err(|errors| {
            for err in &errors {
                eprintln!("{}:{}: {}", config_path_buf.display(), err.line(), err);
            }
            anyhow::anyhow!("config parse failed with {} error(s)", errors.len())
        })?
    } else {
        tla_check::Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        }
    };

    let module = Arc::new(module);

    match mode {
        ExploreMode::Repl => {
            repl::run_repl(module, config, engine, max_symbolic_depth, no_invariants)
        }
        ExploreMode::Http => {
            let mut server =
                tla_check::InteractiveServer::with_mode(module, config, engine, max_symbolic_depth);
            http_server::run_http_server(&mut server, port)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_explore_mode_variants() {
        assert_ne!(ExploreMode::Repl, ExploreMode::Http);
    }
}
