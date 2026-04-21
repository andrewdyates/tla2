// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared detection for env-gated TIR modes.
//!
//! The sequential checker supports TIR eval/parity today; the direct parallel
//! checker supports only the narrower next-only eval slice. Centralizing env
//! parsing keeps containment logic consistent across adaptive and direct
//! parallel entry points.

use tla_core::ast::Module;
use tla_eval::tir::{TirProgram, TirProgramCaches};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TirEvalSelection {
    select_all: bool,
    selected_ops: Vec<String>,
}

impl TirEvalSelection {
    /// Parse an explicit `TLA2_TIR_EVAL` env var. Returns `None` when the env
    /// var is unset or empty. Cached via `OnceLock` so the env var is read at
    /// most once per process (Part of #4114).
    fn from_env() -> Option<Self> {
        use std::sync::OnceLock;
        static CACHED: OnceLock<Option<TirEvalSelection>> = OnceLock::new();
        CACHED
            .get_or_init(|| {
                let raw = std::env::var("TLA2_TIR_EVAL").ok()?;
                let trimmed = raw.trim().to_string();
                if trimmed.eq_ignore_ascii_case("all") {
                    return Some(TirEvalSelection {
                        select_all: true,
                        selected_ops: Vec::new(),
                    });
                }

                let selected_ops = parse_selected_ops(&trimmed);
                if selected_ops.is_empty() {
                    return None;
                }

                Some(TirEvalSelection {
                    select_all: false,
                    selected_ops,
                })
            })
            .clone()
    }

    pub(crate) fn is_select_all(&self) -> bool {
        self.select_all
    }

    pub(crate) fn selected_ops(&self) -> &[String] {
        &self.selected_ops
    }

    fn selects_only_names(&self, raw_name: &str, resolved_name: &str) -> bool {
        !self.select_all
            && !self.selected_ops.is_empty()
            && self
                .selected_ops
                .iter()
                .all(|name| name == raw_name || name == resolved_name)
    }

    fn render(&self) -> String {
        if self.select_all {
            "all".to_string()
        } else {
            self.selected_ops.join(",")
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ParallelNextTirEvalSelection {
    raw_next_name: String,
    resolved_next_name: String,
}

impl ParallelNextTirEvalSelection {
    fn new(raw_next_name: &str, resolved_next_name: &str) -> Self {
        Self {
            raw_next_name: raw_next_name.to_string(),
            resolved_next_name: resolved_next_name.to_string(),
        }
    }

    /// Part of #3392: build a `TirProgram` with shared caches for per-worker
    /// cache persistence. Lowered operators and expressions accumulate across
    /// work items within the same worker thread.
    pub(crate) fn tir_program_with_cache<'a>(
        &self,
        root: &'a Module,
        deps: &'a [Module],
        caches: &'a TirProgramCaches,
    ) -> Option<TirProgram<'a>> {
        let dep_refs: Vec<&Module> = deps.iter().collect();
        let program = TirProgram::from_modules_with_cache(root, &dep_refs, caches);

        let labels = if self.raw_next_name == self.resolved_next_name {
            vec![self.raw_next_name.clone()]
        } else {
            vec![self.raw_next_name.clone(), self.resolved_next_name.clone()]
        };
        Some(program.with_probe_labels(labels))
    }
}

fn parse_selected_ops(raw: &str) -> Vec<String> {
    raw.split(',')
        .map(str::trim)
        .filter(|name| !name.is_empty())
        .map(ToOwned::to_owned)
        .collect()
}

/// Cache `env_has_selected_ops` per key using a static OnceLock per known key.
/// Part of #4114: avoid repeated env var syscalls.
fn env_has_selected_ops(key: &str) -> bool {
    use std::sync::OnceLock;

    fn check_env(key: &str) -> bool {
        std::env::var(key).ok().is_some_and(|raw| {
            let trimmed = raw.trim();
            trimmed.eq_ignore_ascii_case("all")
                || trimmed
                    .split(',')
                    .map(str::trim)
                    .any(|name| !name.is_empty())
        })
    }

    // Cache the two known callers with dedicated statics.
    static TIR_EVAL: OnceLock<bool> = OnceLock::new();
    static TIR_PARITY: OnceLock<bool> = OnceLock::new();

    match key {
        "TLA2_TIR_EVAL" => *TIR_EVAL.get_or_init(|| check_env(key)),
        "TLA2_TIR_PARITY" => *TIR_PARITY.get_or_init(|| check_env(key)),
        _ => check_env(key),
    }
}

/// Returns the explicit `TLA2_TIR_EVAL` selection (env-var only, no default).
/// Used by the parallel path gating which needs to distinguish explicit
/// requests from the sequential-default behavior.
pub(crate) fn tir_eval_selection() -> Option<TirEvalSelection> {
    TirEvalSelection::from_env()
}

/// Returns parsed `TLA2_TIR_PARITY` operator names, if set and non-empty.
/// Returns `None` when the env var is unset or empty.
/// Cached via `OnceLock` (Part of #4114).
pub(crate) fn tir_parity_ops() -> Option<Vec<String>> {
    use std::sync::OnceLock;
    static CACHED: OnceLock<Option<Vec<String>>> = OnceLock::new();
    CACHED
        .get_or_init(|| {
            let raw = std::env::var("TLA2_TIR_PARITY").ok()?;
            let ops = parse_selected_ops(raw.trim());
            if ops.is_empty() {
                None
            } else {
                Some(ops)
            }
        })
        .clone()
}

/// Returns true when the user has *explicitly* requested TIR eval via env var.
/// Does NOT return true for the default-on sequential TIR behavior (#3323).
pub(crate) fn tir_eval_requested() -> bool {
    env_has_selected_ops("TLA2_TIR_EVAL")
}

/// Returns true when the user has *explicitly* requested TIR parity via env var.
pub(crate) fn tir_parity_requested() -> bool {
    env_has_selected_ops("TLA2_TIR_PARITY")
}

/// Returns true when the user has *explicitly* requested any TIR mode via env
/// vars. Used by the adaptive checker to force sequential mode for explicit TIR
/// requests. Does NOT return true for the default-on sequential TIR (#3323),
/// so parallel mode is not affected by TIR becoming the default.
pub(crate) fn tir_mode_requested() -> bool {
    tir_eval_requested() || tir_parity_requested()
}

/// Returns true when `TIR_EVAL_STATS=1` is set, requesting runtime TIR
/// coverage measurement. Part of #3351 Phase 3.
/// Cached via `OnceLock` (Part of #4114).
pub(crate) fn tir_eval_stats_requested() -> bool {
    static CACHED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *CACHED.get_or_init(|| {
        std::env::var("TIR_EVAL_STATS")
            .ok()
            .is_some_and(|v| !v.trim().is_empty())
    })
}

pub(crate) fn parallel_direct_next_tir_eval_selection(
    raw_next_name: &str,
    resolved_next_name: &str,
) -> Result<Option<ParallelNextTirEvalSelection>, String> {
    if tir_parity_requested() {
        return Err(
            "ParallelChecker does not support TLA2_TIR_PARITY. \
             Use AdaptiveChecker or the sequential ModelChecker so TIR runs on the supported path."
                .to_string(),
        );
    }

    let Some(eval_selection) = tir_eval_selection() else {
        return Ok(None);
    };

    if !eval_selection.select_all
        && !eval_selection.selects_only_names(raw_next_name, resolved_next_name)
    {
        return Err(format!(
            "ParallelChecker only supports next-only TLA2_TIR_EVAL selecting {raw_next_name:?} \
             or {resolved_next_name:?} on the direct parallel path; requested TLA2_TIR_EVAL={}.",
            eval_selection.render()
        ));
    }

    Ok(Some(ParallelNextTirEvalSelection::new(
        raw_next_name,
        resolved_next_name,
    )))
}
