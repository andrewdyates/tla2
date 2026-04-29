// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Model checker setup: construction, configuration, and top-level entry points.
//!
//! Heavy implementation details are split into private submodules:
//! - `setup_imports`: import graph resolution and operator/variable collection
//! - `setup_build`: constructor assembly (`new_with_extends_impl`)
//! - `setup_config`: setter/getter configuration surface

#[path = "setup_build.rs"]
mod setup_build;
#[path = "setup_config.rs"]
pub(crate) mod setup_config;
#[path = "setup_imports.rs"]
pub(crate) mod setup_imports;

// Re-import parent module items so child modules can access them via `super::`.
use super::debug;
use super::module_set_validation;
use super::{
    Arc, CapacityStatus, CheckError, CheckResult, CheckStats, CheckpointState, CompiledSpec,
    CoverageState, DebugDiagnostics, Duration, ExplorationControl, Expr, FairnessConstraint,
    Fingerprint, FingerprintSet, FxHashMap, InitProgressCallback, LivenessCacheState, LivenessMode,
    ModelChecker, Module, ModuleState, OperatorDef, PathBuf, PeriodicLivenessState, PorState,
    ProgressCallback, RuntimeHooksState, Spanned, StateStorage, SymmetryState, TraceFile,
    TraceLocationsStorage, TraceState,
};
use crate::eval::stack_safe;
use crate::Config;
use tla_core::ast::Unit;

impl<'a> ModelChecker<'a> {
    const TRACE_DEGRADED_WARNING: &'static str =
        "WARNING: Counterexample trace may be incomplete due to I/O errors during model checking.";

    /// Create a new model checker
    pub fn new(module: &'a Module, config: &'a Config) -> Self {
        Self::new_with_extends(module, &[], config)
    }

    /// Create a new model checker with additional loaded modules.
    ///
    /// Despite the historical name, `extended_modules` is **not** "EXTENDS-only".
    /// It must be a *loaded-module superset* for the whole run:
    ///
    /// - Include every non-stdlib module that may be referenced, via `EXTENDS` or `INSTANCE`
    ///   (including transitive and nested instance dependencies).
    /// - Put the modules that contribute to the **unqualified** operator namespace first, in a
    ///   TLC-shaped deterministic order (the `EXTENDS` closure and standalone `INSTANCE` imports).
    ///   Remaining loaded modules may follow in any deterministic order.
    ///
    /// Missing referenced non-stdlib modules are treated as a setup error.
    pub fn new_with_extends(
        module: &'a Module,
        extended_modules: &[&Module],
        config: &'a Config,
    ) -> Self {
        // Part of #758: module loading and stdlib/operator expansion can recurse deeply on some
        // specs. Guard construction so callers don't need a special thread stack size.
        stack_safe(|| Self::new_with_extends_impl(module, extended_modules, config))
    }

    /// Provide a source path for a given FileId to enable TLC-style line/col location rendering.
    ///
    /// If a path is not registered (or cannot be read), location rendering falls back to byte
    /// offsets (e.g., "bytes 0-0 of module M").
    pub fn register_file_path(&mut self, file_id: tla_core::FileId, path: std::path::PathBuf) {
        // Keep IO builtins (JsonDeserialize/ndJsonDeserialize) spec-relative.
        // We anchor to the root module's directory when available.
        if let Some(module_name) = self.module.file_id_to_name.get(&file_id) {
            if module_name == &self.module.root_name {
                self.ctx
                    .set_input_base_dir(path.parent().map(std::path::Path::to_path_buf));
            }
        }
        self.module.file_id_to_path.entry(file_id).or_insert(path);
    }

    /// Run the model checker
    pub fn check(&mut self) -> CheckResult {
        if let Some(result) =
            crate::check::runtime_config_validation_result(self.config, &self.stats)
        {
            return result;
        }
        let _model_check_run_guard = crate::intern::ModelCheckRunGuard::begin();
        let _subset_profile_guard = crate::enumerate::subset_profile::RunGuard::begin();
        crate::guard_error_stats::reset();
        // Part of #3351: enable TIR eval probe when TIR_EVAL_STATS=1 is set.
        let tir_stats = crate::tir_mode::tir_eval_stats_requested();
        if tir_stats {
            tla_eval::tir::enable_tir_eval_probe();
        }
        // Part of #758: Some evaluation/expansion paths can recurse deeply enough to overflow
        // constrained per-thread stacks (tests, embedded callers, small worker stacks). Guard the
        // top-level run to avoid a hard-abort stack overflow.
        let result = stack_safe(|| self.check_impl())
            .with_suppressed_guard_errors(crate::guard_error_stats::take_and_reset());
        self.emit_terminal_warnings();
        if tir_stats {
            Self::emit_tir_eval_stats();
        }
        result
    }

    /// Print TIR eval coverage stats to stderr. Part of #3351 Phase 3.
    fn emit_tir_eval_stats() {
        use std::io::Write as _;
        let snapshot = tla_eval::tir::tir_eval_probe_snapshot();
        if snapshot.is_empty() {
            let _ = writeln!(
                std::io::stderr().lock(),
                "[TIR_EVAL_STATS] No operators evaluated."
            );
            return;
        }
        let mut total_named = 0usize;
        let mut total_expr = 0usize;
        let _ = writeln!(
            std::io::stderr().lock(),
            "[TIR_EVAL_STATS] Operator coverage:"
        );
        for (name, counts) in &snapshot {
            let _ = writeln!(
                std::io::stderr().lock(),
                "  {name}: named_op_evals={}, expr_evals={} ({})",
                counts.named_op_evals,
                counts.expr_evals,
                if counts.expr_evals > 0 {
                    "TIR"
                } else {
                    "AST fallback"
                },
            );
            total_named += counts.named_op_evals;
            total_expr += counts.expr_evals;
        }
        let tir_ops = snapshot.values().filter(|c| c.expr_evals > 0).count();
        let ast_ops = snapshot.values().filter(|c| c.expr_evals == 0).count();
        let pct = if !snapshot.is_empty() {
            tir_ops as f64 / snapshot.len() as f64 * 100.0
        } else {
            0.0
        };
        let _ = writeln!(
            std::io::stderr().lock(),
            "[TIR_EVAL_STATS] Summary: {tir_ops}/{} operators via TIR ({pct:.1}%), \
             {ast_ops} AST fallback. Total evals: named={total_named}, expr={total_expr}.",
            snapshot.len(),
        );
    }

    pub(in crate::check::model_checker) fn emit_terminal_warnings(&self) {
        if self.trace.trace_degraded {
            use std::io::Write as _;

            let _ = writeln!(std::io::stderr().lock(), "{}", Self::TRACE_DEGRADED_WARNING);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    fn simple_checker() -> (Module, Config) {
        let src = r#"
---- MODULE SetupPathTest ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
        let tree = parse_to_syntax_tree(src);
        let lowered = lower(FileId(0), &tree);
        let module = lowered.module.expect("lowered module");
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };
        (module, config)
    }

    #[test]
    fn register_file_path_sets_eval_input_base_dir_for_root_module() {
        let (module, config) = simple_checker();
        let mut checker = ModelChecker::new(&module, &config);

        let spec_path = std::path::PathBuf::from("/tmp/setup-path-test/Spec.tla");
        checker.register_file_path(FileId(0), spec_path.clone());

        assert_eq!(
            checker.ctx.input_base_dir(),
            spec_path.parent().map(std::path::Path::to_path_buf)
        );
    }

    #[test]
    fn set_checkpoint_paths_sets_eval_input_base_dir() {
        let (module, config) = simple_checker();
        let mut checker = ModelChecker::new(&module, &config);

        checker.set_checkpoint_paths(Some("/tmp/setup-path-test/Spec.tla".to_string()), None);

        assert_eq!(
            checker.ctx.input_base_dir(),
            Some(std::path::PathBuf::from("/tmp/setup-path-test"))
        );
    }

    #[test]
    fn set_checkpoint_accepts_duration() {
        let (module, config) = simple_checker();
        let mut checker = ModelChecker::new(&module, &config);
        let checkpoint_dir = std::path::PathBuf::from("/tmp/setup-path-test/checkpoint");
        let interval = Duration::from_secs(42);

        checker.set_checkpoint(checkpoint_dir.clone(), interval);

        assert_eq!(checker.checkpoint.dir, Some(checkpoint_dir));
        assert_eq!(checker.checkpoint.interval, interval);
    }
}
