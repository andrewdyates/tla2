// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TIR mode/state selection and module cloning.

use super::*;

/// Mode for TIR integration with the model checker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::check::model_checker) enum TirMode {
    /// Shadow-check: evaluate both AST and TIR, assert results match.
    Parity,
    /// Primary: use TIR as the evaluator for selected operators.
    Eval,
}

pub(in crate::check::model_checker) struct TirParityState {
    pub(super) mode: TirMode,
    /// When true, all operators are selected (TLA2_TIR_EVAL=all).
    pub(super) select_all: bool,
    pub(super) selected_ops: FxHashSet<String>,
    pub(super) root: Module,
    pub(super) deps: Vec<Module>,
    /// Part of #3392: persistent caches shared across all `TirProgram` instances
    /// created during this model-checking run. Eliminates redundant TIR lowering
    /// per state.
    pub(super) shared_caches: TirProgramCaches,
    /// Part of #4251 Stream 5: `ConstantEnv` materialised from
    /// `EvalCtx::precomputed_constants()` once constants have been bound from
    /// the `.cfg` file. Attached to each `TirProgram` built via
    /// `make_tir_program` so that partial evaluation can substitute CONSTANT
    /// names with their concrete values when `TLA2_PARTIAL_EVAL=1` /
    /// `--partial-eval` is set. `None` until the model-checker setup finishes
    /// binding constants.
    pub(super) partial_eval_env: Option<tla_tir::analysis::ConstantEnv>,
}

impl TirParityState {
    /// Build the TIR state for the sequential model checker.
    ///
    /// Priority order (Part of #3354: legacy eval removed):
    /// 1. `TLA2_TIR_EVAL=<ops>|all` → Eval mode with explicit selection
    /// 2. `TLA2_TIR_PARITY=<ops>` → Parity mode
    /// 3. Default → Eval mode with select_all (Part of #3323)
    pub(in crate::check::model_checker) fn from_env(
        root: Module,
        deps: Vec<Module>,
    ) -> Option<Self> {
        use crate::tir_mode;

        // Explicit TLA2_TIR_EVAL takes priority. Env parsing is centralized
        // in tir_mode.rs to avoid duplication with the parallel path.
        if let Some(sel) = tir_mode::tir_eval_selection() {
            return Some(Self {
                mode: TirMode::Eval,
                select_all: sel.is_select_all(),
                selected_ops: sel.selected_ops().iter().cloned().collect(),
                root,
                deps,
                shared_caches: TirProgramCaches::new(),
                partial_eval_env: None,
            });
        }

        // TLA2_TIR_PARITY for shadow-check mode.
        if let Some(ops) = tir_mode::tir_parity_ops() {
            return Some(Self {
                mode: TirMode::Parity,
                select_all: false,
                selected_ops: ops.into_iter().collect(),
                root,
                deps,
                shared_caches: TirProgramCaches::new(),
                partial_eval_env: None,
            });
        }

        // Default: TIR eval=all for the sequential path. Part of #3323.
        Some(Self {
            mode: TirMode::Eval,
            select_all: true,
            selected_ops: FxHashSet::default(),
            root,
            deps,
            shared_caches: TirProgramCaches::new(),
            partial_eval_env: None,
        })
    }

    /// Set the `ConstantEnv` used for partial evaluation in downstream
    /// `TirProgram` builds. Called by the model-checker setup code after
    /// constants have been bound from the `.cfg` file and promoted to
    /// `precomputed_constants`. Part of #4251 Stream 5.
    pub(in crate::check::model_checker) fn set_partial_eval_env(
        &mut self,
        env: tla_tir::analysis::ConstantEnv,
    ) {
        self.partial_eval_env = Some(env);
    }

    pub(in crate::check::model_checker) fn is_selected(&self, name: &str) -> bool {
        self.select_all || self.selected_ops.contains(name)
    }

    pub(in crate::check::model_checker) fn is_eval_mode(&self) -> bool {
        self.mode == TirMode::Eval
    }

    pub(in crate::check::model_checker) fn is_parity_mode(&self) -> bool {
        self.mode == TirMode::Parity
    }

    pub(super) fn matches_selected_name(&self, raw_name: &str, resolved_name: &str) -> bool {
        self.is_selected(raw_name) || self.is_selected(resolved_name)
    }

    /// Clone the root module and dependencies for use in contexts where
    /// `TirProgram` must outlive the `&self` borrow (e.g., liveness checking
    /// where `&mut ModelChecker` is needed concurrently). Part of #3194.
    pub(in crate::check::model_checker) fn clone_modules(&self) -> (Module, Vec<Module>) {
        (self.root.clone(), self.deps.clone())
    }

    /// Clone modules only when eval mode is active for the selected operator.
    ///
    /// Part of #3194: liveness property evaluation should honor the same
    /// `selected_ops` gate used by invariant and `Next` evaluation. Without
    /// this, `TLA2_TIR_EVAL=TypeOK` would also turn on TIR for unrelated
    /// liveness properties.
    pub(in crate::check::model_checker) fn clone_modules_for_selected_eval(
        &self,
        name: &str,
    ) -> Option<(Module, Vec<Module>)> {
        if self.is_eval_mode() && self.is_selected(name) {
            Some(self.clone_modules())
        } else {
            None
        }
    }

    #[cfg(test)]
    pub(in crate::check) fn test_eval_selected<I, S>(
        root: Module,
        deps: Vec<Module>,
        selected_ops: I,
    ) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            mode: TirMode::Eval,
            select_all: false,
            selected_ops: selected_ops.into_iter().map(Into::into).collect(),
            root,
            deps,
            shared_caches: TirProgramCaches::new(),
            partial_eval_env: None,
        }
    }
}
