// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `TirProgram` construction and AST-vs-TIR comparison helpers.

use super::*;

impl TirParityState {
    /// Build a `TirProgram` for leaf-level TIR evaluation during enumeration.
    ///
    /// Part of #3194: the returned program is threaded through `EnumParams` so
    /// that leaf `eval` calls inside the successor enumerator can try TIR.
    ///
    /// Part of #3392: uses shared caches so lowered operators and expressions
    /// persist across states within this model-checking run.
    pub(in crate::check::model_checker) fn make_tir_program(&self) -> TirProgram<'_> {
        let dep_refs: Vec<&Module> = self.deps.iter().collect();
        let program =
            TirProgram::from_modules_with_cache(&self.root, &dep_refs, &self.shared_caches);
        // Part of #4251 Stream 5: attach the CONSTANT bindings to every
        // TirProgram built during this model-checking run. The flag
        // (`TLA2_PARTIAL_EVAL=1` / `--partial-eval`) decides whether the
        // substitution actually runs at preprocessing time.
        if let Some(env) = self.partial_eval_env.as_ref() {
            program.with_partial_eval_env(env.clone())
        } else {
            program
        }
    }

    fn selected_leaf_eval_program_name(
        &self,
        raw_name: &str,
        resolved_name: &str,
    ) -> Option<TirProgram<'_>> {
        if !self.is_eval_mode() || !self.matches_selected_name(raw_name, resolved_name) {
            return None;
        }

        Some(self.make_tir_program())
    }

    #[cfg(test)]
    fn selected_eval_program(&self, name: &str) -> Option<TirProgram<'_>> {
        if !self.is_eval_mode() || !self.is_selected(name) {
            return None;
        }

        let program = self.make_tir_program();
        // Part of #3350: removed named_op_requires_ast_fallback check.
        // Binding-form operators (FuncDef, SetFilter, SetBuilder) now attempt
        // TIR lowering like any other operator, with fallback driven by actual
        // lowering/eval outcomes. can_lower_operator still gates on lowering
        // capability.
        if !program.can_lower_operator(name) {
            return None;
        }
        Some(program)
    }

    fn selected_eval_program_name(
        &self,
        raw_name: &str,
        resolved_name: &str,
    ) -> Option<TirProgram<'_>> {
        if !self.is_eval_mode() || !self.matches_selected_name(raw_name, resolved_name) {
            return None;
        }

        let program = self.make_tir_program();
        if !program.can_lower_operator(resolved_name) {
            return None;
        }
        Some(program)
    }

    /// Build a `TirProgram` only when eval mode is active for the selected operator.
    ///
    /// Part of #3194: non-init call sites must key TIR leaf activation on the
    /// caller's resolved operator name rather than on hard-coded literals like
    /// `Next`.
    #[cfg(test)]
    pub(in crate::check::model_checker) fn make_tir_program_for_selected_eval(
        &self,
        name: &str,
    ) -> Option<TirProgram<'_>> {
        self.selected_eval_program(name)
            .map(|program| program.with_probe_label(name))
    }

    /// Build a `TirProgram` for selected leaf evaluation keyed by either the
    /// caller's raw config name or the resolved implementation name.
    ///
    /// Init/type extraction resolves config replacements before walking the
    /// body, so leaf-TIR selection must honor the same raw/resolved-name
    /// contract as successor evaluation.
    pub(in crate::check::model_checker) fn make_tir_program_for_selected_leaf_eval_name(
        &self,
        raw_name: &str,
        resolved_name: &str,
    ) -> Option<TirProgram<'_>> {
        let labels = if raw_name == resolved_name {
            vec![raw_name.to_string()]
        } else {
            vec![raw_name.to_string(), resolved_name.to_string()]
        };
        self.selected_leaf_eval_program_name(raw_name, resolved_name)
            .map(|program| program.with_probe_labels(labels))
    }

    pub(in crate::check::model_checker) fn make_tir_program_for_selected_eval_name(
        &self,
        raw_name: &str,
        resolved_name: &str,
    ) -> Option<TirProgram<'_>> {
        let labels = if raw_name == resolved_name {
            vec![raw_name.to_string()]
        } else {
            vec![raw_name.to_string(), resolved_name.to_string()]
        };
        self.selected_eval_program_name(raw_name, resolved_name)
            .map(|program| program.with_probe_labels(labels))
    }

    pub(in crate::check::model_checker) fn selected_named_op_uses_tir_eval_name(
        &self,
        raw_name: &str,
        resolved_name: &str,
    ) -> bool {
        self.selected_eval_program_name(raw_name, resolved_name)
            .is_some()
    }

    /// Evaluate a named operator via TIR only (no AST comparison).
    ///
    /// Part of #3392: uses `make_tir_program()` to share caches with other
    /// call sites instead of creating a fresh TirProgram.
    pub(in crate::check::model_checker) fn eval_named_op(
        &self,
        ctx: &EvalCtx,
        name: &str,
    ) -> EvalResult<Value> {
        let program = self.make_tir_program();
        program.eval_named_op(ctx, name)
    }

    pub(in crate::check::model_checker) fn assert_matches_ast(
        &self,
        ctx: &EvalCtx,
        name: &str,
    ) -> EvalResult<()> {
        if !self.is_selected(name) {
            return Ok(());
        }

        let ast = ctx.eval_op(name);
        let tir = self.eval_named_op(ctx, name);
        if eval_results_match(&ast, &tir) {
            return Ok(());
        }

        Err(EvalError::Internal {
            message: format!(
                "TLA2_TIR_PARITY mismatch for '{name}': AST={} TIR={}",
                format_eval_result(&ast),
                format_eval_result(&tir)
            ),
            span: None,
        })
    }
}

pub(in crate::check::model_checker) fn eval_results_match(
    left: &EvalResult<Value>,
    right: &EvalResult<Value>,
) -> bool {
    match (left, right) {
        (Ok(left), Ok(right)) => left == right,
        (Err(left), Err(right)) => format!("{left:?}") == format!("{right:?}"),
        _ => false,
    }
}

pub(in crate::check::model_checker) fn format_eval_result(result: &EvalResult<Value>) -> String {
    match result {
        Ok(value) => format!("Ok({value:?})"),
        Err(error) => format!("Err({error:?})"),
    }
}
