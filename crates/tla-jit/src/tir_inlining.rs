// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TIR-level preprocessing passes for the JIT pipeline.
//!
//! The JIT eligibility gate rejects functions containing `Call` opcodes
//! (see [`crate::bytecode_lower::eligibility`]). Many of these `Call`s
//! originate from small user-defined operators that are simple enough to
//! inline at the TIR level *before* bytecode lowering. After inlining,
//! the operator body no longer contains `Apply` nodes for those callees,
//! so bytecode compilation produces no `Call` opcodes and the function
//! passes the eligibility gate.
//!
//! After inlining, constant propagation folds compile-time-computable
//! subtrees (e.g. `3 + 4` -> `7`) so that bytecode lowering emits
//! `LoadConst` instead of arithmetic opcodes, reducing the work the
//! JIT backend must compile and execute.
//!
//! Pipeline: TIR -> inline -> const_prop -> bytecode -> JIT
//!
//! This module wires [`tla_tir::analysis::inlining::inline_functions`]
//! and [`tla_tir::analysis::const_prop::const_prop_expr`] into the JIT
//! compilation pipeline via [`preprocess_tir_for_jit`].
//!
//! Part of #3909.

use tla_tir::analysis::const_prop::ConstPropStats;
use tla_tir::analysis::inlining::InliningStats;
use tla_tir::analysis::preprocess::{preprocess_tir, PreprocessProfile, PreprocessResult};
use tla_tir::bytecode::{BytecodeCompiler, CompileError};
use tla_tir::TirModule;

/// Combined statistics from all TIR preprocessing passes.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PreprocessStats {
    /// Statistics from the inlining pass.
    pub inlining: InliningStats,
    /// Aggregated statistics from constant propagation across all operators.
    pub const_prop: ConstPropStats,
}

impl From<PreprocessResult> for PreprocessStats {
    fn from(result: PreprocessResult) -> Self {
        Self {
            inlining: result.inlining,
            const_prop: result.const_prop,
        }
    }
}

/// JIT-specific preprocessing configuration.
///
/// Controls both inlining and constant propagation passes that run
/// on the TIR before bytecode lowering.
///
/// The JIT uses a slightly higher default `max_inline_size` than the
/// generic inlining pass because eliminating even moderately-sized
/// operators is worthwhile when the alternative is falling back to
/// the interpreter for the entire function.
#[derive(Debug, Clone)]
pub struct JitPreprocessConfig {
    /// Maximum number of TIR expression nodes in a function body for it
    /// to be considered an inline candidate.
    pub max_inline_size: usize,

    /// Whether TIR inlining is enabled. When `false`, the inlining step
    /// in [`preprocess_tir_for_jit`] is skipped.
    pub inlining_enabled: bool,

    /// Whether constant propagation is enabled. When `false`, the const
    /// prop step in [`preprocess_tir_for_jit`] is skipped.
    pub const_prop_enabled: bool,
}

impl Default for JitPreprocessConfig {
    fn default() -> Self {
        Self {
            max_inline_size: 30,
            inlining_enabled: true,
            const_prop_enabled: true,
        }
    }
}

impl JitPreprocessConfig {
    /// Create a configuration from environment variables, falling back to defaults.
    ///
    /// - `TLA2_JIT_INLINE_MAX_SIZE` -> max_inline_size (default: 30)
    /// - `TLA2_JIT_INLINE_ENABLED` -> inlining_enabled (default: true, set "0" to disable)
    /// - `TLA2_JIT_CONST_PROP_ENABLED` -> const_prop_enabled (default: true, set "0" to disable)
    pub fn from_env() -> Self {
        let max_inline_size = std::env::var("TLA2_JIT_INLINE_MAX_SIZE")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(30);
        let inlining_enabled = std::env::var("TLA2_JIT_INLINE_ENABLED")
            .map(|s| s != "0")
            .unwrap_or(true);
        let const_prop_enabled = std::env::var("TLA2_JIT_CONST_PROP_ENABLED")
            .map(|s| s != "0")
            .unwrap_or(true);
        Self {
            max_inline_size,
            inlining_enabled,
            const_prop_enabled,
        }
    }

    /// Convert to a [`PreprocessProfile`] for the shared TIR pipeline.
    ///
    /// If the config matches the JIT defaults, returns `PreprocessProfile::Jit`.
    /// Otherwise, returns `PreprocessProfile::Custom` with the specified
    /// thresholds.
    fn to_profile(&self) -> PreprocessProfile {
        let defaults = Self::default();
        if self.max_inline_size == defaults.max_inline_size
            && self.inlining_enabled == defaults.inlining_enabled
            && self.const_prop_enabled == defaults.const_prop_enabled
        {
            PreprocessProfile::Jit
        } else {
            PreprocessProfile::Custom {
                max_inline_size: self.max_inline_size,
                inlining_enabled: self.inlining_enabled,
                const_prop_enabled: self.const_prop_enabled,
            }
        }
    }
}

/// Backward-compatible alias for [`JitPreprocessConfig`].
///
/// Existing callers that use `JitInliningConfig` continue to work.
/// New code should prefer `JitPreprocessConfig`.
pub type JitInliningConfig = JitPreprocessConfig;

/// Pre-process a [`TirModule`] by running the inlining pass followed by
/// constant propagation on each operator body.
///
/// This is the main entry point for integrating TIR optimization passes
/// into the JIT pipeline. Delegates to the shared
/// [`tla_tir::analysis::preprocess::preprocess_tir`] pipeline with
/// JIT-appropriate configuration.
///
/// Pipeline order: **inline** (inter-procedural) -> **const_prop** (per-operator).
/// Const prop runs after inlining so that expressions exposed by inlining
/// (e.g. `Double(5)` inlined to `5 + 5`) are also folded.
///
/// # Arguments
///
/// * `module` - The TIR module to optimize. Modified in place.
/// * `config` - Preprocessing configuration controlling which passes run
///   and their thresholds.
///
/// # Returns
///
/// Combined statistics from both passes.
pub fn preprocess_tir_for_jit(
    module: &mut TirModule,
    config: &JitPreprocessConfig,
) -> PreprocessStats {
    let profile = config.to_profile();
    let result = preprocess_tir(module, &profile);
    PreprocessStats::from(result)
}

/// Convenience: preprocess a TIR module (inline + const_prop) and compile
/// all zero-arity operators to a [`tla_tir::bytecode::BytecodeChunk`],
/// returning both the chunk and preprocessing statistics.
///
/// This combines [`preprocess_tir_for_jit`] with bytecode compilation
/// in a single call for callers that want the full pipeline.
///
/// Only zero-arity operators are compiled to bytecode. Parameterized
/// operators serve as inline candidates only and are not compiled
/// separately (their bodies have already been inlined into callers).
pub fn inline_and_compile(
    module: &mut TirModule,
    config: &JitPreprocessConfig,
) -> Result<(tla_tir::bytecode::BytecodeChunk, PreprocessStats), CompileError> {
    let stats = preprocess_tir_for_jit(module, config);

    let mut compiler = BytecodeCompiler::new();
    // First pass: compile parameterized operators so they appear in
    // op_indices for any un-inlined calls.  These may fail (parameter
    // names are unresolved), which is fine -- failures just mean the
    // callee won't be available for bytecode-level Call resolution.
    for op in &module.operators {
        if !op.params.is_empty() {
            let _ = compiler.compile_operator(op);
        }
    }
    // Second pass: compile zero-arity operators (invariants, actions).
    for op in &module.operators {
        if op.params.is_empty() {
            compiler.compile_operator(op)?;
        }
    }

    Ok((compiler.finish(), stats))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bytecode_lower::check_eligibility;
    use tla_core::intern_name;
    use tla_core::span::{FileId, Span};
    use tla_core::Spanned;
    use tla_tir::bytecode::BytecodeCompiler;
    use tla_tir::nodes::*;
    use tla_tir::types::TirType;
    use tla_tir::{TirModule, TirOperator};
    use tla_value::Value;

    fn span() -> Span {
        Span::new(FileId(0), 0, 0)
    }

    fn spanned(expr: TirExpr) -> Spanned<TirExpr> {
        Spanned::new(expr, span())
    }

    fn int_const(n: i64) -> Spanned<TirExpr> {
        spanned(TirExpr::Const {
            value: Value::int(n),
            ty: TirType::Int,
        })
    }

    fn bool_const(b: bool) -> Spanned<TirExpr> {
        spanned(TirExpr::Const {
            value: Value::bool(b),
            ty: TirType::Bool,
        })
    }

    fn name_ident(name: &str) -> Spanned<TirExpr> {
        spanned(TirExpr::Name(TirNameRef {
            name: name.to_string(),
            name_id: intern_name(name),
            kind: TirNameKind::Ident,
            ty: TirType::Dyn,
        }))
    }

    fn name_state_var(name: &str, index: u16) -> Spanned<TirExpr> {
        spanned(TirExpr::Name(TirNameRef {
            name: name.to_string(),
            name_id: intern_name(name),
            kind: TirNameKind::StateVar { index },
            ty: TirType::Int,
        }))
    }

    fn make_operator(name: &str, params: Vec<&str>, body: Spanned<TirExpr>) -> TirOperator {
        TirOperator {
            name: name.to_string(),
            name_id: intern_name(name),
            params: params.into_iter().map(String::from).collect(),
            is_recursive: false,
            body,
        }
    }

    /// Find a bytecode function by operator name in a chunk.
    fn find_function<'a>(
        chunk: &'a tla_tir::bytecode::BytecodeChunk,
        name: &str,
    ) -> &'a tla_tir::bytecode::BytecodeFunction {
        for i in 0..chunk.function_count() {
            let f = chunk.get_function(i as u16);
            if f.name == name {
                return f;
            }
        }
        panic!("function '{}' not found in chunk", name);
    }

    /// Compile a module using the two-pass strategy: parameterized operators
    /// first (best-effort, ignoring failures), then zero-arity operators.
    ///
    /// This mirrors what `inline_and_compile` does internally and avoids
    /// the "unresolved identifier" errors that occur when compiling
    /// parameterized operators whose parameter names are not in scope.
    fn compile_callers_only(module: &TirModule) -> tla_tir::bytecode::BytecodeChunk {
        let mut compiler = BytecodeCompiler::new();
        for op in &module.operators {
            if !op.params.is_empty() {
                let _ = compiler.compile_operator(op);
            }
        }
        for op in &module.operators {
            if op.params.is_empty() {
                compiler
                    .compile_operator(op)
                    .expect("zero-arity compile failed");
            }
        }
        compiler.finish()
    }

    // =========================================================
    // Inlining tests (preserved from original)
    // =========================================================

    /// Verify that a function calling a small operator becomes JIT-eligible
    /// after TIR inlining eliminates the Apply node.
    ///
    /// Setup:
    ///   Double(x) == x + x       (small leaf, inlineable)
    ///   Main == Double(5)         (contains Apply -> Call -> ineligible)
    ///
    /// After inlining: Main == 5 + 5 (no Apply -> no Call -> eligible)
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tir_inlining_makes_call_eligible() {
        let double = make_operator(
            "Double",
            vec!["x"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("x")),
                op: TirArithOp::Add,
                right: Box::new(name_ident("x")),
            }),
        );

        let main = TirOperator {
            name: "Main".to_string(),
            name_id: intern_name("Main"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("Double")),
                args: vec![int_const(5)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![double, main],
        };

        // Before inlining: Main's TIR body is an Apply node.
        assert!(
            matches!(&module.operators[1].body.node, TirExpr::Apply { .. }),
            "Main should have an Apply node before inlining"
        );

        // Run TIR preprocessing.
        let config = JitPreprocessConfig::default();
        let stats = preprocess_tir_for_jit(&mut module, &config);
        assert_eq!(
            stats.inlining.functions_inlined, 1,
            "Double should be inlined"
        );
        assert_eq!(
            stats.inlining.call_sites_replaced, 1,
            "one call site replaced"
        );

        // After inlining: Main's body should no longer be an Apply.
        assert!(
            !matches!(&module.operators[1].body.node, TirExpr::Apply { .. }),
            "Main should NOT have an Apply node after inlining"
        );

        // Compile AFTER preprocessing -- Main should now be JIT-eligible.
        {
            let chunk = compile_callers_only(&module);
            let main_func = find_function(&chunk, "Main");
            let elig = check_eligibility(main_func);
            assert!(
                elig.is_ok(),
                "Main should be eligible after inlining: {:?}",
                elig.unwrap_err()
            );
        }
    }

    /// Verify that the convenience `inline_and_compile` function produces
    /// eligible bytecode.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inline_and_compile_convenience() {
        let double = make_operator(
            "Double2",
            vec!["x"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("x")),
                op: TirArithOp::Add,
                right: Box::new(name_ident("x")),
            }),
        );

        let main = TirOperator {
            name: "Main2".to_string(),
            name_id: intern_name("Main2"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("Double2")),
                args: vec![int_const(10)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![double, main],
        };

        let config = JitPreprocessConfig::default();
        let (chunk, stats) = inline_and_compile(&mut module, &config).expect("compile failed");

        assert_eq!(stats.inlining.call_sites_replaced, 1);
        let main_func = find_function(&chunk, "Main2");
        assert!(
            check_eligibility(main_func).is_ok(),
            "Main2 should be eligible after inline_and_compile"
        );
    }

    /// Verify that disabling inlining preserves Call opcodes.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inlining_disabled_preserves_calls() {
        let double = make_operator(
            "Double3",
            vec!["x"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("x")),
                op: TirArithOp::Add,
                right: Box::new(name_ident("x")),
            }),
        );

        let main = TirOperator {
            name: "Main3".to_string(),
            name_id: intern_name("Main3"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("Double3")),
                args: vec![int_const(7)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![double, main],
        };

        let config = JitPreprocessConfig {
            inlining_enabled: false,
            ..Default::default()
        };

        // With inlining disabled, the inlining step is a no-op.
        let stats = preprocess_tir_for_jit(&mut module, &config);
        assert_eq!(
            stats.inlining.call_sites_replaced, 0,
            "no inlining should occur"
        );
        assert_eq!(
            stats.inlining.functions_inlined, 0,
            "no functions should be inlined"
        );

        // Main3's body should still be an Apply (un-inlined call).
        assert!(
            matches!(&module.operators[1].body.node, TirExpr::Apply { .. }),
            "Main3 should still have an Apply node when inlining is disabled"
        );
    }

    /// Verify that `max_inline_size` threshold controls which operators get inlined.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_max_inline_size_threshold() {
        let double = make_operator(
            "Double4",
            vec!["x"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("x")),
                op: TirArithOp::Add,
                right: Box::new(name_ident("x")),
            }),
        );

        let main = TirOperator {
            name: "Main4".to_string(),
            name_id: intern_name("Main4"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("Double4")),
                args: vec![int_const(1)],
            }),
        };

        // Use a threshold of 2 -- Double4's body has 3 nodes, so it should
        // NOT be inlined.
        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![double, main],
        };

        let config = JitPreprocessConfig {
            max_inline_size: 2,
            inlining_enabled: true,
            const_prop_enabled: true,
        };

        let stats = preprocess_tir_for_jit(&mut module, &config);
        assert_eq!(
            stats.inlining.call_sites_replaced, 0,
            "Double4 body (3 nodes) should exceed threshold of 2"
        );
    }

    /// Verify that a multi-param operator inlines correctly and the
    /// resulting bytecode is eligible.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_tir_inlining_multi_param_eligible() {
        let add = make_operator(
            "Add",
            vec!["a", "b"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("a")),
                op: TirArithOp::Add,
                right: Box::new(name_ident("b")),
            }),
        );

        let main = TirOperator {
            name: "MainAdd".to_string(),
            name_id: intern_name("MainAdd"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("Add")),
                args: vec![int_const(3), int_const(4)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![add, main],
        };

        let config = JitPreprocessConfig::default();
        let (chunk, stats) = inline_and_compile(&mut module, &config).expect("compile failed");

        assert_eq!(stats.inlining.call_sites_replaced, 1);
        let main_func = find_function(&chunk, "MainAdd");
        assert!(
            check_eligibility(main_func).is_ok(),
            "MainAdd should be eligible after inlining: {:?}",
            check_eligibility(main_func).unwrap_err()
        );
    }

    /// Verify the default JitPreprocessConfig values.
    #[test]
    fn test_jit_preprocess_config_defaults() {
        let config = JitPreprocessConfig::default();
        assert_eq!(config.max_inline_size, 30);
        assert!(config.inlining_enabled);
        assert!(config.const_prop_enabled);
    }

    /// Verify that recursive operators are never inlined.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_recursive_not_inlined() {
        let mut fib = make_operator(
            "Fib",
            vec!["n"],
            spanned(TirExpr::Apply {
                op: Box::new(name_ident("Fib")),
                args: vec![name_ident("n")],
            }),
        );
        fib.is_recursive = true;

        let main = TirOperator {
            name: "MainFib".to_string(),
            name_id: intern_name("MainFib"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("Fib")),
                args: vec![int_const(10)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![fib, main],
        };

        let config = JitPreprocessConfig::default();
        let stats = preprocess_tir_for_jit(&mut module, &config);
        assert_eq!(
            stats.inlining.call_sites_replaced, 0,
            "recursive ops must not be inlined"
        );
    }

    // =========================================================
    // Constant propagation tests
    // =========================================================

    /// Verify that constant arithmetic expressions are folded during
    /// preprocessing. A zero-arity operator with body `3 + 4` should
    /// be reduced to `7` (a single Const node).
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_const_prop_folds_arithmetic() {
        let main = make_operator(
            "ConstArith",
            vec![],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(int_const(3)),
                op: TirArithOp::Add,
                right: Box::new(int_const(4)),
            }),
        );

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![main],
        };

        let config = JitPreprocessConfig::default();
        let stats = preprocess_tir_for_jit(&mut module, &config);

        // The body should now be a single Const(7).
        match &module.operators[0].body.node {
            TirExpr::Const {
                value,
                ty: TirType::Int,
            } => {
                assert_eq!(value.as_i64(), Some(7), "3 + 4 should fold to 7");
            }
            other => panic!("expected Const(7), got: {other:?}"),
        }
        assert_eq!(stats.const_prop.arith_folds, 1, "one arith fold expected");
    }

    /// Verify that nested constant expressions fold completely.
    /// `(2 * 3) + (10 - 6)` -> `6 + 4` -> `10`.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_const_prop_folds_nested_arithmetic() {
        let main = make_operator(
            "NestedArith",
            vec![],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::ArithBinOp {
                    left: Box::new(int_const(2)),
                    op: TirArithOp::Mul,
                    right: Box::new(int_const(3)),
                })),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::ArithBinOp {
                    left: Box::new(int_const(10)),
                    op: TirArithOp::Sub,
                    right: Box::new(int_const(6)),
                })),
            }),
        );

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![main],
        };

        let config = JitPreprocessConfig::default();
        let stats = preprocess_tir_for_jit(&mut module, &config);

        match &module.operators[0].body.node {
            TirExpr::Const {
                value,
                ty: TirType::Int,
            } => {
                assert_eq!(value.as_i64(), Some(10), "(2*3) + (10-6) should fold to 10");
            }
            other => panic!("expected Const(10), got: {other:?}"),
        }
        assert_eq!(
            stats.const_prop.arith_folds, 3,
            "three arith folds expected"
        );
    }

    /// Verify that boolean constant expressions are folded.
    /// `TRUE /\ FALSE` -> `FALSE`.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_const_prop_folds_boolean() {
        let main = make_operator(
            "ConstBool",
            vec![],
            spanned(TirExpr::BoolBinOp {
                left: Box::new(bool_const(true)),
                op: TirBoolOp::And,
                right: Box::new(bool_const(false)),
            }),
        );

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![main],
        };

        let config = JitPreprocessConfig::default();
        let stats = preprocess_tir_for_jit(&mut module, &config);

        match &module.operators[0].body.node {
            TirExpr::Const {
                value,
                ty: TirType::Bool,
            } => {
                assert_eq!(
                    value.as_bool(),
                    Some(false),
                    "TRUE /\\ FALSE should fold to FALSE"
                );
            }
            other => panic!("expected Const(false), got: {other:?}"),
        }
        assert_eq!(stats.const_prop.bool_folds, 1, "one bool fold expected");
    }

    /// Verify that constant comparison expressions are folded.
    /// `3 < 5` -> `TRUE`.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_const_prop_folds_comparison() {
        let main = make_operator(
            "ConstCmp",
            vec![],
            spanned(TirExpr::Cmp {
                left: Box::new(int_const(3)),
                op: TirCmpOp::Lt,
                right: Box::new(int_const(5)),
            }),
        );

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![main],
        };

        let config = JitPreprocessConfig::default();
        let stats = preprocess_tir_for_jit(&mut module, &config);

        match &module.operators[0].body.node {
            TirExpr::Const {
                value,
                ty: TirType::Bool,
            } => {
                assert_eq!(value.as_bool(), Some(true), "3 < 5 should fold to TRUE");
            }
            other => panic!("expected Const(true), got: {other:?}"),
        }
        assert_eq!(stats.const_prop.cmp_folds, 1, "one cmp fold expected");
    }

    /// Verify that IF/THEN/ELSE with a constant condition is simplified.
    /// `IF TRUE THEN 42 ELSE 0` -> `42`.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_const_prop_simplifies_if() {
        let main = make_operator(
            "ConstIf",
            vec![],
            spanned(TirExpr::If {
                cond: Box::new(bool_const(true)),
                then_: Box::new(int_const(42)),
                else_: Box::new(int_const(0)),
            }),
        );

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![main],
        };

        let config = JitPreprocessConfig::default();
        let stats = preprocess_tir_for_jit(&mut module, &config);

        match &module.operators[0].body.node {
            TirExpr::Const {
                value,
                ty: TirType::Int,
            } => {
                assert_eq!(
                    value.as_i64(),
                    Some(42),
                    "IF TRUE THEN 42 ELSE 0 should fold to 42"
                );
            }
            other => panic!("expected Const(42), got: {other:?}"),
        }
        assert_eq!(
            stats.const_prop.if_simplifications, 1,
            "one if simplification expected"
        );
    }

    /// Verify that IF with a foldable condition chains correctly.
    /// `IF 3 < 5 THEN 10 + 20 ELSE 0` -> `30`.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_const_prop_cascading_if_and_arith() {
        let main = make_operator(
            "CascadeIf",
            vec![],
            spanned(TirExpr::If {
                cond: Box::new(spanned(TirExpr::Cmp {
                    left: Box::new(int_const(3)),
                    op: TirCmpOp::Lt,
                    right: Box::new(int_const(5)),
                })),
                then_: Box::new(spanned(TirExpr::ArithBinOp {
                    left: Box::new(int_const(10)),
                    op: TirArithOp::Add,
                    right: Box::new(int_const(20)),
                })),
                else_: Box::new(int_const(0)),
            }),
        );

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![main],
        };

        let config = JitPreprocessConfig::default();
        let stats = preprocess_tir_for_jit(&mut module, &config);

        match &module.operators[0].body.node {
            TirExpr::Const {
                value,
                ty: TirType::Int,
            } => {
                assert_eq!(value.as_i64(), Some(30), "IF 3<5 THEN 10+20 ELSE 0 -> 30");
            }
            other => panic!("expected Const(30), got: {other:?}"),
        }
        assert_eq!(stats.const_prop.cmp_folds, 1);
        assert_eq!(stats.const_prop.arith_folds, 1); // only then-branch (10+20) is an ArithBinOp; else is already int_const(0)
        assert_eq!(stats.const_prop.if_simplifications, 1);
    }

    /// Verify that disabling const_prop leaves constant expressions un-folded.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_const_prop_disabled_preserves_expressions() {
        let main = make_operator(
            "NoFold",
            vec![],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(int_const(3)),
                op: TirArithOp::Add,
                right: Box::new(int_const(4)),
            }),
        );

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![main],
        };

        let config = JitPreprocessConfig {
            const_prop_enabled: false,
            ..Default::default()
        };
        let stats = preprocess_tir_for_jit(&mut module, &config);

        // Body should remain an ArithBinOp, not a folded Const.
        assert!(
            matches!(&module.operators[0].body.node, TirExpr::ArithBinOp { .. }),
            "body should remain ArithBinOp when const_prop is disabled"
        );
        assert_eq!(stats.const_prop, ConstPropStats::default());
    }

    /// Verify that expressions with state variables are NOT folded
    /// (only the constant sub-parts are folded where possible).
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_const_prop_preserves_state_vars() {
        // `x + (3 + 4)` -> `x + 7`  (inner folds, outer does not)
        let main = make_operator(
            "MixedExpr",
            vec![],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_state_var("x", 0)),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::ArithBinOp {
                    left: Box::new(int_const(3)),
                    op: TirArithOp::Add,
                    right: Box::new(int_const(4)),
                })),
            }),
        );

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![main],
        };

        let config = JitPreprocessConfig::default();
        let stats = preprocess_tir_for_jit(&mut module, &config);

        // Outer should still be ArithBinOp (x + 7).
        match &module.operators[0].body.node {
            TirExpr::ArithBinOp { left, right, .. } => {
                // Left is a state var, unchanged.
                assert!(
                    matches!(&left.node, TirExpr::Name(_)),
                    "left should be state var"
                );
                // Right should be folded to 7.
                match &right.node {
                    TirExpr::Const {
                        value,
                        ty: TirType::Int,
                    } => {
                        assert_eq!(value.as_i64(), Some(7), "3+4 sub-expr should fold to 7");
                    }
                    other => panic!("expected Const(7) for right, got: {other:?}"),
                }
            }
            other => panic!("expected ArithBinOp, got: {other:?}"),
        }
        assert_eq!(stats.const_prop.arith_folds, 1, "inner 3+4 should fold");
    }

    /// Verify that const prop aggregates stats across multiple operators.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_const_prop_aggregates_stats_across_operators() {
        let op1 = make_operator(
            "Op1",
            vec![],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(int_const(1)),
                op: TirArithOp::Add,
                right: Box::new(int_const(2)),
            }),
        );
        let op2 = make_operator(
            "Op2",
            vec![],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(int_const(10)),
                op: TirArithOp::Mul,
                right: Box::new(int_const(20)),
            }),
        );

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![op1, op2],
        };

        let config = JitPreprocessConfig::default();
        let stats = preprocess_tir_for_jit(&mut module, &config);

        assert_eq!(
            stats.const_prop.arith_folds, 2,
            "one fold per operator, two total"
        );
    }

    /// Verify that inlining + const_prop chain correctly.
    ///
    /// Setup:
    ///   Offset(x) == x + 10
    ///   Main == Offset(5)
    ///
    /// After inlining: Main == 5 + 10
    /// After const_prop: Main == 15
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inline_then_const_prop_chains() {
        let offset = make_operator(
            "Offset",
            vec!["x"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("x")),
                op: TirArithOp::Add,
                right: Box::new(int_const(10)),
            }),
        );

        let main = TirOperator {
            name: "MainChain".to_string(),
            name_id: intern_name("MainChain"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("Offset")),
                args: vec![int_const(5)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![offset, main],
        };

        // Before: Main body is Apply(Offset, 5).
        assert!(matches!(
            &module.operators[1].body.node,
            TirExpr::Apply { .. }
        ));

        let config = JitPreprocessConfig::default();
        let stats = preprocess_tir_for_jit(&mut module, &config);

        // After: inlining turned Apply(Offset, 5) -> 5 + 10,
        // then const_prop folded 5 + 10 -> 15.
        assert_eq!(
            stats.inlining.call_sites_replaced, 1,
            "Offset should be inlined"
        );
        assert!(stats.const_prop.arith_folds >= 1, "5 + 10 should be folded");

        match &module.operators[1].body.node {
            TirExpr::Const {
                value,
                ty: TirType::Int,
            } => {
                assert_eq!(value.as_i64(), Some(15), "Offset(5) should fold to 15");
            }
            other => panic!("expected Const(15), got: {other:?}"),
        }
    }

    /// Verify that `inline_and_compile` produces folded bytecode.
    /// After inlining+const_prop, a constant operator should compile to
    /// a simple LoadConst in bytecode.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_inline_and_compile_with_const_prop() {
        let offset2 = make_operator(
            "Offset2",
            vec!["x"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("x")),
                op: TirArithOp::Add,
                right: Box::new(int_const(100)),
            }),
        );

        let main = TirOperator {
            name: "MainCompile".to_string(),
            name_id: intern_name("MainCompile"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("Offset2")),
                args: vec![int_const(42)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![offset2, main],
        };

        let config = JitPreprocessConfig::default();
        let (chunk, stats) = inline_and_compile(&mut module, &config).expect("compile failed");

        assert_eq!(stats.inlining.call_sites_replaced, 1);
        assert!(stats.const_prop.arith_folds >= 1);

        // The compiled function should be JIT-eligible (no Call opcodes).
        let main_func = find_function(&chunk, "MainCompile");
        assert!(
            check_eligibility(main_func).is_ok(),
            "MainCompile should be eligible after inline+const_prop+compile"
        );
    }

    /// Verify the backward-compatible type alias works.
    #[test]
    fn test_jit_inlining_config_alias() {
        let config: JitInliningConfig = JitInliningConfig::default();
        assert_eq!(config.max_inline_size, 30);
        assert!(config.inlining_enabled);
        assert!(config.const_prop_enabled);
    }

    /// Verify PreprocessStats default.
    #[test]
    fn test_preprocess_stats_default() {
        let stats = PreprocessStats::default();
        assert_eq!(stats.inlining, InliningStats::default());
        assert_eq!(stats.const_prop, ConstPropStats::default());
    }
}
