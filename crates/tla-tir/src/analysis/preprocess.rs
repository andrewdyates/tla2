// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared TIR preprocessing pipeline for all downstream consumers.
//!
//! Wraps the inlining and constant propagation passes with consumer-specific
//! configuration presets. Both the JIT compiler and code generator call
//! [`preprocess_tir`] instead of wiring the individual passes themselves.
//!
//! # Consumer presets
//!
//! - **JIT** ([`PreprocessProfile::Jit`]): Aggressive inlining (`max_inline_size=30`)
//!   to eliminate `Apply` nodes that would produce `Call` opcodes and fail the
//!   JIT eligibility gate. Constant propagation is always enabled.
//!
//! - **Codegen** ([`PreprocessProfile::Codegen`]): Moderate inlining (`max_inline_size=15`)
//!   for readability — inlined bodies become part of generated Rust source, so
//!   excessively large inline expansions hurt readability without proportional
//!   benefit. Constant propagation is always enabled.
//!
//! - **Custom** ([`PreprocessProfile::Custom`]): User-supplied thresholds for
//!   testing and experimentation.
//!
//! Part of #3931.

use crate::analysis::const_prop::{const_prop_expr, ConstPropStats};
use crate::analysis::inlining::{inline_functions, InliningConfig, InliningStats};
use crate::lower::TirModule;
use crate::nodes::TirExpr;
use crate::types::TirType;
use tla_core::span::Span;
use tla_core::Spanned;

/// Consumer-specific preprocessing profile.
///
/// Selects default thresholds appropriate for the downstream consumer.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PreprocessProfile {
    /// Aggressive inlining for JIT compilation.
    ///
    /// Higher `max_inline_size` (30) because eliminating even moderately-sized
    /// operators is worthwhile when the alternative is falling back to the
    /// interpreter for the entire function.
    Jit,

    /// Moderate inlining for Rust code generation.
    ///
    /// Lower `max_inline_size` (15) because inlined bodies become part of
    /// generated Rust source. Very large inline expansions hurt readability
    /// without proportional benefit.
    Codegen,

    /// Custom thresholds for testing and experimentation.
    Custom {
        /// Maximum TIR expression nodes for an inline candidate.
        max_inline_size: usize,
        /// Whether inlining is enabled.
        inlining_enabled: bool,
        /// Whether constant propagation is enabled.
        const_prop_enabled: bool,
    },
}

impl PreprocessProfile {
    /// Resolve the profile to concrete configuration values.
    fn resolve(&self) -> ResolvedConfig {
        match self {
            PreprocessProfile::Jit => ResolvedConfig {
                max_inline_size: 30,
                inlining_enabled: true,
                const_prop_enabled: true,
            },
            PreprocessProfile::Codegen => ResolvedConfig {
                max_inline_size: 15,
                inlining_enabled: true,
                const_prop_enabled: true,
            },
            PreprocessProfile::Custom {
                max_inline_size,
                inlining_enabled,
                const_prop_enabled,
            } => ResolvedConfig {
                max_inline_size: *max_inline_size,
                inlining_enabled: *inlining_enabled,
                const_prop_enabled: *const_prop_enabled,
            },
        }
    }
}

/// Resolved preprocessing configuration values.
struct ResolvedConfig {
    max_inline_size: usize,
    inlining_enabled: bool,
    const_prop_enabled: bool,
}

/// Combined statistics from inlining and constant propagation passes.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PreprocessResult {
    /// Statistics from the inlining pass.
    pub inlining: InliningStats,
    /// Aggregated statistics from constant propagation across all operators.
    pub const_prop: ConstPropStats,
}

/// Run the shared TIR preprocessing pipeline on a module.
///
/// Pipeline order: **inline** (inter-procedural) -> **const_prop** (per-operator).
/// Const prop runs after inlining so that expressions exposed by inlining
/// (e.g. `Double(5)` inlined to `5 + 5`) are also folded.
///
/// # Arguments
///
/// * `module` - The TIR module to optimize. Modified in place.
/// * `profile` - The consumer preset controlling thresholds.
///
/// # Returns
///
/// Combined statistics from both passes.
pub fn preprocess_tir(module: &mut TirModule, profile: &PreprocessProfile) -> PreprocessResult {
    let config = profile.resolve();
    let mut result = PreprocessResult::default();

    // Step 1: Inlining (inter-procedural).
    if config.inlining_enabled {
        let inline_config = InliningConfig {
            max_inline_size: config.max_inline_size,
        };
        result.inlining = inline_functions(module, &inline_config);
    }

    // Step 2: Constant propagation (per-operator).
    if config.const_prop_enabled {
        for op in &mut module.operators {
            // Swap out body, fold, swap back.
            let body = std::mem::replace(
                &mut op.body,
                Spanned::new(
                    TirExpr::Const {
                        value: tla_value::Value::bool(false),
                        ty: TirType::Bool,
                    },
                    Span::new(tla_core::span::FileId(0), 0, 0),
                ),
            );
            let (folded, cp_stats) = const_prop_expr(body);
            op.body = folded;

            // Aggregate stats.
            result.const_prop.arith_folds += cp_stats.arith_folds;
            result.const_prop.bool_folds += cp_stats.bool_folds;
            result.const_prop.cmp_folds += cp_stats.cmp_folds;
            result.const_prop.if_simplifications += cp_stats.if_simplifications;
            result.const_prop.let_propagations += cp_stats.let_propagations;
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower::{TirModule, TirOperator};
    use crate::nodes::*;
    use crate::types::TirType;
    use tla_core::intern_name;
    use tla_core::span::{FileId, Span};
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

    fn name_ident(name: &str) -> Spanned<TirExpr> {
        spanned(TirExpr::Name(TirNameRef {
            name: name.to_string(),
            name_id: intern_name(name),
            kind: TirNameKind::Ident,
            ty: TirType::Dyn,
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

    /// JIT profile uses aggressive inlining (max_inline_size=30).
    #[test]
    fn test_jit_profile_inlines_medium_ops() {
        let double = make_operator(
            "DoubleJit",
            vec!["x"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("x")),
                op: TirArithOp::Add,
                right: Box::new(name_ident("x")),
            }),
        );

        let main = TirOperator {
            name: "MainJit".to_string(),
            name_id: intern_name("MainJit"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("DoubleJit")),
                args: vec![int_const(5)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![double, main],
        };

        let result = preprocess_tir(&mut module, &PreprocessProfile::Jit);
        assert_eq!(
            result.inlining.call_sites_replaced, 1,
            "JIT profile should inline"
        );
    }

    /// Codegen profile uses moderate inlining (max_inline_size=15).
    #[test]
    fn test_codegen_profile_inlines_small_ops() {
        let double = make_operator(
            "DoubleCg",
            vec!["x"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("x")),
                op: TirArithOp::Add,
                right: Box::new(name_ident("x")),
            }),
        );

        let main = TirOperator {
            name: "MainCg".to_string(),
            name_id: intern_name("MainCg"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("DoubleCg")),
                args: vec![int_const(5)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![double, main],
        };

        let result = preprocess_tir(&mut module, &PreprocessProfile::Codegen);
        assert_eq!(
            result.inlining.call_sites_replaced, 1,
            "Codegen profile should inline small ops"
        );
    }

    /// Custom profile with inlining disabled.
    #[test]
    fn test_custom_profile_no_inlining() {
        let double = make_operator(
            "DoubleCust",
            vec!["x"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("x")),
                op: TirArithOp::Add,
                right: Box::new(name_ident("x")),
            }),
        );

        let main = TirOperator {
            name: "MainCust".to_string(),
            name_id: intern_name("MainCust"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("DoubleCust")),
                args: vec![int_const(5)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![double, main],
        };

        let profile = PreprocessProfile::Custom {
            max_inline_size: 20,
            inlining_enabled: false,
            const_prop_enabled: true,
        };
        let result = preprocess_tir(&mut module, &profile);
        assert_eq!(
            result.inlining.call_sites_replaced, 0,
            "inlining should be disabled"
        );
    }

    /// Codegen profile threshold rejects large operators.
    #[test]
    fn test_codegen_profile_rejects_large_ops() {
        // Build a body that's >15 nodes but <=30 nodes.
        // 16 nodes total: the ArithNeg wrapper on one leaf pushes it past 15.
        // Inliner uses `size > max_inline_size`, so 16 > 15 is true (rejected).
        let big_body = spanned(TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::ArithBinOp {
                    left: Box::new(name_ident("x")),
                    op: TirArithOp::Add,
                    right: Box::new(name_ident("x")),
                })),
                op: TirArithOp::Add,
                right: Box::new(spanned(TirExpr::ArithBinOp {
                    left: Box::new(name_ident("x")),
                    op: TirArithOp::Add,
                    right: Box::new(name_ident("x")),
                })),
            })),
            op: TirArithOp::Add,
            right: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(spanned(TirExpr::ArithBinOp {
                    left: Box::new(name_ident("x")),
                    op: TirArithOp::Mul,
                    right: Box::new(spanned(TirExpr::ArithNeg(Box::new(name_ident("x"))))),
                })),
                op: TirArithOp::Sub,
                right: Box::new(spanned(TirExpr::ArithBinOp {
                    left: Box::new(name_ident("x")),
                    op: TirArithOp::Mul,
                    right: Box::new(name_ident("x")),
                })),
            })),
        });

        let big_op = make_operator("BigOp", vec!["x"], big_body);
        let main = TirOperator {
            name: "MainBig".to_string(),
            name_id: intern_name("MainBig"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("BigOp")),
                args: vec![int_const(1)],
            }),
        };

        let mut cg_module = TirModule {
            name: "Test".to_string(),
            operators: vec![big_op.clone(), main.clone()],
        };
        let cg_result = preprocess_tir(&mut cg_module, &PreprocessProfile::Codegen);

        let mut jit_module = TirModule {
            name: "Test".to_string(),
            operators: vec![big_op, main],
        };
        let jit_result = preprocess_tir(&mut jit_module, &PreprocessProfile::Jit);

        // 16 nodes: codegen (max=15) rejects (16 > 15), JIT (max=30) accepts (16 <= 30)
        assert_eq!(
            cg_result.inlining.call_sites_replaced, 0,
            "Codegen should reject 16-node operator (16 > 15)"
        );
        assert_eq!(
            jit_result.inlining.call_sites_replaced, 1,
            "JIT should accept 16-node operator (16 <= 30)"
        );
    }

    /// Const prop chains with inlining.
    #[test]
    fn test_inline_then_const_prop() {
        let offset = make_operator(
            "OffsetPP",
            vec!["x"],
            spanned(TirExpr::ArithBinOp {
                left: Box::new(name_ident("x")),
                op: TirArithOp::Add,
                right: Box::new(int_const(10)),
            }),
        );

        let main = TirOperator {
            name: "MainPP".to_string(),
            name_id: intern_name("MainPP"),
            params: vec![],
            is_recursive: false,
            body: spanned(TirExpr::Apply {
                op: Box::new(name_ident("OffsetPP")),
                args: vec![int_const(5)],
            }),
        };

        let mut module = TirModule {
            name: "Test".to_string(),
            operators: vec![offset, main],
        };

        let result = preprocess_tir(&mut module, &PreprocessProfile::Jit);
        assert_eq!(result.inlining.call_sites_replaced, 1);
        assert!(result.const_prop.arith_folds >= 1);

        // Main body should be folded to 15.
        match &module.operators[1].body.node {
            TirExpr::Const { value, .. } => {
                assert_eq!(value.as_i64(), Some(15));
            }
            other => panic!("expected Const(15), got: {other:?}"),
        }
    }
}
