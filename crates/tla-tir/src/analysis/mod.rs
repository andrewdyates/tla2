// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Static analysis passes over TIR expressions.
//!
//! These analyses run once at spec load time and produce information that
//! downstream consumers (JIT compiler, code generator, symbolic engine) can
//! use without re-deriving independently.

pub mod const_prop;
pub mod inlining;
pub mod partial_eval;
pub mod preprocess;
pub mod type_bridge;
pub mod type_inference;

pub use const_prop::{const_prop_expr, ConstPropStats};
pub use inlining::{inline_functions, InliningConfig, InliningStats};
pub use partial_eval::{
    partial_eval_expr, partial_eval_module, partial_eval_operator, ConstantEnv, PartialEvalStats,
};
pub use preprocess::{preprocess_tir, PreprocessProfile, PreprocessResult};
pub use type_bridge::{tir_type_to_layout, tir_type_to_rust, TirLayout, TirTypeAnalysis};
pub use type_inference::{ExprClass, TirTypeInfo};
