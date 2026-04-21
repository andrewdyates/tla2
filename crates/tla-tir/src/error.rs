// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use thiserror::Error;
use tla_core::Span;

/// Lowering errors for the current supported TIR slice.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum TirLowerError {
    #[error("unsupported AST expression `{kind}` at {span:?}")]
    UnsupportedExpr { kind: &'static str, span: Span },

    #[error(
        "invalid action-subscript bridge at {span:?}; marked spans must have canonical lowered `[A]_v` or `<<A>>_v` shape"
    )]
    InvalidActionSubscriptBridge { span: Span },

    #[error(
        "invalid chained module target at {span:?}; chained INSTANCE/module targets must be built from nested module references"
    )]
    InvalidChainedTarget { span: Span },

    #[error("undefined TLA+ module or named instance `{name}` during TIR lowering at {span:?}")]
    UndefinedModule { name: String, span: Span },

    #[error(
        "undefined operator `{module}!{operator}` during TIR lowering at {span:?}; TIR lowering requires the referenced body to be available in the lowering environment"
    )]
    UndefinedOperator {
        module: String,
        operator: String,
        span: Span,
    },

    #[error(
        "arity mismatch for `{module}!{operator}` during TIR lowering at {span:?}: expected {expected}, got {got}"
    )]
    ArityMismatch {
        module: String,
        operator: String,
        expected: usize,
        got: usize,
        span: Span,
    },

    #[error(
        "operator body for `{module}!{operator}` is not an INSTANCE definition at {span:?}; INSTANCE-chain lowering only traverses operators whose bodies resolve to INSTANCE expressions"
    )]
    ExpectedInstance {
        module: String,
        operator: String,
        span: Span,
    },

    #[error(
        "recursive INSTANCE/module reference `{module}!{operator}` encountered during TIR lowering at {span:?}"
    )]
    RecursiveModuleRef {
        module: String,
        operator: String,
        span: Span,
    },

    #[error(
        "`@` (EXCEPT-AT) used outside an EXCEPT value subtree at {span:?}; `@` is only valid inside EXCEPT right-hand-side expressions"
    )]
    InvalidExceptAt { span: Span },
}
