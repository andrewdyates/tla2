// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
#![forbid(unsafe_code)]

//! Typed Intermediate Representation (TIR) for TLA2.
//!
//! TIR is the sole evaluation IR — all expression evaluation routes through TIR
//! since the legacy AST evaluator was removed (#3354). All lowering entry points
//! are **strict constructors**:
//! success means the requested unit was fully lowered; failure means the unit
//! contains expressions outside the current supported slice.
//!
//! The currently supported slice covers:
//!
//! - literals, identifiers, and state variables
//! - module/instance references resolved to concrete operator bodies when a
//!   `TirLoweringEnv` provides the referenced modules
//! - `SubstIn` wrappers eliminated into lowering-time bindings
//! - boolean connectives, comparisons, membership, arithmetic/ranges, and `IF`
//! - `UNCHANGED`, `Prime`
//! - real `[A]_v` / `<<A>>_v` action subscripts
//! - `[]` / `<>` / `~>` / `WF_` / `SF_` / `ENABLED`
//! - `EXCEPT` with index and field path elements, `@` (EXCEPT-AT)
//! - record field access (`r.field`), record/record-set constructors
//! - quantifiers (`\A`, `\E`, `CHOOSE`), `LET`/`IN`, `CASE`
//! - set operations (`{..}`, `\union`, `\intersect`, `\`, `SUBSET`, `UNION`)
//! - set comprehensions (`{x \in S : P}`, `{e : x \in S}`)
//! - functions (`[x \in S |-> e]`, `f[x]`, `DOMAIN`, `[S -> T]`)
//! - tuples (`<<..>>`), cross product (`\X`)
//! - generic operator application (`Apply`)
//! - `LAMBDA` expressions (higher-order closures)
//! - bare operator references (`OpRef`) for higher-order use
//! - labeled subexpressions (`P0:: expr`) — transparent wrappers

pub mod analysis;
pub mod bytecode;
pub mod constraint_gen;
mod error;
mod lower;
pub mod nodes;
pub mod passes;
pub mod preprocess;
pub mod types;
pub mod unify;

pub use analysis::{
    ConstPropStats, ExprClass, InliningConfig, InliningStats, PreprocessProfile, PreprocessResult,
    TirLayout, TirTypeAnalysis, TirTypeInfo, const_prop_expr, inline_functions, preprocess_tir,
    tir_type_to_layout, tir_type_to_rust,
};
pub use constraint_gen::{ConstraintGenerator, TypeEnv};
pub use error::TirLowerError;
pub use lower::{
    lower_expr, lower_expr_with_env, lower_module, lower_module_for_codegen, lower_module_with_env,
    lower_operator, lower_operator_in_instance_scope, lower_operator_with_env,
    lower_operator_with_env_permissive, TirLoweringEnv, TirModule, TirOperator,
};
pub use nodes::{
    StoredTirBody, TirAction, TirActionSubscriptKind, TirArithOp, TirBoolOp, TirBoundPattern,
    TirBoundVar, TirCaseArm, TirCmpOp, TirExceptPathElement, TirExceptSpec, TirExpr, TirFieldName,
    TirLetDef, TirModuleRefSegment, TirNameKind, TirNameRef, TirOperatorRef, TirSetOp, TirTemporal,
};
pub use passes::PassPipeline;
pub use preprocess::PreprocessPipeline;
pub use types::TirType;
pub use unify::{TypeError, TypeScheme, TypeUnifier};
