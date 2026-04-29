// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TIR integration for the sequential model checker.
//!
//! Three modes:
//! - **Default** (no env vars): TIR eval=all is the default sequential
//!   evaluation path. Part of #3323.
//! - **Parity** (`TLA2_TIR_PARITY`): shadow-check both AST and TIR paths,
//!   assert results match. Used for validation.
//! - **Eval** (`TLA2_TIR_EVAL`): use TIR as the primary evaluator for
//!   selected operators. AST path is bypassed.
//!
//! Part of #3354: `TLA2_LEGACY_EVAL` removed — TIR is the sole evaluation
//! path. The AST tree-walker is still used internally by TIR for unsupported
//! expression forms, but no env var can disable TIR at the top level.

use super::{ArrayState, CheckError, EvalCtx, ModelChecker, Module, Value};
use crate::EvalCheckError;
use rustc_hash::FxHashSet;
use tla_eval::tir::{TirProgram, TirProgramCaches};
use tla_value::error::{EvalError, EvalResult};

mod checker;
mod program;
mod state;
#[cfg(test)]
mod tests;

pub(super) use state::TirParityState;
// TirMode only consumed by tests (struct initialization in test fixtures).
#[cfg(test)]
pub(super) use state::TirMode;
