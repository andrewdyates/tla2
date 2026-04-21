// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! AST-to-live conversion tests — split from monolithic tests.rs (2,663 lines, 81 tests)
//!
//! Split into 9 themed files — Part of #2779

use super::core::{debug_instance_resolve, debug_let, debug_resolve, debug_subst, AstToLive};
use super::errors::ConvertError;
use super::reify::{value_is_reifiable_for_substitution, value_to_expr, value_variant_name};
use crate::eval::{eval, EvalCtx};
use crate::liveness::{ExprLevel, LiveExpr};
use crate::Value;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use tla_core::ast::{BoundPattern, BoundVar, CaseArm, Expr};
use tla_core::{ExprFold, Spanned};

use crate::liveness::test_helpers::spanned;
use crate::value::{
    FuncBuilder, IntIntervalFunc, RecordSetValue, SetBuilder, SetCapValue, SetCupValue,
    SetDiffValue, TupleSetValue, UnionValue,
};
use crate::{FuncSetValue, IntervalValue, SubsetValue};
use num_bigint::BigInt;

mod helpers;

mod bounded_quantifiers;
mod bounded_quantifiers_temporal;
mod convert_errors;
mod convert_temporal;
mod convert_temporal_fairness_fallback;
mod current_target_reify;
mod level_and_resolve;
mod regressions;
mod substitution;
mod value_to_expr;
