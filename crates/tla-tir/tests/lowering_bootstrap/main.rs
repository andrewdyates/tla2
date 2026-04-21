// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[path = "../common/mod.rs"]
mod common;

mod action_subscripts;
mod expression_nodes;
mod instance_bootstrap;
mod module_lowering;

use common::{
    expect_bool_const, expect_ident, expect_int_const, expect_name, instance_source,
    lower_main_module_with_env, lower_named_operator, lower_named_operator_result,
    lower_named_operator_with_env,
};
use tla_core::ast::{Expr, Substitution, Unit};
use tla_core::{intern_name, lower, parse_to_syntax_tree, FileId, Spanned};
use tla_tir::{
    lower_expr, lower_module, TirActionSubscriptKind, TirArithOp, TirBoolOp, TirCmpOp, TirExpr,
    TirLowerError,
};
