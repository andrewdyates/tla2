// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
pub(super) use crate::test_support::parse_module_with_id as parse_module;
pub(super) use crate::Config;
pub(super) use tla_core::ast::Expr;
pub(super) use tla_core::FileId;

mod expression_regressions;
mod fixtures;
mod helper_classification;
mod named_instance;

use fixtures::{
    boxed, dummy, inner_named_instance_module, named_instance_config, operator_body,
    outer_named_instance_init_split_module, outer_named_instance_module,
};
