// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for liveness consistency checking.

use super::*;
use crate::liveness::test_helpers::empty_successors;
use crate::liveness::LiveExpr;
use crate::Value;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;

mod basics;
mod enabled;
mod transition;
