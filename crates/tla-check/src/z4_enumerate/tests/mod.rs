// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z4 init-enumeration tests — split from monolithic tests.rs (1,418 lines, 22 tests)
//!
//! Split into 6 themed files — Part of #2779

use super::*;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use std::collections::HashMap;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::{lower, parse_to_syntax_tree, FileId, Span, Spanned};

use crate::{EvalCtx, State, Value};

fn span() -> Span {
    Span::new(FileId(0), 0, 0)
}

fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::new(node, span())
}

fn state_int_i64(state: &State, var: &str) -> i64 {
    match state.get(var) {
        Some(Value::SmallInt(n)) => *n,
        Some(Value::Int(n)) => n.to_i64().unwrap(),
        other => panic!("expected Int, got {:?}", other),
    }
}

fn value_int_i64(value: &Value) -> i64 {
    match value {
        Value::SmallInt(n) => *n,
        Value::Int(n) => n.to_i64().unwrap(),
        other => panic!("expected Int, got {:?}", other),
    }
}

fn value_is_i64(value: &Value, expected: i64) -> bool {
    match value {
        Value::SmallInt(n) => *n == expected,
        Value::Int(n) => n.to_i64() == Some(expected),
        _ => false,
    }
}

mod basic_constraints;
mod ident_resolution;
mod pre_evaluated_constants;
mod solver_incremental;
mod tuple_membership;
mod type_inference;
