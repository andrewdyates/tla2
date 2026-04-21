// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;
use tla_core::ast::{BoundVar, ModuleTarget};
use tla_core::{FileId, Span};

mod compound_dispatch;
mod conjunct_selection;
mod core;
mod cross_type;
mod div_mod;
mod enumeration;
mod functions;
mod membership;
mod powerset_ops;
mod quantifiers;
mod set_comprehensions;
mod strings;
mod tuple_basics;
mod tuple_semantics;

fn span() -> Span {
    Span::new(FileId(0), 0, 0)
}

fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::new(node, span())
}

/// Helper: shorthand for BigInt::from(n), used throughout tests after z4 API
/// changed int_val() to return Option<&BigInt> instead of Option<i64> (#3048).
fn bi(n: i64) -> BigInt {
    BigInt::from(n)
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_try_check_sat_zero_timeout_reports_timeout_reason() {
    use std::time::Duration;

    let mut trans = Z4Translator::new();
    trans.set_timeout(Some(Duration::ZERO));

    assert_eq!(trans.get_timeout(), Some(Duration::ZERO));
    assert_eq!(trans.try_check_sat().unwrap(), SolveResult::Unknown);
    assert_eq!(
        trans.last_unknown_reason(),
        Some(crate::UnknownReason::Timeout)
    );
}
