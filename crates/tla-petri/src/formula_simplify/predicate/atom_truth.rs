// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tier 1: per-atom LP truth for IntLe leaves.

use crate::formula_simplify::SimplificationContext;
use crate::property_xml::StatePredicate;

/// Resolves individual `IntLe` atoms to `True` or `False` via the cached
/// LP atom truth layer. Non-IntLe predicates pass through unchanged.
pub(super) fn simplify_int_le_atom(
    pred: &StatePredicate,
    ctx: &mut SimplificationContext<'_>,
) -> StatePredicate {
    if let StatePredicate::IntLe(..) = pred {
        if let Some(truth) = ctx.resolve_and_query_atom(pred) {
            return if truth {
                StatePredicate::True
            } else {
                StatePredicate::False
            };
        }
    }
    pred.clone()
}
