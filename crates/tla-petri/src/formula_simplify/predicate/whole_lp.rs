// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tier 6: whole-predicate LP proofs (conjunction-level).

use crate::formula_simplify::SimplificationContext;
use crate::lp_state_equation::{lp_always_true, lp_unreachable};
use crate::property_xml::StatePredicate;
use crate::resolved_predicate::{count_unresolved_with_aliases, resolve_predicate_with_aliases};

/// If the predicate is fully resolved (no unresolved names), try:
/// - `lp_unreachable(φ)` → the predicate is never satisfiable → False
/// - `lp_always_true(φ)` → the predicate always holds → True
pub(super) fn lp_prove(pred: &StatePredicate, ctx: &SimplificationContext<'_>) -> StatePredicate {
    if matches!(pred, StatePredicate::True | StatePredicate::False) {
        return pred.clone();
    }

    let (_total_names, unresolved_count) = count_unresolved_with_aliases(pred, ctx.aliases);
    if unresolved_count > 0 {
        return pred.clone();
    }

    let resolved = resolve_predicate_with_aliases(pred, ctx.aliases);

    if lp_unreachable(ctx.net, &resolved) {
        return StatePredicate::False;
    }

    if lp_always_true(ctx.net, &resolved) {
        return StatePredicate::True;
    }

    pred.clone()
}
