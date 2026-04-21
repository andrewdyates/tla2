// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tier 2: pure boolean folding.

use crate::property_xml::StatePredicate;

/// Pure boolean folding.
///
/// - `And(…, False, …)` → False
/// - `And(…, True, …)` → drop the True
/// - `Or(…, True, …)` → True
/// - `Or(…, False, …)` → drop the False
/// - `Not(True)` → False, `Not(False)` → True
/// - Singleton `And`/`Or` → unwrap
/// - Empty `And` → True, empty `Or` → False
pub(crate) fn boolean_fold(pred: &StatePredicate) -> StatePredicate {
    match pred {
        StatePredicate::And(children) => {
            let mut filtered = Vec::with_capacity(children.len());
            for child in children {
                match child {
                    StatePredicate::False => return StatePredicate::False,
                    StatePredicate::True => {} // drop
                    other => filtered.push(other.clone()),
                }
            }
            match filtered.len() {
                0 => StatePredicate::True,
                1 => filtered.into_iter().next().unwrap(),
                _ => StatePredicate::And(filtered),
            }
        }
        StatePredicate::Or(children) => {
            let mut filtered = Vec::with_capacity(children.len());
            for child in children {
                match child {
                    StatePredicate::True => return StatePredicate::True,
                    StatePredicate::False => {} // drop
                    other => filtered.push(other.clone()),
                }
            }
            match filtered.len() {
                0 => StatePredicate::False,
                1 => filtered.into_iter().next().unwrap(),
                _ => StatePredicate::Or(filtered),
            }
        }
        StatePredicate::Not(inner) => match inner.as_ref() {
            StatePredicate::True => StatePredicate::False,
            StatePredicate::False => StatePredicate::True,
            StatePredicate::Not(double_inner) => double_inner.as_ref().clone(),
            _ => pred.clone(),
        },
        _ => pred.clone(),
    }
}
