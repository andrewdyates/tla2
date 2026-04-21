// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared helper functions for binary set operations.

use super::super::super::*;

/// Filter an iterator by a membership predicate, collecting matching values.
///
/// Phase 1A (#3073): Vec-based alternative to `filter_by_membership` that avoids
/// im::OrdSet B-tree insertion overhead. Callers hand the collected values to
/// `SortedSet::from_iter()`, which normalizes lazily if the source iterator
/// was not already sorted and deduplicated.
pub(crate) fn filter_to_vec(
    iter: Box<dyn Iterator<Item = Value> + '_>,
    pred: impl Fn(&Value) -> Option<bool>,
) -> Option<Vec<Value>> {
    let mut result = Vec::new();
    for v in iter {
        match pred(&v) {
            Some(true) => {
                result.push(v);
            }
            Some(false) => {}
            None => return None,
        }
    }
    Some(result)
}

/// Check if all elements from an iterator are members of a set.
/// Returns None if any membership check is indeterminate (e.g. SetPred).
pub(crate) fn all_in_set<'a>(iter: impl Iterator<Item = &'a Value>, set: &Value) -> Option<bool> {
    for elem in iter {
        match set.set_contains(elem) {
            Some(true) => {}
            Some(false) => return Some(false),
            None => return None,
        }
    }
    Some(true)
}
