// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Symmetry reduction: value permutation for model values.
//!
//! Provides `permute` (FuncValue-based) and `permute_fast` (MVPerm-based, O(1) lookup)
//! for applying permutations to all model values within a composite value.
//!
//! Both methods share a single generic implementation via the `PermLookup` trait,
//! which abstracts over the permutation lookup strategy.

use super::{FuncValue, IntIntervalFunc, MVPerm, RecordValue, Value};
use std::sync::Arc;

/// Trait abstracting permutation lookup for model values.
///
/// `FuncValue` provides O(log n) lookup via sorted entries; `MVPerm` provides
/// O(1) lookup via array indexing. Both return `None` when the value is unchanged
/// (identity mapping or not in domain).
pub(crate) trait PermLookup {
    /// Apply this permutation to a model value name.
    /// Returns `Some(permuted_value)` if the value changes, `None` if unchanged.
    fn apply_to_model_value(&self, name: &Arc<str>) -> Option<Value>;
}

impl PermLookup for FuncValue {
    fn apply_to_model_value(&self, name: &Arc<str>) -> Option<Value> {
        let mv = Value::ModelValue(name.clone());
        if let Some(permuted) = self.mapping_get(&mv) {
            if permuted != &mv {
                Some(permuted.clone())
            } else {
                None // Permuted to itself
            }
        } else {
            None // Not in permutation domain
        }
    }
}

impl PermLookup for MVPerm {
    fn apply_to_model_value(&self, name: &Arc<str>) -> Option<Value> {
        self.apply(name)
            .map(|permuted_name| Value::ModelValue(Arc::clone(permuted_name)))
    }
}

impl Value {
    // === Symmetry: Value permutation ===

    /// Apply a permutation function to all model values in this value.
    /// The permutation should be a function from model values to model values.
    /// Used for symmetry reduction in model checking.
    ///
    /// TLC optimization: Returns self (cheap Arc bump) when permutation doesn't
    /// change the value. This avoids allocating new collections when most values
    /// are unchanged by a permutation.
    pub fn permute(&self, perm: &FuncValue) -> Value {
        match self.permute_impl(perm) {
            Some(v) => v,         // Changed - return new value
            None => self.clone(), // Unchanged - cheap Arc bump
        }
    }

    /// Apply a permutation using MVPerm for O(1) model value lookup (Part of #358).
    ///
    /// This is 10x faster than `permute()` for specs with many model values
    /// because it uses array indexing instead of binary search.
    pub fn permute_fast(&self, perm: &MVPerm) -> Value {
        match self.permute_impl(perm) {
            Some(v) => v,         // Changed - return new value
            None => self.clone(), // Unchanged - cheap Arc bump
        }
    }

    /// Generic inner permute: returns None if unchanged, Some(v) if changed.
    /// This enables TLC's allocation-avoidance optimization.
    fn permute_impl<P: PermLookup>(&self, perm: &P) -> Option<Value> {
        match self {
            // Primitive values never change
            Value::Bool(_) | Value::SmallInt(_) | Value::Int(_) | Value::String(_) => None,

            // Model values: apply the permutation
            Value::ModelValue(name) => perm.apply_to_model_value(name),

            // Sets: permute all elements, track changes
            Value::Set(s) => {
                let mut changed = false;
                let permuted: Vec<Value> = s
                    .raw_slice() // O(1) — no normalization; permutation is a bijection
                    .iter()
                    .map(|v| match v.permute_impl(perm) {
                        Some(new_v) => {
                            changed = true;
                            new_v
                        }
                        None => v.clone(),
                    })
                    .collect();
                if changed {
                    Some(Value::set(permuted))
                } else {
                    None
                }
            }

            // Sequences: permute all elements, track changes
            Value::Seq(s) => {
                let mut changed = false;
                let permuted: Vec<Value> = s
                    .iter()
                    .map(|v| match v.permute_impl(perm) {
                        Some(new_v) => {
                            changed = true;
                            new_v
                        }
                        None => v.clone(),
                    })
                    .collect();
                if changed {
                    Some(Value::Seq(Arc::new(permuted.into())))
                } else {
                    None
                }
            }

            // Tuples: permute all elements, track changes
            Value::Tuple(t) => {
                let mut changed = false;
                let permuted: Vec<Value> = t
                    .iter()
                    .map(|v| match v.permute_impl(perm) {
                        Some(new_v) => {
                            changed = true;
                            new_v
                        }
                        None => v.clone(),
                    })
                    .collect();
                if changed {
                    Some(Value::Tuple(permuted.into()))
                } else {
                    None
                }
            }

            // Records: permute all field values (NameId keys unchanged)
            Value::Record(r) => {
                let mut changed = false;
                let permuted: RecordValue = r
                    .iter()
                    .map(|(k, v)| match v.permute_impl(perm) {
                        Some(new_v) => {
                            changed = true;
                            (k, new_v)
                        }
                        None => (k, v.clone()),
                    })
                    .collect();
                if changed {
                    Some(Value::Record(permuted))
                } else {
                    None
                }
            }

            // Functions: permute both keys and values, collect into sorted entries
            Value::Func(f) => {
                let mut key_changed = false;
                let mut any_changed = false;

                let mut permuted_entries: Vec<(Value, Value)> = f
                    .mapping_iter()
                    .map(|(k, v)| {
                        let new_k = match k.permute_impl(perm) {
                            Some(new_v) => {
                                key_changed = true;
                                any_changed = true;
                                new_v
                            }
                            None => k.clone(),
                        };
                        let new_v = match v.permute_impl(perm) {
                            Some(new_v) => {
                                any_changed = true;
                                new_v
                            }
                            None => v.clone(),
                        };
                        (new_k, new_v)
                    })
                    .collect();

                if any_changed {
                    // Only sort if keys changed; if only values changed,
                    // the original sorted key order is preserved.
                    if key_changed {
                        permuted_entries.sort_by(|a, b| a.0.cmp(&b.0));
                    }
                    Some(Value::Func(Arc::new(FuncValue::from_sorted_entries(
                        permuted_entries,
                    ))))
                } else {
                    None
                }
            }

            // IntFunc: domain is integers (unchanged), permute only values
            Value::IntFunc(f) => {
                let mut changed = false;
                let permuted_values: Vec<Value> = f
                    .values
                    .iter()
                    .map(|v| match v.permute_impl(perm) {
                        Some(new_v) => {
                            changed = true;
                            new_v
                        }
                        None => v.clone(),
                    })
                    .collect();
                if changed {
                    Some(Value::IntFunc(Arc::new(IntIntervalFunc::new(
                        f.min,
                        f.max,
                        permuted_values,
                    ))))
                } else {
                    None
                }
            }

            // Intervals are integers, no model values
            Value::Interval(_) => None,

            // Other lazy types: convert to concrete and permute
            // Note: For efficiency, symmetry should be applied to states which
            // typically have concrete values, not lazy sets
            Value::Subset(sv) => {
                if let Some(set) = sv.to_sorted_set() {
                    let mut changed = false;
                    let permuted: Vec<Value> = set
                        .raw_slice()
                        .iter()
                        .map(|v| match v.permute_impl(perm) {
                            Some(new_v) => {
                                changed = true;
                                new_v
                            }
                            None => v.clone(),
                        })
                        .collect();
                    if changed {
                        Some(Value::set(permuted))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }

            // These lazy types typically shouldn't appear in states
            Value::FuncSet(_)
            | Value::RecordSet(_)
            | Value::TupleSet(_)
            | Value::SetCup(_)
            | Value::SetCap(_)
            | Value::SetDiff(_)
            | Value::SetPred(_)
            | Value::KSubset(_)
            | Value::BigUnion(_)
            | Value::StringSet
            | Value::AnySet
            | Value::SeqSet(_)
            | Value::LazyFunc(_)
            | Value::Closure(_) => None,
        }
    }
}
