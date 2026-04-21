// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array-based successor state for ENABLED constraint propagation.
//!
//! Flat array indexed by variable ordinal. O(1) bind, O(1) lookup, O(k) clone
//! where k is the number of state variables (typically 5-20).
//!
//! TLC reference: `TLCStateFun.java:28-60` — uses `Value[] values` array.
//!
//! Part of #3365: Replaces linked-list WitnessState to eliminate per-bind Arc
//! allocation and per-eval HashMap construction overhead.

use tla_value::Value;

/// Array-based successor state accumulating primed variable bindings.
///
/// Each slot corresponds to a state variable (indexed by `VarRegistry` ordinal).
/// `None` = unbound, `Some(v)` = bound to value `v`.
///
/// Part of #3004: ENABLED constraint propagation decision procedure.
/// Part of #3365: Converted from linked-list to flat array.
#[derive(Clone)]
pub(crate) struct WitnessState {
    /// One slot per state variable, indexed by var_idx.
    values: Box<[Option<Value>]>,
}

impl WitnessState {
    /// Create an empty witness with `num_vars` unbound slots.
    pub(crate) fn new(num_vars: usize) -> Self {
        WitnessState {
            values: vec![None; num_vars].into_boxed_slice(),
        }
    }

    /// True if no variables are bound.
    pub(crate) fn is_empty(&self) -> bool {
        self.values.iter().all(|v| v.is_none())
    }

    /// Bind a primed variable. O(k) — clones the array and sets one slot.
    ///
    /// TLC reference: `TLCStateFun.bind()` at `TLCStateFun.java:47-49`
    pub(crate) fn bind(&self, var_idx: usize, value: Value) -> Self {
        let mut new_values = self.values.clone();
        new_values[var_idx] = Some(value);
        WitnessState { values: new_values }
    }

    /// Look up a primed variable binding. O(1) array index.
    ///
    /// TLC reference: `TLCStateFun.lookup()` at `TLCStateFun.java:55-60`
    pub(crate) fn lookup(&self, target_idx: usize) -> Option<&Value> {
        self.values.get(target_idx)?.as_ref()
    }

    /// Borrow the raw values slice for sparse overlay binding.
    ///
    /// Part of #3365: Used by `eval_in_witness_ctx` to create a
    /// `SparseStateEnvRef` without materializing an `Env` HashMap.
    pub(crate) fn values_slice(&self) -> &[Option<Value>] {
        &self.values
    }

    /// Iterate bound (var_idx, &Value) pairs. Used by eval_in_witness_ctx.
    #[cfg(test)]
    pub(crate) fn bound_pairs(&self) -> impl Iterator<Item = (usize, &Value)> {
        self.values
            .iter()
            .enumerate()
            .filter_map(|(idx, v)| v.as_ref().map(|val| (idx, val)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_witness_state_empty_lookup_returns_none() {
        let ws = WitnessState::new(5);
        assert!(ws.lookup(0).is_none());
        assert!(ws.lookup(4).is_none());
    }

    #[test]
    fn test_witness_state_bind_then_lookup() {
        let ws = WitnessState::new(5);
        let ws = ws.bind(0, Value::int(42));
        assert_eq!(ws.lookup(0), Some(&Value::int(42)));
        assert!(ws.lookup(1).is_none());
    }

    #[test]
    fn test_witness_state_multiple_bindings() {
        let ws = WitnessState::new(5);
        let ws = ws.bind(0, Value::int(1));
        let ws = ws.bind(1, Value::int(2));
        let ws = ws.bind(2, Value::int(3));
        assert_eq!(ws.lookup(0), Some(&Value::int(1)));
        assert_eq!(ws.lookup(1), Some(&Value::int(2)));
        assert_eq!(ws.lookup(2), Some(&Value::int(3)));
    }

    #[test]
    fn test_witness_state_latest_binding_wins() {
        let ws = WitnessState::new(5);
        let ws = ws.bind(0, Value::int(1));
        let ws = ws.bind(0, Value::int(2));
        // Latest binding replaces earlier one
        assert_eq!(ws.lookup(0), Some(&Value::int(2)));
    }

    #[test]
    fn test_witness_state_structural_sharing() {
        let ws1 = WitnessState::new(5);
        let ws2 = ws1.bind(0, Value::int(1));
        let ws3a = ws2.bind(1, Value::int(2));
        let ws3b = ws2.bind(1, Value::int(3));
        // ws3a and ws3b diverge at slot 1
        assert_eq!(ws3a.lookup(1), Some(&Value::int(2)));
        assert_eq!(ws3b.lookup(1), Some(&Value::int(3)));
        // Both see the same binding for var 0
        assert_eq!(ws3a.lookup(0), Some(&Value::int(1)));
        assert_eq!(ws3b.lookup(0), Some(&Value::int(1)));
    }

    #[test]
    fn test_witness_state_is_empty() {
        let ws = WitnessState::new(3);
        assert!(ws.is_empty());
        let ws = ws.bind(0, Value::int(1));
        assert!(!ws.is_empty());
    }

    #[test]
    fn test_witness_state_bound_pairs() {
        let ws = WitnessState::new(5);
        let ws = ws.bind(1, Value::int(10));
        let ws = ws.bind(3, Value::int(30));
        let pairs: Vec<_> = ws.bound_pairs().collect();
        assert_eq!(pairs.len(), 2);
        assert_eq!(pairs[0], (1, &Value::int(10)));
        assert_eq!(pairs[1], (3, &Value::int(30)));
    }
}
