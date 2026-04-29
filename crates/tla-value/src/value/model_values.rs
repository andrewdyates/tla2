// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use dashmap::DashMap;
use std::sync::atomic::{AtomicU16, Ordering};
use std::sync::{Arc, OnceLock};

use super::{strings::intern_string, FuncValue, Value};
use crate::error::EvalError;

/// Global model value registry: maps model value name (Arc<str>) to index.
/// Index 0 is reserved for "not found".
static MODEL_VALUE_REGISTRY: OnceLock<DashMap<Arc<str>, u16>> = OnceLock::new();

/// Next available model value index (starts at 1, 0 is reserved).
static MODEL_VALUE_NEXT_INDEX: AtomicU16 = AtomicU16::new(1);

/// Maximum number of model values supported (u16::MAX - 1 = 65534).
const MODEL_VALUE_MAX: u16 = u16::MAX - 1;

/// Get the model value registry, initializing if needed.
#[inline]
fn get_model_value_registry() -> &'static DashMap<Arc<str>, u16> {
    MODEL_VALUE_REGISTRY.get_or_init(DashMap::new)
}

/// Get or assign an index for a model value name.
///
/// Returns the existing index if the model value was previously registered,
/// or assigns a new index if this is a new model value.
///
/// Returns `Err(EvalError::Internal)` if more than 65534 model values are created.
#[inline]
pub fn get_or_assign_model_value_index(name: &Arc<str>) -> Result<u16, EvalError> {
    let registry = get_model_value_registry();

    // Fast path: already registered
    if let Some(idx) = registry.get(name) {
        return Ok(*idx.value());
    }

    // Slow path: assign new index
    let idx = MODEL_VALUE_NEXT_INDEX.fetch_add(1, Ordering::Relaxed);
    if idx > MODEL_VALUE_MAX {
        return Err(EvalError::Internal {
            message: format!("Too many model values (max {MODEL_VALUE_MAX})"),
            span: None,
        });
    }

    // Use entry API to handle concurrent registration
    Ok(*registry.entry(Arc::clone(name)).or_insert(idx))
}

/// Look up a model value's index without assigning one if missing.
/// Returns None if the model value is not registered.
#[inline]
pub fn lookup_model_value_index(name: &Arc<str>) -> Option<u16> {
    get_model_value_registry().get(name).map(|r| *r.value())
}

/// Get the current number of registered model values.
#[inline]
pub fn model_value_count() -> u16 {
    MODEL_VALUE_NEXT_INDEX
        .load(Ordering::Relaxed)
        .saturating_sub(1)
}

/// Clear the model value registry and reset the index counter.
///
/// Call between model checking runs to free memory and ensure a clean
/// namespace. Existing `MVPerm` values and model value indices become
/// invalid after this call.
///
/// Part of #1331: memory safety audit — unbounded intern tables.
pub fn clear_model_value_registry() {
    if let Some(registry) = MODEL_VALUE_REGISTRY.get() {
        registry.clear();
    }
    MODEL_VALUE_NEXT_INDEX.store(1, Ordering::Relaxed);
}

/// Create an interned ModelValue.
///
/// Uses the string intern table to ensure pointer equality for repeated model values.
/// Also registers the model value in the global registry for O(1) permutation lookup.
///
/// Returns `Err(EvalError::Internal)` if the model value limit is exceeded.
#[inline]
pub fn interned_model_value(s: &str) -> Result<Value, EvalError> {
    let name = intern_string(s);
    // Register for O(1) permutation lookup (Part of #358)
    get_or_assign_model_value_index(&name)?;
    Ok(Value::ModelValue(name))
}

/// Model value permutation with O(1) lookup.
///
/// Stores permutation as an array where index i maps to the permuted model value.
/// Only non-identity mappings are stored (sparse array with None for identity).
#[derive(Clone, Debug)]
pub struct MVPerm {
    /// Array of permuted model values, indexed by original model value index.
    /// elems[i] = Some(name) means model value with index i maps to name.
    /// elems[i] = None means identity (maps to itself).
    elems: Vec<Option<Arc<str>>>,
}

impl MVPerm {
    /// Create an MVPerm from a FuncValue permutation.
    ///
    /// The FuncValue should be a permutation over model values.
    /// Non-model-value entries are ignored.
    pub fn from_func_value(perm: &FuncValue) -> Result<Self, EvalError> {
        let count = model_value_count() as usize + 1;
        let mut elems = vec![None; count.max(16)]; // Pre-allocate reasonable size

        for (k, v) in perm.mapping_iter() {
            if let (Value::ModelValue(k_name), Value::ModelValue(v_name)) = (k, v) {
                // Get index for key, assign if needed
                let idx = get_or_assign_model_value_index(k_name)? as usize;

                // Grow elems if needed
                if idx >= elems.len() {
                    elems.resize(idx + 1, None);
                }

                // Only store non-identity mappings
                if k_name != v_name {
                    elems[idx] = Some(Arc::clone(v_name));
                }
            }
        }

        Ok(MVPerm { elems })
    }

    /// Apply the permutation to a model value.
    ///
    /// Returns the permuted model value name, or None if identity.
    #[inline]
    pub fn apply(&self, name: &Arc<str>) -> Option<&Arc<str>> {
        let idx = lookup_model_value_index(name)? as usize;
        if idx < self.elems.len() {
            self.elems[idx].as_ref()
        } else {
            None // Not in permutation domain - identity
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::EvalError;
    use std::sync::Mutex;

    /// Guard for tests that mutate global MODEL_VALUE_NEXT_INDEX / MODEL_VALUE_REGISTRY.
    /// Cargo runs tests in parallel within the same process; without serialization,
    /// the limit test corrupts the counter for concurrent tests (race on fetch_add).
    static MODEL_VALUE_TEST_LOCK: Mutex<()> = Mutex::new(());

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_model_value_limit_returns_error() {
        let _guard = MODEL_VALUE_TEST_LOCK.lock().unwrap();
        clear_model_value_registry();

        // Set counter to near the limit
        MODEL_VALUE_NEXT_INDEX.store(MODEL_VALUE_MAX, Ordering::Relaxed);

        // The next assignment should succeed (index == MODEL_VALUE_MAX)
        let name: Arc<str> = Arc::from("__test_limit_ok__");
        let result = get_or_assign_model_value_index(&name);
        assert!(result.is_ok(), "index at MODEL_VALUE_MAX should succeed");

        // The next assignment should fail (index > MODEL_VALUE_MAX)
        let name2: Arc<str> = Arc::from("__test_limit_exceeded__");
        let result2 = get_or_assign_model_value_index(&name2);
        assert!(result2.is_err(), "index beyond MODEL_VALUE_MAX should fail");

        match result2 {
            Err(EvalError::Internal { ref message, .. }) => {
                assert!(
                    message.contains("Too many model values"),
                    "error message should mention the limit, got: {message}"
                );
            }
            other => panic!("expected EvalError::Internal, got: {other:?}"),
        }

        // Reset so subsequent tests get clean state
        clear_model_value_registry();
    }

    /// Regression test: is_finite_set() must return false for ALL model values.
    /// Nat/Int/Real are infinite sets → false.
    /// User model values (symmetry elements like p1, p2) are atoms, not sets → false.
    /// TLC: ModelValue is not Enumerable, so isFinite() returns false.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_model_value_is_finite_set_always_false() {
        let _guard = MODEL_VALUE_TEST_LOCK.lock().unwrap();
        clear_model_value_registry();

        use crate::Value;

        // Infinite set model values
        assert!(
            !Value::try_model_value("Nat").unwrap().is_finite_set(),
            "Nat is infinite"
        );
        assert!(
            !Value::try_model_value("Int").unwrap().is_finite_set(),
            "Int is infinite"
        );
        assert!(
            !Value::try_model_value("Real").unwrap().is_finite_set(),
            "Real is infinite"
        );

        // User model values (symmetry elements) are NOT sets at all
        assert!(
            !Value::try_model_value("p1").unwrap().is_finite_set(),
            "p1 is an atom, not a set"
        );
        assert!(
            !Value::try_model_value("a").unwrap().is_finite_set(),
            "user model value 'a' is an atom, not a set"
        );
    }
}
