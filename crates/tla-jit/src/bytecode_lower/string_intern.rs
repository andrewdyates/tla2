// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bidirectional string interning table for JIT compilation.
//!
//! Maps TLA+ string values to integer IDs so that string equality in
//! JIT-compiled code becomes a single integer comparison. IDs start at 1;
//! 0 is reserved as a sentinel (no valid string maps to 0).

use rustc_hash::FxHashMap;
use std::sync::Arc;

/// Bidirectional string <-> i64 intern table.
///
/// Each unique string is assigned a positive i64 ID. The table supports
/// O(1) lookup in both directions (string -> ID via hash map, ID -> string
/// via index into a Vec).
pub struct StringInternTable {
    str_to_id: FxHashMap<Arc<str>, i64>,
    id_to_str: Vec<Arc<str>>,
}

impl StringInternTable {
    /// Create an empty intern table. IDs start at 1; 0 is reserved.
    #[must_use]
    pub fn new() -> Self {
        StringInternTable {
            str_to_id: FxHashMap::default(),
            id_to_str: Vec::new(),
        }
    }

    /// Return the ID for `s`, interning it if not already present.
    ///
    /// The returned ID is always > 0.
    pub fn get_or_intern(&mut self, s: &Arc<str>) -> i64 {
        if let Some(&id) = self.str_to_id.get(s) {
            return id;
        }
        let id = (self.id_to_str.len() as i64) + 1; // IDs start at 1
        self.id_to_str.push(Arc::clone(s));
        self.str_to_id.insert(Arc::clone(s), id);
        id
    }

    /// Look up the ID for `s` without interning. Returns `None` if `s`
    /// has not been interned.
    #[must_use]
    pub fn get_id(&self, s: &str) -> Option<i64> {
        self.str_to_id.get(s).copied()
    }

    /// Look up the string for a previously returned ID. Returns `None`
    /// if `id` is out of range (including the reserved value 0).
    #[must_use]
    pub fn get_str(&self, id: i64) -> Option<&Arc<str>> {
        if id <= 0 {
            return None;
        }
        self.id_to_str.get((id - 1) as usize)
    }

    /// Number of interned strings.
    #[must_use]
    pub fn len(&self) -> usize {
        self.id_to_str.len()
    }

    /// Returns `true` if no strings have been interned.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.id_to_str.is_empty()
    }
}

impl Default for StringInternTable {
    fn default() -> Self {
        Self::new()
    }
}
